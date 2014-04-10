(*
  Implementation of formula-parsing.

  @author Stephan Falke

  Copyright 2009-2014 Stephan Falke

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
*)

open Formula

(** General parse exception. *)
exception ParseException of int * string

(* Checks whether the formula f conforms to the signature f. *)
let rec checkFormula signa f =
  match f with
    | True | False -> ()
    | Formula fs -> checkFormulaAux signa fs
and checkFormulaAux signa f =
  List.iter (fun (Atom (s, t, _)) -> TermParse.checkTerm signa s; TermParse.checkTerm signa t) f

exception SortConflictEquality of string
exception SortConflictFormula of string * string * string

let rec formulaOk signa f =
  match f with
    | True | False -> ()
    | Formula fs -> formulaOkAux signa fs
and formulaOkAux signa f =
  List.iter (checkAtom signa) f
and checkAtom signa (Atom (s, t, c)) =
  let lsa = TermParse.sortAssumption signa s
  and rsa = TermParse.sortAssumption signa t
  and csa = getSortAssumption c
  and ls = Term.getSort signa s
  and rs = Term.getSort signa t in
    let lss = TermParse.getSortFor rsa s
    and rss = TermParse.getSortFor lsa t in
      if (rs = "unspec" && rss <> "none" && rss <> ls) ||
         (ls = "unspec" && lss <> "none" && lss <> rs) ||
         (rs <> "unspec" && ls <> "unspec" && ls <> rs) then
        raise (SortConflictEquality (Formula.toString (Formula [ Atom (s, t, c) ])))
      else
      (
        TermParse.agreeAssumptions lsa rsa;
        TermParse.agreeAssumptions lsa csa
      )
and getSortAssumption c =
  let vars = Util.remdup (List.concat (List.map Constraint.getVars c)) in
    List.map (fun v -> (v, "Int")) vars

let rec getSortedFormula signa f =
  match f with
    | True | False -> f
    | Formula fs -> getSortedFormulaAux signa fs
and getSortedFormulaAux signa f =
  Formula (List.map (getSortedAtom signa) f)
and getSortedAtom signa (Atom (s, t, c)) =
  let lsa = TermParse.sortAssumption signa s
  and rsa = TermParse.sortAssumption signa t
  and csa = getSortAssumption c in
    let sa = TermParse.mergeSortAssumptions csa (TermParse.mergeSortAssumptions lsa rsa) in
      let sx = TermParse.getSortedTerm sa s
      and sy = TermParse.getSortedTerm sa t in
        if Term.isVariable sx && (not (Term.isVariable sy)) then
          Atom (Term.createVar (Term.getTopSymbol sx) (Term.getSort signa sy), sy, c)
        else if Term.isVariable sy && (not (Term.isVariable sx)) then
          Atom (sx, Term.createVar (Term.getTopSymbol sy) (Term.getSort signa sx), c)
        else
          Atom (sx, sy, c)

let rec checkUnique f =
  match f with
    | True | False -> ()
    | Formula fs -> checkUniqueAux fs
and checkUniqueAux f =
  isUnique (List.concat (List.map (fun (Atom (s, t, c)) -> (Term.getVarNameSorts s) @ (Term.getVarNameSorts t) @ (getSortAssumption c)) f))
and isUnique l =
  match l with
    | [] -> ()
    | ((x, s)::xs) -> isUnique (checkRemove x s xs)
and checkRemove x s xs =
  match xs with
    | [] -> []
    | ((y, s')::ys) -> if y = x then
                         if s = s' || s = "unspec" || s' = "unspec" then
                           checkRemove x s ys
                         else
                           raise (SortConflictFormula (x, s, s'))
                       else
                         (y, s')::(checkRemove x s ys)

let rec removeUnspec f =
  match f with
    | True | False -> f
    | Formula fs -> removeUnspecAux fs
and removeUnspecAux f =
  Formula (applySorts (List.concat (List.map (fun (Atom (s, t, c)) -> (Term.getVarNameSorts s) @ (Term.getVarNameSorts t)) f)) f)
and applySorts binds f =
  List.map (fun (Atom (s, t, c)) -> Atom (applySortsTerms binds s, applySortsTerms binds t, c)) f
and applySortsTerms bind t =
  if Term.isVariable t then
    if Term.getVarSort t = "unspec" then
      let newsort = getSortFrom bind (Term.getTopSymbol t) in
        Term.createVar (Term.getTopSymbol t) newsort
    else
      t
  else
    let f = Term.getTopSymbol t
    and args = Term.getArgs t in
      Term.createFun f (List.map (fun t -> applySortsTerms bind t) args)
and getSortFrom bind x =
  match bind with
    | [] -> "unspec"
    | (x', s)::bind' -> if x = x' && s <> "unspec" then s else getSortFrom bind' x

let rec fixAll f sort =
  match f with
    | True | False -> f
    | Formula fs -> fixAllAux fs sort
and fixAllAux f sort =
  Formula (List.map (fun (Atom (s, t, c)) -> Atom (fixTerm s sort, fixTerm t sort, c)) f)
and fixTerm t sort =
  if Term.isVariable t then
    Term.createVar (Term.getTopSymbol t) sort
  else
    let f = Term.getTopSymbol t
    and args = Term.getArgs t in
      Term.createFun f (List.map (fun t -> fixTerm t sort) args)

(* Parses a formula over a given trs from an in_channel. *)
let getFormula ttrs chan =
  try
    Formula_lexer.pos := 1;
    let lexbuf = Lexing.from_channel chan
    and signa = Trs.getSignature ttrs in
      let f = Formula_parser.formula_eol Formula_lexer.token lexbuf in
        checkFormula signa f;
        formulaOk signa f;
        let res = getSortedFormula signa f in
          if List.length (Trs.getSorts ttrs) > 1 then
            (checkUnique res; removeUnspec res)
          else
            fixAll res (List.nth (Trs.getSorts ttrs) 0)
  with
    | Parsing.Parse_error ->
        raise
          (
            ParseException
              (
                !Formula_lexer.pos,
                Printf.sprintf "Error: Parse error at position %d." !Formula_lexer.pos
              )
            )
    | Formula_lexer.Unknown ->
        raise
          (
            ParseException
              (
                !Formula_lexer.pos,
                Printf.sprintf "Error: Unknown token at position %d." !Formula_lexer.pos
              )
          )
    | Signature.NotInSignature f ->
        raise
          (
            ParseException
              (
                -1,
                Printf.sprintf "Error: Unknown function Symbol \"%s\"." f
              )
          )
    | TermParse.ArityConflict (f, n, nn) ->
        raise
          (
            ParseException
              (
                -1,
                Printf.sprintf "Error: Function symbol \"%s\" has arity %d, not %d." f n nn
              )
          )
    | TermParse.SortConflict (t, n) ->
        raise
          (
            ParseException
              (
                -1,
                Printf.sprintf "Error: Argument %d of \"%s\" has the wrong sort." n t
              )
          )
    | TermParse.SortConflictVar (x, s1, s2) ->
        raise
          (
            ParseException
              (
                -1,
                Printf.sprintf "Error: Variable \"%s\" is used with sorts %s and %s." x s1 s2
              )
          )
    | SortConflictEquality r ->
        raise
          (
            ParseException
              (
                -1,
                Printf.sprintf "Error: Sort conflict in \"%s\"." r
              )
          )
    | SortConflictFormula (v, s1, s2) ->
        raise
          (
            ParseException
              (
                -1,
                Printf.sprintf "Error: Variable \"%s\" is used with sorts \"%s\" and \"%s\"." v s1 s2
              )
          )
