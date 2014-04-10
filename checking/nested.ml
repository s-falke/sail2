(*
  Implementation of checking for simple nested conjectures.

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

let box = Term.createVar "Box" "Dummy"
let indterms = ref []
let hasContext = ref false
let context = ref (Term.createVar "Box" "Dummy")
let innermostcontext = ref (Term.createVar "Box" "Dummy")
let notLIACBased = ref []
let gg = ref ""
let ff = ref ""

let buildPseudoFormula inductterms signa =
  Formula (List.map (fun t -> Formula.Atom (t, Term.createVar "X" (Term.getSort signa t), [])) inductterms)

(* Determines whether a formula is simple nested w.r.t. a TRS. *)
let rec isNested ttrs f =
  indterms := [];
  hasContext := false;
  context := Term.createVar "Box" "Dummy";
  notLIACBased := [];
  let defs = Trs.getDefined ttrs in
  let tmp = hasNestedForm defs (Trs.getConstructors ttrs) f in
    if not (tmp = None) then
      ([Proof.Nested (f, false, tmp, [], None, None, f)], f)
    else
      let pseudo = buildPseudoFormula !indterms (Trs.getSignature ttrs)
      and indtermsfuns = (getIndtermsFuns !indterms) in
        let tmp = ref (Simple.isImpeq ttrs indtermsfuns pseudo) in
          if not (!tmp = None) then
            ([Proof.Nested (f, false, !tmp, [], None, None, f)], f)
          else
            match (checkLIAC ttrs indtermsfuns) with
              | None -> if isCompatible ttrs then
                          ([Proof.Nested (f, true, None, [], None, None, f)], f)
                        else
                          ([Proof.Nested (f, false, None, [], None, Some (!gg, !ff), f)], f)
              | Some ru -> ([Proof.Nested (f, false, None, !notLIACBased, Some ru, None, f)], f)
and getIndtermsFuns indterms =
  Util.remdup (List.map Term.getTopSymbol indterms)
and checkLIAC ttrs indtermsfuns =
  let res = Simple.isLIACBased ttrs indtermsfuns in
    if res = None then
      checkLIACContext ttrs (Term.getFuns !context)
    else
    (
      notLIACBased := indtermsfuns;
      res
    )
and checkLIACContext ttrs funs =
  match funs with
    | [] -> None
    | f::ff -> let res = Simple.isLIACBased ttrs [f] in
                 if res = None then
                   checkLIACContext ttrs ff
                 else
                 (
                   notLIACBased := [f];
                   res
                 )
and isCompatible ttrs =
  gg := "";
  ff := "";
  if !context = box then
    true
  else
    if checkContext (Trs.getDefined ttrs) (Trs.getConstructors ttrs) then
      let inncon = getInnermostContext ttrs in
        checkIndterms (Term.getTopSymbol inncon) (getBoxPos inncon)
    else
      false
and getBoxPos t =
  getNum (Term.getArgs t) 1
and getNum args i =
  match args with
    | [] -> failwith "internal error in Nested.isCompatible"
    | a::aa -> if a = box then
                 i
               else
                 getNum aa (i + 1)
and checkContext defs cons =
  let seq = getSeq !context defs cons in
    checkSeq seq
and print_seq seq =
  Printf.printf "%s\n" (get_string seq); flush stdout
and get_string seq =
  match seq with
    | [] -> ""
    | (f, i)::seq' -> "(" ^ f ^ ", " ^ (string_of_int i) ^ ") " ^ (get_string seq')
and getSeq t defs cons =
  if Term.isVariable t then
    []
  else
    let f = Term.getTopSymbol t
    and args = Term.getArgs t in
      if (List.for_all (fun tt -> Term.isBasedOn cons tt) args) then
        [(f, -1)]
      else
        let (t', i) = getDefSub args defs 1 in
          (f, i)::(getSeq t' defs cons)
and getDefSub ts defs i =
  match ts with
    | [] -> failwith "internal error in Nested.getDefSub"
    | t::tt -> let f = Term.getTopSymbol t in
                 if List.mem f defs then
                   (t, i)
                 else
                   getDefSub tt defs (i + 1)
and checkSeq seq =
  match seq with
    | [] -> true
    | [_] -> true
    | (g, i)::(f, k)::ss ->
        (
          if Compat.isCompat g f i then
            checkSeq ((f, k)::ss)
          else
            (gg := g; ff := f; false)
        )
and getInnermostContext ttrs=
  getInnConAux !context (Trs.getDefined ttrs) (Trs.getConstructors ttrs)
and getInnConAux t defs cons =
  if Term.isVariable t then
    failwith "internal error in Nested.getInnermostContext"
  else
    let f = Term.getTopSymbol t in
      if List.mem f defs then
        if List.for_all (fun tt -> Term.isBasedOn cons tt) (Term.getArgs t) then
          t
        else
          let args = Term.getArgs t in
            getInnConAux (List.nth (List.filter (fun t -> (List.mem (Term.getTopSymbol t) defs)) args) 0) defs cons
      else
        failwith "internal error in Nested.getInnermostContext"
and checkIndterms g i =
  checkIndtermsAux g i !indterms
and checkIndtermsAux g i ts =
  match ts with
    | [] -> true
    | t::tt -> if Compat.isCompat g (Term.getTopSymbol t) i then
                 checkIndtermsAux g i tt
               else
                 (gg := g; ff := Term.getTopSymbol t; false)
and hasNestedForm defs conss f =
  match f with
    | True | False | Formula [] -> None
    | Formula atoms -> checkAtoms defs conss atoms
and checkAtoms defs conss atoms =
  match atoms with
    | [] -> None
    | (Atom (s, t, c))::aas -> if not (List.mem (Term.getTopSymbol s) defs && Term.isBasedOn conss t) then
                                 Some (Atom (s, t, c))
                               else
                                 if not (examineTerm s defs conss) then
                                   Some (Atom (s, t, c))
                                 else
                                   checkAtoms defs conss aas
and examineTerm s defs conss =
  match getInductTerm s defs conss with
    | None -> false
    | Some t ->
      (
        indterms := t::!indterms;
        let skel = replace t s in
          if !hasContext then
            (
            if skel <> !context then
              false
            else
              true
            )
          else
            (
              hasContext := true;
              context := skel;
              true
            )
      )
and getInductTerm s defs conss =
  getInductTermAux s defs conss []
and getInductTermAux s defs conss vars =
  let f = Term.getTopSymbol s in
    if List.mem f conss then
      None
    else
      if (List.for_all (fun t -> Term.isVariable t) (Term.getArgs s)) then
        if (List.for_all (fun t -> not (List.mem t vars)) (Term.getArgs s)) then
          Some s
        else
          None
      else
        if (List.for_all (fun t -> Term.isBasedOn conss t) (Term.getArgs s)) then
          if (List.for_all (fun t -> not (containsVar t vars)) (Term.getArgs s)) then
            Some s
          else
            None
        else
          let (flag, defterm, consterms) = split_it s defs in
            if flag then
              getInductTermAux defterm defs conss (getNewVars vars consterms)
            else
              None
and containsVar t vars =
  List.exists (fun v -> List.mem v vars) (Term.getVarsAsTerms t)
and split_it s defs =
  let args = Term.getArgs s in
    if (get_num_defs args defs 0 > 1) then
      (false, s, [])
    else
      let (defterm, consterms) = split_it_aux args defs [] in
        (true, defterm, consterms)
and get_num_defs args defs i =
  match args with
    | [] -> i
    | t::ts -> if List.mem (Term.getTopSymbol t) defs then
                 get_num_defs ts defs (i + 1)
               else
                 get_num_defs ts defs i
and split_it_aux args defs accu =
  match args with
    | [] -> failwith "internal error in Nested.split_it_aux"
    | t::ts -> if List.mem (Term.getTopSymbol t) defs then
                 (t, accu @ ts)
               else
                 split_it_aux ts defs (accu @ [t])
and replace t s =
  if s = t then
    Term.createVar "Box" "Dummy"
  else
    if Term.isVariable s then
      s
    else
      let f = Term.getTopSymbol s in
        let args = Term.getArgs s in
          let newargs = List.map (fun s -> replace t s) args in
            Term.createFun f newargs
and getNewVars vars consterms =
  match consterms with
    | [] -> vars
    | t::ts -> getNewVars (mergeVars vars (Term.getVarsAsTerms t)) ts
and mergeVars vars newvars =
  match newvars with
    | [] -> vars
    | v::vs -> if List.mem v vars then
                 mergeVars vars vs
               else
                 mergeVars (v::vars) vs
