(*
  Implementation of compatibility of function symbols.

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

type compat = (string * ((string * int) list)) list (* (f, (g, i) list) list *)

let cache = ref []

let tmp = ref []

let counter = ref 1

(* Computes Compat for a TRS and caches the results. *)
let rec compute ttrs =
  cache := [];
  let defs = Trs.getDefined ttrs in
    computeAll ttrs defs defs
and computeAll ttrs gg ff =
  match gg with
    | [] -> ()
    | g::gs -> (computeForOne ttrs g ff; computeAll ttrs gs ff)
and computeForOne ttrs g ff =
  match ff with
    | [] -> (cache := !cache @ [(g, !tmp)]; tmp := [])
    | f::fs -> (tmp := !tmp @ (computegf ttrs g f); computeForOne ttrs g fs)
and computegf ttrs g f =
  let signa = Trs.getSignature ttrs in
    let gAr = Signature.getArity signa g
    and gArgSorts = Signature.getArgSorts signa g
    and gskel = getSkeleton g (Signature.getArgSorts signa g)
    and fSort = Signature.getSort signa f
    and frules = Trs.getRulesForSymbol ttrs f in
      let res = ref [] in
        for j = 1 to gAr do
          if (List.nth gArgSorts (j - 1)) = fSort then
            if rewritesAll g gskel j frules ttrs then
              res := !res @ [(f, j)]
            else
              ()
          else
            ()
        done;
        !res
and getSkeleton g sorts =
  let args = getArgs 1 sorts in
    Term.createFun g args
and getArgs i sorts =
  match sorts with
    | [] -> []
    | s::ss -> (Term.createVar ("x" ^ (string_of_int i)) s)::(getArgs (i + 1) ss)
and rewritesAll g gskel j frules ttrs =
  List.for_all (fun ru -> rewritesOne g gskel j ru ttrs) frules
and rewritesOne g gskel j ru ttrs =
  let context = getContext (Rule.getRight ru) (Trs.getDefined ttrs) in
    let newSkel = Term.replaceSubtermAt gskel (Position.Pos (j, Position.Root)) context in
      let newSkelNorms = getSimpTreeLeaves ttrs newSkel (Rule.getConstraint ru) in
        List.for_all (fun (newSkelNorm, _) -> checkGood g newSkelNorm j (Trs.getConstructors ttrs)) newSkelNorms
and getSimpTreeLeaves ttrs t c =
  getSimpTreeLeavesLoop ttrs [(t, c)] []
and getSimpTreeLeavesLoop ttrs todo acc =
  match todo with
    | [] -> acc
    | (t, c)::tt -> let newt = applyCaseSimplify ttrs t c in
                      if newt = [(t, c)] then
                        getSimpTreeLeavesLoop ttrs tt ((t, c)::acc)
                      else
                        getSimpTreeLeavesLoop ttrs (newt @ tt) acc
and applyCaseSimplify ttrs t c =
  let newterms = List.map (fun (t', c') -> (t', c @ c')) (applyCaseSimplifyAux ttrs t c) in
    List.filter (fun (_, d) -> Decproc.isSatisfiablePAConjunction d <> Ynm.No) newterms
and applyCaseSimplifyAux ttrs t c =
  if (Term.isVariable t) then
    [(t, [])]
  else
    (
      let args = Term.getArgs t in
        let newArgs = getNewArgs ttrs args c in
          if newArgs = [(args, [])] then
            doRootStep ttrs t c
          else
            List.map (fun (args, c') -> (Term.createFun (Term.getTopSymbol t) args, c')) newArgs
    )
and getNewArgs ttrs args c =
  match args with
    | [] -> []
    | arg::aa -> let newa = applyCaseSimplifyAux ttrs arg c in
                   if newa = [(arg, [])] then                     
                     List.map (fun (newaa, c') -> (arg::newaa, c')) (getNewArgs ttrs aa c)
                   else
                     List.map (fun (newarg, c') -> (newarg::aa, c')) newa
and doRootStep ttrs t c =
  let ru = getRulesFor ttrs t in
    let res = doAll t ru in
      if isValid res then
        res
      else
        [(t, [])]
and doAll t ru =
  match ru with
    | [] -> []
    | (Rule.Rule (l, r, c))::rus ->
        (
          let sigma = Unification.matchTermsNoException l t in
            match sigma with
              | None -> doAll t rus
              | Some sigma' -> (Substitution.applyToTerm sigma' r, List.map (Constraint.applySubstitution sigma') c)::(doAll t rus)
        )
and isValid res =
  List.for_all isValidConstraint res
and isValidConstraint (_, c) =
  List.for_all Constraint.isZbased c
and getRulesFor ttrs t =
  Ruletrie.getRules (Trs.getRuleTrie ttrs) t
and getContext t defs =
  counter := 0;
  getContextAux t defs
and getContextAux t defs =
  if Term.isVariable t then
    t
  else
    let f = Term.getTopSymbol t in
      if List.mem f defs then
        (
          incr counter;
          Term.createVar ("z" ^ (string_of_int !counter)) "Dummy"
        )
      else
        let newargs = List.map (fun tt -> getContextAux tt defs) (Term.getArgs t) in
          Term.createFun f newargs
and checkGood g newSkelNorm j conss =
  let repSkel = replaceInSkel g newSkelNorm in
    Term.isBasedOn conss repSkel &&
    checkVars repSkel &&
    allGgood newSkelNorm g j
and replaceInSkel g t =
  if Term.isVariable t then
    t
  else
    let f = Term.getTopSymbol t in
      if f = g then
        Term.createVar "y" "Dummy"
      else
        let args = Term.getArgs t in
          let newargs = List.map (fun tt -> replaceInSkel g tt) args in
            Term.createFun f newargs
and checkVars repSkel =
  let vars = Term.getVars repSkel in
    List.for_all (fun v -> not (String.get v 0 = 'z')) vars
and allGgood repSkel g j =
  let gterms = (getAllG repSkel g) in
    List.for_all (fun gt -> isGgood gt j) gterms;
and getAllG t g =
  if Term.isVariable t then
    []
  else
    let f = Term.getTopSymbol t in
      if f = g then
        [t]
      else
        List.concat (List.map (fun tt -> getAllG tt g) (Term.getArgs t))
and isGgood t j =
  let args = Term.getArgs t in
    checkArgs args 1 j
and checkArgs args i j =
  match args with
    | [] -> true
    | a::aa -> if i = j then
                 String.get (Term.getTopSymbol a) 0 = 'z' &&
                 checkArgs aa (i+1) j
               else
                 String.get (Term.getTopSymbol a) 0 = 'x' &&
                 checkArgs aa (i+1) j

(* Returns Compat for two function symbols. *)
let rec isCompat g f i =
  search_compat !cache g f i
and search_compat c g f i =
  match c with
    | [] -> false
    | (g', c')::cc -> if g' = g then
                        search_compat_one c' f i
                      else
                        search_compat cc g f i
and search_compat_one c f i =
  match c with
    | [] -> false
    | (f', i')::cc -> if f = f' && i = i' then
                        true
                      else
                        search_compat_one cc f i

(** Returns a string for the currently cached Compat. *)
let rec toString () =
  toStringAux !cache
and toStringAux co =
  String.concat "\n" (List.map toStringLine co)
and toStringLine (f, c) =
  f ^ ": " ^ (toStringLineAux c)
and toStringLineAux c =
  String.concat ", " (List.map toStringEntry c)
and toStringEntry (g, i) =
  "(" ^ g ^ ", " ^ (string_of_int i) ^ ")"
