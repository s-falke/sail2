(*
  Implementation of NoTheory.

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

let cache = ref []
let signa = ref (Signature.Sig [])
let thetrs = ref (Trs.Trs (Signature.createEmpty (), [], Ruletrie.empty ()))

(* Determines whether a single function is LIAC-based *)
let rec isLIACBased allconss frules f =
  match frules with
    | [] -> true
    | ru::rules' -> if not (isLIACBasedRule allconss f (Rule.getLeft ru) (Rule.getRight ru)) then
                      false
                    else
                      isLIACBased allconss rules' f
and isLIACBasedRule allconss f l r =
  List.for_all (Term.isBasedOn allconss) (Term.getArgs l) && check_calls allconss f r
and check_calls allconss f t =
  if Term.isVariable t then
    true
  else
    let g = Term.getTopSymbol t in
      if List.mem g allconss then
        List.for_all (check_calls allconss f) (Term.getArgs t)
      else if g = f then
        List.for_all (Term.isBasedOn allconss) (Term.getArgs t)
      else
        false

(* Determines whether a function symbol is a member of a simple mutually recursive set *)
let rec isSimpleMutual allcons alldefs ttrs f =
  let fRules = Trs.getRulesForSymbol ttrs f in
    let fCalls = Util.remdup (List.concat (List.map (fun r -> Term.getAllSubtermsForSymbols r alldefs) (List.map Rule.getRight fRules))) in
      let fCallsSymbols = Util.remdup (List.map Term.getTopSymbol fCalls) in
        if List.length fCallsSymbols > 1 then
          false
        else
          let g = List.nth fCallsSymbols 0 in
            if check_calls_mutual fCalls [] then
              checkCallsOnlyTo allcons alldefs ttrs g f
            else
              false
and checkCallsOnlyTo allcons alldefs ttrs g f =
  let gRules = Trs.getRulesForSymbol ttrs g in
    let gCalls = Util.remdup (List.concat (List.map (fun r -> Term.getAllSubtermsForSymbols r alldefs) (List.map Rule.getRight gRules))) in
      let gCallsSymbols = Util.remdup (List.map Term.getTopSymbol gCalls) in
        if List.length gCallsSymbols > 1 then
          false
        else
          let h = List.nth gCallsSymbols 0 in
            if f = h then
              check_calls_mutual gCalls []
            else
              false
and check_calls_mutual calls seenVars =
  match calls with
    | [] -> true
    | t::tt -> let tVars = Term.getVars t in
                 if (List.for_all Term.isVariable (Term.getArgs t)) &&
                    (Term.isLinear t) &&
                    (List.for_all (fun v -> not (List.mem v seenVars)) tVars) then
                       check_calls_mutual tt (seenVars @ tVars)
                 else
                   false

(* Computes NoTheory for a TRS and caches the results. *)
let rec compute ttrs =
  cache := [];
  signa := Trs.getSignature ttrs;
  thetrs := ttrs;
  let defs = Trs.getDefined ttrs
  and conss = Trs.getConstructors ttrs in
    let res = List.iter (computeFun defs conss ttrs) defs in
    (
      (* Printf.printf "%s\n\n" (String.concat "\n" (List.map entryString !cache));
         flush stdout; *)
      res
    )
and entryString (f, nt) =
  if nt then
    f ^ ": " ^ "yes"
  else
    f ^ ": " ^ "no"
and computeFun alldefs allconss ttrs f =
  let fRules = Trs.getRulesForSymbol ttrs f in
  if isLIACBased allconss fRules f then
    cache := (f, checkNoTheory fRules allconss f)::!cache
  else if (isSimpleMutual allconss alldefs ttrs f) && (checkNoTheory (unroll ttrs alldefs fRules f) allconss f) then
    cache := (f, true)::!cache
  else
    cache := (f, checkNoTheoryCap fRules allconss f)::!cache
(* checkNoTheory for LIAC-based *)
and checkNoTheory fRules allconss f =
  let cand = getCandidateSet fRules allconss in
    if cand = [] then
      false
    else
    (
      (* Printf.printf "Candidate set for %s: %s\n" f (String.concat ", " (List.map Term.toString cand)); *)
      let checkerLhs = Term.createFun f (getVarList 1 (Signature.getArgSorts !signa f)) in
        List.for_all (fun q -> List.exists (contradicts (getCheckerTRS checkerLhs q)) fRules) cand
    )
and getCheckerTRS lhs rhs =
  let rule = Rule.Rule (lhs, rhs, []) in
    let trie = Ruletrie.insert (Ruletrie.empty ()) rule in
      Trs.Trs (!signa, [rule], trie)
and contradicts checkerTRS (Rule.Rule (l, r, _)) =
  (Trs.normalizeZfree checkerTRS l) <> (Trs.normalizeZfree checkerTRS r)
and getCandidateSet fRules allconss =
  match fRules with
    | [] -> []
    | rule::rules' -> if isNonrecursive rule allconss then
                        getCandidateSetOne rule
                      else
                        getCandidateSet rules' allconss
and isNonrecursive (Rule.Rule (_, r, _)) allconss =
  Term.isBasedOn allconss r
and getCandidateSetOne (Rule.Rule (l, r, _)) =
  let sstar = Term.getArgs l in
    getCandidateSetOneAux sstar (getVarList 1 (List.map (Term.getSort !signa) sstar)) r
and getCandidateSetOneAux sstar xstar r =
  if Term.isVariable r then
    getVarCollapses sstar xstar r
  else
    let c = Term.getTopSymbol r
    and children = List.map (getCandidateSetOneAux sstar xstar) (Term.getArgs r) in
      (getVarCollapses sstar xstar r) @ (constructChildren c children)
and constructChildren c children =
  let childLists = constructChildLists children in
    List.map (Term.createFun c) childLists
and constructChildLists children =
  match children with
    | [] -> [[]]
    | c::cc -> let tmp = constructChildLists cc in
                 extendAll c tmp
and extendAll c tmp =
  match c with
    | [] -> []
    | onec::c' -> (List.map (fun cd -> onec::cd) tmp) @ (extendAll c' tmp)
and getVarCollapses sstar xstar r =
  match sstar with
    | [] -> []
    | s::ss -> if s = r then
                 (List.hd xstar)::(getVarCollapses ss (List.tl xstar) r)
               else
                 getVarCollapses ss (List.tl xstar) r
and getVarList i sorts =
  match sorts with
    | [] -> []
    | s::ss -> (Term.createVar ("x" ^ (string_of_int i)) s)::(getVarList (i+1) ss)
(* unroll simple mutual recursive *)
and unroll ttrs alldefs fRules f =
  let g = List.nth (List.map Term.getTopSymbol (List.concat (List.map (fun r -> Term.getAllSubtermsForSymbols r alldefs) (List.map Rule.getRight fRules)))) 0 in
    let gRules = renameNice (Trs.getRulesForSymbol ttrs g) in
      List.concat (List.map (unrollRule g gRules) fRules)
and num = ref 0
and renameNice rules =
  num := 1;
  List.map renameNiceOne rules
and renameNiceOne rule =
  let vars = Term.getVarsAsTerms (Rule.getLeft rule) in
    let subby = createSubstitution vars (Substitution.createEmptySubstitution ()) in
      Rule.Rule (Substitution.applyToTerm subby (Rule.getLeft rule),
                 Substitution.applyToTerm subby (Rule.getRight rule),
                 [])
and createSubstitution vars subby =
  match vars with
    | [] -> subby
    | x::xs -> let newVar = Term.createVar ("x" ^ (string_of_int !num)) (Term.getVarSort x) in
               (
                 incr num;
                 createSubstitution xs (Substitution.extendSubstitution subby (Term.getTopSymbol x) newVar)
               )
and unrollRule g gRules rule =
  let r = Rule.getRight rule in
    let gCalls = List.filter (fun (t, _) -> Term.getTopSymbol t = g) (Term.getAllSubtermsWithPositions r) in
      doUnroll gCalls gRules rule
and doUnroll gCalls gRules rule =
  match gCalls with
    | [] -> [rule]
    | (gt, p)::gtt -> List.concat (List.map (doUnroll gtt gRules) (doUnrollOnePosition rule gRules gt p))
and doUnrollOnePosition rule gRules gt p =
  List.map (fun grule -> doUnrollOnePositionOneRule rule grule gt p) gRules
and doUnrollOnePositionOneRule rule grule gt p =
  let tau = setupTau (Rule.getLeft grule) gt in
    Rule.Rule (Substitution.applyToTerm tau (Rule.getLeft rule),
               Term.replaceSubtermAt (Substitution.applyToTerm tau (Rule.getRight rule)) p (Rule.getRight grule),
               [])
and setupTau gLeft gt =
  setupTauAux (Term.getArgs gLeft) (Term.getArgs gt) (Substitution.createEmptySubstitution ())
and setupTauAux gLeftArgs gtArgs subby =
  match gtArgs with
    | [] -> subby
    | v::vv -> setupTauAux (List.tl gLeftArgs) vv (Substitution.extendSubstitution subby (Term.getTopSymbol v) (List.hd gLeftArgs))
(* checkNoTheory with cap *)
and checkNoTheoryCap fRules allconss f =
  let cand = getCandidateSet fRules allconss in
    if cand = [] then
      false
    else
    (
      (* Printf.printf "Candidate set for %s: %s\n" f (String.concat ", " (List.map Term.toString cand)); *)
      let checkerLhs = Term.createFun f (getVarList 1 (Signature.getArgSorts !signa f)) in
        List.for_all (fun q -> List.exists (contradictsCap (getCheckerTRS checkerLhs q)) fRules) cand
    )
and capnum = ref 0
and contradictsCap checkerTRS (Rule.Rule (l, r, _)) =
  capnum := 0;
  let normL = Trs.normalizeZfree checkerTRS l
  and normR = cap (Trs.getDefined !thetrs) (Trs.normalizeZfree checkerTRS r) in
    Formula.isSatisfiableLIACConjunction !thetrs (Formula.Formula [Formula.Atom (normL, normR, [])]) = Ynm.No
and cap defs t =
  if Term.isVariable t then
    t
  else
    let f = Term.getTopSymbol t in
      if List.mem f defs then
      (
        incr capnum;
        Term.createVar ("z_" ^ (string_of_int !capnum)) (Signature.getSort !signa f)
      )
      else
        Term.createFun f (List.map (cap defs) (Term.getArgs t))

(* Returns NoTheory for a function symbol. *)
let isNoTheory f =
  try
    List.assoc f !cache
  with
    | Not_found -> false
