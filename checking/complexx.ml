(*
  Implementation of checking for complex conjectures.

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
let splitTerms = ref [] (* (fTerm, fContext, fDef, gTerm, gContext, gDef) *)
let atoms = ref []
let hasFailureAtom = ref false
let failureAtom = ref (Atom (Term.createVar "x" "Dummy", Term.createVar "y" "Dummy", []))
let ff = ref ""
let gg = ref ""
let notLIACBased = ref []
let noTheoryProblem = ref (Term.createVar "Dumm" "Brot")
let hasNoTheoryProblem = ref false
let defs = ref []
let thetrs = ref (Trs.Trs (Signature.createEmpty (), [], Ruletrie.empty ()))

let rec buildPseudoFormula inductterms signa =
  Formula (List.map (fun t -> Formula.Atom (t, Term.createVar "X" (Term.getSort signa t), [])) inductterms)

(* Determines whether a formula is complex w.r.t. a TRS. *)
let rec isComplex ttrs f =
  match f with
    | True | False | Formula [] -> ([], False)
    | Formula fs -> isComplexReal ttrs fs
and isComplexReal ttrs fs =
  splitTerms := [];
  atoms := fs;
  hasFailureAtom := false;
  ff := "";
  gg := "";
  notLIACBased := [];
  hasNoTheoryProblem := false;
  defs := Trs.getDefined ttrs;
  thetrs := ttrs;
  setup ttrs fs;
  if !hasFailureAtom then
    ([Proof.Complex (Formula fs, false, Some !failureAtom, [], None, None, None, Formula fs)], Formula fs)
  else
  (
    checkCompatibility (Trs.getDefined ttrs) (Trs.getConstructors ttrs) !splitTerms box false 0;
    if !hasFailureAtom then
      ([Proof.Complex (Formula fs, false, None, [], None, Some (!gg, !ff), None, Formula fs)], Formula fs)
    else
    (
      let fSet = getFSet !splitTerms in
        match checkLIAC ttrs fSet (getLeftContext !splitTerms) with
          | Some ru -> ([Proof.Complex (Formula fs, false, None, !notLIACBased, Some ru, None, None, Formula fs)], Formula fs)
          | None -> (
                      let (iTerms, iFuns) = getIStuff !splitTerms in
                        let pseudo = buildPseudoFormula iTerms (Trs.getSignature ttrs) in
                          let tmp = Simple.isImpeq ttrs iFuns pseudo in
                            if tmp <> None then
                              ([Proof.Complex (Formula fs, false, tmp, [], None, None, None, Formula fs)], Formula fs)
                            else
                            (
                              checkDefCondition ttrs !splitTerms 0;
                              if !hasFailureAtom then
                                ([Proof.Complex (Formula fs, false, Some !failureAtom, [], None, None, None, Formula fs)], Formula fs)
                              else
                              (
                                checkNoTheory !splitTerms;
                                if !hasNoTheoryProblem then
                                  ([Proof.Complex (Formula fs, false, None, [], None, None, Some !noTheoryProblem, Formula fs)], Formula fs)
                                else
                                  ([Proof.Complex (Formula fs, true, None, [], None, None, None, Formula fs)], Formula fs)
                              )
                            )
                    )
    )
  )
and failAtom atom =
  if !hasFailureAtom then
    ()
  else
  (
    hasFailureAtom := true;
    failureAtom := atom
  )
and failNoTheory term =
  if !hasNoTheoryProblem then
    ()
  else
  (
    hasNoTheoryProblem := true;
    noTheoryProblem := term
  )
and getFSet terms =
  Util.remdup (List.map (fun (t, _, _, _, _, _) -> Term.getTopSymbol t) terms)
and getIStuff terms =
  match terms with
    | [] -> ([], [])
    | (s, _, _, _, _, _)::rest -> let (res1, res2) = getIStuff rest in
                                    (s::res1, (Term.getTopSymbol s)::res2)
and getLeftContext terms =
  match terms with
    | [] -> failwith "internal error in Complexx.getLeftContext"
    | (_, sC, _, _, _, _)::_ -> sC
(* no-theory test *)
and checkNoTheory splitTerms =
  checkNoTheoryAll splitTerms splitTerms
and checkNoTheoryAll splitTerms allSplitTerms =
  match splitTerms with
    | [] -> ()
    | (_, _, sDefR, t, tContext, tDefR)::rest -> (
                                                   checkNoTheoryOne sDefR t tContext tDefR allSplitTerms;
                                                   checkNoTheoryAll rest allSplitTerms
                                                 )
and checkNoTheoryOne sDefR t tContext tDefR allSplitTerms =
  let allTerms = Util.remdup (List.flatten (List.map (getNoTheoryTerms (Term.getVars t) tContext tDefR allSplitTerms) sDefR)) in
    checkSafeGeneralizations allTerms []
and checkSafeGeneralizations terms seenvars =
  match terms with
    | [] -> ()
    | t::tt -> if List.exists (fun a -> not (Term.isVariable a)) (Term.getArgs t) then
                 failNoTheory t
               else
                 let tVars = Term.getVars t in
                   if List.exists (fun v -> List.mem v seenvars) tVars then
                     failNoTheory t
                   else
                     let f = Term.getTopSymbol t in
                       if List.length tVars <> Signature.getArity (Trs.getSignature !thetrs) f then
                         failNoTheory t
                       else if Notheory.isNoTheory f then
                         checkSafeGeneralizations tt (tVars @ seenvars)
                       else
                         failNoTheory t
and getNoTheoryTerms tVars tContext tDefR allSplitTerms sDef =
  getMaxDefined ((getNoTheoryTerms1 tContext (Scheme.getCorresponding sDef tDefR tVars)) @
                 (getNoTheoryTerms2 sDef allSplitTerms))
and getMaxDefined terms =
  List.flatten (List.map (fun t -> Term.getAllMaximalSubtermsForSymbols t !defs) terms)
and getNoTheoryTerms1 tContext def =
  match def with
    | None -> failwith "internal error in Complexx.getNoTheoryTerms1"
    | Some (rule, sigma') -> let calls = Term.getAllSubtermsForSymbols (Rule.getRight rule) !defs in
                               List.map (fun call -> Trs.normalizeZfree !thetrs (Substitution.applyToTerm sigma' (replaceContext tContext call))) calls
and getNoTheoryTerms2 sDef allSplitTerms =
  List.flatten (List.map (getNoTheoryTerms2One sDef) allSplitTerms)
and getNoTheoryTerms2One sDef (sTerm, _, _, tTerm, tContext, _) =
  let taus = Scheme.computeCall !thetrs sDef sTerm in
    List.map (fun tau -> Trs.normalizeZfree !thetrs (Substitution.applyToTerm tau (replaceContext tContext tTerm))) taus
and replaceContext context t =
  if context = box then
    t
  else
    if Term.isVariable context then
      context
    else
      let f = Term.getTopSymbol context in
        let args = Term.getArgs context in
          let newargs = List.map (fun s -> replaceContext s t) args in
            Term.createFun f newargs
(* Def-condition test *)
and checkDefCondition ttrs splitTerms i =
  match splitTerms with
    | [] -> ()
    | (_, _, sDef, t, _, tDef)::rest -> (
                                          let tVars = Term.getVars t in
                                            if Scheme.areIdentical sDef tDef tVars then
                                              checkDefCondition ttrs rest (i + 1)
                                            else
                                              failAtom (List.nth !atoms i)
                                        )
(* LIAC-test for left sides *)
and checkLIAC ttrs fSet context =
  let res = Simple.isLIACBased ttrs fSet in
    if res = None then
      checkLIACContext ttrs (Term.getFuns context)
    else
    (
      notLIACBased := fSet;
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
(* LIAC good *)
and isLIACGood ttrs funs =
  let conss = Trs.getConstructors ttrs
  and defs = Trs.getDefined ttrs
  and rules = List.concat (List.map (Trs.getRulesForSymbol ttrs) funs) in
    checkAllGood defs conss rules
and checkAllGood defs conss rules =
  match rules with
    | [] -> None
    | ru::rules' -> if not (isLIACGoodRule defs conss (Rule.getLeft ru) (Rule.getRight ru)) then
                      Some ru
                    else
                      checkAllGood defs conss rules'
and isLIACGoodRule defs conss l r =
  List.for_all (Term.isBasedOn conss) (Term.getArgs l) &&
  checkAllCalls defs conss r
and checkAllCalls defs conss t =
  if Term.isVariable t then
    true
  else
    let f = Term.getTopSymbol t in
      if List.mem f conss then
        List.for_all (checkAllCalls defs conss) (Term.getArgs t)
      else if List.mem f defs then
        List.for_all (Term.isBasedOn conss) (Term.getArgs t)
      else
        false
(* Compatibility requirements *)
and checkCompatibility defs conss terms context hasContext i =
  match terms with
    | [] -> ()
    | (sTerm, sContext, _, tTerm, tContext, _)::rest -> if hasContext then
                                                          if (sContext <> context) || (not (hasCompatSeq defs conss sContext sTerm)) || (not (hasCompatSeq defs conss tContext tTerm)) then
                                                            failAtom (List.nth !atoms i)
                                                          else
                                                            checkCompatibility defs conss rest context hasContext (i + 1)
                                                        else
                                                          if (not (hasCompatSeq defs conss sContext sTerm)) || (not (hasCompatSeq defs conss tContext tTerm)) then
                                                            failAtom (List.nth !atoms i)
                                                          else
                                                            checkCompatibility defs conss rest sContext true (i + 1)
and hasCompatSeq defs conss context term =
  ff := "";
  gg := "";
  if context = box then
    true
  else
    if (checkVariables context term) && (checkContext defs conss context) then
      let inncon = getInnermostContext defs conss context in
        checkTerm (Term.getTopSymbol inncon) (getBoxPos inncon) term
    else
      false
and checkVariables context term =
  let cVars = Term.getVars context
  and tVars = Term.getVars term in
    if List.exists (fun v -> List.mem v cVars) tVars then
      false
    else
      true
and getBoxPos t =
  getNum (Term.getArgs t) 1
and getNum args i =
  match args with
    | [] -> failwith "internal error in Complexx.isCompatible"
    | a::aa -> if a = box then
                 i
               else
                 getNum aa (i + 1)
and checkContext defs conss context =
  let seq = getSeq context defs conss in
    checkSeq seq
and getSeq t defs conss =
  if Term.isVariable t then
    []
  else
    let f = Term.getTopSymbol t
    and args = Term.getArgs t in
      if List.for_all (Term.isBasedOn conss) args then
        [(f, -1)]
      else
        let (t', i) = getDefSub args defs 1 in
          (f, i)::(getSeq t' defs conss)
and getDefSub ts defs i =
  match ts with
    | [] -> failwith "internal error in Complexx.getDefSub"
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
and getInnermostContext defs conss context =
  if Term.isVariable context then
    failwith "internal error in Complexx.getInnermostContext"
  else
    let f = Term.getTopSymbol context in
      if List.mem f defs then
        if List.for_all (Term.isBasedOn conss) (Term.getArgs context) then
          context
        else
          let (defSub, _) = getDefSub (Term.getArgs context) defs 0 in
            getInnermostContext defs conss defSub
      else
        failwith "internal error in Complexx.getInnermostContext"
and checkTerm g i t =
  if Compat.isCompat g (Term.getTopSymbol t) i then
    true
  else
   (gg := g; ff := Term.getTopSymbol t; false)
(* Setup *)
and setup ttrs fs =
  List.iter (setupOne ttrs (Trs.getDefined ttrs) (Trs.getConstructors ttrs)) fs;
  splitTerms := List.rev !splitTerms;
and setupOne ttrs defs conss (Atom (s, t, c)) =
  let sOpt = decompose defs conss s box
  and tOpt = decompose defs conss t box in
    match (sOpt, tOpt) with
      | (None, _) | (_, None) -> failAtom (Atom (s, t, c))
      | (Some (sTerm, sContext), Some (tTerm, tContext)) -> splitTerms := (sTerm, sContext, Scheme.computeDefR ttrs sTerm, tTerm, tContext, Scheme.computeDefR ttrs tTerm)::!splitTerms
and decompose defs conss s context =
  let f = Term.getTopSymbol s in
    if List.mem f conss then
      None
    else
      if (List.for_all (fun t -> Term.isVariable t) (Term.getArgs s)) then
        Some (s, context)
      else
        let (flag, defterm, consterms, argno) = split_it s defs in
          if flag then
            decompose defs conss defterm (getNewContext f consterms argno context)
          else
            None
and split_it s defs =
  let args = Term.getArgs s in
    if (get_num_defs args defs 0 <> 1) then
      (false, s, [], 0)
    else
      let (defterm, consterms, i) = split_it_aux args defs [] 0 in
        (true, defterm, consterms, i)
and get_num_defs args defs i =
  match args with
    | [] -> i
    | t::ts -> if List.mem (Term.getTopSymbol t) defs then
                 get_num_defs ts defs (i + 1)
               else
                 get_num_defs ts defs i
and split_it_aux args defs accu i =
  match args with
    | [] -> failwith "internal error in Complexx.split_it_aux"
    | t::ts -> if List.mem (Term.getTopSymbol t) defs then
                 (t, accu @ ts, i)
               else
                 split_it_aux ts defs (accu @ [t]) (i + 1)
and getNewContext f consterms argno context =
  let (a1, a2) = partition consterms [] argno 0 in
    Term.createFun f (a1 @ (context::a2))
and partition tt res1 argno i =
  if argno = i then
    (res1, tt)
  else
    partition (List.tl tt) ((List.hd tt)::res1) argno (i + 1)
