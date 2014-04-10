(*
  Implementation of LIAC decision procedure.

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

(* Time spend in the smt proof in msec. *)
let smtTime = ref 0.0
let failed = ref false

(* Applies. *)
let rec apply ttrs f =
  smtTime := 0.0;
  failed := false;
  let genF = generalizeFormula ttrs f in
    if !failed then
      None
    else
      let start = Unix.gettimeofday () in
      let res = doSimp ttrs genF in
      let stop = Unix.gettimeofday () in
        (
          smtTime := (stop -. start) *. 1000.0;
          match res with
            | Ynm.Yes -> Some (Formula.True, [Proof.Direct (f, "the decision procedure for LIAC with safe generalizations", Formula.True)])
            | Ynm.No -> Some (Formula.False, [Proof.Direct (f, "the decision procedure for LIAC with safe generalizations", Formula.False)])
            | Ynm.Maybe -> None
        )
and doSimp ttrs f =
  Formula.isValidLIACConjunction ttrs f
and generalizeFormula ttrs f =
  match f with
    | Formula.True | Formula.False | Formula.Formula [] -> f
    | Formula.Formula fs -> Formula.Formula (List.map (generalizeAtom ttrs (Trs.getDefined ttrs)) fs)
and generalizeAtom ttrs defs atom =
  if hasConstraint atom then
  (
    failed := true;
    atom
  )
  else
  (
    let signa = Trs.getSignature ttrs
    and aliens = Util.remdup (getAliensAtom defs atom) in
      if checkAliens aliens [] then
        generalize signa defs atom
      else
      (
        failed := true;
        atom
      )
  )
and hasConstraint (Formula.Atom (_, _, c)) =
  c <> []
and getAliensAtom defs (Formula.Atom (s, t, _)) =
  (Term.getAllSubtermsForSymbols s defs) @ (Term.getAllSubtermsForSymbols t defs)
and checkAliens aliens seenvars =
  match aliens with
    | [] -> true
    | a::aa -> let aArgs = Term.getArgs a in
                 if List.exists (fun t -> not (Term.isVariable t)) aArgs then
                   false
                 else if Term.isLinear a then
                   let aVars = Term.getVars a in
                   (
                     if List.exists (fun v -> List.mem v seenvars) aVars then
                       false
                     else if Notheory.isNoTheory (Term.getTopSymbol a) then
                       checkAliens aa (aVars @ seenvars)
                     else
                       false
                   )
                 else
                   false
and genMap = ref []
and genNum = ref 0
and generalize signa defs (Formula.Atom (s, t, _)) =
  genMap := [];
  genNum := 0;
  let res = Formula.Atom (generalizeTerm signa defs s, generalizeTerm signa defs t, []) in
    res
and generalizeTerm signa defs t =
  if Term.isVariable t then
    t
  else
    let f = Term.getTopSymbol t in
      if List.mem f defs then
        try
          let genVar = List.assoc t !genMap in
            genVar
        with
          | Not_found -> (
                           incr genNum;
                           let genVar = Term.createVar ("z_" ^ (string_of_int !genNum)) (Signature.getSort signa f) in
                           (
                             genMap := (t, genVar)::!genMap;
                             genVar
                           )
                         )
      else
        Term.createFun f (List.map (generalizeTerm signa defs) (Term.getArgs t))
