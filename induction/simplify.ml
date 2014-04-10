(*
  Implementation of the Simplify rule.

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

(* Time spend in the smt solver in msec. *)
let smtTime = ref 0.0

let rec apply ttrs hyps f =
  smtTime := 0.0;
  match f with
    | True | False -> None
    | Formula fs -> (
                      let fs' = normalize ttrs hyps fs in
                        if fs' = fs then
                          None
                        else
                          let fs'' = Util.remdup fs' in
                            Some (Formula fs'', [Proof.Direct (Formula fs, "simplification w.r.t. R and the hypotheses", Formula fs'')])
                    )
and normalize ttrs hyps fs =
  normalizeAux hyps (Trs.getRuleTrie ttrs) fs
and normalizeAux hyps rules fs =
  List.map (fun (Atom (s, t, c)) -> (Atom (termnormalize hyps rules s c, termnormalize hyps rules t c, c))) fs
and termnormalize hyps rules t c =
  let t' = rewriteOnce hyps rules t c in
    if t = t' then
      t
    else
      termnormalize hyps rules t' c
and rewriteOnce hyps rules t c =
  if (Term.isVariable t) then
    t
  else
    (
      let f = Term.getTopSymbol t in
        let t' = getNewArgs hyps rules f t c in
          let ru = getRulesFor hyps rules t' in
            doFirst t' ru c
    )
and getNewArgs hyps rules f t c =
  let ts = Term.getArgs t in
    let newts = List.map (fun tt -> termnormalize hyps rules tt c) ts in
      Term.createFun f newts
and doFirst t rules c =
  match rules with
    | [] -> t
    | (Rule.Rule (l, r, c'))::rus ->
        (
          let sigma = Unification.matchTermsNoException l t in
            match sigma with
              | None -> doFirst t rus c
              | Some sigma' -> if (constraintImplicationTrue c c' sigma') then
                                 Substitution.applyToTerm sigma' r
                               else
                                 doFirst t rus c
        )
and constraintImplicationTrue c c' sigma =
  let start = Unix.gettimeofday () in
  let res = constraintTrueAux c (List.map (Constraint.applySubstitution sigma) c') in
  let stop = Unix.gettimeofday () in
    (
      smtTime := !smtTime +. ((stop -. start) *. 1000.0);
      res
    )
and constraintTrueAux c c' =
  if c' = [] then
    true
  else
  (
    if c = [] then
      Decproc.isValidPAConjunction c' = Ynm.Yes
    else
      Decproc.isValidPAImplication c c' = Ynm.Yes
  )
and getRulesFor hyps rules t =
  (Ruletrie.getRules hyps t) @ (Ruletrie.getRules rules t)
