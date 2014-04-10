(*
  Implementation of the Case-Simplify rule.  Assumes that the formula
  has been normalized with Simplify before.


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
  @author Stephan Falke
*)

open Formula

(* Time spend in the smt solver in msec. *)
let smtTime = ref 0.0

let rec apply ttrs f =
  smtTime := 0.0;
  match f with
    | True | False -> None
    | Formula fs -> (
                      let fs' = doFirst ttrs fs in
                        if fs' = fs then
                          None
                        else
                          let fs'' = Util.remdup fs' in
                            Some (Formula fs'', [Proof.Direct (Formula fs, "case simplification w.r.t. R", Formula fs'')])
                    )
and doFirst ttrs fs =
  doFirstAux (Trs.getRuleTrie ttrs) fs
and doFirstAux rules fs =
  match fs with
    | [] -> []
    | a::aa -> let newas = getNewAtoms rules a in
                 if newas <> [] then
                   newas @ aa
                 else
                   a::(doFirstAux rules aa)
and getNewAtoms rules (Atom (s, t, c)) =
  let news = doCaseStep rules s in
    if news = [] then
      let newt = doCaseStep rules t in
        if newt = [] then
          []
        else
          List.filter (fun (Atom (s, t, c)) -> Decproc.isSatisfiablePAConjunction c <> Ynm.No) (List.map (fun (tt, c') -> Atom (s, tt, c @ c')) newt)
    else
      List.filter (fun (Atom (s, t, c)) -> Decproc.isSatisfiablePAConjunction c <> Ynm.No) (List.map (fun (ss, c') -> Atom (ss, t, c @ c')) news)
and doCaseStep rules t =
  if (Term.isVariable t) then
    [(t, [])]
  else
    (
      let args = Term.getArgs t in
        let newArgs = getNewArgs rules args in
          if newArgs = [(args, [])] then
            doRootStep rules t
          else
            List.map (fun (args, c) -> (Term.createFun (Term.getTopSymbol t) args, c)) newArgs
    )
and getNewArgs rules args =
  match args with
    | [] -> []
    | arg::aa -> let newa = doCaseStep rules arg in
                   if newa = [(arg, [])] then                     
                     List.map (fun (newaa, c) -> (arg::newaa, c)) (getNewArgs rules aa)
                   else
                     List.map (fun (newarg, c) -> (newarg::aa, c)) newa
and doRootStep rules t =
  let ru = getRulesFor rules t in
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
and getRulesFor rules t =
  Ruletrie.getRules rules t
