(**
  Implementation of decision procedure.

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

let header logic =
  "(benchmark sail-formula\n  :status unknown\n  :logic " ^ logic

let midder ="\n  :formula "

let footer = "\n)"

let swap x =
  match x with
    | Ynm.Yes -> Ynm.No
    | Ynm.No -> Ynm.Yes
    | Ynm.Maybe -> x

(* Determines whether a conjunction of constraints is valid in PA. *)
let rec isValidPAConjunction c =
  if c = [] then
    Ynm.Yes
  else
    let vars = Util.remdup (List.concat (List.map Constraint.getVars c)) in
      let formstring = (header "QF_LIA") ^ (getVarsPA vars) ^ midder ^ (getNegFormulaConj c) ^ footer in
        swap (Yices.isSatisfiable formstring)
and getVarsPA vars =
  "  :extrafuns (" ^ (String.concat " " (List.map getVarsPAAux vars)) ^ ")\n"
and getVarsPAAux var =
  "(" ^ var ^ " Int)"
and getNegFormulaConj atoms =
  "(not (and " ^ (String.concat " " (List.map getAtomString atoms)) ^ "))\n"
and getAtomString atom =
  "(" ^ (Constraint.toSMT atom) ^ ")"

(* Determines whether a conjunction of constraints is satisfiable in PA. *)
let rec isSatisfiablePAConjunction c =
  if c = [] then
    Ynm.Yes
  else
    let vars = Util.remdup (List.concat (List.map Constraint.getVars c)) in
      let formstring = (header "QF_LIA") ^ (getVarsPA vars) ^ midder ^ (getFormulaConj c) ^ footer in
        Yices.isSatisfiable formstring
and getFormulaConj atoms =
  "(and " ^ (String.concat " " (List.map getAtomString atoms)) ^ ")\n"

(* Determines whether the implication of a conjunction of constraints to a conjunction of constraints is valid in PA. *)
let rec isValidPAImplication c1 c2 =
  if c1 = [] then
    isValidPAConjunction c2
  else if c2 = [] then
    swap (isSatisfiablePAConjunction c1)
  else
    let vars = Util.remdup (List.concat (List.map Constraint.getVars (c1 @ c2))) in
      let formstring = (header "QF_LIA") ^ (getVarsPA vars) ^ midder ^ (getFormulaNegImpl c1 c2) ^ footer in
        swap (Yices.isSatisfiable formstring)
and getFormulaNegImpl c1 c2 =
  "(not (implies " ^ (getFormulaConj c1) ^ (getFormulaConj c2) ^ "))"

(* Determines whether a disjunction of conjunctions of constraints is valid in PA. *)
let rec isValidPADisjunctionConjunction c =
  if c = [] then
    Ynm.No
  else if List.exists (fun l -> l = []) c then
    Ynm.Yes
  else
    let vars = Util.remdup (List.concat (List.map Constraint.getVars (List.concat c))) in
      let formstring = (header "QF_LIA") ^ (getVarsPA vars) ^ midder ^ (getNegFormulaDisjConj c) ^ footer in
        swap (Yices.isSatisfiable formstring)
and getNegFormulaDisjConj dualclauses =
  "(not (or " ^ (String.concat " " (List.map getFormulaConj dualclauses)) ^ "))\n"

(* Determines whether a disjunction of conjunctions of constraints is satisfiable in PA. *)
let rec isSatisfiablePADisjunctionConjunction c =
  if c = [] then
    Ynm.No
  else if List.exists (fun l -> l = []) c then
    Ynm.Yes
  else
    let vars = Util.remdup (List.concat (List.map Constraint.getVars (List.concat c))) in
      let formstring = (header "QF_LIA") ^ (getVarsPA vars) ^ midder ^ (getFormulaDisjConj c) ^ footer in
        Yices.isSatisfiable formstring
and getFormulaDisjConj dualclauses =
  "(or " ^ (String.concat " " (List.map getFormulaConj dualclauses)) ^ ")\n"
