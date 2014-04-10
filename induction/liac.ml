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

(* Applies. *)
let rec apply ttrs f =
  smtTime := 0.0;
  match f with
    | Formula.True | Formula.False | Formula.Formula [] -> None
    | Formula.Formula atoms -> doApply ttrs f atoms
and hasFalse = ref false
and doApply ttrs f atoms =
  hasFalse := false;
  smtTime := 0.0;
  let new_atoms = List.filter (isNotValid ttrs (Trs.getConstructors ttrs)) atoms in
    if !hasFalse then
      Some (Formula.False, [Proof.Direct (f, "the decision procedure for LIAC", Formula.False)])
    else if new_atoms = atoms then
      None
    else if new_atoms = [] then
      Some (Formula.True, [Proof.Direct (f, "the decision procedure for LIAC", Formula.True)])
    else
      let newf = Formula.Formula new_atoms in
        Some (newf, [Proof.Direct (f, "the decision procedure for LIAC", newf)])
and isNotValid ttrs conss atom =
  if not (isApplicable conss atom) then
    true
  else
    let start = Unix.gettimeofday () in
    let res = doSimp ttrs atom in
    let stop = Unix.gettimeofday () in
      (
        smtTime := !smtTime +. ((stop -. start) *. 1000.0);
        match res with
          | Ynm.Yes -> false
          | Ynm.No -> (hasFalse := true; true)
          | Ynm.Maybe -> true
      )
and doSimp ttrs atom =
  Formula.isValidLIACConjunction ttrs (Formula.Formula [atom])
and isApplicable conss (Formula.Atom (s, t, _)) =
  (Term.isBasedOn conss s) && (Term.isBasedOn conss t)
