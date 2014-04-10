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
  if not (isApplicable ttrs f) then
    None
  else
    let start = Unix.gettimeofday () in
    let res = doSimp ttrs f in
    let stop = Unix.gettimeofday () in
      (
        smtTime := (stop -. start) *. 1000.0;
        match res with
          | Ynm.Yes -> Some (Formula.True, [Proof.Direct (f, "the decision procedure for LIAC", Formula.True)])
          | Ynm.No -> Some (Formula.False, [Proof.Direct (f, "the decision procedure for LIAC", Formula.False)])
          | Ynm.Maybe -> None
      )
and doSimp ttrs f =
  Formula.isValidLIACConjunction ttrs f
and isApplicable ttrs f =
  Formula.isBasedOn (Trs.getConstructors ttrs) f
