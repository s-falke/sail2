(*
  Implementation of Delete rule.

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

(* Time spend in the smt proof in msec. *)
let smtTime = ref 0.0

(* Applies. *)
let rec apply f =
  smtTime := 0.0;
  match f with
    | True | False -> None
    | Formula fs -> let fs' = remove fs in
                        if fs' = fs then
                          None
                        else if fs' = [] then
                          Some (True, [Proof.Direct (Formula fs, "deletion of trivial atoms", True)])
                        else
                          Some (Formula fs', [Proof.Direct (Formula fs, "deletion of trivial atoms", Formula fs')])
and remove fs =
  match fs with
    | [] -> []
    | (Atom (s, t, c))::fss -> if (s = t) || (isUnsatisfiable c) then
                                 remove fss
                               else
                                 (Atom (s, t, c))::(remove fss)

and isUnsatisfiable c =
  let start = Unix.gettimeofday () in
  let res = Decproc.isSatisfiablePAConjunction c in
  let stop = Unix.gettimeofday () in
    (
      smtTime := !smtTime +. ((stop -. start) *. 1000.0);
      match res with
        | Ynm.Yes -> false
        | Ynm.No -> true
        | Ynm.Maybe -> false
    )
