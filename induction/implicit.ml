(*
  Implementation of implicit induction.

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

(* Time spend checking the conjecture in msec. *)
let checkTime = ref 0.0

(* Time spend proofing the conjecture in msec. *)
let proofTime = ref 0.0

(* Time spend in the termination proof in msec. *)
let terminationTime = ref 0.0

(* Time spend in the smt proof in msec. *)
let smtTime = ref 0.0

let hyps = ref (Ruletrie.empty ())
let hypsrules = ref []

(* Applies. *)
let rec apply ttrs terminates f =
  hyps := Ruletrie.empty ();
  hypsrules := [];
  smtTime := 0.0;
  let start = Unix.gettimeofday () in
  let (p, _) = Checker.check ttrs f in
  let stop = Unix.gettimeofday () in
    (
      checkTime := (stop -. start) *. 1000.0;
      let start2 = Unix.gettimeofday () in
      let (f', p') = doSimpStep ttrs terminates f in
      let stop2 = Unix.gettimeofday () in
        (
          terminationTime := !Expand.terminationTime;
          proofTime := ((stop2 -. start2) *. 1000.0) -. !terminationTime;
          if f = f' then
          (
            if !Checker.lastVerdict = Checker.Simple then
              (f, [Proof.Simple (f, false, None, [], None, f)])
            else if !Checker.lastVerdict = Checker.Nested then
              (f, [Proof.Nested (f, false, None, [], None, None, f)])
            else
              (f, [Proof.Leaf f])
          )
          else
            (f', p @ p')
        )
    )
and doSimpStep ttrs terminates f =
  doDelete (doLIAC ttrs (doLIACAll ttrs (doSimplifyLoop ttrs !hyps (doExpand ttrs terminates f))))
and doExpand ttrs terminates f =
  let tmp = Expand.apply ttrs terminates (Trs.getRules ttrs) f in
  (
    smtTime := !smtTime +. !Expand.smtTime;
    match tmp with
      | None -> (f, [])
      | Some (f', p) -> (extractHyps p; (f', p))
  )
and extractHyps p =
  match p with
    | [Proof.Expand (_, _, newhyps, _)] -> insertAll newhyps
    | _  -> ()
and insertAll newhyps =
  match newhyps with
    | [] -> ()
    | h::hh -> (
                 hyps := Ruletrie.insert !hyps h;
                 hypsrules := h::!hypsrules;
                 insertAll hh
               )
and doSimplifyLoop ttrs hyps (f, p) =
  let (f', p') = doSimplify ttrs hyps (f, p) in
    if f' = f then
      let (f'', p'') = doCaseSimplify ttrs (f', p') in
        if f'' = f' then
          (f'', p'')
        else
          doSimplifyLoop ttrs hyps (f'', p'')
    else
      doSimplifyLoop ttrs hyps (f', p')
and doSimplify ttrs hyps (f, p) =
  let tmp = Simplify.apply ttrs hyps f in
  (
    smtTime := !smtTime +. !Simplify.smtTime;
    match tmp with
      | None -> (f, p)
      | Some (f', p') -> (f', p @ p')
  )
and doCaseSimplify ttrs (f, p) =
  let tmp = CaseSimplify.apply ttrs f in
  (
    smtTime := !smtTime +. !CaseSimplify.smtTime;
    match tmp with
      | None -> (f, p)
      | Some (f', p') -> (f', p @ p')
  )
and doLIACAll ttrs (f, p) =
  let tmp = LiacAll.apply ttrs f in
  (
    smtTime := !smtTime +. !LiacAll.smtTime;
    match tmp with
      | None -> (f, p)
      | Some (f', p') -> (f', p @ p')
  )
(*
and doLIACGenAll ttrs (f, p) =
  let tmp = LiacGenAll.apply ttrs f in
  (
    smtTime := !smtTime +. !LiacGenAll.smtTime;
    match tmp with
      | None -> (f, p)
      | Some (f', p') -> (f', p @ p')
  )
*)
and doLIAC ttrs (f, p) =
  let tmp = Liac.apply ttrs f in
  (
    smtTime := !smtTime +. !Liac.smtTime;
    match tmp with
      | None -> (f, p)
      | Some (f', p') -> (f', p @ p')
  )
(*
and doLIACGen ttrs (f, p) =
  let tmp = LiacGen.apply ttrs f in
  (
    smtTime := !smtTime +. !LiacGen.smtTime;
    match tmp with
      | None -> (f, p)
      | Some (f', p') -> (f', p @ p')
  )
*)
and doDelete (f, p) =
  let tmp = Delete.apply f in
  (
    smtTime := !smtTime +. !Delete.smtTime;
    match tmp with
      | None -> (f, p)
      | Some (f', p') -> (f', p @ p')
  )
