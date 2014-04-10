(**
  Interface of implicit induction.

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

(** {2 Global variables} *)

(** Time spend checking the conjecture in msec. *)
val checkTime : float ref

(** Time spend proofing the conjecture in msec. *)
val proofTime : float ref

(** Time spend in the termination proof in msec. *)
val terminationTime : float ref

(** Time spend in the smt proof in msec. *)
val smtTime : float ref

(** {2 Functions} *)

(** Applies strategy with a TRS to a formula, producing a new formula and a proof. *)
val apply : Trs.trs -> (Trs.trs -> bool) -> Formula.formula -> (Formula.formula * Proof.proof)
