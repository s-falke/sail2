(**
  Interface of the Simplify rule.  Assumes that the formula has been
  normalized with Simplify before.


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

(** {2 Global variables} *)

(** Time spend in the SMT solver in msec. *)
val smtTime : float ref

(** {2 Functions} *)

(** Applies Simplify with a TRS and hypotheses to a formula, producing a new formula and a proof. *)
val apply : Trs.trs -> Formula.formula -> (Formula.formula * Proof.proof) option
