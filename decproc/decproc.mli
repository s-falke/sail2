(**
  Interface of decision procedure.

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

(** {2 Functions} *)

(** Determines whether a conjunction of constraints is valid in PA. *)
val isValidPAConjunction : Constraint.cond list -> Ynm.ynm

(** Determines whether a conjunction of constraints is satisfiable in PA. *)
val isSatisfiablePAConjunction : Constraint.cond list -> Ynm.ynm

(** Determines whether the implication of a conjunction of constraints to a conjunction of constraints is valid in PA. *)
val isValidPAImplication : Constraint.cond list -> Constraint.cond list -> Ynm.ynm

(** Determines whether a disjunction of conjunctions of constraints is valid in PA. *)
val isValidPADisjunctionConjunction : Constraint.cond list list -> Ynm.ynm

(** Determines whether a disjunction of conjunctions of constraints is satisfiable in PA. *)
val isSatisfiablePADisjunctionConjunction : Constraint.cond list list -> Ynm.ynm
