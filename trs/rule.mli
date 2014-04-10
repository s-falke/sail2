(**
  Interface of rules.

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

(** {2 Types} *)

(** A rewrite rule. *)
type rule = Rule of Term.term * Term.term * (Constraint.cond list) (** Obviously, a triple [(lhs, rhs, cond)]. *)

(** {2 Exceptions} *)

(** Thrown when lhs and rhs have different sorts. *)
exception SortConflictRule of string

(** Thrown when the variable condition is violated. *)
exception VariableConflict of string

(** Thrown when lhs is a variable. *)
exception NoRule of string

(** {2 Functions} *)

(** Returns the lhs of a rule. *)
val getLeft : rule -> Term.term

(** Returns the rhs of a rule. *)
val getRight : rule -> Term.term

(** Returns the constraint of a rule. *)
val getConstraint : rule -> Constraint.cond list

(** Applies a substitution to a rule. *)
val applySubstitution : rule -> Substitution.substitution -> rule

(** Returns a string representing the a rule. *)
val toString : rule -> string

(** Returns a string representing a rule with sorts for variables. *)
val toStringSorts : rule -> string

(** Returns a string representing the a rule for AProVE. *)
val toStringAProVE : rule -> string

(** Determines whether a rule is Z-free. *)
val isZfree : rule -> bool

(** Determines whether a rule is Z-free on its LHS. *)
val isZfreeLeft : rule -> bool
