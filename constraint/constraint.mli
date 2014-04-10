(**
  Interface of integer constraints.

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

(** Integer constraints. *)
type cond =
  | Eq of Term.term * Term.term
  | Geq of Term.term * Term.term
  | Gtr of Term.term * Term.term

(** {2 Functions} *)

(** Returns a string representing a constraint. *)
val toString : cond -> string

(** Returns a string representing a constraint with sorts for variables. *)
val toStringSorts : cond -> string

(** Applies a substitution. *)
val applySubstitution : Substitution.substitution -> cond -> cond

(** Returns the variables (strings) of a constraint. *)
val getVars : cond -> string list

(** Returns the variables (terms) of a constraint. *)
val getVarsAsTerms : cond -> Term.term list

(** Returns the function symbols of a constraint. *)
val getFuns : cond -> string list

(** Returns a constraint in SMTLib format. *)
val toSMT : cond -> string

(** Returns a constraint in CVC3 format. *)
val toCVC3 : cond -> string

(** Checks whether a constraint is based on Z. *)
val isZbased : cond -> bool
