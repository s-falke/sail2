(**
  Interface of definition and call schemes.

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

(** Computes DefR for a term. *)
val computeDefR : Trs.trs -> Term.term -> (Rule.rule * Substitution.substitution) list

(** Checks whether two definition schemes are identical for a set of variables. *)
val areIdentical : (Rule.rule * Substitution.substitution) list -> (Rule.rule * Substitution.substitution) list -> string list -> bool

(** Get the "corresponding" entry. *)
val getCorresponding : Rule.rule * Substitution.substitution -> (Rule.rule * Substitution.substitution) list -> string list -> (Rule.rule * Substitution.substitution) option

(** Computes Call for an element of a definition scheme and a term. *)
val computeCall : Trs.trs -> Rule.rule * Substitution.substitution -> Term.term -> Substitution.substitution list
