(**
  Interface of proofs.

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

(** A single step in a proof. *)
type proof_step =
  | Leaf of Formula.formula                                 (** No further steps applicable. *)
  | Direct of Formula.formula * string * Formula.formula    (** Transformation into one single new formula. *)
  | Expand of Formula.formula * string * Rule.rule list * Formula.formula  (** Expansion for implicit induction. *)
  | Liac of Formula.formula * Formula.formula (** Check for LIAC-based conjecture. *)
  | Simple of Formula.formula * bool * Formula.atom option * string list * Rule.rule option * Formula.formula  (** Check for simple conjecture. *)
  | Nested of Formula.formula * bool * Formula.atom option * string list * Rule.rule option * (string * string) option * Formula.formula  (** Check for simple nested conjecture. *)
  | Complex of Formula.formula * bool * Formula.atom option * string list * Rule.rule option * (string * string) option * Term.term option * Formula.formula  (** Check for complex conjecture. *)

type proof = proof_step list  (** A collection of single steps. *)

(** {2 Functions} *)

(** Returns a string representing a proof for a formula. *)
val toString : proof -> Formula.formula -> string

(** Returns a proof for a formula in HTML. *)
val toHTML : proof -> Formula.formula -> string list -> string
