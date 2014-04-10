(**
  Interface of formulas.

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

(** Equality between two terms, with a constraint. *)
type atom = Atom of Term.term * Term.term * Constraint.cond list

(** Conjunction of atoms. *)
type formula = Formula of atom list | True | False

(** {2 Functions} *)

(** Returns all variables (terms) of a formula. *)
val getVars : formula -> Term.term list

(** Returns all function symbols occuring in a formula. *)
val getFuns : formula -> string list

(** Applies a substitution to a formula. *)
val applySubstitution : formula -> Substitution.substitution -> formula

(** Returns a string representing a formula. *)
val toString : formula -> string

(** Returns a string representing a formula containing the sorts of variables. *)
val toStringSorts : formula -> string

(** Returns a string for a formula in HTML, taking a set of defined symbols. *)
val toHTML : formula -> string list -> string

(** Checks whether a formula is fully typed. *)
val isFullyTyped : formula -> bool

(** Returns all subterms of a formula. *)
val getAllSubterms : formula -> Term.term list

(** Returns all subterms of a formula headed by a given symbol. *)
val getAllSubtermsForSymbol : formula -> string -> Term.term list

(** Returns all subterms of a formula headed by a symbol from a given set. *)
val getAllSubtermsForSymbols : formula -> string list -> Term.term list

(** Returns all maximal terms in a formula. *)
val getAllMaximalTerms : formula -> Term.term list

(** Normalizes a formula with a TRS. *)
val normalize : Trs.trs -> formula -> formula

(** Normalizes a Z-free formula with a Z-free TRS. *)
val normalizeZfree : Trs.trs -> formula -> formula

(** Normalizes a formula with PA rules. *)
val normalizePA : formula -> formula

(** Determines whether a formula is Z-free. *)
val isZfree : formula -> bool

(** Determines whether a formula is Z-free on its LHSs. *)
val isZfreeLeft : formula -> bool

(** Determines whether a formula contains only function symbols from the given set. *)
val isBasedOn : string list -> formula -> bool

(** Determines whether a formula is valid in LIAC. *)
val isValidLIACConjunction : Trs.trs -> formula -> Ynm.ynm

(** Determines whether a formula is satisfiable in LIAC. *)
val isSatisfiableLIACConjunction : Trs.trs -> formula -> Ynm.ynm

(** Determines whether a formula and a constraint list are satisfiable in LIAC. *)
val isSatisfiableLIACConjunctionConstraint : Trs.trs -> formula -> Constraint.cond list -> Ynm.ynm

(** Determines whether a formula implies a formula in LIAC. *)
val isValidLIACImplication : Trs.trs -> formula -> formula -> Ynm.ynm

(** Determines whether a constraint list and a formula imply a formula in LIAC. *)
val isValidLIACImplicationConstraint : Trs.trs -> Constraint.cond list -> formula -> formula -> Ynm.ynm
