(**
  Interface of syntactic unification/matching.

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

(** {2 Exceptions} *)

(** Occurs check failure. *)
exception Occur of (string * Term.term)

(** Function symbol clash failure. *)
exception Clash of (string * string)

(** Not matchable. *)
exception NoMatch of (Term.term * Term.term)

(** {2 Functions} *)

(** {3 Unifying} *)

(** Computes an mgu of two terms.
    @raise Occur If an occur failure is encountered.
    @raise Clash If a function symbol clash is encountered.
*)
val unify : Term.term -> Term.term -> Substitution.substitution

(** {3 Matching} *)

(** Computes a substitution such that the image of the first term is the second term.
    @raise NoMatch If first term does not match second term. *)
val matchTerms : Term.term -> Term.term -> Substitution.substitution

(** Computes a substitution option such that the image of the first term is the second term. *)
val matchTermsNoException : Term.term -> Term.term -> Substitution.substitution option
