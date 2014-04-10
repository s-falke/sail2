(**
  Interface of term-related functions used for parsing.

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

(** General parse exception. *)
exception ParseException of int * string

(** Thrown when arities do not match. *)
exception ArityConflict of (string * int * int)

(** Thrown when sorts do not match. *)
exception SortConflict of (string * int)

(** Thrown when a variable is used with two sorts. *)
exception SortConflictVar of (string * string * string)

(** {2 Functions} *)

(** {3 Checking} *)

(** Checks whether a term conforms to a given signature.
    @raise Signature.NotInSignature If the term contains a function symbol not in the signature.
    @raise ArityConflict If the term contains a function application with the wrong number of arguments.
    @raise SortConflict If the term is not sort-correct. *)
val checkTerm : Signature.signature -> Term.term -> unit

(** Get sort assumptions for variables of the a term for a given signature.
    A sort assumption consists of pairs (var name, inferred sort).
    @raise SortConflictVar If a variable is used with two different sorts. *)
val sortAssumption : Signature.signature -> Term.term -> (string * string) list

(** Determines whether the first sort assumption contains the second sort
    assumption.  The function checks whether all assumptions contained in
    the second sort assumption are compatible with assumptions in the first
    sort assumption, i.e., are more specific.
    @raise SortConflictVar If the second sort assumption contains a more general assumption than the first. *)
val containsAssumption : (string * string) list -> (string * string) list -> unit

(** Determines whether two assumptions agree on shared variables.
    @raise SortConflictVar If they disagree on a shared variable. *)
val agreeAssumptions : (string * string) list -> (string * string) list -> unit

(** Merges two sort assumptions.  Only use if agreeAssumptions was successfull. *)
val mergeSortAssumptions : (string * string) list -> (string * string) list -> (string * string) list

(** {3 Accessing} *)

(** Returns a sorted term constructed from a unsorted term by setting the
    sorts sorts of the variables as specified in a sort assumption. *)
val getSortedTerm : (string * string) list -> Term.term -> Term.term

(** Get inferred sort for a variable (term) from a sort assumption. *)
val getSortFor : (string * string) list -> Term.term -> string
