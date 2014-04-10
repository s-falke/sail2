(**
  Interface of positions.

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

(** A position in a term. *)
type position =
  | Root                   (** Root position of a term. *)
  | Pos of int * position  (** Descend into i-th subterm. *)
  | End                    (** "End" position needed for term-indexing. *)

(** {2 Exceptions} *)

(** Thrown if a position is illegal. *)
exception IllegalPosition

(** {2 Functions} *)

(** Is first position a prefix of second position? *)
val isPrefixPosition : position -> position -> bool

(** Returns a string representing a position. *)
val toString : position -> string

(** Adds argument at end. *)
val addAtEnd : position -> int -> position
