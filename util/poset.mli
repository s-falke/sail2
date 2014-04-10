(**
  Interface of partially ordered sets.

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

(** A partially ordered set. *)
type 'a poset = PO of 'a list * (bool array)  (** Underlying base set and matrix of the relation. *)

(** {2 Functions} *)

(** {3 Creating} *)

(** Creates an empty poset on a baseset. *)
val create : 'a list -> 'a poset

(** Sets first element bigger than second element in a poset, returning the changed poset. *)
val setBigger : 'a poset -> 'a -> 'a -> 'a poset

(** {3 Accessing} *)

(** Determines whether first element is bigger than second element in a poset. *)
val isBigger : 'a poset -> 'a -> 'a -> bool

(** Determines all elements such that the element is bigger in the poset. *)
val getAllBigger : 'a poset -> 'a -> 'a list
