(**
  Interface of various utilities.

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

(** Removes duplicates from a list. *)
val remdup : 'a list -> 'a list

(** Removes the first occurence of an element from a list. *)
val remove : 'a list -> 'a -> 'a list

(** Removes all occurence of elements that also occurs in the second argument from a list. *)
val removeAll : 'a list -> 'a list -> 'a list

(** Determines whether a list is a set. *)
val isSet : 'a list -> bool

(** Determines the number of occurences of an element in a list. *)
val getcount : 'a -> 'a list -> int
