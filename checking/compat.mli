(**
  Interface of compatibility of function symbols.

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

(** Computes Compat for a TRS and caches the results. *)
val compute : Trs.trs -> unit

(** Returns Compat for two function symbols, i.e., is the first compatible with the second on given position? *)
val isCompat : string -> string -> int -> bool

(** Returns a string for the currently cached Compat. *)
val toString : unit -> string
