(**
  Interface of ImpEq.

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

type impeq = (string * int * int * (string * int * int) list) list (** list of <f, l1, l2, C> where C is a list of <g, k1, k2> *)

(** {2 Functions} *)

(** Computes ImpEq for each rule in a TRS and caches the results. *)
val compute : Trs.trs -> unit

(** Returns ImpEq for a set of rules. *)
val getForRules : Rule.rule list -> impeq

(** Returns ImpEq' for a set of rules. *)
val getForRules' : Rule.rule list -> impeq

(** Returns a string representing an impeq. *)
val toString : impeq -> string
