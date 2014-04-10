(**
  Interface of tries used for indexing the rules.

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

(** Trie for fast retrieval of rewrite rules. *)
type ruletrie = Trie of (Rule.rule list) option * (string * ruletrie) list
(** Each node possibly stores rules, and has sons indexed by function symbols or "*". *)

(** {2 Functions} *)

(** {3 Creating} *)

(** Returns an empty trie. *)
val empty : unit -> ruletrie

(** Creates a trie containing all rules from a set of rules. *)
val createRuleTrie : Rule.rule list -> ruletrie

(** Inserts a rule into a ruletrie. *)
val insert : ruletrie -> Rule.rule -> ruletrie

(** {3 Accessing} *)

(** Returns the rules for a term from a ruletrie. *)
val getRules : ruletrie -> Term.term -> Rule.rule list
