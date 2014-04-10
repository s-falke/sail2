(**
  Interface of TRSs.

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

(** A term rewriting system. *)
type trs = Trs of Signature.signature * (Rule.rule list) * Ruletrie.ruletrie
(** A triple [(underlying signature, rewrite rules, trie storing the rules)]. *)

(** {2 Functions} *)

(** {3 Checking} *)

(** Determines whether a function symbol is defined. *)
val isDefined : trs -> string -> bool

(** Determines whether a TRS is constructor based, i.e., all lhs's
    of rules contain only constructors below the root. *)
val isConstructorBased : trs -> bool

(** Determines whether a TRS has no nested recursive calls. *)
val isNonnestedDefined : trs -> bool

(** Determines whether a TRS has defined function symbols on left sides
    below the root. *)
val hasDefinedOnLeftSides : trs -> bool

(** Determines whether a TRS contains builtins on left sides. *)
val hasBuiltinsOnLeftSides : trs -> bool

(** Determines whether a TRS is left-linear. *)
val isLeftLinear : trs -> bool

(** Determines whether a TRS is overlapping. *)
val isOverlapping : trs -> bool

(** Checks whether the functions in a TRS are completely defined.  Returns
    (missing patterns, patterns where disjunction of constraints is not valid). *)
val checkComplete : trs -> Term.term list * Term.term list

(** Checks whether each sort in a TRS has at least two constructor ground terms.
    Returns a list of sorts not satisfying this condition. *)
val checkConstructors : trs -> string list

(** Checks whether there a constructor symbols with resulting sort Int. *)
val hasIntResultConstructor : trs -> bool

(** Checks whether a TRS is Z-free. *)
val isZfree : trs -> bool

(** Checks whether a TRS is Z-free in its LHSs. *)
val isZfreeLeft : trs -> bool

(** Checks whether a TRS is unconstrained. *)
val isUnconstrained : trs -> bool

(** {3 Accessing} *)

(** Returns the signature of a TRS. *)
val getSignature : trs -> Signature.signature

(** Returns the rules of a TRS. *)
val getRules : trs -> Rule.rule list

(** Returns the rules of a TRS defining a function symbol. *)
val getRulesForSymbol : trs -> string -> Rule.rule list

(** Returns the ruletrie of a TRS. *)
val getRuleTrie : trs -> Ruletrie.ruletrie

(** Returns the function symbols of a TRS. *)
val getSymbols : trs -> string list

(** Returns the defined function symbols of a TRS. *)
val getDefined : trs -> string list

(** Returns the constructor symbols of a TRS. *)
val getConstructors : trs -> string list

(** Returns the constructor constants of a TRS. *)
val getConstructorConstants : trs -> string list

(** Returns the constructor non-constants of a TRS. *)
val getConstructorNonConstants : trs -> string list

(** Returns the constructor symbols of a given sort from a TRS. *)
val getConstructorsForSort : trs -> string -> string list

(** Returns the constructor constants of a given sort from a TRS. *)
val getConstructorConstantsForSort : trs -> string -> string list

(** Returns the constructor non-constants of a given sort from a TRS. *)
val getConstructorNonConstantsForSort : trs -> string -> string list

(** Returns the sorts of a TRS. *)
val getSorts : trs -> string list

(** Returns the sorts that are used in constructors of a given sort
    (reflexive-transitive) in a TRS. *)
val getDepSorts : trs -> string -> string list

(** {3 Normalizing} *)

(** Normalizes a term with a TRS.  This might be nonterminating... *)
val normalize : trs -> Term.term -> Term.term

(** Normalizes a Z-free term with a Z-free TRS.  This might be nonterminating... *)
val normalizeZfree : trs -> Term.term -> Term.term

(** Normalizes a term with PA rules. *)
val normalizePA : Term.term -> Term.term

(** {3 Other} *)

(** Returns a TRS in AProVE's format. *)
val toAProVE : trs -> string

(** Returns a TRS in AProVE's format as a list of lines. *)
val toAProVELines : trs -> string list

(** Returns a string representing a TRS. *)
val toString : trs -> string

(** Returns a string representing a TRS containing sorts for variables. *)
val toStringSorts : trs -> string

(** Returns an HTML string for a TRS. *)
val toHTML : trs -> string

(** Returns datatype declarations for constructors in CVC3 format. *)
val getConstructorsCVC3 : trs -> string
