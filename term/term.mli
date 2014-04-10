(**
  Interface of terms.

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

(** First-order terms. *)
type term =
  | Var of string * string         (** Variables are [(name, sort)] pairs. *)
  | Fun of string * term list      (** Function application, [(function symbol, arguments)]. *)

(** {2 Functions} *)

(** {3 Creating} *)

(** Creates a variable with a name and a sort. *)
val createVar : string -> string -> term

(** Creates a function application with function name and arguments. *)
val createFun : string -> term list -> term

(** {3 Checking} *)

(** Is is a variable? *)
val isVariable : term -> bool

(** Is it a function application? *)
val isFun : term -> bool

(** Checks whether a term contains the variable (name). *)
val containsVar : string -> term -> bool

(** Checks whether the first term is a subterm of the second term. *)
val contains : term -> term -> bool

(** Determines whether a term contains only function symbols from the given set. *)
val isBasedOn : string list -> term -> bool

(** Determines whether a term is linear. *)
val isLinear : term -> bool

(** Checks whether a term is fully typed. *)
val isFullyTyped : term -> bool

(** Determines whether first term contains second term as direct argument. *)
val isArg : term -> term -> bool

(** Determines whether a term is Z-free. *)
val isZfree : term -> bool

(** {3 Destructing} *)

(** Returns the variables (names) occuring in a term. *)
val getVars : term -> string list

(** Returns the variables (terms) occuring in a term. *)
val getVarsAsTerms : term -> term list

(** Returns the non-linear variables (terms) of a term. *)
val getNonlinearVars : term -> term list

(** Returns all functions occuring in a term. *)
val getFuns : term -> string list

(** Returns the sort of a term relative to a signature. *)
val getSort : Signature.signature -> term -> string

(** Returns the sort of a variable (term). *)
val getVarSort : term -> string

(** Returns the names and sorts of all variables in a term. *)
val getVarNameSorts : term -> (string * string) list

(** Returns the top symbol of a term. *)
val getTopSymbol : term -> string

(** Returns the arguments of a function application. *)
val getArgs : term -> term list

(** Returns the number of arguments of a term. *)
val getNumArgs : term -> int

(** Returns the p-String of a term. *)
val getPstring : term -> string list

(** Returns the subterm of a term at a given position.
    @raise Position.IllegalPosition If the position is not legal in the term.
*)
val getSubtermAt : term -> Position.position -> term

(** Returns the symbol in a term at a given position.
    @raise Position.IllegalPosition If the position is not legal in the term.
*)
val getSymbolAt : term -> Position.position -> string

(** Returns the positions of a term. *)
val getPositions : term -> Position.position list

(** Returns all subterms of a term. *)
val getAllSubterms : term -> term list

(** Returns all subterms of a term with their positions. *)
val getAllSubtermsWithPositions : term -> (term * Position.position) list

(** Returns all subterms of a term that are headed by a function symbol. *)
val getAllSubtermsForSymbol : term -> string -> term list

(** Returns all subterms of a term that are headed by a symbol from given set. *)
val getAllSubtermsForSymbols : term -> string list -> term list

(** Returns all maximal subterms of a term that are headed by a symbol from given set. *)
val getAllMaximalSubtermsForSymbols : term -> string list -> term list

(** Returns all subterms occuring multiple times in a term. *)
val getAllDuplicateSubterms : term -> term list

(** {3 Other} *)

(** Replaces the subterm of a term at given position by another term.
    @raise Position.IllegalPosition If the position is not legal in the first term.
*)
val replaceSubtermAt : term -> Position.position -> term -> term

(** Returns a string representing a term. *)
val toString : term -> string

(** Returns a string representing a term with sorts for variables. *)
val toStringSorts : term -> string

(** Returns a term in HTML, where the defined function symbols is specified. *)
val toHTML : term -> string list -> string

(** Returns a Z-term in SMT-LIB format. *)
val toSMT : term -> string

(** Returns a string representing a term in CVC3 format. *)
val toCVC3 : term -> string

(** Returns the argument position of the second term in the first term. *)
val argPos : term -> term -> Position.position
