(**
  Interface of signatures.

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

(** A signature containing information about the arity of function symbols. *)
type signature = Sig of (string * int * string list * string) list
(** A list of tuples [(name, arity, argument sorts, target sort)]. *)

(** {2 Exceptions} *)

(** Thrown when a function symbol does not occur in a signature. *)
exception NotInSignature of string

(** Thrown when a function symbol to be added already occurs in a signature. *)
exception AlreadyInSignature of string

(** Thrown when sort decl uses unknown sort. *)
exception UnknownSort of string * string

(** {2 Functions} *)

(** {3 Creating} *)

(** Returns an empty signature.  *)
val createEmpty : unit -> signature

(** Adds a function symbol with its arity to a signature.
    @param def The name, number of arguments, sorts of the arguments, and target sort. *)
val addFun : signature -> (string * int * string list * string) -> signature

(** Returns a sub-signature. *)
val getSubSignature : signature -> string list -> signature

(** {3 Accessing} *)

(** Checks whether a signature contains a function symbol. *)
val contains : signature -> string -> bool

(** Returns the arity of a function symbol in a signature. *)
val getArity : signature -> string -> int

(** Returns the sort of a function symbol in a signature. *)
val getSort : signature -> string -> string

(** Returns the argument sorts of a function symbol in a signature. *)
val getArgSorts : signature -> string -> string list

(** Returns the names of all function symbols in a signature. *)
val getNames : signature -> string list

(** Returns all sorts in a signature. *)
val getSorts : signature -> string list

(** {3 Other} *)

(** Returns a string representing a signture. *)
val toString : signature -> string

(** Returns a string representing a signture for AProVE. *)
val toAProVE : signature -> string

(** Returns a list of strings representing a signture for AProVE. *)
val toAProVELines : signature -> string list

(** Checks whether there is a function with resulting sort Int other than 0, 1, +, -. *)
val hasIntResult : signature -> bool
