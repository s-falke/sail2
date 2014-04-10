(**
  Interface of substitutions.

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

(** A substitution from variables to terms. *)
type substitution = Sub of (string * Term.term) list  (** A list of [(variable name, term)] pairs. *)

(** {2 Functions} *)

(** {3 Creating} *)

(** Returns an empty substitution. *)
val createEmptySubstitution : unit -> substitution

(** Extends a substitution by mapping a variable (name) to a term. *)
val extendSubstitution : substitution -> string -> Term.term -> substitution

(** {3 Other} *)

(** Applies a substitution to a term. *)
val applyToTerm : substitution -> Term.term -> Term.term

(** Returns binding for a variable.
    @raise Not_found If there is no binding.
*)
val getBinding : substitution -> string -> Term.term

(** Is there a binding for a variable? *)
val hasBinding : substitution -> string -> bool

(** Returns a new substitution that is the restriction to a set of variables. *)
val restrict : substitution -> string list -> substitution

(** Determines whether a term is changed by a substitution. *)
val changes : substitution -> Term.term -> bool

(** Composes two substitutions. *)
val compose : substitution -> substitution -> substitution

(** Determines whether a substitution is a variable renaming. *)
val isVarRenaming : substitution -> bool

(** Returns a string representing a substitution. *)
val toString : substitution -> string
