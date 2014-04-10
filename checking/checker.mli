(**
  Interface of Meta-Checker.

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

(** Result of checking. *)
type verdict = Neither | Liac | Simple | Nested (*| Complex*)

(** {2 Global variables} *)

(** Last verdict. *)
val lastVerdict : verdict ref

(** {2 Functions} *)

(** Checks a formula w.r.t. a TRS. *)
val check : Trs.trs -> Formula.formula -> Proof.proof * Formula.formula

(** Convert verdict to string. *)
val toString : verdict -> string
