(*
  Implementation of rules.

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

type rule = Rule of Term.term * Term.term * Constraint.cond list

(* Thrown when lhs and rhs have different sorts. *)
exception SortConflictRule of string

(* Thrown when the variable condition is violated. *)
exception VariableConflict of string

(* Thrown when lhs is a variable. *)
exception NoRule of string

(* Returns a string representing a rule. *)
let rec toString (Rule (l, r, c)) =
  (Term.toString l) ^ " -> " ^ (Term.toString r) ^ (condString c)
and condString c =
  if c = [] then
    ""
  else
    " [ " ^ (String.concat " /\\ " (List.map Constraint.toString c)) ^ " ]"

(* Returns a string representing a rule with sorts for variables. *)
let rec toStringSorts (Rule (l, r, c)) =
  (Term.toStringSorts l) ^ " -> " ^ (Term.toStringSorts r) ^ (condStringSorts c)
and condStringSorts c =
  if c = [] then
    ""
  else
    " [ " ^ (String.concat " /\\ " (List.map Constraint.toStringSorts c)) ^ " ]"

(** Returns a string representing a rule for AProVE. *)
let toStringAProVE ru =
  toString ru

(* Returns the lhs of a rule. *)
let getLeft (Rule (l, _, _)) =
  l

(* Returns the rhs of a rule. *)
let getRight (Rule (_, r, _)) =
  r

(* Returns the constraint of a rule. *)
let getConstraint (Rule (_, _, c)) =
  c

(* Applies a substitution to a rule. *)
let applySubstitution (Rule (l, r, c)) sub =
  Rule (Substitution.applyToTerm sub l, Substitution.applyToTerm sub r, List.map (Constraint.applySubstitution sub) c)

(** Determines whether a rule is Z-free. *)
let isZfree (Rule (l, r, _)) =
  (Term.isZfree l) && (Term.isZfree r)

(** Determines whether a rule is Z-free on its LHS. *)
let isZfreeLeft (Rule (l, _, _)) =
  Term.isZfree l
