(*
  Implementation of integer constraints.

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

type cond =
  | Eq of Term.term * Term.term
  | Geq of Term.term * Term.term
  | Gtr of Term.term * Term.term

(* Returns a string representing a constraint. *)
let toString c =
  match c with
    | Eq (s, t) -> (Term.toString s) ^ " = " ^ (Term.toString t)
    | Geq (s, t) -> (Term.toString s) ^ " >= " ^ (Term.toString t)
    | Gtr (s, t) -> (Term.toString s) ^ " > " ^ (Term.toString t)

(* Returns a string representing a constraint with sorts for variables. *)
let toStringSorts c =
  match c with
    | Eq (s, t) -> (Term.toStringSorts s) ^ " = " ^ (Term.toStringSorts t)
    | Geq (s, t) -> (Term.toStringSorts s) ^ " >= " ^ (Term.toStringSorts t)
    | Gtr (s, t) -> (Term.toStringSorts s) ^ " > " ^ (Term.toStringSorts t)

(* Applies a substitution. *)
let applySubstitution sigma c =
  match c with
    | Eq (s, t) -> Eq (Substitution.applyToTerm sigma s, Substitution.applyToTerm sigma t)
    | Geq (s, t) -> Geq (Substitution.applyToTerm sigma s, Substitution.applyToTerm sigma t)
    | Gtr (s, t) -> Gtr (Substitution.applyToTerm sigma s, Substitution.applyToTerm sigma t)

(* Returns the variables of a constraint. *)
let getVars c =
  match c with
    | Eq (s, t) -> Util.remdup ((Term.getVars s) @ (Term.getVars t))
    | Geq (s, t) -> Util.remdup ((Term.getVars s) @ (Term.getVars t))
    | Gtr (s, t) -> Util.remdup ((Term.getVars s) @ (Term.getVars t))

(* Returns the variables of a constraint. *)
let getVarsAsTerms c =
  match c with
    | Eq (s, t) -> Util.remdup ((Term.getVarsAsTerms s) @ (Term.getVarsAsTerms t))
    | Geq (s, t) -> Util.remdup ((Term.getVarsAsTerms s) @ (Term.getVarsAsTerms t))
    | Gtr (s, t) -> Util.remdup ((Term.getVarsAsTerms s) @ (Term.getVarsAsTerms t))

(* Returns the function symbols of a constraint. *)
let getFuns c =
  match c with
    | Eq (s, t) -> Util.remdup ((Term.getFuns s) @ (Term.getFuns t))
    | Geq (s, t) -> Util.remdup ((Term.getFuns s) @ (Term.getFuns t))
    | Gtr (s, t) -> Util.remdup ((Term.getFuns s) @ (Term.getFuns t))

(* Returns a constraint in SMTLib format. *)
let rec toSMT c =
  match c with
    | Eq (s, t) -> "=" ^ "(" ^ (toSMTTerm s) ^ ") (" ^ (toSMTTerm t) ^ ")"
    | Geq (s, t) -> ">=" ^ "(" ^ (toSMTTerm s) ^ ") (" ^ (toSMTTerm t) ^ ")"
    | Gtr (s, t) -> ">" ^ "(" ^ (toSMTTerm s) ^ ") (" ^ (toSMTTerm t) ^ ")"
and toSMTTerm t =
  if Term.isVariable t then
    Term.toString t
  else
    let f = Term.getTopSymbol t
    and args = Term.getArgs t in
      if f = "0" then
        "0"
      else if f = "1" then
        "1"
      else if f = "+" then
        "(+ " ^ (toSMTTerm (List.nth args 0)) ^ " " ^ (toSMTTerm (List.nth args 1)) ^ ")"
      else
        "(- " ^ (toSMTTerm (List.nth args 0)) ^ ")"

(* Returns a constraint in CVC3 format. *)
let toCVC3 c =
  match c with
    | Eq (s, t) -> (Term.toCVC3 s) ^ " = " ^ (Term.toCVC3 t)
    | Geq (s, t) -> (Term.toCVC3 s) ^ " >= " ^ (Term.toCVC3 t)
    | Gtr (s, t) -> (Term.toCVC3 s) ^ " > " ^ (Term.toCVC3 t)

(* Checks whether a constraint is based on Z. *)
let isZbased c =
  let zs = ["0";"1";"+";"-"] in
    match c with
      | Eq (s, t) | Geq (s, t) | Gtr (s, t) -> (Term.isBasedOn zs s) && (Term.isBasedOn zs t)
