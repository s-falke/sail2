(*
  Implementation of substitutions.

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

type substitution = Sub of (string * Term.term) list

(* Returns an empty substitution. *)
let createEmptySubstitution () = Sub []

(* Removes all mappings for v from xs. *)
let rec remove v xs =
  match xs with
    | [] -> []
    | (y, t)::ys -> if v = y then
                      remove v ys
                    else
                      (y, t)::(remove v ys)

(* Extends a substitution by mapping a variable to a term. *)
let extendSubstitution (Sub xs) v t =
  Sub ((v, t)::(remove v xs))

(* Returns a string representing a substitution. *)
let toString (Sub xs) =
  "[" ^ (String.concat ", " (List.map (fun (v, t) -> v ^ "/" ^ (Term.toString t)) xs)) ^ "]"

(* Thrown if variable is not in the domain.  Internal use only! *)
exception NotMapped

(* Returns the value of variable x under a substitution. *)
let rec getValue (Sub xs) x =
  getValueAux xs x
and getValueAux xs x =
  match xs with
    | [] -> raise NotMapped
    | ((y, t)::xs') -> if x = y then
                        t
                      else
                        getValueAux xs' x

(* Returns binding for a variable. *)
let getBinding (Sub xs) x =
  List.assoc x xs

(* Is there a binding? *)
let hasBinding (Sub xs) x =
  try
    ignore (List.assoc x xs);
    true
  with
    Not_found -> false

(* Returns a new substitution that is the restriction to a set of variables. *)
let restrict (Sub xs) vars =
  Sub (List.filter (fun (x, _) -> List.mem x vars) xs)

(* Applies a substitution to a term. *)
let rec applyToTerm sub t =
  if Term.isVariable t then
    let x = Term.getTopSymbol t in
      (
        try
          getValue sub x
        with
          NotMapped -> t
      )
  else
    let f = Term.getTopSymbol t
    and ts = Term.getArgs t in
      Term.createFun f (List.map (fun t -> applyToTerm sub t) ts)

(* Determines whether a term is changed by a substitution. *)
let rec changes sub t =
  if Term.isVariable t then
    not (t = (applyToTerm sub t))
  else
    let ts = Term.getArgs t in
      List.exists (fun t -> changes sub t) ts

(* Determines whether sub maps v to a term. *)
let rec maps (Sub sub) v =
  mapsAux sub v
and mapsAux sub v =
  match sub with
    | [] -> false
    | ((y, _)::ys) -> if v = y then
                        true
                      else
                        mapsAux ys v

(* Adds theta's bindings to acc if acc does not map the variable. *)
let rec extendIt (Sub theta) acc =
  extendItAux theta acc
and extendItAux theta acc =
  match theta with
    | [] -> acc
    | ((v, t)::xs) -> if maps acc v then
                        extendItAux xs acc
                      else
                        extendItAux xs (extendSubstitution acc v t)

(* Modifies sigma into acc by applying theta to sigma's domain. *)
let rec composeIt (Sub sigma) theta acc =
  composeItAux sigma theta acc
and composeItAux sigma theta acc =
  match sigma with
    | [] -> extendIt theta acc
    | ((v, t)::xs) -> composeItAux xs theta (extendSubstitution acc v (applyToTerm theta t))

(* Composes two substitutions. *)
let compose sigma theta = composeIt sigma theta (createEmptySubstitution ())

(* Determines whether a substitution is a variable renaming. *)
let isVarRenaming (Sub map) =
  let (vars, terms) = List.split map in
    if List.for_all Term.isVariable terms then
      List.length vars = List.length (Util.remdup terms)
    else
      false
