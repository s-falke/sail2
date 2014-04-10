(*
  Implementation of of term-related functions used for parsing.

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

open Term

(* General parse exception. *)
exception ParseException of int * string

(* Thrown when arities do not match. *)
exception ArityConflict of (string * int * int)

(* Thrown when sorts do not match. *)
exception SortConflict of (string * int)

(* Thrown when a variable is used with two sorts. *)
exception SortConflictVar of (string * string * string)

(* Determines sort-correctness, returns first not sort-correct index or -1. *)
let rec sortCorrect s ts ss = sortCorrectAux s ts ss 1
and sortCorrectAux s ts ss n =
  match ts with
    | [] -> -1
    | (x::xs) -> let xsort = getSort s x in
                   if not (xsort = List.hd ss || xsort = "unspec") then
                     n
                   else
                     sortCorrectAux s xs (List.tl ss) (n + 1)

(* Checks whether a term conforms to a given signature. *)
let rec checkTerm s t =
  match t with
    | Var _ -> ()
    | Fun (f, ts) -> if not (Signature.contains s f) then
                       raise (Signature.NotInSignature f)
                     else
                       let n = Signature.getArity s f
                       and nn = List.length ts in
                         if not (n = nn) then
                           raise (ArityConflict (f, n, nn))
                         else
                           let arg = sortCorrect s ts (Signature.getArgSorts s f) in
                             if not (arg = -1) then
                               raise (SortConflict (toString t, arg))
                             else
                               ignore (List.map (fun t -> checkTerm s t) ts)

(* Implodes a sort assumption, i.e., removes duplicates and checks for conflicts. *)
let rec implode ss =
  match ss with
    | [] -> []
    | x::xs -> x::(implode (removeOther x xs))
and removeOther x xs =
  let v = fst x and s = snd x in
    match xs with
      | [] -> []
      | y::ys -> if (fst y = v) then
                   if (snd y <> s) then
                     raise (SortConflictVar (v, s, snd y))
                   else
                     removeOther x ys
                 else
                   y::(removeOther x ys)

(* Get sort assumption for the variables of a term. *)
let rec sortAssumption s t = implode (sortAssumptionAux s t "unspec")
and sortAssumptionAux s t a =
  match t with
    | Var (x, _) -> [(x, a)]
    | Fun (f, ts) -> let ss = (Signature.getArgSorts s f) in
                       List.flatten (List.map2 (sortAssumptionAux s) ts ss)

(* Compares two sort assumptions. *)
let rec containsAssumption xs ys =
  match ys with
    | [] -> ()
    | z::zs -> let zv = (fst z) and za = (snd z) in
                 let xsa = getBinding zv xs in
                   if (xsa <> za && za <> "unspec") then
                     raise (SortConflictVar (zv, xsa, za))
                   else
                     containsAssumption xs zs
and getBinding v b =
  match b with
    | [] -> "none"
    | (y, ya)::ys -> if v = y then
                       ya
                     else
                       getBinding v ys

(* Compares two type assumptions. *)
let rec agreeAssumptions xs ys =
  match ys with
    | [] -> ()
    | z::zs -> let zv = (fst z) and za = (snd z) in
                 let xsa = getBinding zv xs in
                   if (xsa <> za && xsa <> "none" && za <> "unspec" && xsa <> "unspec") then
                     raise (SortConflictVar (zv, xsa, za))
                   else
                     agreeAssumptions xs zs

(* Merges two type assumptions that agree. *)
let rec mergeSortAssumptions xs ys =
  mergeSortAssumptionsAux xs ys []
and mergeSortAssumptionsAux xs ys zs =
  match xs with
    | [] -> ys @ zs
    | (v, a)::vs -> let ysa = getBinding v ys in
                      if ysa = "none" then
                        mergeSortAssumptionsAux vs ys ((v, a)::zs)
                      else if a <> "unspec" then
                        mergeSortAssumptionsAux vs (removeBinding v ys) ((v, a)::zs)
                      else
                        mergeSortAssumptionsAux vs ys zs
and removeBinding v ys =
  match ys with
    | [] -> []
    | (v', a)::vs -> if v = v' then
                       vs
                     else
                       (v', a)::(removeBinding v vs)

(* Returns a new term that takes the sorts into account. *)
let rec getSortedTerm ass t =
  match t with
    | Var (x, _) -> Var (x, getBinding x ass)
    | Fun (f, ts) -> Fun (f, List.map (fun t -> getSortedTerm ass t) ts)

(* Get inferred sort for a variable. *)
let getSortFor ass t =
  match t with
    | Var (x, _) -> getBinding x ass
    | Fun _ -> ""
