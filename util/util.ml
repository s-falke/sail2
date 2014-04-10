(*
  Implementation of various utilities.

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

(* Removed duplicates from a list. *)
let rec remdup l =
  match l with
    | [] -> []
    | x::xs -> x::(remdup (List.filter (fun y -> x <> y) xs))

(* Removes the first occurence of an element from a list. *)
let rec remove l e =
  match l with
    | [] -> []
    | x::xs -> if x = e then
                 xs
               else
                 x::(remove xs e)

(* Removes all occurence of elements that also occurs in the second argument from a list. *)
let rec removeAll a b =
  match a with
    | [] -> []
    | x::xs -> if List.mem x b then
                 removeAll xs b
               else
                 x::(removeAll xs b)

(* Determines whether a list is a set. *)
let rec isSet l =
  match l with
    | [] -> true
    | x::xs -> if List.mem x xs then
                 false
               else
                 isSet xs

(* Determines the number of occurences of an element in a list. *)
let rec getcount e l =
  match l with
    | [] -> 0
    | e'::l' -> if e = e' then
                   1 + (getcount e l')
                 else
                   getcount e l'
