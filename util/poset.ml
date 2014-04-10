(*
  Implementation of partially ordered sets.

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

type 'a poset = PO of 'a list * (bool array)

(* Creates an empty poset on a base set. *)
let create baseset =
  let len = List.length baseset in
    PO (baseset, Array.make (len * len) false)

(* Returns index of element in a list. *)
let rec getIndex l e =
  getIndexAux l e 0
and getIndexAux l e i =
  match l with
    | [] -> raise Not_found
    | x::xs -> if x = e then i else (getIndexAux xs e (i + 1))

(* Sets one element bigger than another. *)
let rec setBigger po x y =
  match po with PO (baseSet, relation) ->
    let i = getIndex baseSet x
    and j = getIndex baseSet y
    and len = List.length baseSet in
      (
        Array.set relation (i + j*len) true;
        updateTrans po i j;
        po
      )
and updateTrans po l r =
  (* l > r *)
  match po with PO (baseSet, relation) ->
    let size = List.length baseSet in
      (
        for i = 0 to (size - 1) do
          if relation.(i + size*l) then
            (* elem_i > elem_l, so we have to add elem_i > elem_r *)
            Array.set relation (i + size*r) true
        done;
        for i = 0 to (size - 1) do
          if relation.(r + size*i) then
            (* elem_r > elem_i, so we have to add elem_l > elem_i *)
            Array.set relation (l + size*i) true
        done;
        for i = 0 to (size - 1) do
          if relation.(i + size*l) then
            for j = 0 to (size - 1) do
              if relation.(r + size*j) then
                (* elem_i > elem_l and elem_r > elem_j, so we have to add elem_i > elem_j *)
                Array.set relation (i + size*j) true
            done;
        done
      )

(* Determines whether one element is bigger than another. *)
let isBigger po x y =
  match po with PO (baseSet, relation) ->
    let i = getIndex baseSet x
    and j = getIndex baseSet y
    and len = List.length baseSet in
      relation.(i + j*len)

(* Determines all elements such that the given one is bigger. *)
let getAllBigger po x =
  match po with PO (baseSet, _) ->
    List.filter (fun y -> isBigger po x y) baseSet
