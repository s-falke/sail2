(*
  Implementation of positions.

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

type position =
  | Root
  | Pos of int * position
  | End

(* Thrown if a position is illegal. *)
exception IllegalPosition

(* Is first position a prefix of second position? *)
let rec isPrefixPosition p1 p2 =
  match p1 with
    | Root -> true
    | Pos (i, p') -> (
                       match p2 with
                         | Root -> false
                         | Pos (j, p'') -> (i = j && (isPrefixPosition p' p''))
                         | End -> false
                     )
    | End -> false

(* Returns a string representing a position. *)
let rec toString p =
  match p with
    | Root -> "d"
    | End -> "e"
    | Pos (i, p') -> String.concat "." [string_of_int i; toString p']

(* Adds argument at end. *)
let rec addAtEnd p i =
  match p with
    | Root -> Pos (i, Root)
    | Pos (j, pp) -> Pos (j, addAtEnd pp i)
    | End -> failwith "Internal error in Position.addAtEnd"
