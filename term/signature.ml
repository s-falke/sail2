(*
  Implementation of signatures.

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

type signature = Sig of (string * int * string list * string) list

(* Thrown when a function symbol does not occur in a signature. *)
exception NotInSignature of string

(* Thrown when a function symbol to be added already occurs in a signature. *)
exception AlreadyInSignature of string

(* Thrown when sort decl uses unknown sort. *)
exception UnknownSort of string * string

(* Returns an empty signature. *)
let createEmpty () = Sig []

(* Returns a sub-signature. *)
let rec getSubSignature (Sig ss) funs =
  getSubSignatureAux ss funs
and getSubSignatureAux ss funs =
  Sig (List.filter (fun (f, _, _, _) -> List.mem f funs) ss)

(* Checks whether a signature contains a function symbol. *)
let rec contains (Sig ss) f =
  containsAux ss f
and containsAux ss f =
  match ss with
    | [] -> false
    | x::xs -> match x with (f', _, _, _) ->
                 if f' = f then
                   true
                 else
                   containsAux xs f

(* Returns the arity of a function symbol. *)
let rec getArity (Sig ss) f =
  getArityAux ss f
and getArityAux ss f =
  match ss with
    | [] -> raise (NotInSignature f)
    | x::xs -> match x with (f', n, _, _) ->
                 if f' = f then
                   n
                 else
                   getArityAux xs f

(* Returns the sort of a function symbol. *)
let rec getSort (Sig ss) f =
  getSortAux ss f
and getSortAux ss f =
  match ss with
    | [] -> raise (NotInSignature f)
    | x::xs -> match x with (f', _, _, goal) ->
                 if f' = f then
                   goal
                 else
                   getSortAux xs f

(* Returns the argument sorts of a function symbol. *)
let rec getArgSorts (Sig ss) f =
  getArgSortsAux ss f
and getArgSortsAux ss f =
  match ss with
    | [] -> raise (NotInSignature f)
    | x::xs -> match x with (f', _, tys, _) ->
                 if f' = f then
                   tys
                 else
                   getArgSortsAux xs f

(* Adds a function symbol with its arity and types to a signature. *)
let addFun s (f, n, tys, goal) =
  if contains s f then
    raise (AlreadyInSignature f)
  else
    match s with
      Sig xs -> Sig (xs @ [(f, n, tys, goal)])

(* Returns the names of the function symbols. *)
let rec getNames (Sig ss) =
  getNamesAux ss
and getNamesAux ss =
  match ss with
    | [] -> []
    | (f, _, _, _)::s' -> f::(getNamesAux s')

(* Returns the sorts. *)
let rec getSorts (Sig ss) =
  Util.remdup (getSortsAux ss)
and getSortsAux ss =
  match ss with
    | [] -> []
    | (_, _, args, target)::fs -> (target::args) @ (getSortsAux fs)

(* Returns a string representing a signture. *)
let rec toString (Sig ss) =
  String.concat "\n" (List.map toStringAux ss)
and toStringAux (f, _, args, target) =
  "[ " ^ f ^ " : " ^ (String.concat ", " args) ^ (if (List.length args <> 0) then " " else "") ^ "-> " ^ target ^ " ] "

(* Returns a string representing a signture for AProVE. *)
let rec toAProVE (Sig ss) =
  String.concat "\n" (List.map toAProVEAux (List.filter nonbuiltin ss))
and toAProVEAux (f, _, args, target) =
  "[ " ^ f ^ " : " ^ (String.concat ", " (List.map aproveit args)) ^ (if (List.length args <> 0) then " " else "") ^ "-> " ^ (aproveit target) ^ " ] "
and aproveit sortname =
  if sortname = "Int" then
    "int"
  else
    "univ"
and nonbuiltin (f, _, _, _) =
  if f = "0" || f = "1" || f = "+" || f = "-" then
    false
  else
    true

(* Returns a list of strings representing a signture for AProVE. *)
let toAProVELines (Sig ss) =
  List.map toAProVEAux (List.filter nonbuiltin ss)

(* Checks whether there is a function with resulting sort Int other than 0, 1, +, -. *)
let rec hasIntResult (Sig ss) =
  List.exists isIntResult ss
and isIntResult (f, _, _, res) =
  f <> "0" && f <> "1" && f <> "+" && f <> "-" && res = "Int"
