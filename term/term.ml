(*
  Implementation of terms.

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

type term =
  | Var of string * string
  | Fun of string * term list

(* Creates a variable. *)
let createVar x s = Var (x, s)

(* Is it a variable? *)
let isVariable t =
  match t with
    | Var _ -> true
    | Fun _ -> false

(* Creates a function application. *)
let createFun f ts = Fun (f, ts)

(* Is it a function application? *)
let isFun t =
  match t with
    | Fun _ -> true
    | Var _ -> false

(* Returns a string representing a term. *)
let rec toString t =
  match t with
    | (Var (x, _)) -> x
    | (Fun (f, ts)) -> if List.length ts = 0 then
                         f
                       else
                         let args = String.concat ", " (List.map (fun t -> toString t) ts) in
                           f ^ "(" ^ args ^ ")"

(* Returns a string with sorts for variables. *)
and toStringSorts t =
  match t with
    | (Var (x, s)) -> x ^ ":" ^ s
    | (Fun (f, ts)) -> if List.length ts = 0 then
                         f
                       else
                         let args = String.concat ", " (List.map (fun t -> toStringSorts t) ts) in
                           f ^ "(" ^ args ^ ")"

(* Checks whether a term contains a variable. *)
let rec containsVar v t = match t with
  | Var (y, _) -> v = y
  | Fun (_, ts) -> List.exists (fun t -> containsVar v t) ts

(* Returns the variables occuring in a term. *)
let rec getVars t = Util.remdup (getVarsAux t)
and getVarsAux t =
  match t with
    | Var (x, _) -> [x]
    | Fun (_, ts) -> List.flatten (List.map getVarsAux ts)

(* Returns the variables occuring in a term. *)
let rec getVarsAsTerms t = Util.remdup (getVarsAsTermsAux t)
and getVarsAsTermsAux t =
  match t with
    | Var _ -> [t]
    | Fun (_, ts) -> List.flatten (List.map getVarsAsTermsAux ts)

(* Returns all functions occuring in a term. *)
let rec getFuns t = Util.remdup (getFunsAux t)
and getFunsAux t =
  match t with
    | Var _ -> []
    | Fun (f, ts) -> f::(List.flatten (List.map getFunsAux ts))

(* Gets the sort of a term. *)
let getSort s t =
  match t with
    | Var (_, so) -> so
    | Fun (f, _) -> Signature.getSort s f

(* Returns the sort of a variable. *)
let getVarSort t =
  match t with
    | Var (_, so) -> so
    | Fun _ -> failwith "Internal error in Term.getVarSort"

(* Returns names and sorts of all variables of a sorted term. *)
let rec getVarNameSorts t = Util.remdup (getVarNameSortsAux t)
and getVarNameSortsAux t =
  match t with
    | Var (x, s) -> [(x, s)]
    | Fun (_, ts) -> List.flatten (List.map (fun t -> getVarNameSorts t) ts)

(* Get the top symbol of a term. *)
let getTopSymbol t =
  match t with
    | Var (x, _) -> x
    | Fun (f, _) -> f

(* Determines whether t contains only function symbols from a given set. *)
let rec isBasedOn funs t =
  match t with
    | Var _ -> true
    | Fun (f, ts) -> (List.mem f funs) && (List.for_all (fun t -> isBasedOn funs t) ts)

(* Determines whether t is linear. *)
let rec isLinear t = Util.isSet (isLinearAux t)
and isLinearAux t =
  match t with
    | Var (x, _) -> [x]
    | Fun (_, ts) -> (List.flatten (List.map isLinearAux ts))

(* Returns the arguments of a term. *)
let getArgs t =
  match t with
    | Var _ -> []
    | Fun (_, ts) -> ts

(* Returns the number of arguments. *)
let getNumArgs t =
  match t with
    | Var _ -> 0
    | Fun (_, ts) -> List.length ts

(* Returns the p-String of a term. *)
let rec getPstring t =
  match t with
    | Var _ -> ["Var"]
    | Fun (f, ts) -> [f] @ (List.flatten (List.map (fun t -> getPstring t) ts))

(* Returns the subterm at a given position. Throws IllegalPosition. *)
let rec getSubtermAt t p =
  match p with
    | Position.End -> raise Position.IllegalPosition
    | Position.Root -> t
    | Position.Pos (i, p') ->
      (
        match t with
          | Var _ -> raise Position.IllegalPosition
          | Fun (_, ts) -> (
                             try
                               getSubtermAt (List.nth ts (i - 1)) p'
                             with
                               Failure _ -> raise Position.IllegalPosition
                           )
      )

(* Replaces the subterm of t at position p by the term s. Throws IllegalPosition. *)
let rec replaceSubtermAt t p s =
  match p with
    | Position.End -> raise Position.IllegalPosition
    | Position.Root -> s
    | Position.Pos (i, p') ->
      (
        match t with
          | Var _ -> raise Position.IllegalPosition
          | Fun (f, ts) -> (
                             try
                               let s' = replaceSubtermAt (List.nth ts (i - 1)) p' s in
                                 let newts = createNewts ts (i - 1) s' in
                                   createFun f newts
                             with
                               Failure _ -> raise Position.IllegalPosition
                           )
      )
and createNewts ts i s =
  match ts with
    | [] -> []
    | t::ts' -> if i = 0 then
                 s::ts'
               else
                 t::(createNewts ts' (i - 1) s)

(* Returns the symbol at position p. Throws IllegalPosition. *)
let getSymbolAt t p =
  getTopSymbol (getSubtermAt t p)

(* Returns the positions of a term. *)
let rec getPositions t = (getPosAux t) @ [Position.End]
and getPosAux t =
  match t with
    | Var _ -> [Position.Root]
    | Fun (_, ts) -> Position.Root::(getSubPos 1 ts)
and getSubPos i ts =
  match ts with
    | [] -> []
    | t::tts -> (List.map (fun p -> Position.Pos (i, p)) (getPosAux t)) @ (getSubPos (i + 1) tts)

(* Checks whether the term [t] contains the term [s] as a subterm. *)
let rec contains s t =
  if s = t then
    true
  else if isVariable t then
    false
  else
    List.exists (fun tt -> contains s tt) (getArgs t)

(* Checks whether the term t is fully typed. *)
let rec isFullyTyped t =
  match t with
    | Var (_, s) -> s <> "unspec"
    | Fun (_, ts) -> List.for_all (fun t -> isFullyTyped t) ts

(* Returns all subterms of t. *)
let rec getAllSubterms t =
  Util.remdup (getAllSubtermsAux t)
and getAllSubtermsAux t =
  match t with
    | Var _ -> [t]
    | Fun (_, ts) -> t::(List.flatten (List.map getAllSubtermsAux ts))

(* Returns all subterms of t with their positions. *)
let rec getAllSubtermsWithPositions t =
  getAllSubtermsWithPositionsAux t Position.Root
and getAllSubtermsWithPositionsAux t pos =
  match t with
    | Var _ -> [(t, pos)]
    | Fun (_, ts) -> (t, pos)::(getAllSubtermsWithPositionsList ts 1 pos [])
and getAllSubtermsWithPositionsList ts i p acc =
  match ts with
    | [] -> acc
    | t::tt -> getAllSubtermsWithPositionsList tt (i + 1) p (acc @ (getAllSubtermsWithPositionsAux t (Position.addAtEnd p i)))

(* Determines whether t is an argument of s. *)
let isArg s t =
  match s with
    | Var _ -> false
    | Fun (_, ts) -> List.mem t ts

(* Returns the argument position of t in s. *)
let rec argPos s t =
  match s with
    | Var _ -> failwith "internal error 1 in Term.argPos"
    | Fun (_, ts) -> getIndex t ts 1
and getIndex t ts i =
  match ts with
    | [] -> failwith "internal error 2 in Term.argPos"
    | t'::ts' -> if t = t' then
                   Position.Pos (i, Position.Root)
                 else
                   getIndex t ts' (i+1)

(* Determines whether a term is Z-free. *)
let rec isZfree t =
  checkZfree (getFuns t)
and checkZfree funs =
  List.for_all (fun f -> f <> "+" && f <> "-") funs

(* Returns all subterms of t that are headed by f. *)
let getAllSubtermsForSymbol t f =
  List.filter (fun t -> getTopSymbol t = f) (getAllSubterms t)

(* Returns all subterms of t that are headed by a symbol from symbs. *)
let getAllSubtermsForSymbols t symbs =
  List.concat (List.map (fun f -> getAllSubtermsForSymbol t f) symbs)

(* Returns all maximal subterms of a term that are headed by a symbol from given set. *)
let rec getAllMaximalSubtermsForSymbols t funs =
  Util.remdup (getAllMaximalSubtermsForSymbolsAux t funs)
and getAllMaximalSubtermsForSymbolsAux t funs =
  match t with
    | Var _ -> []
    | Fun (f, ts) -> if List.mem f funs then
                       [t]
                     else
                       List.flatten (List.map (fun t -> getAllMaximalSubtermsForSymbolsAux t funs) ts)

(* Returns the non-linear variables in t. *)
let getNonlinearVars t =
  let varlist = getVarsAsTermsAux t in
    List.filter (fun v -> Util.getcount v varlist <> 1) varlist

(* Returns all subterms occuring multiple times in t. *)
let getAllDuplicateSubterms t =
  let allsubs = getAllSubtermsAux t in
    List.filter (fun t -> Util.getcount t allsubs <> 1) allsubs

(* Returns the term t in HTML, where defn contains the defined function symbols. *)
let rec toHTML t defn =
  let f = getTopSymbol t in
    if isVariable t then
      "<FONT COLOR=\"#FF00FF\"><I>" ^ f ^ "</I></FONT>"
    else
      (
        let args = getArgs t in
          if List.length args = 0 then
            write_fun f defn
          else
            (
              (write_fun f defn)
              ^ "("
              ^ (write_term_list args defn)
              ^ ")"
            )
      )
and write_term_list ts defn =
  String.concat ", " (List.map (fun t -> toHTML t defn) ts)
and write_fun f defn =
  if List.mem f defn then
    "<FONT COLOR=\"#8B0000\">" ^ f ^ "</FONT>"
  else
    "<FONT COLOR=\"#00008B\">" ^ f ^ "</FONT>"

(* Returns a Z-term in SMT-LIB format. *)
let rec toSMT t =
  let f = getTopSymbol t in
    if isVariable t then
      "(" ^ f ^ ")"
    else
      "(" ^ (getName f) ^ (String.concat " " (List.map toSMT (getArgs t))) ^ ")"
and getName f =
  if f = "true" then "TT" else if f = "false" then "FF" else f

(* Returns a string representing a term in CVC3 format. *)
let rec toCVC3 t =
  match t with
    | (Var (x, _)) -> x
    | (Fun (f, ts)) -> if List.length ts = 0 then
                         f
                       else if f = "+" then
                         "(" ^ (toCVC3 (List.hd ts)) ^ ") + (" ^ (toCVC3 (List.hd (List.tl ts))) ^ ")"
                       else
                         let args = String.concat ", " (List.map (fun t -> toCVC3 t) ts) in
                           f ^ "(" ^ args ^ ")"
