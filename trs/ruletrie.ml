(*
  Implementation of tries used for indexing the rules.

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

type ruletrie = Trie of (Rule.rule list) option * (string * ruletrie) list

(* Returns an empty trie. *)
let empty () = Trie (None, [])

(* Thrown when p-string is not in Leaf, only internally. *)
exception NotFound

(* Returns the rules for a term. *)
let rec getRules trie t =
  lookupp trie t Position.Root (List.tl (Term.getPositions t))
and lookupp trie t p pp =
  if p = Position.End then
    match trie with
      | Trie (None, _) -> []
      | Trie (Some rs, _) -> rs
  else
    if not (Term.isVariable (Term.getSubtermAt t p)) then
      let (afterp, afterpp) = after pp p in
        (getStar trie t afterpp afterp) @ (getRegular trie t p pp)
    else
      let (afterp, afterpp) = after pp p in
        getStar trie t afterpp afterp
and getRegular trie t p pp =
  let froot = Term.getSymbolAt t p
  and (nextp, nextpp) = next pp p in
    let c =
      (
        let (found, v') = findit froot trie in
          if found then
            lookupp v' t nextp nextpp
          else
            []
      )
    in
      c
and getStar trie t pp afterp =
  match trie with
    | Trie (_, ll) -> getStarAux ll t pp afterp
and getStarAux ll t pp afterp =
  match ll with
    | [] -> []
    | ("Var", tt)::ts -> (lookupp tt t afterp pp) @ (getStarAux ts t pp afterp)
    | (_, _)::ts -> getStarAux ts t pp afterp
and next pp p =
  match pp with
    | [] -> (p, pp)
    | p'::ps -> (p', ps)
and after pp p =
  match pp with
    | [] -> (p, pp)
    | p'::ps -> if (Position.isPrefixPosition p p') then
                  after ps p
                else
                  (p', ps)
and findit f trie =
  match trie with
    | Trie (_, ts) -> findinlist f ts
and findinlist f ll =
  match ll with
    | [] -> (false, empty ())
    | (f', t)::xs -> if f = f' then
                       (true, t)
                     else
                       findinlist f xs

(* Inserts a rule into a trie. *)
let rec insert trie r = insertp trie r (Term.getPstring (Rule.getLeft r))
and insertp trie r pstring =
  match pstring with
    | [] -> (match trie with
               | Trie (None, t) -> Trie (Some [r], t)
               | Trie (Some l, t) -> Trie (Some (r::l), t)
            )
    | f::fs -> (match trie with
                  | Trie (v, m) ->
                      let (t, i) = try (findinlistEx f m, true) with NotFound -> (empty (), false) in
                        let t' = insertp t r fs in
                          if i then
                            subst trie f t'
                          else
                            Trie (v, (f, t')::m)
               )
and findinlistEx f ll =
  match ll with
    | [] -> raise NotFound
      | (f', t)::xs -> if f = f' then
                         t
                       else
                         findinlistEx f xs
and subst trie f t =
  match trie with
    | Trie (_, []) -> trie
    | Trie (x, ll) -> Trie (x, (substinlist ll f t))
and substinlist ll f t =
  match ll with
    | [] -> raise NotFound
    | (f', t')::xs -> if f = f' then
                        (f, t)::xs
                      else
                        (f', t')::(substinlist xs f t)

(* Creates a trie containing some rules. *)
let rec createRuleTrie rr =
  match rr with
    | [] -> empty ()
    | r::rs -> insert (createRuleTrie rs) r
