(*
  Implementation of syntactic unification/matching.

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

type unificationProblem = UP of (Term.term * Term.term) list

(* Applies a substitution to all terms in an unification problem. *)
let rec apply sigma (UP x) =
  UP (applyAux sigma x)
and applyAux sigma x =
  List.map (fun (s, t) -> (Substitution.applyToTerm sigma s, Substitution.applyToTerm sigma t)) x

(* Extends an unification problem. *)
let rec extend ss ts (UP x) =
  UP (extendAux ss ts x)
and extendAux ss ts up =
  match (ss, ts) with
    | (x::xs, y::ys) -> extendAux xs ys ((x, y)::up)
    | _ -> up

(* Occurs check failure. *)
exception Occur of (string * Term.term)

(* Function symbol clash failure. *)
exception Clash of (string * string)

(* Not matchable. *)
exception NoMatch of (Term.term * Term.term)

(* Solves an unification problem. *)
let rec solveUP up sub = match up with
  | UP [] -> sub
  | UP ((s, t)::ups) ->
      if s = t then
        solveUP (UP ups) sub (* trivial *)
      else
        let svar = Term.isVariable s
        and tvar = Term.isVariable t in
          match (svar, tvar) with
            | (false, true) -> solveUP (UP ((t, s)::ups)) sub
            | (true, _) -> let x = Term.getTopSymbol s in
                             if (Term.containsVar x t) then
                               raise (Occur (x, t))
                             else
                               let sigma = Substitution.extendSubstitution (Substitution.createEmptySubstitution ()) x t in
                                 solveUP (apply sigma (UP ups)) (Substitution.compose sub sigma)
            | (false, false) -> let f = Term.getTopSymbol s
                                and g = Term.getTopSymbol t in
                                  if f <> g then
                                    raise (Clash (f, g))
                                  else
                                    let ss = Term.getArgs s
                                    and ts = Term.getArgs t in
                                      solveUP (extend ss ts (UP ups)) sub

(* Computes an mgu or throws one of the above exceptions. *)
let unify s t = solveUP (UP [(s, t)]) (Substitution.createEmptySubstitution ())

(* Solves the matching problem s <= t. *)
let rec solveMatch s t sub =
  if Term.isVariable s then
    let x = Term.getTopSymbol s in
      (
        if (Substitution.hasBinding sub x) && (Substitution.applyToTerm sub s) <> t then
          raise (NoMatch (s, t))
        else
          Substitution.extendSubstitution sub x t
      )
  else if Term.isVariable t then
    raise (NoMatch (s, t))
  else
    let f = Term.getTopSymbol s
    and g = Term.getTopSymbol t in
      if f <> g then
        raise (NoMatch (s, t))
      else
        let ss = Term.getArgs s
        and ts = Term.getArgs t in
          extendAll ss ts sub
and extendAll ss ts sub =
  match ss with
    | [] -> sub
    | x::xs -> extendAll xs (List.tl ts) (solveMatch x (List.hd ts) sub)

(* Computes sigma such that the image of the first term is the second. *)
let matchTerms s t = solveMatch s t (Substitution.createEmptySubstitution ())

(* Solves the matching problem s <= t. *)
let rec solveMatchNoException s t sub =
  let (sol, subb) = solveMatchNo s t (true, sub) in
    if sol then
      Some subb
    else
      None
and solveMatchNo s t (flag, sub) =
  if not flag then
    (flag, sub)
  else
    if Term.isVariable s then
      let x = Term.getTopSymbol s in
        (
          if (Substitution.hasBinding sub x) && (Substitution.applyToTerm sub s) <> t then
            (false, sub)
          else
            (true, Substitution.extendSubstitution sub x t)
        )
    else if Term.isVariable t then
      (false, sub)
    else
      let f = Term.getTopSymbol s
      and g = Term.getTopSymbol t in
        if f <> g then
          (false, sub)
        else
          let ss = Term.getArgs s
          and ts = Term.getArgs t in
            extendAllNo ss ts (flag, sub)
and extendAllNo ss ts (flag, sub) =
  if not flag then
    (flag, sub)
  else
    (
      match ss with
        | [] -> (flag, sub)
        | x::xs -> extendAllNo xs (List.tl ts) (solveMatchNo x (List.hd ts) (flag, sub))
    )

(* Computes sigma such that the image of the first term is the second. *)
let matchTermsNoException s t = solveMatchNoException s t (Substitution.createEmptySubstitution ())
