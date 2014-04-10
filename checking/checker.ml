(*
  Implementation of Meta-Checker.

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

open Formula

type verdict = Neither | Liac | Simple | Nested (*| Complex*)

let lastVerdict = ref Neither

(* Checks a formula w.r.t. a TRS. *)
let rec check ttrs f =
  lastVerdict := Neither;
  let defs = Trs.getDefined ttrs
  and conss = Trs.getConstructors ttrs in
    if (Formula.isBasedOn conss f) then
    (
      lastVerdict := Liac;
      ([Proof.Liac (f, f)], f)
    )
    else
    (
      let tmp = hasSimpleForm defs conss f in
        if (tmp = None) then
        (
          let tmp' = hasNoConstraints f in
            if (tmp' = None) then
            (
              let (p, f') = Simple.isSimple ttrs f in
                if isGood p then
                (
                  lastVerdict := Simple;
                  (p, f')
                )
                else
                (
                  lastVerdict := Neither;
                  (p, f')
                )
            )
            else
            (
              lastVerdict := Neither;
              ([Proof.Simple (f, false, tmp', [], None, f)], f)
            )
        )
        else
        (
          let tmp = hasNoConstraints f in
            if (tmp = None) then
            (
              let (p, f') = Nested.isNested ttrs f in
                if isGood p then
                (
                  lastVerdict := Nested;
                  (p, f')
                )
                else
                (
                  lastVerdict := Neither;
                  (p, f')
                  (*if (Trs.isUnconstrained ttrs) then
                    let (p, f') = Complexx.isComplex ttrs f in
                      if isGood p then
                      (
                        lastVerdict := Complex;
                        (p, f')
                      )
                      else
                      (
                        lastVerdict := Neither;
                        (p, f')
                      )
                  else
                  (
                    lastVerdict := Neither;
                    (p, f')
                  *)
                )
            )
            else
            (
              lastVerdict := Neither;
              ([Proof.Nested (f, false, tmp, [], None, None, f)], f)
            )
        )
    )
and isGood p =
  match p with
    | [] -> false
    | pp::_ -> isGoodOne pp
and isGoodOne pp =
  match pp with
    | Proof.Simple (_, flag, _, _, _, _) | Proof.Nested (_, flag, _, _, _, _, _) | Proof.Complex (_, flag, _, _, _, _, _, _) -> flag
    | Proof.Leaf _ | Proof.Direct _ | Proof.Expand _ | Proof.Liac _ -> false
and hasSimpleForm defs conss f =
  match f with
    | True | False | Formula [] -> None
    | Formula fs -> check_all defs conss fs
and check_all defs conss fs =
  match fs with
    | [] -> None
    | a::aa -> if hasSimpleFormAtom defs conss a then
                 check_all defs conss aa
               else
                 Some a
and hasSimpleFormAtom defs conss (Atom (s, t, _)) =
  (checkTermLeft defs s) && (Term.isBasedOn conss t)
and checkTermLeft defs s =
  (List.mem (Term.getTopSymbol s) defs) && (List.for_all Term.isVariable (Term.getArgs s))
and hasNoConstraints f =
  match f with
    | True | False | Formula [] -> None
    | Formula fs -> check_all_noc fs
and check_all_noc atoms =
  match atoms with
    | [] -> None
    | (Atom (s, t, c))::aas -> if c <> [] then
                                 Some (Atom (s, t, c))
                               else
                                 check_all_noc aas

let toString v =
  match v with
    | Neither -> "neither"
    | Liac  -> "LIAC"
    | Simple -> "simple"
    | Nested -> "nested"
