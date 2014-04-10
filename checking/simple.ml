(*
  Implementation of checking for simple conjecture.

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

(* Determines whether a set of functions is LIAC-based *)
let rec isLIACBased ttrs funs =
  let conss = Trs.getConstructors ttrs
  and rules = List.concat (List.map (Trs.getRulesForSymbol ttrs) funs) in
    check_all conss funs rules
and check_all conss funs rules =
  match rules with
    | [] -> None
    | ru::rules' -> if not (isLIACBasedRule conss funs (Rule.getLeft ru) (Rule.getRight ru)) then
                      Some ru
                    else
                      check_all conss funs rules'
and isLIACBasedRule conss defs l r =
  List.for_all (Term.isBasedOn conss) (Term.getArgs l) && check_calls conss defs r
and check_calls conss defs t =
  if Term.isVariable t then
    true
  else
    let f = Term.getTopSymbol t in
      if List.mem f conss then
        List.for_all (check_calls conss defs) (Term.getArgs t)
      else if List.mem f defs then
        List.for_all (Term.isBasedOn conss) (Term.getArgs t)
      else
        false

(* Determines whether a formula has ImpEq'. *)
let rec isImpeq ttrs funs f =
  match f with
    | True | False | Formula [] -> None
    | Formula fs -> isImpeqReal ttrs funs fs
and isImpeq' ttrs funs f =
  match f with
    | True | False | Formula [] -> None
    | Formula fs -> isImpeqReal' ttrs funs fs
and isImpeqReal ttrs funs fs =
  let rules = List.concat (List.map (Trs.getRulesForSymbol ttrs) funs) in
    let impeq = Impeq.getForRules rules in
      isImpeqAux fs impeq fs
and isImpeqReal' ttrs funs fs =
  let rules = List.concat (List.map (Trs.getRulesForSymbol ttrs) funs) in
    let impeq = Impeq.getForRules' rules in
      isImpeqAux fs impeq fs
and isImpeqAux atoms impeq allatoms =
  match atoms with
    | [] -> None
    | a::atoms' -> if checkAtom a impeq allatoms then
                     isImpeqAux atoms' impeq allatoms
                   else
                     Some a
and checkAtom a impeq allatoms =
  let (f, args) = getTerm a in
    if List.exists (fun t -> not (Term.isVariable t)) args then
      false
    else
      checkAllEq f args impeq allatoms
and checkAllEq f args impeq allatoms =
  let eqlist = getEqList args in
    checkAllEqAux eqlist (getFor f impeq) allatoms
and getFor f impeq =
  match impeq with
    | [] -> []
    | (g, l1, l2, c)::impeq' -> if f = g then
                                  (f, l1, l2, c)::(getFor f impeq')
                                else
                                  getFor f impeq'
and checkAllEqAux eqlist impeq allatoms =
  match eqlist with
    | [] -> true
    | (i, j)::eqlist' -> if checkij (getImpeqij i j impeq) allatoms then
                           checkAllEqAux eqlist' impeq allatoms
                         else
                           false
and getImpeqij i j impeq =
  match impeq with
    | [] -> []
    | (_, i', j', c)::impeq' -> if i = i' && j = j' then
                                  c::(getImpeqij i j impeq')
                                else
                                  (getImpeqij i j impeq')
and checkij impeq allatoms =
  match impeq with
    | [] -> false
    | c::cs -> if isGood c allatoms then
                 true
               else
                 checkij cs allatoms
and isGood c allatoms =
  match c with
    | [] -> true
    | (g, k1, k2)::c' -> if isTrue g k1 k2 allatoms then
                           isGood c' allatoms
                         else
                           false
and isTrue g k1 k2 allatoms =
  List.for_all (fun a -> let (f, args) = getTerm a in
                           if f = g then
                             (List.nth args (k1 - 1)) = (List.nth args (k2 - 1))
                           else
                             true)
               allatoms
and getEqList args =
  getEqListAux args 1
and getEqListAux args n =
  match args with
    | [] -> []
    | t::args' -> collectAll t args' n (n + 1)
and collectAll t args n k =
  match args with
    | [] -> []
    | t'::args' -> if t = t' then
                     (n, k)::(collectAll t args' n (k + 1))
                   else
                     (collectAll t args' n (k + 1))
and getTerm (Atom (s, _, _)) =
  (Term.getTopSymbol s, Term.getArgs s)


(* Determines whether a formula is simple w.r.t. a TRS. *)
let rec isSimple ttrs f =
  match f with
    | True | False | Formula [] -> ([], f)
    | Formula fs -> isSimpleReal ttrs f fs
and isSimpleReal ttrs form fs =
  let defs = Trs.getDefined ttrs in
    let fFuns = Formula.getFuns form in
      let deffFuns = List.filter (fun f -> List.mem f defs) fFuns in
        let tmp = ref (isImpeqReal' ttrs deffFuns fs) in
          if (!tmp <> None) then
            ([Proof.Simple (form, false, !tmp, deffFuns, None, form)], form)
          else
            match isLIACBased ttrs deffFuns with
              | None -> ([Proof.Simple (form, true, None, deffFuns, None, form)], form)
              | Some ru -> ([Proof.Simple (form, false, None, deffFuns, Some ru, form)], form)
