(*
  Implementation of definition and call schemes.

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

(* Computes DefR for a term. *)
let rec computeDefR ttrs t =
  if Term.isVariable t || List.exists Term.isFun (Term.getArgs t) then
    []
  else
    let fRules = Trs.getRulesForSymbol ttrs (Term.getTopSymbol t) in
      computeDefScheme fRules t
and computeDefScheme fRules t =
  match fRules with
    | [] -> []
    | r::rr -> match computeDefSchemeOne r t with
                 | None -> computeDefScheme rr t
                 | Some res -> res::(computeDefScheme rr t)
and computeDefSchemeOne r t =
  let lhs = Rule.getLeft r in
    try
      let ren = renameAway lhs (Term.getVars t) in
        let unif = Unification.unify t (Substitution.applyToTerm ren lhs) in
          Some (Rule.applySubstitution r ren, unif)
    with
      | Unification.Occur _ | Unification.Clash _ -> None
and renameAway l vars =
  let lvars = Term.getVarsAsTerms l in
    let nlvars = primeAll vars lvars in
      constructSub lvars nlvars
and constructSub lvars nlvars =
  constructSubAux lvars nlvars (Substitution.createEmptySubstitution ())
and constructSubAux lvars nlvars sub =
  match lvars with
    | [] -> sub
    | v::vs -> constructSubAux vs (List.tl nlvars) (Substitution.extendSubstitution sub (Term.getTopSymbol v) (List.hd nlvars))
and primeAll vars lvars =
  match lvars with
    | [] -> []
    | v::vs -> let vn = Term.getTopSymbol v
               and vsort = Term.getVarSort v in
                 let vn' = primeName vn vars in
                   (Term.createVar vn' vsort)::(primeAll (vn'::vars) vs)
and primeName vn vars =
  if not (List.mem vn vars) then
    vn
  else
    primeName (vn ^ "'") vars

(* Checks whether two DefSchemes are identical for a set of variables. *)
let rec areIdentical defscheme1 defscheme2 vars =
  let subs1 = List.map (fun (_, sigma) -> Substitution.restrict sigma vars) defscheme1
  and subs2 = List.map (fun (_, sigma) -> Substitution.restrict sigma vars) defscheme2 in
    if (List.length subs1) <> (List.length subs2) then
      false
    else
      checkEqual subs1 subs2 vars
and checkEqual subs1 subs2 vars =
  match subs1 with
    | [] -> true
    | sub::subs -> let equalOne = findEqual sub subs2 vars in
                     match equalOne with
                       | None -> false
                       | Some sigma -> checkEqual subs (Util.remove subs2 sigma) vars
and findEqual sigma subs vars =
  match subs with
    | [] -> None
    | tau::rest -> if substitutionsEqual sigma tau vars then
                     Some tau
                   else
                     findEqual sigma rest vars
and substitutionsEqual sigma tau vars =
  let sigmaArgs = List.map (Substitution.getBinding sigma) vars
  and tauArgs = List.map (Substitution.getBinding tau) vars in
    try
      let unif = Unification.unify (Term.createFun "TUPLE" sigmaArgs) (Term.createFun "TUPLE" tauArgs) in
        Substitution.isVarRenaming unif
    with
      Unification.Occur _ | Unification.Clash _ -> false

(* Get the "corresponding" entry. *)
let rec getCorresponding (rule, sigma) defscheme vars =
  match defscheme with
    | [] -> None
    | (rule', sigma')::rest -> if substitutionsEqual sigma sigma' vars then
                                 Some (rule', sigma')
                               else
                                 getCorresponding (rule, sigma) rest vars

(* Computes Call for two terms. *)
let rec computeCall ttrs defscheme gy =
  if Term.isVariable gy || List.exists Term.isFun (Term.getArgs gy) then
    []
  else
    computeCallScheme defscheme gy
and computeCallScheme (rule, sigma) gy =
  let gCalls = Term.getAllSubtermsForSymbol (Rule.getRight rule) (Term.getTopSymbol gy) in
    doCompute gCalls sigma gy
and doCompute gCalls sigma gy =
  match gCalls with
    | [] -> []
    | c::cc -> match Unification.matchTermsNoException gy (Substitution.applyToTerm sigma c) with
                 | None -> doCompute cc sigma gy
                 | Some tau -> tau::(doCompute cc sigma gy)
