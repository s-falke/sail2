(*
  Implementation of the Expand rule.

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

(* Time spend in the termination proof in msec. *)
let terminationTime = ref 0.0

(* Time spend in the smt solver in msec. *)
let smtTime = ref 0.0

(* Applies Expand. *)
let rec apply ttrs terminates rules f =
  terminationTime := 0.0;
  smtTime := 0.0;
  if (Formula.isBasedOn (Trs.getConstructors ttrs) f) then
    None
  else
    applyReal ttrs terminates rules f
and applyReal ttrs terminates rules f =
  match f with
    | True | False -> None
    | Formula fs -> (
                      if varCondViolation fs then
                        None
                      else
                      (
                        let orient = doOrient fs ttrs terminates rules in
                          if orient = [] then
                            None
                          else
                            let fs' = expand ttrs orient fs in
                              if fs' = fs then
                                None
                              else
                                Some (Formula fs', [Proof.Expand (Formula fs, "expansion w.r.t. R", ashyps orient, Formula fs')])
                      )
                    )
and varCondViolation fs =
  List.exists (fun (Atom (s, t, c)) -> (checkVarCondViolation (Util.remdup ((Term.getVars t) @ (List.flatten (List.map Constraint.getVars c)))) (Term.getVars s))) fs
and checkVarCondViolation v1 v2 =
  match v1 with
    | [] -> false
    | v::vv -> if List.mem v v2 then
                 checkVarCondViolation vv v2
               else
                 true
and ashyps orient =
  List.map (fun (Atom (l, r, c)) -> Rule.Rule (l, r, c)) orient
and doOrient fs ttrs terminates rules =
  tryOrient ttrs terminates rules fs
and tryOrient ttrs terminates rules fs =
  let start = Unix.gettimeofday () in
  let res = terminates (Trs.Trs (Trs.getSignature ttrs, rules @ (ashyps fs), Ruletrie.empty ())) in
  let stop = Unix.gettimeofday () in
    terminationTime := (stop -. start) *. 1000.0;
    if res then
      fs
    else
      []
and expand ttrs orient fs =
  List.flatten (List.map (doExpand ttrs orient) fs)
and doExpand ttrs orient (Atom (s, t, c)) =
  let (r1, r2) = if List.mem (Atom (s, t, c)) orient then (s, t) else (t, s) in
    let candi = termexpand ttrs (Trs.getDefined ttrs) (Trs.getConstructors ttrs) (Term.getVars r1) r1 in
      if candi = [] then
        [ Atom (s, t, c) ]
      else
        List.filter isSat (List.map (fun (r1', sigma, c') -> Atom (Substitution.applyToTerm sigma r1',
                                                                   Substitution.applyToTerm sigma r2,
                                                                   List.map (Constraint.applySubstitution sigma) (c @ c')))
                                    candi)
and isSat (Atom (_, _, c)) =
  let start = Unix.gettimeofday () in
  let res = (Decproc.isSatisfiablePAConjunction c = Ynm.Yes) in
  let stop = Unix.gettimeofday () in
    (
      smtTime := !smtTime +. ((stop -. start) *. 1000.0);
      res
    )
and termexpand rules defs conss vars t =
  if (Term.isVariable t) then
    []
  else
  (
    let f = Term.getTopSymbol t in
      let ts = Term.getArgs t in
        if (List.mem f defs) && (List.for_all (fun t -> Term.isBasedOn conss t) ts) then
          expandThat (Trs.getRulesForSymbol rules f) vars t
        else
          expandArg rules defs conss vars f t
  )
and expandArg rules defs conss vars f t =
  let ts = Term.getArgs t in
    let newtss = expandArgAux rules defs conss vars ts in
      List.map (fun (ts, sigma, c) -> (Term.createFun f ts, sigma, c)) newtss
and expandArgAux rules defs conss vars tt =
  match tt with
    | [] -> []
    | t::ts -> let te = termexpand rules defs conss vars t in
                 if te <> [] then
                   List.map (fun (t', sigma, c) -> (t'::ts, sigma, c)) te
                 else
                   List.map (fun (tss, sigma, c) -> (t::tss, sigma, c)) (expandArgAux rules defs conss vars ts)
and expandThat rules vars t =
  match rules with
    | [] -> []
    | (Rule.Rule (l, r, c))::rus ->
        (
          try
            let ren = renameAway l vars in
              let sigma = Unification.unify (Substitution.applyToTerm ren l) t in
                (Substitution.applyToTerm ren r, sigma, List.map (Constraint.applySubstitution ren) c)::(expandThat rus vars t)
          with
            Unification.Clash _ | Unification.Occur _ -> expandThat rus vars t
        )
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
