(*
  Implementation of TRSs.

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

type trs = Trs of Signature.signature * (Rule.rule list) * Ruletrie.ruletrie

let pae =
  let x = Term.createVar "X" "Int"
  and y = Term.createVar "Y" "Int"
  and z = Term.createVar "Z" "Int" in
    let pxy = Term.createFun "+" [x;y]
    and pyx = Term.createFun "+" [y;x]
    and pyz = Term.createFun "+" [y;z] in
      let pxpyz = Term.createFun "+" [x;pyz]
      and ppxyz = Term.createFun "+" [pxy;z] in
        (Rule.Rule (pxy, pyx, []))::
        (Rule.Rule (pxpyz, ppxyz, []))::
        (Rule.Rule (ppxyz, pxpyz, []))::
        []

let pastrie =
  let x = Term.createVar "X" "Int"
  and y = Term.createVar "Y" "Int"
  and zero = Term.createFun "0" [] in
    let pxy = Term.createFun "+" [x;y]
    and pxzero = Term.createFun "+" [x;zero]
    and pzeroy = Term.createFun "+" [zero;y]
    and mx = Term.createFun "-" [x]
    and my = Term.createFun "-" [y]
    and mzero = Term.createFun "-" [zero] in
      let mmx = Term.createFun "-" [mx]
      and mpxy = Term.createFun "-" [pxy]
      and pmxmy = Term.createFun "+" [mx;my]
      and pxmx = Term.createFun "+" [x;mx] in
        let ppxmxy = Term.createFun "+" [pxmx;y] in
          let rules = (Rule.Rule (pxzero, x, []))::
                      (Rule.Rule (mmx, x, []))::
                      (Rule.Rule (mzero, zero, []))::
                      (Rule.Rule (mpxy, pmxmy, []))::
                      (Rule.Rule (pxmx, zero, []))::
                      (Rule.Rule (ppxmxy, pzeroy, []))::
                      [] in
          Ruletrie.createRuleTrie rules

(* Returns a string representing a trs. *)
let toString (Trs (_, t, _)) =
  String.concat "\n" (List.map (fun ru -> Rule.toString ru) t)

(* Returns a string representing a trs containing sorts for variables. *)
let toStringSorts (Trs (_, t, _)) =
  String.concat "\n" (List.map (fun ru -> Rule.toStringSorts ru) t)

(* Returns the signature of a trs. *)
let getSignature (Trs (s, _, _)) =
  s

(* Returns the rules of a trs. *)
let getRules (Trs (_, t, _)) =
  t

(* Returns the rules of a trs defining a given function symbol. *)
let getRulesForSymbol (Trs (_, t, _)) f =
  List.filter (fun ru -> Term.getTopSymbol (Rule.getLeft ru) = f) t

(* Returns the ruletrie of a trs. *)
let getRuleTrie (Trs (_, _, t)) =
  t

(* Determines whether a function symbol is defined. *)
let rec isDefined (Trs (_, t, _)) f =
  isDefinedAux t f
and isDefinedAux rules f =
  match rules with
    | [] -> false
    | (Rule.Rule (l, _, c))::rus -> if f = (Term.getTopSymbol l) then
                                      true
                                    else
                                      isDefinedAux rus f

(* Returns the symbols of a trs. *)
let getSymbols (Trs (s, _, _)) =
  Signature.getNames s

(* Returns the defined symbols of a trs. *)
let getDefined ttrs =
  List.filter (fun f -> isDefined ttrs f) (getSymbols ttrs)

(* Returns the constructor symbols of a trs. *)
let getConstructors ttrs =
  List.filter (function f -> not (isDefined ttrs f)) (getSymbols ttrs)

(* Returns the constructor constants of a trs. *)
let getConstructorConstants ttrs =
  let signa = getSignature ttrs in
    List.filter (function f -> Signature.getArity signa f = 0) (getConstructors ttrs)

(* Returns the constructor non-constants of a trs. *)
let getConstructorNonConstants ttrs =
  let signa = getSignature ttrs in
    List.filter (function f -> Signature.getArity signa f <> 0) (getConstructors ttrs)

(* Returns the constructor symbols of a given sort for a trs. *)
let getConstructorsForSort ttrs sort =
  let signa = getSignature ttrs in
    List.filter (function f -> Signature.getSort signa f = sort) (getConstructors ttrs)

(* Returns the constructor constants of a given sort for a trs. *)
let getConstructorConstantsForSort ttrs sort =
  let signa = getSignature ttrs in
    List.filter (function f -> Signature.getSort signa f = sort) (getConstructorConstants ttrs)

(* Returns the constructor non-constants of a given sort for a trs. *)
let getConstructorNonConstantsForSort ttrs sort =
  let signa = getSignature ttrs in
    List.filter (function f -> Signature.getSort signa f = sort) (getConstructorNonConstants ttrs)

(* Returns the sorts of a trs. *)
let getSorts (Trs (s, _, _)) =
  Signature.getSorts s

let rec getVars rules =
  Util.remdup (List.flatten (List.map (function ru -> Term.getVars (Rule.getLeft ru)) rules))

(* Returns a TRS in AProVE's format. *)
let rec toAProVE (Trs (signa, rules, _)) =
  (Signature.toAProVE signa) ^ "\n" ^ (toStringRules rules)
and toStringRules rules = String.concat "\n" (List.map (fun ru -> Rule.toStringAProVE ru) rules)

let rec toAProVELines (Trs (signa, rules, _)) =
  let signas = Signature.toAProVELines signa
  and ruless = List.map (fun ru -> Rule.toStringAProVE ru) rules in
    signas @ ruless

(* Normalizes a term with a TRS.  This might be nonterminating... *)
let rec normalize ttrs t =
  normalizeAux t (getRuleTrie ttrs) true
and normalizeAux t trie normPA =
  let t' = rewriteOnce t trie normPA in
    if t = t' then
      t
    else
      normalizeAux t' trie normPA
and rewriteOnce t trie normPA =
  if (Term.isVariable t) then
    t
  else
    (
      let f = Term.getTopSymbol t in
        let t' = getNewArgs f t trie normPA in
          let t'' = if normPA then (normalizeArgsPA t') else t' in
            match doFirst (getEquivalenceClass t'') trie with
              | None -> t'
              | Some t''' -> t'''
    )
and getNewArgs f t trie normPA =
  let ts = Term.getArgs t in
    let newts = List.map (fun tt -> normalizeAux tt trie normPA) ts in
      Term.createFun f newts
and normalizeArgsPA t =
  let f = Term.getTopSymbol t in
    Term.createFun f (List.map (fun tt -> normalizePA tt) (Term.getArgs t))
and normalizePA t =
  let eqClass = getEquivalenceClass t in
    let newt = getFirstPAS eqClass in
      match newt with
        | None -> t
        | Some t' -> normalizePA t'
and getFirstPAS eqclass =
  match eqclass with
    | [] -> None
    | s::ss -> let s' = normalizeAux s pastrie false in
                 if s' = s then
                   getFirstPAS ss
                 else
                   Some s'
and getEquivalenceClass t =
  Util.remdup (getEquivalenceClassAux [] [t])
and getEquivalenceClassAux res todo =
  match todo with
    | [] -> res
    | s::todo' -> let newterms = List.filter (fun e -> not (List.mem e res)) (getAll s) in
                    getEquivalenceClassAux (Util.remdup (s::res)) (Util.remdup (todo' @ newterms))
and getAll s =
  Util.remdup (rewriteAll s pae)
and rewriteAll s r =
  rewriteAllAux s (Term.getAllSubtermsWithPositions s) r []
and rewriteAllAux s subbys r acc =
  match subbys with
    | [] -> acc
    | (subterm, pos)::sss -> rewriteAllAux s sss r ((rewriteSubterm s subterm pos (getRulesFor (Term.getTopSymbol subterm) r)) @ acc)
and getRulesFor f r =
  List.filter (fun (Rule.Rule (l, _, _)) -> (Term.getTopSymbol l) = f) r
and rewriteSubterm s st pos rules =
  rewriteSubtermAux s st pos rules []
and rewriteSubtermAux s st pos rules acc =
  match rules with
    | [] -> acc
    | (Rule.Rule (l, r, _))::ruru -> let sigma = Unification.matchTermsNoException l st in
                                       match sigma with
                                         | None -> rewriteSubtermAux s st pos ruru acc
                                         | Some sigma' -> rewriteSubtermAux s st pos ruru ((Term.replaceSubtermAt s pos (Substitution.applyToTerm sigma' r))::acc)
and doFirst ts trie =
  match ts with
    | [] -> None
    | t::tt -> match doFirstAux t (Ruletrie.getRules trie t) with
                | None -> doFirst tt trie
                | Some t' -> Some t'
and doFirstAux t rules =
  match rules with
    | [] -> None
    | (Rule.Rule (l, r, c))::rus -> let sigma = Unification.matchTermsNoException l t in
                                      match sigma with
                                        | None -> doFirstAux t rus
                                        | Some sigma' -> if (constraintTrue c sigma') then
                                                           Some (Substitution.applyToTerm sigma' r)
                                                         else
                                                           doFirstAux t rus
and constraintTrue c sigma =
  if c = [] then
    true
  else
    let c' = List.map (Constraint.applySubstitution sigma) c in
      (List.for_all Constraint.isZbased c') && (Decproc.isValidPAConjunction c' = Ynm.Yes)

(* Normalizes a Z-free term with a Z-free TRS.  This might be nonterminating... *)
let rec normalizeZfree ttrs t =
  normalizeAuxZfree t (getRuleTrie ttrs)
and normalizeAuxZfree t trie =
  let t' = rewriteOnceZfree t trie in
    if t = t' then
      t
    else
      normalizeAuxZfree t' trie
and rewriteOnceZfree t trie =
  if (Term.isVariable t) then
    t
  else
    (
      let f = Term.getTopSymbol t in
        let t' = getNewArgsZfree f t trie in
          match doFirstZfree t' trie with
            | None -> t'
            | Some t'' -> t''
    )
and getNewArgsZfree f t trie =
  let ts = Term.getArgs t in
    let newts = List.map (fun tt -> normalizeAuxZfree tt trie) ts in
      Term.createFun f newts
and doFirstZfree t trie =
  doFirstAuxZfree t (Ruletrie.getRules trie t)
and doFirstAuxZfree t rules =
  match rules with
    | [] -> None
    | (Rule.Rule (l, r, c))::rus -> let sigma = Unification.matchTermsNoException l t in
                                      match sigma with
                                        | None -> doFirstAuxZfree t rus
                                        | Some sigma' -> if (constraintTrue c sigma') then
                                                           Some (Substitution.applyToTerm sigma' r)
                                                         else
                                                           doFirstAuxZfree t rus

(* Determines whether a TRS is constructor-based. *)
let rec isConstructorBased ttrs =
  let constr = getConstructors ttrs in
    checkConstructorBased (getRules ttrs) constr
and checkConstructorBased rules constr =
  match rules with
    | [] -> true
    | r::rs -> (checkConstructorBasedTerm (Rule.getLeft r) constr) &&
               (checkConstructorBased rs constr)
and checkConstructorBasedTerm t constr =
  if Term.isVariable t then
    true
  else
    (
      let ts = Term.getArgs t in
        List.for_all (fun t -> (isConstructorGood t constr)) ts
    )
and isConstructorGood t constr =
  if Term.isVariable t then
    true
  else
    let f = Term.getTopSymbol t
    and args = Term.getArgs t in
      if List.mem f constr then
        List.for_all (fun t -> isConstructorGood t constr) args
      else
        false

(* Check for nested recursive calls *)
let rec isNonnestedDefined ttrs =
  List.for_all (isLIAC (getDefined ttrs) (getConstructors ttrs)) (getRules ttrs)
and isLIAC defs conss (Rule.Rule (_, r, _)) =
  checkLIAC defs conss r
and checkLIAC defs conss r =
  if Term.isVariable r then
    true
  else
    let f = Term.getTopSymbol r in
      if (List.mem f defs) then
        List.for_all (Term.isBasedOn conss) (Term.getArgs r)
      else
        List.for_all (checkLIAC defs conss) (Term.getArgs r)

(* Determines whether a TRS has defined function symbols on left sides below the root. *)
let rec hasDefinedOnLeftSides ttrs =
  let defs = getDefined ttrs
  and rules = getRules ttrs in
    checkHasDefinedOnLeftSides (List.map (fun ru -> Rule.getLeft ru) rules) defs
and checkHasDefinedOnLeftSides lhss defs =
  match lhss with
    | [] -> false
    | t::tt -> (List.exists (checkHasDefined defs) (Term.getArgs t)) ||
               (checkHasDefinedOnLeftSides tt defs)
and checkHasDefined defs t =
  if Term.isVariable t then
    false
  else
    let f = Term.getTopSymbol t in
      if List.mem f defs then
        true
      else
        List.exists (checkHasDefined defs) (Term.getArgs t)

(* Determines whether a TRS contains builtins on left sides. *)
let rec hasBuiltinsOnLeftSides ttrs =
  let builtins = ["0"; "1"; "+"; "-"]
  and rules = getRules ttrs in
    checkHasDefinedOnLeftSides (List.map (fun ru -> Rule.getLeft ru) rules) builtins

(* Determines whether a TRS is left-linear. *)
let isLeftLinear ttrs =
  List.for_all (fun t -> Term.isLinear t) (List.map (fun ru -> Rule.getLeft ru) (getRules ttrs))

(* Determines whether a TRS is overlapping. *)
let onum = ref 0
let rec isOverlapping ttrs =
  isOverlappingAux (getRules ttrs)
and isOverlappingAux rules =
  match rules with
    | [] -> false
    | (Rule.Rule (l, _, c))::rus -> if hasOverlap l c rus then
                                      true
                                    else
                                      isOverlappingAux rus
and hasOverlap l c rus =
  match rus with
    | [] -> false
    | (Rule.Rule (l', _, c'))::ruru -> if hasOverlapOne l c l' c' then
                                         true
                                       else
                                         hasOverlap l c ruru
and hasOverlapOne l c l' c' =
  let (lnew, cnew) = renameRuleConstraint l c in
    try
      let unif = Unification.unify lnew l' in
        let sat = Decproc.isSatisfiablePAConjunction (List.map (Constraint.applySubstitution unif) (c @ c')) in
          sat <> Ynm.No
    with
      | Unification.Occur _ | Unification.Clash _ -> false
and renameRuleConstraint l c =
  onum := 1;
  let vars = Term.getVarsAsTerms l in
    let subby = createSubstitution vars (Substitution.createEmptySubstitution ()) in
      (Substitution.applyToTerm subby l, List.map (Constraint.applySubstitution subby) c)
and createSubstitution vars subby =
  match vars with
    | [] -> subby
    | x::xs -> let newVar = Term.createVar ("x" ^ (string_of_int !onum)) (Term.getVarSort x) in
               (
                 incr onum;
                 createSubstitution xs (Substitution.extendSubstitution subby (Term.getTopSymbol x) newVar)
               )

(* Checks whether the functions in a TRS are completely defined. *)
(* cf Christian Haselbach's Masters thesis, p8-9 *)
let num = ref 0
let varnum = ref 0
let mapp = ref []
let rec checkComplete ttrs =
  let defs = getDefined ttrs in
    let individuals = List.map (checkCompleteFun ttrs) defs in
      List.fold_left combine ([], []) individuals
and combine (a, b) (c, d) =
  (a @ (List.map renameNice c), b @ d)
and renameNice t =
  num := 1; mapp := []; renameNiceAux t
and renameNiceAux t =
  if Term.isVariable t then
    let x = Term.getTopSymbol t in
      try
        let newx = List.assoc x !mapp in
          Term.createVar newx (Term.getVarSort t)
      with
        Not_found -> let newx = "X" ^ (string_of_int !num) in
          num := !num + 1;
          mapp := (x, newx)::!mapp;
          Term.createVar newx (Term.getVarSort t)
  else
    let f = Term.getTopSymbol t in
      let args = Term.getArgs t in
        let newargs = getNiceNewargs args in
          Term.createFun f newargs
and getNiceNewargs ts =
  match ts with
    | [] -> []
    | t::ts' -> let t' = renameNiceAux t in
                  t'::(getNiceNewargs ts')
and checkCompleteFun ttrs f =
  num := 0;
  varnum := 0;
  let frules = getRulesForSymbol ttrs f in
    let res2 = getNonvalidDisjunctions frules in
      let lhss = renameList (Util.remdup (List.map (fun ru -> Rule.getLeft ru) frules)) in
        (Util.remdup (iterateUndefPat [createVarPat f ttrs] lhss ttrs), res2)
and getNonvalidDisjunctions frules =
  match frules with
    | [] -> []
    | (Rule.Rule (l, r, c))::frules' -> let (sameLhs, otherLhs) = splitSame l frules' in
                                          if (isNonvalidDisjunction ((Rule.Rule (l, r, c))::sameLhs)) then
                                            l::(getNonvalidDisjunctions otherLhs)
                                          else
                                            (getNonvalidDisjunctions otherLhs)
and isNonvalidDisjunction rules =
  Decproc.isValidPADisjunctionConjunction (List.map Rule.getConstraint rules) <> Ynm.Yes
and splitSame l rules =
  match rules with
    | [] -> ([], [])
    | (Rule.Rule (l', r', c'))::rules' -> let (r1, r2) = splitSame l rules' in
                                            if l = l' then
                                              ((Rule.Rule (l', r', c'))::r1, r2)
                                            else
                                              (r1, (Rule.Rule (l', r', c'))::r2)
and createVarPat f ttrs =
  let signa = getSignature ttrs in
    let argsorts = Signature.getArgSorts signa f in
      let n = List.length argsorts in
        let newargs = List.map2 createVar argsorts (numsFrom (!varnum+1) n) in
          varnum := !varnum + n;
            Term.createFun f newargs
and createVar sort n =
  Term.createVar ("Y" ^ (string_of_int n)) sort
and numsFrom low n =
  match n with
    | 0 -> []
    | n -> low::(numsFrom (low + 1) (n - 1))
(* iterates UndefPat for all lhss *)
and iterateUndefPat m lhss ttrs =
  match lhss with
    | [] -> m
    | l::lls -> iterateUndefPat (undefPat m l ttrs) lls ttrs
and undefPat m l ttrs =
  List.flatten (List.map (fun r -> up r l ttrs) m)
(* computes UP(r,t) *)
and up r t ttrs =
  match Unification.matchTermsNoException t r with
    | Some _ -> []
    | None -> upAux r t ttrs
and upAux r t ttrs =
  try
    let _ = Unification.unify r t in
      upAux2 r t ttrs
  with
    | Unification.Occur _ | Unification.Clash _ -> [r]
and upAux2 r t ttrs =
  let (i, p) = findMinPos (Term.getArgs r) (Term.getArgs t) 0 in
    let ri = List.nth (Term.getArgs r) i in
      let x = Term.getSubtermAt ri p in
        let conss = getConstructorsForSort ttrs (Term.getVarSort x) in
          let consterms = List.map (fun c -> createVarPat c ttrs) conss in
            let newrs = List.map (fun ct -> createNewTerm r i p ct) consterms in
              List.flatten (List.map (fun r -> up r t ttrs) newrs)
and createNewTerm r i p ct =
  let args = Term.getArgs r in
    let ri = List.nth args i in
      let ri' = Term.replaceSubtermAt ri p ct in
        let newargs = getNewArgs args i ri' in
          let f = Term.getTopSymbol r in
            Term.createFun f newargs
and getNewArgs ts i ri' =
  match ts with
    | [] -> []
    | t::ts' -> if i = 0 then
                  ri'::ts'
                else
                  t::(getNewArgs ts' (i - 1) ri')
(* finds minimal position for expansion *)
and findMinPos r t n =
  match r with
    | [] -> (-1, Position.Root)
    | ri::r' -> let poss = findMinPosAux ri (List.hd t) in
                  if poss <> [] then
                    (n, List.hd poss)
                  else
                    findMinPos r' (List.tl t) (n+1)
and findMinPosAux r t =
  let pos0 = List.rev (List.tl (List.rev (Term.getPositions r))) in  (* removes Position.End *)
    let pos1 = List.filter (fun p -> Term.isVariable (Term.getSubtermAt r p)) pos0 in
      List.filter (fun p -> noVariable t p) pos1
and noVariable t p =
  try
    not (Term.isVariable (Term.getSubtermAt t p))
  with
    Position.IllegalPosition -> false
(* renames the variable in all terms *)
and renameList terms =
  match terms with
    | [] -> []
    | t::ts -> let t' = renameTerm t in
                 t'::(renameList ts)
and renameTerm t =
  if Term.isVariable t then
    (
      num := !num + 1;
      Term.createVar ("X" ^ (string_of_int !num)) (Term.getVarSort t)
    )
  else
    let f = Term.getTopSymbol t in
      let newargs = renameList (Term.getArgs t) in
        Term.createFun f newargs

(* Checks whether each sort has at least two constructor ground terms.  Returns a list of sorts not satisfying this condition. *)
let rec checkConstructors ttrs =
  let sorts = getSorts ttrs in
    let constructors = List.map (getConstructorsForSort ttrs) sorts in
      (* less than 2 constructors *)
      let bad1 = List.filter (fun (_, conss) -> List.length conss < 2) (List.combine sorts constructors) in
        (* no constructor that does not take sort with at least two terms as argument *)
        let bad2 = List.filter (fun (_, conss) -> noArg (getSignature ttrs) conss (List.map fst bad1)) bad1 in
          List.map fst bad2
and noArg signa conss bad1 =
  List.for_all (noGoodArg signa bad1) conss
and noGoodArg signa bad1 con =
  List.for_all (fun sort -> List.mem sort bad1) (Signature.getArgSorts signa con)

(* Checks whether there a function symbols with resulting sort Int. *)
let hasIntResultConstructor ttrs =
  Signature.hasIntResult (Signature.getSubSignature (getSignature ttrs) (getConstructors ttrs))

(* Checks whether a TRS is Z-free. *)
let rec isZfree ttrs =
  List.for_all Rule.isZfree (getRules ttrs)

(* Checks whether a TRS is Z-free on its LHSs. *)
let rec isZfreeLeft ttrs =
  List.for_all Rule.isZfreeLeft (getRules ttrs)

(* Checks whether a TRS is unconstrained. *)
let rec isUnconstrained ttrs =
  List.for_all (fun rule -> Rule.getConstraint rule = []) (getRules ttrs)

(* Returns the sorts that are used in constructors of the given sort (reflexive-transitive). *)
let rec getDepSorts ttrs sort =
  let sortPO = constructPO ttrs in
    let dep = Poset.getAllBigger sortPO sort in
      if not (List.mem sort dep) then
        sort::dep
      else
        dep
and constructPO ttrs =
  let signa = getSignature ttrs
  and conss = getConstructors ttrs
  and sorts = getSorts ttrs in
    let po = Poset.create sorts in
      (
        extendPO po signa conss;
      )
and extendPO po signa conss =
  match conss with
    | [] -> po
    | c::cs -> let po' = extendPOAux po signa c in
                 extendPO po' signa cs
and extendPOAux po signa c =
  let sortc = Signature.getSort signa c in
    let argsorts = Signature.getArgSorts signa c in
      addAllBigger po sortc argsorts
and addAllBigger po sortc argsorts =
  match argsorts with
    | [] -> po
    | s::ss -> addAllBigger (Poset.setBigger po sortc s) sortc ss

(* Returns an HTML string for a TRS. *)
let rec toHTML ttrs =
  let defn = getDefined ttrs in
    (write_sorts (getSorts ttrs)) ^
    (write_signa (getSignature ttrs) defn) ^
    (write_rules (getRules ttrs) defn)
and write_sorts sorts =
  match sorts with
    | [] -> ""
    | s::ss -> (
                 "sort " ^
                 ("<FONT COLOR=\"#006400\">" ^ s ^ "</FONT><BR>\n") ^
                 (write_sorts ss)
               )
and write_signa (Signature.Sig s) defn =
  write_signa_aux s defn
and write_signa_aux s defn =
  match s with
    | [] -> ""
    | (f, _, args, target)::xs -> (
                                    "[ "
                                    ^ (write_fun f defn)
                                    ^ " : "
                                    ^ (write_sort_list args)
                                    ^ (if (List.length args <> 0) then " " else "")
                                    ^ "-> "
                                    ^ ("<FONT COLOR=\"#006400\">" ^ target ^ "</FONT>")
                                    ^ " ]<BR>\n"
                                    ^ (write_signa_aux xs defn)
                                  )
and write_fun f defn =
  if List.mem f defn then
    "<FONT COLOR=\"#8B0000\">" ^ f ^ "</FONT>"
  else
    "<FONT COLOR=\"#00008B\">" ^ f ^ "</FONT>"
and write_sort_list l =
  match l with
    | [] -> ""
    | [x] -> (
               "<FONT COLOR=\"#006400\">" ^ x ^ "</FONT>"
             )
    | x::xs -> (
                 "<FONT COLOR=\"#006400\">" ^ x ^ "</FONT>"
                 ^ ", "
                 ^ (write_sort_list xs)
               )
and write_rules r defn =
  match r with
    | [] -> ""
    | [x] -> write_rule x defn
    | x::xs -> (
                 (write_rule x defn)
                 ^ "<BR>\n"
                 ^ (write_rules xs defn)
               )
and write_rule (Rule.Rule (l, r, c)) defs =
  (Term.toHTML l defs) ^
  " -> " ^
  (Term.toHTML r defs) ^
  write_constraints c
and write_constraints c =
  if c = [] then
    ""
  else
    " [ " ^
    (String.concat " &#8743; " (List.map write_constraint c)) ^
    " ]"
and write_constraint c =
  match c with
    | Constraint.Eq (s, t) -> (Term.toHTML s []) ^ " &#61; " ^ (Term.toHTML t [])
    | Constraint.Geq (s, t) -> (Term.toHTML s []) ^ " &ge; " ^ (Term.toHTML t [])
    | Constraint.Gtr (s, t) -> (Term.toHTML s []) ^ " &gt; " ^ (Term.toHTML t [])

(* Returns datatype declarations for constructors in CVC3 format. *)
let rec getConstructorsCVC3 ttrs =
  let sorts = Util.remove (getSorts ttrs) "Int"
  and signa = getSignature ttrs in
    let type_names = String.concat ",\n" (List.map (getTypeDecl ttrs signa) sorts) in
      if type_names = "" then "" else "DATATYPE\n" ^ type_names ^ "\nEND;\n"
and getTypeDecl ttrs signa sort =
  let conss = getConstructorsForSort ttrs sort in
    "  " ^ sort ^ " = " ^ (getConssList signa conss)
and getConssList signa conss =
  String.concat " | " (List.map (getConssListEntry signa) conss)
and getConssListEntry signa consi =
  consi ^ (getArgList signa consi)
and getArgList signa consi =
  if (Signature.getArity signa consi) = 0 then
    ""
  else
    let argSorts = Signature.getArgSorts signa consi in
      " (" ^ (getArgListSel argSorts consi 1) ^ ")"
and getArgListSel argSorts consi n =
  match argSorts with
    | [] -> ""
    | [ass] -> consi ^ (string_of_int n) ^ ": " ^ (getCVCsort ass)
    | ass::asses -> consi ^ (string_of_int n) ^ ": " ^ (getCVCsort ass) ^ ", " ^ (getArgListSel asses consi (n+1))
and getCVCsort sort =
  if sort = "Int" then "INT" else sort
