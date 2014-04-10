(*
  Implementation of formulas.

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

type atom = Atom of Term.term * Term.term * Constraint.cond list

type formula = Formula of atom list | True | False

(* Returns a string representing the formula. *)
let rec toString f =
  match f with
    | True -> "TRUE"
    | False -> "FALSE"
    | Formula fs -> toStringAux fs
and toStringAux f =
  if f = [] then
    "TRUE"
  else
    String.concat " /\\ " (List.map (fun (Atom (s, t, c)) -> (Term.toString s) ^ " = " ^ (Term.toString t) ^ (condString c)) f)
and condString c =
  if c = [] then
    ""
  else
    " [ " ^ (String.concat " /\\ " (List.map Constraint.toString c)) ^ " ]"

(* Returns a string representing the formula containing variable sorts. *)
let rec toStringSorts f =
  match f with
    | True -> "TRUE"
    | False -> "FALSE"
    | Formula fs -> toStringSortsAux fs
and toStringSortsAux f =
  if f = [] then
    "TRUE"
  else
    String.concat " /\\ " (List.map (fun (Atom (s, t, c)) -> (Term.toStringSorts s) ^ " = " ^ (Term.toStringSorts t) ^ (condStringSorts c)) f)
and condStringSorts c =
  if c = [] then
    ""
  else
    " [ " ^ (String.concat " /\\ " (List.map Constraint.toStringSorts c)) ^ " ]"

(* Returns all variables of a formula. *)
let rec getVars f =
  match f with
    | True | False -> []
    | Formula fs -> getVarsAux fs
and getVarsAux f =
  Util.remdup (List.concat (List.map (fun (Atom (s, t, c)) -> (Term.getVarsAsTerms s) @ (Term.getVarsAsTerms t) @ (List.concat (List.map Constraint.getVarsAsTerms c))) f))

(* Returns all function symbols occuring in a formula. *)
let rec getFuns f =
  match f with
    | True | False -> []
    | Formula fs -> getFunsAux fs
and getFunsAux f =
  Util.remdup (List.concat (List.map (fun (Atom (s, t, c)) -> (Term.getFuns s) @ (Term.getFuns t)) f))

(* Applies a substitution to a formula. *)
let rec applySubstitution f sub =
  match f with
    | True | False -> f
    | Formula fs -> applySubstitutionAux fs sub
and applySubstitutionAux f sub =
  Formula (List.map (fun (Atom (s, t, c)) -> (Atom (Substitution.applyToTerm sub s, Substitution.applyToTerm sub t, List.map (Constraint.applySubstitution sub) c))) f)

(* Checks whether the formula is fully typed. *)
let rec isFullyTyped f =
  match f with
    | True | False -> true
    | Formula fs -> isFullyTypedAux fs
and isFullyTypedAux f =
  List.for_all (fun (Atom (s, t, _)) -> Term.isFullyTyped s && Term.isFullyTyped t) f

(* Returns all subterms of a formula. *)
let rec getAllSubterms f =
  match f with
    | True | False -> []
    | Formula fs -> getAllSubtermsAux fs
and getAllSubtermsAux f =
  Util.remdup (List.concat (List.map (fun (Atom (s, t, _)) -> (Term.getAllSubterms s) @ (Term.getAllSubterms t)) f))

(* Returns all subterms of a formula headed by a given symbol. *)
let getAllSubtermsForSymbol f symb =
  List.filter (fun t -> Term.getTopSymbol t = symb) (getAllSubterms f)

(* Returns all subterms of a formula headed by a symbol from a given set. *)
let getAllSubtermsForSymbols f symbs =
  List.concat (List.map (fun symb -> getAllSubtermsForSymbol f symb) symbs)

(* Returns the maximal terms occuring in a formula. *)
let rec getAllMaximalTerms f =
  match f with
    | True | False -> []
    | Formula fs -> getAllMaximalTermsAux fs
and getAllMaximalTermsAux f =
  Util.remdup (List.concat (List.map (fun (Atom (s, t, _)) -> s::t::[]) f))

(* Returns a string for a formula in HTML. *)
let rec toHTML f defs =
  match f with
    | True -> "<B>TRUE</B>"
    | False -> "<B>FALSE</B>"
    | Formula fs -> toHTMLAux fs defs
and toHTMLAux f defs =
  if f = [] then
    "<B>TRUE</B>"
  else
    String.concat " &#8743; " (List.map (fun (Atom (s, t, c)) -> (Term.toHTML s defs) ^ " &#61; " ^ (Term.toHTML t defs) ^ (write_constraints c defs)) f)
and write_constraints c defs =
  if c = [] then
    ""
  else
    " [ " ^
    (String.concat " &#8743; " (List.map (fun co -> write_constraint co defs) c)) ^
    " ]"
and write_constraint c defs =
  match c with
    | Constraint.Eq (s, t) -> (Term.toHTML s defs) ^ " &#61; " ^ (Term.toHTML t defs)
    | Constraint.Geq (s, t) -> (Term.toHTML s defs) ^ " &ge; " ^ (Term.toHTML t defs)
    | Constraint.Gtr (s, t) -> (Term.toHTML s defs) ^ " &gt; " ^ (Term.toHTML t defs)

(* Normalizes a formula with a TRS. *)
let rec normalize trs f =
  match f with
    | True | False -> f
    | Formula fs -> normalizeAux trs fs
and normalizeAux trs f =
  (Formula (List.map (normalizeAtom trs) f))
and normalizeAtom trs (Atom (l, r, c)) =
  Atom (Trs.normalize trs l, Trs.normalize trs r, c)

(* Normalizes a Z-free formula with a Z-free TRS. *)
let rec normalizeZfree trs f =
  match f with
    | True | False -> f
    | Formula fs -> normalizeZfreeAux trs fs
and normalizeZfreeAux trs f =
  (Formula (List.map (normalizeAtomZfree trs) f))
and normalizeAtomZfree trs (Atom (l, r, c)) =
  Atom (Trs.normalizeZfree trs l, Trs.normalizeZfree trs r, c)

(* Normalizes a formula with PA rules. *)
let rec normalizePA f =
  match f with
    | True | False -> f
    | Formula fs -> normalizePAAux fs
and normalizePAAux f =
  (Formula (List.map normalizeAtomPA f))
and normalizeAtomPA (Atom (l, r, c)) =
  Atom (Trs.normalizePA l, Trs.normalizePA r, c)

(* Determines whether a formula is Z-free. *)
let rec isZfree f =
  match f with
    | True | False -> true
    | Formula fs -> isZfreeAux fs
and isZfreeAux f =
  List.for_all isZfreeAtom f
and isZfreeAtom (Atom (l, r, _)) =
  (Term.isZfree l) && (Term.isZfree r)

(* Determines whether a formula is Z-free on its LHSs. *)
let rec isZfreeLeft f =
  match f with
    | True | False -> true
    | Formula fs -> isZfreeLeftAux fs
and isZfreeLeftAux f =
  List.for_all isZfreeLeftAtom f
and isZfreeLeftAtom (Atom (l, _, _)) =
  (Term.isZfree l)

(* Determines whether a formula contains only function symbols from the given set. *)
let rec isBasedOn funs f =
  match f with
    | True | False -> true
    | Formula fs -> isBasedOnAux funs fs
and isBasedOnAux funs f =
  List.for_all (isBasedOnAtom funs) f
and isBasedOnAtom funs (Atom (l, r, _)) =
  (Term.isBasedOn funs l) && (Term.isBasedOn funs r)

(* Determines whether a formula is valid in LIAC. *)
let rec isValidLIACConjunction ttrs f =
  match f with
    | True | Formula [] -> Ynm.Yes
    | False -> Ynm.No
    | Formula fs -> isValidLIACConjunctionAux ttrs fs
and isValidLIACConjunctionAux ttrs f =
  let vars = getVarsAux f in
    let formstring = (Trs.getConstructorsCVC3 ttrs) ^ "\n" ^ (getVarsLIAC vars) ^ "\nformula: BOOLEAN = " ^ (getFormulaConj f) ^ ";\n\n" in
      Cvc3.isValid formstring "formula"
and getVarsLIAC vars =
  (String.concat ";\n" (List.map getVarsLIACAux vars)) ^ ";\n"
and getVarsLIACAux var =
  (Term.getTopSymbol var) ^ ": " ^ (getCVCsort (Term.getVarSort var))
and getCVCsort sort =
  if sort = "Int" then "INT" else sort
and getFormulaConj atoms =
  String.concat " AND " (List.map getAtomString atoms)
and getAtomString (Atom (s, t, c)) =
  if c = [] then
    "(" ^ (Term.toCVC3 s) ^ ") = (" ^ (Term.toCVC3 t) ^ ")"
  else
    "((" ^ (getConstraintString c) ^ ") => ((" ^ (Term.toCVC3 s) ^ ") = (" ^ (Term.toCVC3 t) ^ ")))"
and getConstraintString c =
  String.concat " AND " (List.map wrap c)
and wrap con =
  "(" ^ (Constraint.toCVC3 con) ^ ")"

(* Determines whether a formula is satisfiable in LIAC. *)
let rec isSatisfiableLIACConjunction ttrs f =
  match f with
    | True | Formula [] -> Ynm.Yes
    | False -> Ynm.No
    | Formula fs -> isSatisfiableLIACConjunctionAux ttrs fs
and isSatisfiableLIACConjunctionAux ttrs f =
  let vars = getVarsAux f in
    let formstring = (Trs.getConstructorsCVC3 ttrs) ^ "\n" ^ (getVarsLIAC vars) ^ "\nformula: BOOLEAN = " ^ (getFormulaConj f) ^ ";\n\n" in
      Cvc3.isSatisfiable formstring "formula"

(* Determines whether a formula and a constraint list are satisfiable in LIAC. *)
let rec isSatisfiableLIACConjunctionConstraint ttrs f c =
  match f with
    | False -> Ynm.No
    | True | Formula [] -> Decproc.isSatisfiablePAConjunction c
    | Formula fs -> isSatisfiableLIACConjunctionConstraintAux ttrs fs c
and isSatisfiableLIACConjunctionConstraintAux ttrs fs c =
  if c = [] then
    isSatisfiableLIACConjunction ttrs (Formula fs)
  else
    isSatisfiableLIACConjunctionConstraintReal ttrs fs c
and isSatisfiableLIACConjunctionConstraintReal ttrs f c =
  let vars = Util.remdup ((getVarsAux f) @ (List.flatten (List.map Constraint.getVarsAsTerms c))) in
    let formstring = (Trs.getConstructorsCVC3 ttrs) ^ "\n" ^ (getVarsLIAC vars) ^ "\nformula: BOOLEAN = " ^ (getFormulaConjConst f c) ^ ";\n\n" in
      Cvc3.isSatisfiable formstring "formula"
and getFormulaConjConst f c =
  String.concat " AND " ((List.map getAtomString f) @ (List.map wrap c))

(* Determines whether the implication between two formulas is valid in LIAC. *)
let rec isValidLIACImplicationConstraint ttrs c f1 f2 =
  if c = [] then
    isValidLIACImplication ttrs f1 f2
  else
    match f1 with
      | False -> Ynm.Yes
      | True -> isValidLIACImplicationConstraintAux ttrs c [] f2
      | Formula fs -> isValidLIACImplicationConstraintAux ttrs c fs f2
and isValidLIACImplicationConstraintAux ttrs c fs1 f2 =
  match f2 with
    | True | Formula [] -> Ynm.Yes
    | False -> swap (isSatisfiableLIACConjunctionConstraint ttrs (Formula fs1) c)
    | Formula fs2 -> isValidLIACImplicationConstraintReal ttrs c fs1 fs2
and isValidLIACImplicationConstraintReal ttrs c fs1 fs2 =
  let vars = Util.remdup ((getVarsAux (fs1 @ fs2)) @ (List.flatten (List.map Constraint.getVarsAsTerms c))) in
    let formstring = (Trs.getConstructorsCVC3 ttrs) ^ "\n" ^ (getVarsLIAC vars) ^ "\nformula: BOOLEAN = " ^ (getFormulaImplConst c fs1 fs2) ^ ";\n\n" in
      Cvc3.isValid formstring "formula"
and getFormulaImplConst c fs1 fs2 =
  "(" ^ (getFormulaConjConst fs1 c) ^ ") => (" ^ (getFormulaConj fs2) ^ ")"  
and isValidLIACImplication ttrs f1 f2 =
  match f1 with
    | False -> Ynm.Yes
    | True | Formula [] -> isValidLIACConjunction ttrs f2
    | Formula fs1 -> isValidLIACImplicationAux ttrs fs1 f2
and isValidLIACImplicationAux ttrs fs1 f2 =
  match f2 with
    | True | Formula [] -> Ynm.Yes
    | False -> swap (isSatisfiableLIACConjunction ttrs (Formula fs1))
    | Formula fs2 -> isValidLIACImplicationReal ttrs fs1 fs2
and swap ynm =
  match ynm with
    | Ynm.Yes -> Ynm.No
    | Ynm.No -> Ynm.Yes
    | _ -> ynm
and isValidLIACImplicationReal ttrs fs1 fs2 =
  let vars = getVarsAux (fs1 @ fs2) in
    let formstring = (Trs.getConstructorsCVC3 ttrs) ^ "\n" ^ (getVarsLIAC vars) ^ "\nformula: BOOLEAN = " ^ (getFormulaImpl fs1 fs2) ^ ";\n\n" in
      Cvc3.isValid formstring "formula"
and getFormulaImpl fs1 fs2 =
  "(" ^ (getFormulaConj fs1) ^ ") => (" ^ (getFormulaConj fs2) ^ ")"
