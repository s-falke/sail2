(*
  Implementation of proofs.

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

type proof_step =
  | Leaf of Formula.formula
  | Direct of Formula.formula * string * Formula.formula
  | Expand of Formula.formula * string * Rule.rule list * Formula.formula
  | Liac of Formula.formula * Formula.formula
  | Simple of Formula.formula * bool * Formula.atom option * string list * Rule.rule option * Formula.formula
  | Nested of Formula.formula * bool * Formula.atom option * string list * Rule.rule option * (string * string) option * Formula.formula
  | Complex of Formula.formula * bool * Formula.atom option * string list * Rule.rule option * (string * string) option * Term.term option * Formula.formula

type proof = proof_step list

(* Returns a string representing a proof. *)
let rec toString prf start =
  "Initial formula: " ^ "\n\n1: " ^ (Formula.toString start) ^ "\n\n\n" ^ (toStringAux prf start 1)
and toStringAux prf phi num =
  let (step, rest) = find_step phi prf in
    let phi' = get_formula_res step in
      if phi' = phi && (isDirect step) then
        toStringAux rest phi num
      else
        (
          match step with
            | Leaf _ -> (num_to_string num) ^ ": " ^ "This formula cannot be transformed any further..."
            | Direct (_, expl, phi') -> (num_to_string num)
                                        ^ ": " ^ "This formula is transformed into\n\n" ^
                                        (num_to_string (num + 1))
                                        ^ ": " ^ (Formula.toString phi') ^
                                        "\n\nusing " ^ expl ^ ".\n\n\n" ^ toStringAux rest phi' (num + 1)
            | Expand (_, expl, hyps, phi') -> (num_to_string num)
                                              ^ ": " ^ "This formula is transformed into\n\n" ^
                                              (num_to_string (num + 1))
                                              ^ ": " ^ (Formula.toString phi') ^
                                              "\n\nusing " ^ expl ^ ".\n\n" ^
                                              "Generated hypotheses:\n" ^
                                              (list_to_string hyps) ^ "\n\n\n" ^
                                              toStringAux rest phi' (num + 1)
            | Liac (_, phi') ->
                (num_to_string num)
                ^ ": " ^ "This formula is LIAC-based.\n\n\n" ^
                toStringAux rest phi' num
            | Simple (_, flag, badsub, funs, ruleo, phi') ->
                (num_to_string num)
                ^ ": " ^ "This formula is " ^ (if flag then "" else "not ") ^ "simple"
                ^ (if flag then " (assuming termination).\n\n\n" else (" because " ^ getNotSimple badsub funs ruleo None None) ^ "\n\n\n") ^
                toStringAux rest phi' num
            | Nested (_, flag, badsub, funs, ruleo, compato, phi') ->
                (num_to_string num)
                ^ ": " ^ "This formula is " ^ (if flag then "" else "not ") ^ "simple nested"
                ^ (if flag then " (assuming termination).\n\n\n" else (" because " ^ getNotSimple badsub funs ruleo compato None) ^ "\n\n\n") ^
                toStringAux rest phi' num
            | Complex (_, flag, badsub, funs, ruleo, compato, notheoryo, phi') ->
                (num_to_string num)
                ^ ": " ^ "This formula is " ^ (if flag then "" else "not ") ^ "complex"
                ^ (if flag then " (assuming termination).\n\n\n" else (" because " ^ getNotSimple badsub funs ruleo compato notheoryo) ^ "\n\n\n") ^
                toStringAux rest phi' num
      )
and getNotSimple badsub funs ruleo compato notheoryo =
  match badsub with
    | None -> getNotSimple2 funs ruleo compato notheoryo
    | Some f -> "the atomic conjecture\n\n" ^ (Formula.toString (Formula.Formula [f])) ^ "\n\nprevents this."
and getNotSimple2 funs ruleo compato notheoryo =
  match ruleo with
    | None -> getNotSimple3 compato notheoryo
    | Some ru -> "the set\n\n" ^ (String.concat "," funs) ^ "\n\nis not LIAC-based due to the rule\n\n"
                 ^ (Rule.toString ru)
and getNotSimple3 compato notheoryo =
  match compato with
    | None -> getNotSimple4 notheoryo
    | Some (f, g) -> "the funtion " ^ f ^ " is not compatible with the function " ^ g ^ "."
and getNotSimple4 notheoryo =
  match notheoryo with
    | None -> "termination could not be shown."
    | Some t -> "the no-theory condition for " ^ (Term.toString t) ^ " could not be verified."
and list_to_string hyps =
  String.concat "\n\t" ("\t"::(List.map (fun ru -> Rule.toString ru) hyps))
and num_to_string num =
  string_of_int num
and find_step phi' prf =
  match prf with
    | [] -> (Leaf phi', [])
    | x::xs -> let phi = get_formula x in
                 if phi = phi' then
                   (x, xs)
                 else
                   find_step phi' xs
and get_formula x =
  match x with
    | Leaf phi | Direct (phi, _, _) | Expand (phi, _, _, _)
    | Liac (phi, _) | Simple (phi, _, _, _, _, _) | Nested (phi, _, _, _, _, _, _)
    | Complex (phi, _, _, _, _, _, _, _) -> phi
and get_formula_res x =
  match x with
    | Leaf phi | Direct (_, _, phi) | Expand (_, _, _, phi)
    | Liac (_, phi) | Simple (_, _, _, _, _, phi) | Nested (_, _, _, _, _, _, phi)
    | Complex (_, _, _, _, _, _, _, phi) -> phi
and isDirect x =
  match x with
    | Direct _ -> true
    | Leaf _ | Expand _ | Liac _ | Simple _ | Nested _ | Complex _ -> false

(* toHTML *)
let rec toHTML prf start defs =
  "Initial formula: " ^ "<BR><BR>1: " ^ (Formula.toHTML start defs) ^ "<BR><BR><BR>\n\n" ^ (toHTMLAux prf start 1 defs)
and toHTMLAux prf phi num defs =
  let (step, rest) = find_step phi prf in
    let phi' = get_formula_res step in
      if phi' = phi && (isDirect step) then
        toHTMLAux rest phi num defs
      else
        (
          match step with
            | Leaf _ -> (string_of_int num) ^ ": " ^ "This formula cannot be transformed any further..."
            | Direct (_, expl, phi') -> (string_of_int num)
                                        ^ ": " ^ "This formula is transformed into<BR><BR>" ^
                                        (string_of_int (num + 1))
                                        ^ ": " ^ (Formula.toHTML phi' defs) ^
                                        "<BR><BR>using " ^ expl ^ ".<BR><BR><BR>\n\n" ^ toHTMLAux rest phi' (num + 1) defs
            | Expand (_, expl, hyps, phi') -> (string_of_int num)
                                              ^ ": " ^ "This formula is transformed into<BR><BR>" ^
                                              (string_of_int (num + 1))
                                              ^ ": " ^ (Formula.toHTML phi' defs) ^
                                              "<BR><BR>using " ^ expl ^ ".<BR><BR>" ^
                                              "Generated hypotheses:<BR><BR>" ^
                                              (list_to_html hyps defs) ^ "<BR><BR><BR>\n\n" ^
                                              toHTMLAux rest phi' (num + 1) defs
            | Liac (_, phi') ->
                (string_of_int num)
                ^ ": " ^ "This formula is LIAC-based.\n\n\n" ^
                toHTMLAux rest phi' num defs
            | Simple (_, flag, badsub, funs, ruleo, phi') ->
                (string_of_int num)
                ^ ": " ^ "This formula is " ^ (if flag then "" else "not ") ^ "simple"
                ^ (if flag then " (assuming termination).<BR><BR><BR>\n\n" else (" because " ^ getNotSimpleHTML badsub funs ruleo None None defs) ^ "<BR><BR><BR>\n\n") ^
                toHTMLAux rest phi' num defs
            | Nested (_, flag, badsub, funs, ruleo, compato, phi') ->
                (string_of_int num)
                ^ ": " ^ "This formula is " ^ (if flag then "" else "not ") ^ "simple nested"
                ^ (if flag then " (assuming termination).<BR><BR><BR>\n\n" else (" because " ^ getNotSimpleHTML badsub funs ruleo compato None defs) ^ "<BR><BR><BR>\n\n") ^
                toHTMLAux rest phi' num defs
            | Complex (_, flag, badsub, funs, ruleo, compato, notheoryo, phi') ->
                (string_of_int num)
                ^ ": " ^ "This formula is " ^ (if flag then "" else "not ") ^ "complex"
                ^ (if flag then " (assuming termination).<BR><BR><BR>\n\n" else (" because " ^ getNotSimpleHTML badsub funs ruleo compato notheoryo defs) ^ "<BR><BR><BR>\n\n") ^
                toHTMLAux rest phi' num defs
      )
and getNotSimpleHTML badsub funs ruleo compato notheoryo defs =
  match badsub with
    | None -> getNotSimpleHTML2 funs ruleo compato notheoryo defs
    | Some f -> "the atomic conjecture<BR><BR>" ^ (Formula.toHTML (Formula.Formula [f]) defs) ^ "<BR><BR>prevents this."
and getNotSimpleHTML2 funs ruleo compato notheoryo defs =
  match ruleo with
    | None -> getNotSimpleHTML3 compato notheoryo defs
    | Some ru -> "the set<BR><BR>" ^ (write_funs funs) ^ "<BR><BR>is not LIAC-based due to the rule<BR><BR>"
                 ^ (rulehtml ru defs)
and getNotSimpleHTML3 compato notheoryo defs =
  match compato with
    | None -> getNotSimpleHTML4 notheoryo defs
    | Some (f, g) -> "the funtion " ^ (write_fun f) ^ " is not compatible with the function " ^ (write_fun g) ^ "."
and getNotSimpleHTML4 notheoryo defs =
  match notheoryo with
    | None -> "termination could not be shown."
    | Some t -> "the no-theory condition for " ^ (Term.toHTML t defs) ^ " could not be verified."
and list_to_html hyps defs =
  String.concat "<BR>" (List.map (fun ru -> rulehtml ru defs) hyps)
and rulehtml (Rule.Rule (l, r, c)) defs =
  (Term.toHTML l defs) ^ " -> " ^ (Term.toHTML r defs) ^   (constraintshtml c)
and constraintshtml c =
  if c = [] then
    ""
  else
    " [ " ^
    (String.concat " &#8743; " (List.map constrainthtml c)) ^
    " ]"
and constrainthtml c =
  match c with
    | Constraint.Eq (s, t) -> (Term.toHTML s []) ^ " &#61; " ^ (Term.toHTML t [])
    | Constraint.Geq (s, t) -> (Term.toHTML s []) ^ " &ge; " ^ (Term.toHTML t [])
    | Constraint.Gtr (s, t) -> (Term.toHTML s []) ^ " &gt; " ^ (Term.toHTML t [])
and write_fun f =
  "<FONT COLOR=8B0000>" ^ f ^ "</FONT>"
and write_funs funs =
  match funs with
    | [] -> ""
    | [f] -> write_fun f
    | f::fs -> (
                 (write_fun f)
                 ^ ", "
                 ^ (write_funs fs)
               )
