(*
  Silly GUI, colorful displays

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

open GText
open Gtk.Tags
open Formula
open Proof

let create_tags (buffer:GText.buffer) =
  ignore (buffer#create_tag ~name:"bold" [`WEIGHT `BOLD]);
  ignore (buffer#create_tag ~name:"sort_name" [`FOREGROUND "darkgreen"]);
  ignore (buffer#create_tag ~name:"def_fun_name" [`FOREGROUND "darkred"]);
  ignore (buffer#create_tag ~name:"con_fun_name" [`FOREGROUND "darkblue"]);
  ignore (buffer#create_tag ~name:"var_name" [`FOREGROUND "magenta"; `STYLE `ITALIC]);
  ignore (buffer#create_tag ~name:"size" [`SIZE (12*Pango.scale)]);
  ()

(* WRITE TRS *)
let rec write_trs (buffer:GText.buffer) (ttrs:Trs.trs) =
  buffer#set_text "";
  write_sorts buffer (Trs.getSorts ttrs);
  let defn = Trs.getDefined ttrs in
    (
      write_signa buffer (Trs.getSignature ttrs) defn;
      write_rules buffer (Trs.getRules ttrs) defn
    )
and write_sorts buffer sorts =
  match sorts with
    | [] -> ()
    | s::ss -> (
                 buffer#insert ~tag_names:["size";"bold"] "sort ";
                 buffer#insert ~tag_names:["size";"sort_name"] (s ^ "\n");
                 write_sorts buffer ss
               )
and write_signa buffer (Signature.Sig s) defn =
  write_signa_aux buffer s defn
and write_signa_aux buffer s defn =
  match s with
    | [] -> ()
    | (f, _, args, target)::xs -> (
                                    buffer#insert ~tag_names:["size";"bold"] "[ ";
                                    write_fun buffer f defn;
                                    buffer#insert ~tag_names:["size";"bold"] " : ";
                                    write_sort_list buffer args;
                                    if (List.length args <> 0) then
                                      buffer#insert ~tag_names:["size";"bold"] " ";
                                    buffer#insert ~tag_names:["size";"bold"] "-> ";
                                    buffer#insert ~tag_names:["size";"sort_name"] target;
                                    buffer#insert ~tag_names:["size";"bold"] " ]\n";
                                    write_signa_aux buffer xs defn
                                  )
and write_sort_list buffer l =
  match l with
    | [] -> ();
    | [x] -> (
               buffer#insert ~tag_names:["size";"sort_name"] x
             )
    | x::xs -> (
                 buffer#insert ~tag_names:["size";"sort_name"] x;
                 buffer#insert ~tag_names:["size";"bold"] ", ";
                 write_sort_list buffer xs
               )
and write_fun buffer f defn =
  if List.mem f defn then
    buffer#insert ~tag_names:["size";"def_fun_name"] f
  else
    buffer#insert ~tag_names:["size";"con_fun_name"] f;
and write_rules buffer r defn =
  match r with
    | [] -> ();
    | [x] -> write_rule buffer x defn
    | x::xs -> (
                 write_rule buffer x defn;
                 buffer#insert "\n";
                 write_rules buffer xs defn
               )
and write_rule buffer ru defn =
  match ru with
    | Rule.Rule (l, r, cs) ->
        (
          write_term buffer l defn;
          buffer#insert ~tag_names:["size";"bold"] " -> ";
          write_term buffer r defn;
          write_conds buffer cs
        )
and write_conds buffer cs =
  if cs = [] then
    ()
  else
  (
    buffer#insert ~tag_names:["size";"bold"] " [ ";
    write_conds_real buffer cs;
    buffer#insert ~tag_names:["size";"bold"] " ]"
  )
and write_conds_real buffer cs =
  match cs with
    | [] -> ()
    | [c] -> write_cond buffer c
    | c::ccs ->
        (
          write_cond buffer c;
          buffer#insert ~tag_names:["size";"bold"] " /\\ ";
          write_conds_real buffer ccs
        )
and write_cond buffer c =
  match c with
    | Constraint.Eq (l, r) ->
        (
          write_term buffer l [];
          buffer#insert ~tag_names:["size";"bold"] " = ";
          write_term buffer r []
        )
    | Constraint.Geq (l, r) ->
        (
          write_term buffer l [];
          buffer#insert ~tag_names:["size";"bold"] " >= ";
          write_term buffer r []
        )
    | Constraint.Gtr (l, r) ->
        (
          write_term buffer l [];
          buffer#insert ~tag_names:["size";"bold"] " > ";
          write_term buffer r []
        )
(* WRITE TERM *)
and write_term buffer t defn =
  let f = Term.getTopSymbol t in
    if Term.isVariable t then
      buffer#insert ~tag_names:["size";"var_name"] f
    else
      (
        write_fun buffer f defn;
        let args = Term.getArgs t in
          if List.length args = 0 then
            ()
          else
            (
              buffer#insert ~tag_names:["size";"bold"] "(";
              write_term_list buffer args defn;
              buffer#insert ~tag_names:["size";"bold"] ")"
            )
      )
and write_term_list buffer ts defn =
  match ts with
    | [] -> ();
    | [x] -> (
               write_term buffer x defn
             )
    | x::xs -> (
                 write_term buffer x defn;
                 buffer#insert ~tag_names:["size";"bold"] ", ";
                 write_term_list buffer xs defn
               )

(* WRITE FORMULA *)
let rec write_formula (buffer:GText.buffer) (f:Formula.formula) (ttrs:Trs.trs) =
  let defn = (Trs.getDefined ttrs) in
    match f with
      | Formula [] | True -> buffer#insert ~tag_names:["size";"bold"] "TRUE";
      | False -> buffer#insert ~tag_names:["size";"bold"] "FALSE";
      | Formula fs -> write_atoms buffer fs defn
and write_formula_aux buffer f defn =
  match f with
    | Formula fs -> write_atoms buffer fs defn
    | True -> buffer#insert ~tag_names:["size";"bold"] "TRUE";
    | False -> buffer#insert ~tag_names:["size";"bold"] "FALSE";
and write_atoms buffer fs defn =
  match fs with
    | [] -> ()
    | [Atom (s, t, c)] -> (
                            write_term buffer s defn;
                            buffer#insert ~tag_names:["size";"bold"] " = ";
                            write_term buffer t defn;
                            write_conds buffer c
                          )
    | (Atom (s, t, c))::fs' -> (
                                 write_term buffer s defn;
                                 buffer#insert ~tag_names:["size";"bold"] " = ";
                                 write_term buffer t defn;
                                 write_conds buffer c;
                                 buffer#insert ~tag_names:["size";"bold"] " /\\ ";
                                 write_atoms buffer fs' defn
                            )

(* WRITE PROOF *)
let rec write_proof (buffer:GText.buffer) (f:Formula.formula) (prf:Proof.proof) (ttrs:Trs.trs) =
  let defn = (Trs.getDefined ttrs) in
    write_proof_aux buffer prf f defn
and write_proof_aux buffer prf start defn =
  buffer#insert ~tag_names:["size"] ("Initial formula: " ^ "\n\n");
  buffer#insert ~tag_names:["size";"bold"] "1: ";
  write_formula_aux buffer start defn;
  buffer#insert ~tag_names:["size"] "\n\n\n";
  write_proof_aux_aux buffer prf start 1 defn
and write_proof_aux_aux buffer prf phi num defn =
  let (step, rest) = find_step phi prf in
    let phi' = get_formula_res step in
      if phi' = phi && (isDirect step) then
        write_proof_aux_aux buffer rest phi num defn
      else
        (
          match step with
            | Leaf _ ->
              (
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string num) ^ ": ");
                buffer#insert ~tag_names:["size"] "This formula cannot be transformed any further..."
              )
            | Direct (_, expl, phi') ->
              (
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string num) ^ ": ");
                buffer#insert ~tag_names:["size"] "This formula is transformed into\n\n";
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string (num + 1)) ^ ": ");
                write_formula_aux buffer phi' defn;
                buffer#insert ~tag_names:["size"] ("\n\nusing " ^ expl ^ ".\n\n\n");
                write_proof_aux_aux buffer rest phi' (num + 1) defn
              )
            | Expand (_, expl, hyps, phi') ->
              (
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string num) ^ ": ");
                buffer#insert ~tag_names:["size"] "This formula is transformed into\n\n";
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string (num  + 1)) ^ ": ");
                write_formula_aux buffer phi' defn;
                buffer#insert ~tag_names:["size"] ("\n\nusing " ^ expl ^ ".\n\n");
                buffer#insert ~tag_names:["size"] "Generated hypotheses:\n\n";
                write_rules buffer hyps defn;
                buffer#insert ~tag_names:["size"] "\n\n\n";
                write_proof_aux_aux buffer rest phi' (num + 1) defn
              )
            | Liac (_, phi') ->
              (
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string num) ^ ": ");
                buffer#insert ~tag_names:["size"] ("This formula is LIAC-based.\n\n\n");
                write_proof_aux_aux buffer rest phi' num defn
              )
            | Simple (_, flag, badsub, funs, ruleo, phi') ->
              (
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string num) ^ ": ");
                buffer#insert ~tag_names:["size"] ("This formula is " ^ (if flag then "" else "not ") ^ "simple");
                buffer#insert ~tag_names:["size"] (if flag then " (assuming termination).\n\n\n" else " because ");
                if not flag then
                  (
                    writeNotSimple buffer badsub funs ruleo None None defn;
                    buffer#insert ~tag_names:["size"] "\n\n\n"
                  )
                else
                  ();
                write_proof_aux_aux buffer rest phi' num defn
              )
            | Nested (_, flag, badsub, funs, ruleo, compato, phi') ->
              (
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string num) ^ ": ");
                buffer#insert ~tag_names:["size"] ("This formula is " ^ (if flag then "" else "not ") ^ "simple nested");
                buffer#insert ~tag_names:["size"] (if flag then " (assuming termination).\n\n\n" else " because ");
                if not flag then
                  (
                    writeNotSimple buffer badsub funs ruleo compato None defn;
                    buffer#insert ~tag_names:["size"] "\n\n\n"
                  )
                else
                  ();
                write_proof_aux_aux buffer rest phi' num defn
              )
            | Complex (_, flag, badsub, funs, ruleo, compato, notheoryo, phi') ->
              (
                buffer#insert ~tag_names:["size";"bold"] ((num_to_string num) ^ ": ");
                buffer#insert ~tag_names:["size"] ("This formula is " ^ (if flag then "" else "not ") ^ "complex");
                buffer#insert ~tag_names:["size"] (if flag then " (assuming termination).\n\n\n" else " because ");
                if not flag then
                  (
                    writeNotSimple buffer badsub funs ruleo compato notheoryo defn;
                    buffer#insert ~tag_names:["size"] "\n\n\n"
                  )
                else
                  ();
                write_proof_aux_aux buffer rest phi' num defn
              )
      )
and writeNotSimple buffer badsub funs ruleo compato notheoryo defn =
  match badsub with
    | None -> writeNotSimple2 buffer funs ruleo compato notheoryo defn
    | Some f -> (
                  buffer#insert ~tag_names:["size"] "the atomic conjecture\n\n";
                  write_formula_aux buffer (Formula [f]) defn;
                  buffer#insert ~tag_names:["size"] "\n\nprevents this."
                )
and writeNotSimple2 buffer funs ruleo compato notheoryo defn =
  match ruleo with
    | None -> writeNotSimple3 buffer compato notheoryo defn
    | Some ru -> (
                   buffer#insert ~tag_names:["size"] "the set\n\n";
                   write_funs buffer funs;
                   buffer#insert ~tag_names:["size"] "\n\nis not LIAC-based due to the rule\n\n";
                   write_rules buffer [ru] defn
                 )
and writeNotSimple3 buffer compato notheoryo defn =
  match compato with
    | None -> writeNotSimple4 buffer notheoryo defn
    | Some (f, g) ->
        (
          buffer#insert ~tag_names:["size"] "the funtion ";
          buffer#insert ~tag_names:["size";"def_fun_name"] f;
          buffer#insert ~tag_names:["size"] " is not compatible with the function ";
          buffer#insert ~tag_names:["size";"def_fun_name"] g;
          buffer#insert ~tag_names:["size"] "."
        )
and writeNotSimple4 buffer notheoryo defn =
  match notheoryo with
    | None -> buffer#insert ~tag_names:["size"] "termination could not be shown."
    | Some t ->
        (
          buffer#insert ~tag_names:["size"] "the no-theory condition for ";
          write_term buffer t defn;
          buffer#insert ~tag_names:["size"] " could not be verified."
        )
and write_funs buffer funs =
  match funs with
    | [] -> ()
    | [f] -> buffer#insert ~tag_names:["size";"def_fun_name"] f
    | f::fs -> (
                 buffer#insert ~tag_names:["size";"def_fun_name"] f;
                 buffer#insert ~tag_names:["size"] ",";
                 write_funs buffer fs
               )
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
