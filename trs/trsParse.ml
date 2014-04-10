(*
  Implementation of trs-parsing.

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

(* General parse exception. *)
exception ParseException of int * int * string

(* Parses a trs from an in_channel. *)
let getTrs chan =
  try
    Trs_lexer.pos := 1;
    Trs_lexer.line := 1;
    let lexbuf = Lexing.from_channel chan in
      Trs_parser.trs_eol Trs_lexer.token lexbuf
  with
    | Parsing.Parse_error ->
        raise
          (
            ParseException
              (
                !Trs_lexer.line,
                !Trs_lexer.pos,
                Printf.sprintf "Error: Parse error in line %d at position %d." !Trs_lexer.line !Trs_lexer.pos
              )
          )
    | Trs_lexer.Unknown ->
        raise
          (
            ParseException
              (
                !Trs_lexer.line,
                !Trs_lexer.pos,
                Printf.sprintf "Error: Unknown token in line %d at position %d." !Trs_lexer.line !Trs_lexer.pos
              )
          )
    | TermParse.SortConflict (t, n) ->
        raise
          (
            ParseException
              (
                !Trs_parser_aux.currline,
                -1,
                Printf.sprintf "Error: Argument %d of \"%s\" has the wrong sort on line %d." n t !Trs_parser_aux.currline
              )
          )
    | TermParse.ArityConflict (f, n, nn) ->
        raise
          (
            ParseException
              (
                !Trs_parser_aux.currline,
                -1,
                Printf.sprintf "Error: Symbol \"%s\" has arity %d, not %d on line %d." f n nn !Trs_parser_aux.currline
              )
          )
    | TermParse.SortConflictVar (x, s1, s2) ->
        raise
          (
            ParseException
              (
                !Trs_parser_aux.currline,
                -1,
                Printf.sprintf "Error: Variable \"%s\" is used with sorts \"%s\" and \"%s\" on line %d." x s1 s2 !Trs_parser_aux.currline
              )
          )
    | Rule.SortConflictRule r ->
        raise
          (
            ParseException
              (
                !Trs_parser_aux.currline,
                -1,
                Printf.sprintf "Error: Sort conflict in \"%s\" on line %d." r !Trs_parser_aux.currline
              )
          )
    | Rule.NoRule r ->
        raise
          (
            ParseException
              (
                !Trs_parser_aux.currline,
                -1,
                Printf.sprintf "Error: Left hand side of \"%s\" is a variable on line %d." r !Trs_parser_aux.currline
              )
          )
    | Rule.VariableConflict r ->
        raise
          (
            ParseException
              (
                !Trs_parser_aux.currline,
                -1,
                Printf.sprintf "Error: Variable condition violated in \"%s\" on line %d." r !Trs_parser_aux.currline
              )
          )
    | Signature.NotInSignature f ->
        raise
          (
            ParseException
              (
                !Trs_parser_aux.currline,
                -1,
                Printf.sprintf "Error: Symbol \"%s\" is unknown on line %d." f !Trs_parser_aux.currline
              )
          )
    | Signature.UnknownSort (f, s) ->
        raise
          (
            ParseException
              (
                -1,
                -1,
                Printf.sprintf "Error: Declaration of \"%s\" uses unknown sort \"%s\"." f s
              )
          )
    | Signature.AlreadyInSignature f ->
        raise
          (
            ParseException
              (
                -1,
                -1,
                Printf.sprintf "Error: \"%s\" is declared twice." f
              )
          )
    | Trs_parser_aux.BuiltinRootException l ->
        raise
          (
            ParseException
              (
                l,
                1,
                Printf.sprintf "Error: Builtins cannot be redefined in line %d at position %d." l 1
              )
          )
    | Trs_parser_aux.BuiltinException l ->
        raise
          (
            ParseException
              (
                l,
                -1,
                Printf.sprintf "Error: Builtins cannot occur in left-hand side in line %d." l
              )
          )
