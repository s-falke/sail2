(*
  Lexer for TRSs.

  @author Stephan Falke
  @version $Id: trs_lexer.mll,v 1.3 2009/03/18 20:46:27 spf Exp $
*)

{
  open Trs_parser
  exception Eof
  exception Unknown

  let line = ref 1
  let pos = ref 1
}

rule token = parse
  | '#'[^'\n']*                                 { EOL }
  | [' ']                                       { incr pos; token lexbuf }
  | ['\t']                                      { pos := !pos + 8; token lexbuf }
  | ['\n']                                      { pos := 1; incr line; EOL }
  | [',']                                       { incr pos; COMMA }
  | [':']                                       { incr pos; COL }
  | '-''>'                                      { pos := !pos + 2; TO !line }
  | 'I''n''t'                                   { pos := !pos + 3; INT }
  | 's''o''r''t'                                { pos := !pos + 4; SORT }
  | ['a'-'z']['a' - 'z' '0'-'9']*['\'']*        { let s = Lexing.lexeme lexbuf in
                                                    pos := !pos + (String.length s);
                                                    PREFIX_IDENT s }
  | '+'                                         { incr pos; PLUS }
  | '-'                                         { incr pos; MINUS }
  | '0'                                         { incr pos; ZERO }
  | '1'                                         { incr pos; ONE }
  | ['A'-'Z']['a'-'z']+                         { let s = Lexing.lexeme lexbuf in
                                                    pos := !pos + (String.length s);
                                                    SORT_IDENT s }
  | ['A'-'Z']['A'-'Z' '0'-'9' '\'']*            { let s = Lexing.lexeme lexbuf in
                                                    pos := !pos + (String.length s);
                                                    VAR_IDENT s }
  | '/''\\'                                     { pos := !pos + 2; CONJ }
  | '='                                         { incr pos; EQ }
  | '>''='                                      { pos := !pos + 2; GEQ }
  | '>'                                         { incr pos; GTR }
  | '('                                         { incr pos; OPENPAR }
  | ')'                                         { incr pos; CLOSEPAR }
  | '['                                         { incr pos; OPENSQ }
  | ']'                                         { incr pos; CLOSESQ }
  | eof                                         { EOF }
  | _                                           { raise Unknown }
