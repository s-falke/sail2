(*
  Lexer for formulas.

  @author Stephan Falke
  @version $Id: formula_lexer.mll,v 1.3 2009/03/20 22:09:47 spf Exp $
*)

{
  open Formula_parser
  exception Eof
  exception Unknown

  let pos = ref 1
}

rule token = parse
  | [' ']                                       { incr pos; token lexbuf }
  | ['\t']                                      { pos := !pos + 8; token lexbuf }
  | ['\n']                                      { EOL }
  | [',']                                       { incr pos; COMMA }
  | ['a'-'z']['a' - 'z' '0'-'9']*['\'']*        { let s = Lexing.lexeme lexbuf in
                                                    pos := !pos + (String.length s);
                                                    PREFIX_IDENT s }
  | '+'                                         { incr pos; PLUS }
  | '-'                                         { incr pos; MINUS }
  | '0'                                         { incr pos; ZERO }
  | '1'                                         { incr pos; ONE }
  | ['A'-'Z']['A'-'Z' '0'-'9' '\'']*            { let s = Lexing.lexeme lexbuf in
                                                    pos := !pos + (String.length s);
                                                    VAR_IDENT s }
  | '/''\\'                                     { pos := !pos + 2; CONJ }
  | '='                                         { incr pos; EQ }
  | '('                                         { incr pos; OPENPAR }
  | ')'                                         { incr pos; CLOSEPAR }
  | '>''='                                      { pos := !pos + 2; GEQ }
  | '>'                                         { incr pos; GTR }
  | '['                                         { incr pos; OPENSQ }
  | ']'                                         { incr pos; CLOSESQ }
  | eof                                         { raise Eof }
  | _                                           { raise Unknown }
