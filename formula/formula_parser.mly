/*
  Parser for formulas.

  @author Stephan Falke
  @version $Id: formula_parser.mly,v 1.2 2009/03/20 22:09:04 spf Exp $
*/

%{
%}

%token <string> PREFIX_IDENT
%token <string> VAR_IDENT
%token COMMA OPENPAR CLOSEPAR EOL EQ CONJ ZERO ONE PLUS MINUS GEQ GTR OPENSQ CLOSESQ

%left CONJ
%nonassoc PREFIX_IDENT

%start formula_eol
%type <Formula.formula> formula_eol

%%

formula_eol:
  formula EOL { (Formula.Formula $1) }
;

formula :
| term EQ term
    { [Formula.Atom ($1, $3, [])] }
| term EQ term OPENSQ condlist CLOSESQ
    { [Formula.Atom ($1, $3, $5)] }
| formula CONJ formula
    { $1 @ $3 }
;

condlist :
| cond
    { [$1] }
| cond CONJ condlist
    { ($1::$3) }
;

cond :
| paterm EQ paterm
    { Constraint.Eq ($1, $3) }
| paterm GEQ paterm
    { Constraint.Geq ($1, $3) }
| paterm GTR paterm
    { Constraint.Gtr ($1, $3) }
;

paterm :
| VAR_IDENT
    { Term.createVar $1 "Int" }
| ZERO
    { Term.createFun "0" [] }
| ONE
    { Term.createFun "1" [] }
| PLUS OPENPAR paterm COMMA paterm CLOSEPAR
    { Term.createFun "+" [ $3; $5 ] }
| MINUS OPENPAR paterm CLOSEPAR
    { Term.createFun "-" [ $3 ] }
;

term :
| VAR_IDENT
    { Term.createVar $1 "unspec" }
| PREFIX_IDENT
    { Term.createFun $1 [] }
| PREFIX_IDENT OPENPAR CLOSEPAR
    { Term.createFun $1 [] }
| PREFIX_IDENT OPENPAR term_list CLOSEPAR
    { Term.createFun $1 $3 }
| OPENPAR term CLOSEPAR
    { $2 }
| ZERO
    { Term.createFun "0" [] }
| ONE
    { Term.createFun "1" [] }
| PLUS OPENPAR term COMMA term CLOSEPAR
    { Term.createFun "+" [ $3; $5 ] }
| MINUS OPENPAR term CLOSEPAR
    { Term.createFun "-" [ $3 ] }
;

term_list:
|  term
    { [$1] }
| term COMMA term_list
    { $1 :: $3 }
;

%%
