/*
  Parser for TRSs.

  @author Stephan Falke
  @version $Id: trs_parser.mly,v 1.9 2009/04/07 19:23:49 spf Exp $
*/

%{

  let inSorts sorts s = List.mem s sorts

  let rec getSignature (sorts: string list) (decls: (string * string list * string) list) signa =
    match decls with
      | [] -> signa
      | (x::xs) -> match x with (f, ss, goal) ->
                     if List.exists (fun s -> not (inSorts sorts s)) (goal::ss) then
                       let s = List.find (fun s -> not (inSorts sorts s)) (goal::ss) in
                         raise (Signature.UnknownSort (f, s))
                     else
                       getSignature sorts xs (Signature.addFun signa (f, List.length ss, ss, goal))

  let rec testOk signa (lr, line) =
    Trs_parser_aux.currline := line;
    match lr with
      | Rule.Rule (l, r, c) ->
          if (Term.isVariable l) then
            raise (Rule.NoRule (Rule.toString lr))
          else if (hasBuiltinRoot l) then
            raise (Trs_parser_aux.BuiltinRootException line)
          (* else if (List.exists isPlusMinus (Term.getFuns l)) then
            raise (Trs_parser_aux.BuiltinException line) *)
          else
            TermParse.checkTerm signa l;
            TermParse.checkTerm signa r;
            let lvars = Term.getVars l
            and rvars = Term.getVars r
            and cvars = Util.remdup (List.concat (List.map Constraint.getVars c))
            and ls = Term.getSort signa l
            and rs = Term.getSort signa r
            and lsa = TermParse.sortAssumption signa l
            and rsa = TermParse.sortAssumption signa r in
              if List.exists (fun x -> not (List.mem x lvars)) (rvars @ cvars) then
                raise (Rule.VariableConflict (Rule.toString lr))
              else
                if (rs = "unspec" && (TermParse.getSortFor lsa r) <> ls) || (rs <> "unspec" && ls <> rs) then
                  raise (Rule.SortConflictRule (Rule.toString lr))
                else
                  TermParse.containsAssumption lsa rsa;
                  TermParse.containsAssumption lsa (getCondAssumption c)
  and getCondAssumption c =
    let vars = Util.remdup (List.concat (List.map Constraint.getVars c)) in
      List.map (fun x -> (x, "Int")) vars
  and hasBuiltinRoot t =
    let f = Term.getTopSymbol t in
      f = "0" || f = "1" || f = "+" || f = "-"
  and isPlusMinus f =
    f = "+" || f = "-"

  let rec checkTrs signa rules =
    match rules with
      | [] -> ()
      | (x::xs) -> testOk signa x; checkTrs signa xs

  let rec insertSorts signa rules =
    match rules with
      | [] -> []
      | (x::xs) -> (insertSortsRule signa x)::(insertSorts signa xs)
  and insertSortsRule signa (Rule.Rule (l, r, c)) =
    let lsa = TermParse.sortAssumption signa l in
      (Rule.Rule (TermParse.getSortedTerm lsa l, TermParse.getSortedTerm lsa r, insertSortsCond lsa c))
  and insertSortsCond ass c =
    List.map (insertSortsCondAux ass) c
  and insertSortsCondAux ass c =
    match c with
      | Constraint.Eq (s, t) -> Constraint.Eq (TermParse.getSortedTerm ass s, TermParse.getSortedTerm ass t)
      | Constraint.Geq (s, t) -> Constraint.Geq (TermParse.getSortedTerm ass s, TermParse.getSortedTerm ass t)
      | Constraint.Gtr (s, t) -> Constraint.Gtr (TermParse.getSortedTerm ass s, TermParse.getSortedTerm ass t)

  let rec makeTrs ((sorts, decls, rules): (string list * (string * string list * string) list * (Rule.rule * int) list)) =
    let signa = getSignature ("Int"::sorts) ((getBuiltin ()) @ decls) (Signature.createEmpty ()) in
      checkTrs signa rules;
      let srules = insertSorts signa (List.map fst rules) in
        Trs.Trs (signa, srules, Ruletrie.createRuleTrie srules)
  and getBuiltin () =
    [ ("0", [], "Int"); ("1", [], "Int"); ("+", ["Int"; "Int"], "Int"); ("-", ["Int"], "Int") ]
%}

%token <string> PREFIX_IDENT SORT_IDENT
%token <string> VAR_IDENT
%token <int> TO
%token COMMA OPENPAR CLOSEPAR OPENSQ CLOSESQ EOL EOF SORT COL EQ GEQ GTR CONJ PLUS MINUS ZERO ONE INT

%left INFIX_IDENT
%nonassoc PREFIX_IDENT

%start trs_eol
%type <Trs.trs> trs_eol

%%

trs_eol :
| sorts decls rules
    { makeTrs ($1, $2, $3) }
| decls rules
    { makeTrs ([], $1, $2) }
;

sorts :
| sort eols
    { [$1] }
| sort eols sorts
    { ($1::$3) }
;

sort :
| SORT SORT_IDENT
    { $2 }
;

decls :
| decl eols
    { [$1] }
| decl eols decls
    { ($1::$3) }
;

decl :
| OPENSQ PREFIX_IDENT COL TO SORT_IDENT CLOSESQ
    { ($2, [], $5) }
| OPENSQ PREFIX_IDENT COL TO INT CLOSESQ
    { ($2, [], "Int") }
| OPENSQ PREFIX_IDENT COL fromsorts TO SORT_IDENT CLOSESQ
    { ($2, $4, $6) }
| OPENSQ PREFIX_IDENT COL fromsorts TO INT CLOSESQ
    { ($2, $4, "Int") }
;

fromsorts :
| SORT_IDENT
    { [$1] }
| INT
    { ["Int"] }
| SORT_IDENT COMMA fromsorts
    { ($1::$3) }
| INT COMMA fromsorts
    { ("Int"::$3) }
;

rules :
| EOF
    { [] }
| rule eols rules
    { ($1::$3) }
;

eols:
| EOL {}
| EOL eols {}
;

rule :
| term TO term
    { (Rule.Rule ($1, $3, []), $2) }
| term TO term OPENSQ condlist CLOSESQ
    { (Rule.Rule ($1, $3, $5), $2) }
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
