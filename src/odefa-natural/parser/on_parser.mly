%{
open On_ast;;
module List = BatList;;
exception On_Parse_error of string;;
%}

%token <string> IDENTIFIER
%token <int> INT_LITERAL
%token <bool> BOOL
%token EOF
%token OPEN_BRACE
%token CLOSE_BRACE
%token COMMA
%token BACKTICK
%token OPEN_PAREN
%token CLOSE_PAREN
%token OPEN_BRACKET
%token CLOSE_BRACKET
%token EQUALS
%token ARROW
%token DOT
%token DOUBLE_COLON
%token UNDERSCORE
%token PIPE
%token FUNCTION
%token RECORD
%token WITH
%token LET
%token IN
%token REC
%token IF
%token THEN
%token ELSE
%token AND
%token OR
%token NOT
%token INT
%token BOOL_KEYWORD
%token INPUT
%token MATCH
%token END
%token ASSERT
%token PLUS
%token MINUS
%token ASTERISK
%token SLASH
%token PERCENT
%token LESS
%token LESS_EQUAL
%token GREATER
%token GREATER_EQUAL
%token EQUAL_EQUAL
%token NOT_EQUAL

/*
 * Precedences and associativities.  Lower precedences come first.
 */
%nonassoc prec_let prec_fun   /* Let-ins and functions */
%nonassoc prec_if             /* Conditionals */
%left OR                      /* Or */
%left AND                     /* And */
%right NOT                    /* Not */
/* == <> < <= > >= */
%left EQUAL_EQUAL NOT_EQUAL LESS LESS_EQUAL GREATER GREATER_EQUAL
%right DOUBLE_COLON           /* :: */
%left PLUS MINUS              /* + - */
%left ASTERISK SLASH PERCENT  /* * / % */
%right ASSERT prec_variant    /* Asserts and variants */
%left prec_appl               /* Function application */
%left DOT                     /* Record projection */

%start <On_ast.expr> prog
%start <On_ast.expr option> delim_expr


%%

prog:
  | expr EOF
      { $1 }
  ;

delim_expr:
  | EOF
      { None }
  | expr EOF
      { Some ($1) }
  ;

/* **** Expressions **** */

expr:
  | simple_expr
      { $1 }
  | simple_and_proj_expr expr %prec prec_appl
      { Appl($1, $2) }
  | expr PLUS expr
      { Plus($1, $3) }
  | expr MINUS expr
      { Minus($1, $3) }
  | expr ASTERISK expr
      { Times($1, $3) }
  | expr SLASH expr
      { Divide($1, $3) }
  | expr PERCENT expr
      { Modulus($1, $3) }
  | expr LESS expr
      { LessThan($1, $3) }
  | expr LESS_EQUAL expr
      { Leq($1, $3) }
  | expr GREATER expr
      { GreaterThan($1, $3) }
  | expr GREATER_EQUAL expr
      { Geq($1, $3) }
  | expr AND expr
      { And($1, $3) }
  | expr OR expr
      { Or($1, $3) }
  | NOT expr
    { Not($2) }
  | expr EQUAL_EQUAL expr
      { Equal($1, $3) }
  | expr NOT_EQUAL expr
      { Neq($1, $3) }
  | FUNCTION param_list ARROW expr %prec prec_fun
      { Function($2, $4) }
  | LET REC fun_sig_list IN expr %prec prec_fun
      { LetRecFun($3, $5) }
  | IF expr THEN expr ELSE expr %prec prec_if
      { If($2, $4, $6) }
  | LET ident_decl EQUALS expr IN expr %prec prec_let
      { Let($2, $4, $6) }
  | LET fun_sig IN expr %prec prec_fun
      { LetFun($2, $4)}
  | expr DOT label
      { RecordProj($1, $3) }
  | expr DOUBLE_COLON expr
      { ListCons($1, $3) }
  | MATCH expr WITH PIPE? match_expr_list END
      { Match($2, $5) }
  | ASSERT expr
      { Assert($2) }
  | variant_label expr %prec prec_variant
      { VariantExpr($1, $2) }
;

/* let foo x = ... */
fun_sig:
  | ident_decl param_list EQUALS expr
      { Funsig ($1, $2, $4) }

/* let rec foo x y = ... with bar a b = ... in ... */
fun_sig_list:
  | fun_sig { [$1] }
  | fun_sig WITH fun_sig_list { $1 :: $3 }

/* In a simple_expr, only primitives, vars, records, and lists do not need
   surrounding parentheses. */
simple_expr:
  | INT_LITERAL
      { Int $1 }
  | BOOL
      { Bool $1 }
  | INPUT
      { Input }
  | ident_usage
      { $1 }
  | OPEN_BRACE record_body CLOSE_BRACE
      { Record $2 }
  | OPEN_BRACE CLOSE_BRACE
      { Record (Ident_map.empty) }
  | OPEN_BRACKET list_body CLOSE_BRACKET
      { List $2 }
  | OPEN_BRACKET CLOSE_BRACKET
      { List [] }
  | OPEN_PAREN expr CLOSE_PAREN
      { $2 }
;

/* Hardcode the two expressions with precedence above function application,
   to avoid shift-reduce errors. */
simple_and_proj_expr:
  | simple_expr { $1 }
  | expr DOT label { RecordProj($1, $3) }
;

/* **** Idents + labels **** */

param_list:
  | ident_decl param_list { $1 :: $2 }
  | ident_decl { [$1] }
;

label:
  | IDENTIFIER { Label $1 }
;

ident_usage:
  | ident_decl { Var $1 }
;

ident_decl:
  | IDENTIFIER { Ident $1 }
;

/* **** Records, lists, and variants **** */

/* {x = 1, y = 2, z = 3} */
record_body:
  | label EQUALS expr
      { let (Label k) = $1 in
        let key = Ident k in
        Ident_map.singleton key $3 }
  | label EQUALS expr COMMA record_body
      { let (Label k) = $1 in
        let key = Ident k in
        let old_map = $5 in
        let dup_check = Ident_map.mem key old_map in
        if dup_check then
          raise (On_Parse_error "Duplicate label names in record!")
        else
          let new_map = Ident_map.add key $3 old_map in
          new_map
      }
;

/* [1, 2, true] (Unlike ocaml, natodefa lists can be heterogenous) */
list_body:
  | expr COMMA list_body { $1 :: $3 }
  | expr { [$1] }
;

/* `Variant 2 */
variant_label:
  | BACKTICK IDENTIFIER { Variant_label $2 }

/* **** Pattern matching **** */

match_expr_list:
  | match_expr PIPE match_expr_list
      { $1 :: $3 }
  | match_expr
      { [$1] }
;

match_expr:
  | pattern ARROW expr
      { ($1, $3) }

pattern:
  | UNDERSCORE { AnyPat }
  | INT { IntPat }
  | BOOL_KEYWORD { BoolPat }
  | FUNCTION { FunPat }
  | IDENTIFIER { VarPat(Ident($1)) }
  | variant_label ident_decl { VariantPat($1, $2) }
  | variant_label OPEN_PAREN ident_decl CLOSE_PAREN { VariantPat($1, $3) }
  | OPEN_BRACE rec_pattern_body CLOSE_BRACE { RecPat $2 }
  | OPEN_BRACE CLOSE_BRACE { RecPat (Ident_map.empty) }
  | RECORD { RecPat (Ident_map.empty) }
  | OPEN_BRACKET CLOSE_BRACKET { EmptyLstPat }
  | ident_decl DOUBLE_COLON ident_decl { LstDestructPat($1, $3) }
  | OPEN_PAREN pattern CLOSE_PAREN { $2 }
;

rec_pattern_body:
  | label EQUALS ident_decl
      { let (Label k) = $1 in
        let key = Ident k in
        Ident_map.singleton key (Some $3) }
  | label EQUALS ident_decl COMMA rec_pattern_body
      { let (Label k) = $1 in
        let key = Ident k in
        let old_map = $5 in
        let dup_check = Ident_map.mem key old_map in
        if dup_check then
          raise (On_Parse_error "Duplicate label names in record!")
        else
          let new_map = Ident_map.add key (Some $3) old_map in
          new_map
      }
;