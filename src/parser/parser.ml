(**
   A front-end for the parser library.
*)

open Batteries;;

open Lexing;;

exception Parse_error of exn * int * int * string;;

let handle_parse_error buf f =
  try
    f ()
  with
  | exn ->
    let curr = buf.lex_curr_p in
    let line = curr.pos_lnum in
    let column = curr.pos_cnum - curr.pos_bol in
    let tok = lexeme buf in
    raise @@ Parse_error(exn,line,column,tok)
;;

let parse_expressions (input : IO.input) =
  let buf = Lexing.from_channel input in
  let read_expr () =
    handle_parse_error buf @@ fun () ->
    Generated_parser.delim_expr Generated_lexer.token buf
  in
  LazyList.from_while read_expr
;;

let parse_program (input : IO.input) =
  let buf = Lexing.from_channel input in
  handle_parse_error buf @@ fun () ->
  Generated_parser.prog Generated_lexer.token buf
;;

(** Parse a string as an odefa expression. *)
let parse_expression_string (expr_str : string) =
  let buf = Lexing.from_string expr_str in
  let read_expr () =
    handle_parse_error buf @@ fun () ->
    Generated_parser.delim_expr Generated_lexer.token buf
  in
  LazyList.to_list @@ LazyList.from_while read_expr
;;

(** Parse a string containing a single odefa clause. *)
let parse_clause_string (clause_str : string) =
  let expr_lst = parse_expression_string clause_str in
  match expr_lst with
  | [expr] ->
    begin
      let Odefa_ast.Ast.Expr clist = expr in
      match clist with
      | [clause] -> clause
      | [] ->
        raise @@ Invalid_argument "expression does not contain a clause"
      | _ ->
        raise @@ Invalid_argument "expression contains more than one clause"
    end
  | _ -> raise @@ Invalid_argument "string has more than one expression"
;;