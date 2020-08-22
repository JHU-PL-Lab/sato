open Jhupllib;;

open Batteries;;
open Odefa_ast;;

open Error_types;;

exception Parse_failure of string;;

type t = error;;

let eq = equal_error;;

let pp_alias_list formatter aliases =
  Pp_utils.pp_concat_sep
    "="
    (fun formatter x -> Ast_pp.pp_ident formatter x)
    formatter
    (List.enum aliases)
;;

let pp_error_binop formatter err =
  let open Ast_pp in
  let pp_left_value formatter err =
    let l_aliases = err.err_binop_left_aliases in
    let l_value = err.err_binop_left_val in
    if (List.length l_aliases) > 0 then
      Format.fprintf formatter
        "@[* Left Value  : @[%a@ =@ %a@]@]@,"
        pp_alias_list l_aliases
        pp_clause_body l_value
    else
      Format.pp_print_string formatter ""
  in
  let pp_right_value formatter err =
    let r_aliases = err.err_binop_right_aliases in
    let r_value = err.err_binop_right_val in
    if (List.length r_aliases) > 0 then
      Format.fprintf formatter
        "@[* Right Value : @[%a@ =@ %a@]@]@,"
        pp_alias_list r_aliases
        pp_clause_body r_value
    else
      Format.pp_print_string formatter ""
  in
  let pp_constraint formatter err =
    let l_value = err.err_binop_left_val in
    let r_value = err.err_binop_right_val in
    let op = err.err_binop_operation in
    let l_alias_opt = List.Exceptionless.hd err.err_binop_left_aliases in
    let r_alias_opt = List.Exceptionless.hd err.err_binop_right_aliases in
    match (l_alias_opt, r_alias_opt) with
    | (Some l_alias, Some r_alias) ->
      Format.fprintf formatter
        "@[* Constraint  : @[%a@ %a@ %a@]@]@,"
        pp_ident l_alias
        pp_binary_operator op
        pp_ident r_alias
    | (None, Some r_alias) ->
      Format.fprintf formatter
        "@[* Constraint  : @[%a@ %a@ %a@]@]@,"
        pp_clause_body l_value
        pp_binary_operator op
        pp_ident r_alias
    | (Some l_alias, None) ->
      Format.fprintf formatter
        "@[* Constraint  : @[%a@ %a@ %a@]@]@,"
        pp_ident l_alias
        pp_binary_operator op
        pp_clause_body r_value
    | (None, None) ->
      Format.fprintf formatter
        "@[* Constraint  : @[%a@ %a@ %a@]@]@,"
        pp_clause_body l_value
        pp_binary_operator op
        pp_clause_body r_value
  in
  let pp_clause formatter err =
    Format.fprintf formatter
      "@[* Clause      : @[%a@]@]"
      pp_clause err.err_binop_clause
  in
  Format.fprintf formatter
    "@[<v 0>%a%a%a%a@]"
    pp_left_value err
    pp_right_value err
    pp_constraint err
    pp_clause err
;;

let pp_error_match formatter err =
  let open Ast_pp in
  let pp_value formatter err =
    let aliases = err.err_match_aliases in
    let value = err.err_match_value in
    if not @@ List.is_empty aliases then
      Format.fprintf formatter 
        "@[* Value    : @[%a@ =@ %a@]@]@,"
        pp_alias_list aliases
        pp_clause_body value
    else
      Format.fprintf formatter 
        "@[* Value    : @[%a@]@]@,"
        pp_clause_body value
  in
  let pp_clause formatter err =
    Format.fprintf formatter
      "@[* Clause   : @[%a@]@]@,"
      pp_clause err.err_match_clause
  in
  let pp_expected formatter err =
    Format.fprintf formatter
      "@[* Expected : @[%a@]@]@,"
      pp_type_sig err.err_match_expected_type
  in
  let pp_actual formatter err =
    Format.fprintf formatter
      "@[* Actual   : @[%a@]@]"
      pp_type_sig err.err_match_actual_type
  in
  Format.fprintf formatter
    "@[<v 0>%a%a%a%a@]"
    pp_value err
    pp_clause err
    pp_expected err
    pp_actual err
;;

let pp_error_value formatter err =
  let open Ast_pp in
  let pp_value formatter err =
    let aliases = err.err_value_aliases in
    let value = err.err_value_val in
    if not @@ List.is_empty aliases then
      Format.fprintf formatter 
        "@[* Value    : @[%a@ =@ %a@]@]@,"
        pp_alias_list aliases
        pp_clause_body value
    else
      Format.fprintf formatter 
        "@[* Value    : @[%a@]@]@,"
        pp_clause_body value
  in
  let pp_clause formatter err =
    Format.fprintf formatter
      "@[* Clause   : @[%a@]@]"
      pp_clause err.err_value_clause
  in
  Format.fprintf formatter
    "@[<v 0>%a%a@]"
    pp_value err
    pp_clause err
;;

let pp formatter error =
  match error with
  | Error_binop err -> pp_error_binop formatter err
  | Error_match err -> pp_error_match formatter err
  | Error_value err -> pp_error_value formatter err
;;

let show = Pp_utils.pp_to_string pp;;

(* **** String to error parsing **** *)

let _parse_aliases alias_str =
  alias_str
  |> Str.split (Str.regexp "[ ]+=[ ]+") 
  |> List.map (fun str -> Ast.Ident str)
;;

let _parse_clause clause_str =
  let expr_lst =
    try
      Odefa_parser.Parser.parse_expression_string clause_str
    with Odefa_parser.Parser.Parse_error (_, _, _, _) ->
      raise @@ Parse_failure ("cannot parse clause " ^ clause_str)
  in
  match expr_lst with
  | [expr] ->
    begin
      let Expr clist = expr in
      match clist with
      | [clause] -> clause
      | _ -> raise @@ Parse_failure "expression contains more than one clause"
    end
  | _ -> raise @@ Parse_failure "more than one expression"
;;

let _parse_type type_str =
  match type_str with
  | "int" | "integer" -> Ast.Int_type
  | "bool" | "boolean" -> Ast.Bool_type
  | "fun" | "function" -> Ast.Fun_type
  | _ ->
    let is_rec_str =
      Str.string_match (Str.regexp "{.*}") type_str 0 in
    if is_rec_str then begin
      let lbl_set =
        type_str
        |> String.lchop
        |> String.rchop
        |> Str.split (Str.regexp ",")
        |> List.map String.trim
        |> List.map (fun lbl -> Ast.Ident lbl)
        |> Ast.Ident_set.of_list
      in
      Rec_type lbl_set
    end else begin
      raise @@ Parse_failure "cannot parse type"
    end
;;

let _parse_op op_str =
  let open Ast in
  match op_str with
  | "+" -> Binary_operator_plus
  | "-" -> Binary_operator_minus
  | "*" -> Binary_operator_times
  | "/" -> Binary_operator_divide
  | "%" -> Binary_operator_modulus
  | "==" -> Binary_operator_equal_to
  | "<>" -> Binary_operator_not_equal_to
  | "<" -> Binary_operator_less_than
  | "<=" -> Binary_operator_less_than_or_equal_to
  | "and" -> Binary_operator_and
  | "or" -> Binary_operator_or
  | "xor" -> Binary_operator_xor
  | _ ->
    raise @@ Parse_failure "cannot parse operation"
;;

let parse error_str =
  let args_list =
    error_str
    |> String.trim
    |> String.lchop
    |> String.rchop
    |> Str.split (Str.regexp "\"[ ]*\"")
  in
  match args_list with
  | [error_str; l_alias_str; l_val_str; r_alias_str; r_val_str; op_str; clause_str]
    when String.equal error_str "binop" ->
    begin
      let (Clause (_, l_body)) = _parse_clause @@ "dummy = " ^ l_val_str in
      let (Clause (_, r_body)) = _parse_clause @@ "dummy = " ^ r_val_str in
      Error_binop {
        err_binop_clause = _parse_clause clause_str;
        err_binop_left_val = l_body;
        err_binop_right_val = r_body;
        err_binop_left_aliases = _parse_aliases l_alias_str;
        err_binop_right_aliases = _parse_aliases r_alias_str;
        err_binop_operation = _parse_op op_str;
      }
    end
  | [error_str; alias_str; val_str; clause_str; expected_str; actual_str]
    when String.equal error_str "match" ->
    begin
      let (Clause (_, val_body)) = _parse_clause @@ "dummy = " ^ val_str in
      Error_match {
        err_match_aliases = _parse_aliases alias_str;
        err_match_value = val_body;
        err_match_clause = _parse_clause clause_str;
        err_match_expected_type = _parse_type expected_str;
        err_match_actual_type = _parse_type actual_str;
      }
    end
  | [error_str; alias_str; val_str; clause_str]
    when String.equal error_str "value" ->
    begin
      let (Clause (_, val_body)) = _parse_clause @@ "dummy = " ^ val_str in
      Error_value {
        err_value_aliases = _parse_aliases alias_str;
        err_value_val = val_body;
        err_value_clause = _parse_clause clause_str;
      }
    end
  | _ -> raise @@ Parse_failure "Missing or spurious arguments"
;;