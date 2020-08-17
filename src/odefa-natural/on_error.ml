open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_symbolic_interpreter;;

(* **** Errors in natodefa **** *)

type error_binop = {
  err_binop_left_aliases : On_ast.ident list;
  err_binop_right_aliases : On_ast.ident list;
  err_binop_left_value : On_ast.expr;
  err_binop_right_value : On_ast.expr;
  err_binop_constraint : On_ast.expr;
  err_binop_expr : On_ast.expr;
}
;;

type error_match = {
  err_match_aliases : On_ast.ident list;
  err_match_expr : On_ast.expr;
  err_match_value : On_ast.expr;
  err_match_expected : On_ast.type_sig;
  err_match_actual : On_ast.type_sig;
}

type error_value = {
  err_value_aliases : On_ast.ident list;
  err_value_val : On_ast.expr;
  err_value_expr : On_ast.expr;
}

type error =
  | Error_binop of error_binop
  | Error_match of error_match
  | Error_value of error_value
;;

(* **** Error pretty-printers **** *)

let pp_alias_list formatter aliases =
  Pp_utils.pp_concat_sep
    " ="
    (fun formatter x -> On_ast_pp.pp_ident formatter x)
    formatter
    (List.enum aliases)
;;

let pp_error_binop formatter err =
  let open On_ast_pp in
  let pp_left_value formatter (l_aliases, l_value) =
    if (List.length l_aliases) > 0 then
      Format.fprintf formatter
        "@[* Left Value  : @[%a@ =@ %a@]@]@,"
        pp_alias_list l_aliases
        pp_expr l_value
    else
      Format.pp_print_string formatter ""
  in
  let pp_right_value formatter (r_aliases, r_value) =
    if (List.length r_aliases) > 0 then
      Format.fprintf formatter
        "@[* Right Value : @[%a@ =@ %a@]@]@,"
        pp_alias_list r_aliases
        pp_expr r_value
    else
      Format.pp_print_string formatter ""
  in
  let pp_constraint formatter constraint_expr =
    Format.fprintf formatter
      "@[* Constraint  : @[%a@]@]@,"
      pp_expr constraint_expr
  in
  let pp_expression formatter binop_expr =
    Format.fprintf formatter
      "@[* Expression  : @[%a@]@]"
      pp_expr binop_expr
  in
  Format.fprintf formatter
    "@[<v 0>%a%a%a%a@]"
    pp_left_value (err.err_binop_left_aliases, err.err_binop_left_value)
    pp_right_value (err.err_binop_right_aliases, err.err_binop_right_value)
    pp_constraint err.err_binop_constraint
    pp_expression err.err_binop_expr
;;

let pp_error_match formatter err =
  let open On_ast_pp in
  let pp_value formatter (aliases, value) =
    if (List.length aliases) > 0 then
      Format.fprintf formatter 
        "@[* Value       : @[%a@ =@ %a@]@]@,"
        pp_alias_list aliases
        pp_expr value
    else
      Format.fprintf formatter
        "@[* Value       : @[%a@]@]@,"
        pp_expr value
  in
  let pp_expression formatter match_expr =
    Format.fprintf formatter
      "@[* Expression  : @[%a@]@]@,"
      pp_expr match_expr
  in
  let pp_expected formatter expected_type =
    Format.fprintf formatter
      "@[* Expected    : @[%a@]@]@,"
      pp_on_type expected_type
  in
  let pp_actual formatter actual_type =
    Format.fprintf formatter
      "@[* Actual      : @[%a@]@]"
      pp_on_type actual_type
  in
  Format.fprintf formatter
    "@[<v 0>%a%a%a%a@]"
    pp_value (err.err_match_aliases, err.err_match_value)
    pp_expression err.err_match_expr
    pp_expected err.err_match_expected
    pp_actual err.err_match_actual
;;

let pp_error_value formatter err =
  let open On_ast_pp in
  let pp_value formatter (aliases, value) =
    if (List.length aliases) > 0 then
      Format.fprintf formatter 
        "@[* Value       : @[%a@ =@ %a@]@]@,"
        pp_alias_list aliases
        pp_expr value
    else
      Format.fprintf formatter
        "@[* Value       : @[%a@]@,"
        pp_expr value
  in
  let pp_expression formatter value_expr =
    Format.fprintf formatter
      "@[* Expression  : @[%a@]@]"
      pp_expr value_expr
  in
  Format.fprintf formatter
    "@[<v 0>%a%a@]"
    pp_value (err.err_value_aliases, err.err_value_val)
    pp_expression err.err_value_expr
;;

let pp formatter error =
  match error with
  | Error_binop err -> pp_error_binop formatter err
  | Error_match err -> pp_error_match formatter err
  | Error_value err -> pp_error_value formatter err
;;

let show = Pp_utils.pp_to_string pp;;

(* **** Error list submodule **** *)

module type Error_list = sig
  type t;;
  val wrap : error list -> t;;
  val empty : t;;
  val is_empty : t -> bool;;
  val count : t -> int;;
  val to_string : t -> string;;
end;;

module Error_list : Error_list = struct
  type t = error list
  ;;

  let wrap error_list = error_list;;

  let empty = [];;

  let is_empty = List.is_empty;;

  let count error_list = List.length error_list;;

  let to_string error_list =
    let string_list = List.map show error_list in
    String.join "\n---------------\n" string_list
  ;;
end
;;

let odefa_to_on_binop
    (odefa_binop : Ast.binary_operator)
  : (On_ast.expr -> On_ast.expr -> On_ast.expr) =
  match odefa_binop with
  | Ast.Binary_operator_plus -> (fun e1 e2 -> On_ast.Plus (e1, e2))
  | Ast.Binary_operator_minus -> (fun e1 e2 -> On_ast.Minus (e1, e2))
  | Ast.Binary_operator_times -> (fun e1 e2 -> On_ast.Times (e1, e2))
  | Ast.Binary_operator_divide -> (fun e1 e2 -> On_ast.Divide (e1, e2))
  | Ast.Binary_operator_modulus -> (fun e1 e2 -> On_ast.Modulus (e1, e2))
  | Ast.Binary_operator_equal_to -> (fun e1 e2 -> On_ast.Equal (e1, e2))
  | Ast.Binary_operator_not_equal_to -> (fun e1 e2 -> On_ast.Neq (e1, e2))
  | Ast.Binary_operator_less_than -> (fun e1 e2 -> On_ast.LessThan (e1, e2))
  | Ast.Binary_operator_less_than_or_equal_to -> (fun e1 e2 -> On_ast.Leq (e1, e2))
  | Ast.Binary_operator_and -> (fun e1 e2 -> On_ast.And (e1, e2))
  | Ast.Binary_operator_or -> (fun e1 e2 -> On_ast.Or (e1, e2))
  | Ast.Binary_operator_xor -> (fun e1 e2 -> On_ast.Neq (e1, e2))
  | Ast.Binary_operator_xnor -> (fun e1 e2 -> On_ast.Equal (e1, e2))
;;

let odefa_to_natodefa_error
    (odefa_on_maps : On_to_odefa_maps.t)
    (odefa_err : Error.error)
  : error =
  (* Helper functions *)
  let odefa_to_on_expr =
    On_to_odefa_maps.get_natodefa_equivalent_expr odefa_on_maps
  in
  let odefa_to_on_aliases (aliases : Ast.ident list) : On_ast.ident list =
    List.filter_map
      (fun alias ->
        match odefa_to_on_expr alias with
        | (On_ast.Var ident) -> Some ident
        | _ -> None
      )
      aliases
  in
  let odefa_to_on_value (aliases : Ast.ident list) : On_ast.expr =
    let last_var =
      try
        List.last aliases
      with Invalid_argument _ ->
        raise @@ Jhupllib.Utils.Invariant_failure "Can't have empty alias list!"
    in
    odefa_to_on_expr last_var
  in
  let odefa_to_on_type (typ : Ast.type_sig) : On_ast.type_sig =
    match typ with
    | Ast.Top_type -> TopType
    | Ast.Int_type -> IntType
    | Ast.Bool_type -> BoolType
    | Ast.Fun_type -> FunType
    | Ast.Rec_type lbls ->
      On_to_odefa_maps.get_type_from_idents odefa_on_maps lbls
    | Ast.Bottom_type ->
      raise @@ Jhupllib.Utils.Invariant_failure
        (Printf.sprintf "Bottom type not in natodefa")
  in
  (* Odefa to natodefa *)
  match odefa_err with
  | Error.Error_binop err ->
    begin
      let l_aliases = err.err_binop_left_aliases in
      let r_aliases = err.err_binop_right_aliases in
      let l_aliases_on = odefa_to_on_aliases l_aliases in
      let r_aliases_on = odefa_to_on_aliases r_aliases in
      let op = err.err_binop_operation in
      let l_value = odefa_to_on_value l_aliases in
      let r_value = odefa_to_on_value r_aliases in
      let (Clause (Var (v, _), _)) = err.err_binop_clause in
      let constraint_expr =
        let binop_fn = odefa_to_on_binop op in
        let left_expr =
          if (List.length l_aliases_on) > 0 then
            On_ast.Var (List.hd l_aliases_on)
          else
            l_value
        in
        let right_expr =
          if (List.length r_aliases_on) > 0 then
            On_ast.Var (List.hd r_aliases_on)
          else
            r_value
        in
        binop_fn left_expr right_expr
      in
      Error_binop {
        err_binop_left_aliases = l_aliases_on;
        err_binop_right_aliases = r_aliases_on;
        err_binop_left_value = l_value;
        err_binop_right_value = r_value;
        err_binop_constraint = constraint_expr;
        err_binop_expr = odefa_to_on_expr v;
      }
    end
  | Error.Error_match err ->
    begin
      let aliases = err.err_match_aliases in
      let (Clause (Var (v, _), _)) = err.err_match_clause in
      Error_match {
        err_match_aliases = odefa_to_on_aliases aliases;
        err_match_expr = odefa_to_on_expr v;
        err_match_value = odefa_to_on_value aliases;
        err_match_expected = odefa_to_on_type err.err_match_expected_type;
        err_match_actual = odefa_to_on_type err.err_match_actual_type;
      }
    end
  | Error.Error_value err ->
    begin
      let aliases = err.err_value_aliases in
      let (Clause (Var (v, _), _)) = err.err_value_clause in
      Error_value {
        err_value_aliases = odefa_to_on_aliases aliases;
        err_value_val = odefa_to_on_value aliases;
        err_value_expr = odefa_to_on_expr v;
      }
    end
;;

(* **** Parse error from string **** *)

exception Parse_failure of string;;

let _parse_aliases alias_str =
  alias_str
  |> Str.split (Str.regexp "[ ]+=[ ]+")
  |> List.map (fun str -> On_ast.Ident str)
;;

let _parse_expr expr_str =
  let expr_lst =
    try
      On_parse.parse_expression_string expr_str
    with On_parse.Parse_error _ ->
      raise @@ Parse_failure (Printf.sprintf "Cannot parse clause %s" expr_str)
  in
  match expr_lst with
  | [expr] -> expr
  | [] -> raise @@ Parse_failure "Missing expression"
  | _ -> raise @@ Parse_failure "More than one expression"
;;

let _parse_type_sig type_str =
  let open On_ast in
  match type_str with
  | "int" | "integer" | "Integer" -> IntType
  | "bool" | "boolean" | "Boolean" -> BoolType
  | "fun" | "function" | "Function" -> FunType
  | "rec" | "record" | "Record" -> RecType (Ident_set.empty)
  | "list" | "List" -> ListType
  | _ ->
    let is_rec_str =
      Str.string_match (Str.regexp "{.*}") type_str 0
    in
    let is_variant_str =
      Str.string_match (Str.regexp "`.*") type_str 0
    in
    if is_rec_str then begin
      let lbl_set =
        type_str
        |> String.lchop
        |> String.rchop
        |> Str.split (Str.regexp ",")
        |> List.map String.trim
        |> List.map (fun lbl -> Ident lbl)
        |> Ident_set.of_list
      in
      RecType lbl_set
    end else if is_variant_str then begin
      VariantType (Variant_label (String.lchop type_str))
    end else begin
      raise @@ Parse_failure (Printf.sprintf "Cannot parse type %s" type_str)
    end
;;

let parse_error error_str =
  let args_list =
    error_str
    |> String.trim
    |> String.lchop
    |> String.rchop
    |> Str.split (Str.regexp "\[ ]*\"")
  in
  match args_list with
  | [err_str; l_alias_str; l_val_str; r_alias_str; r_val_str; op_str; expr_str]
    when String.equal err_str "binop" ->
    Error_binop {
      err_binop_left_aliases = _parse_aliases l_alias_str;
      err_binop_right_aliases = _parse_aliases r_alias_str;
      err_binop_left_value = _parse_expr l_val_str;
      err_binop_right_value = _parse_expr r_val_str;
      err_binop_constraint = _parse_expr op_str;
      err_binop_expr = _parse_expr expr_str;
    }
  | [err_str; alias_str; val_str; expr_str; expected_str; actual_str]
    when String.equal err_str "match" ->
    Error_match {
      err_match_aliases = _parse_aliases alias_str;
      err_match_value = _parse_expr val_str;
      err_match_expr = _parse_expr expr_str;
      err_match_expected = _parse_type_sig expected_str;
      err_match_actual = _parse_type_sig actual_str;
    }
  | [err_str; alias_str; val_str; expr_str]
    when String.equal err_str "value" ->
    Error_value {
      err_value_aliases = _parse_aliases alias_str;
      err_value_val = _parse_expr val_str;
      err_value_expr = _parse_expr expr_str;
    }
  | _ -> raise @@ Parse_failure "Missing or spurious arguments"