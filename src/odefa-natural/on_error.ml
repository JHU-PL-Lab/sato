open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_symbolic_interpreter;;

(* **** Types in natodefa **** *)

type on_type =
  | TopType
  | IntType
  | BoolType
  | FunType
  | RecType of On_ast.Ident_set.t
  | ListType
  | VariantType of On_ast.variant_label
;;

let pp_on_type formatter on_type =
  let open On_ast_pp in
  match on_type with
  | TopType -> Format.pp_print_string formatter "any"
  | IntType -> Format.pp_print_string formatter "integer"
  | BoolType -> Format.pp_print_string formatter "boolean"
  | FunType -> Format.pp_print_string formatter "function"
  | ListType -> Format.pp_print_string formatter "list"
  | RecType lbls -> pp_ident_set formatter lbls
  | VariantType lbl -> Format.fprintf formatter "`%a" pp_variant_label lbl
;;

let show_on_type = Pp_utils.pp_to_string pp_on_type;;

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
  err_match_expected : on_type;
  err_match_actual : on_type;
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

  let error_to_string error =
    let open On_ast_pp in
    (* Helper functions *)
    let alias_str aliases =
      String.join " = "
        @@ List.map show_ident aliases
    in
    (* String creation *)
    match error with
    | Error_binop err ->
      let l_aliases = err.err_binop_left_aliases in
      let r_aliases = err.err_binop_right_aliases in
      let l_value = err.err_binop_left_value in
      let r_value = err.err_binop_right_value in
      let l_val_str =
        if (List.length l_aliases) > 0 then
          "* Left Value  : " ^ (alias_str l_aliases) ^
                           " = " ^ (show_expr l_value) ^ "\n"
        else
          ""
      in
      let r_val_str =
        if (List.length r_aliases) > 0 then
          "* Right Value : " ^ (alias_str r_aliases) ^
                           " = " ^ (show_expr r_value) ^ "\n"
        else
          ""
      in
      l_val_str ^ r_val_str ^
      "* Constraint  : " ^ (show_expr err.err_binop_constraint) ^ "\n" ^
      "* Expression  : " ^ (show_expr err.err_binop_expr)
    | Error_match err ->
      let aliases = err.err_match_aliases in
      let value = err.err_match_value in
      let val_str =
        if (List.length aliases) > 0 then
          (alias_str aliases) ^ " = " ^ (show_expr value)
        else
          (show_expr value)
      in
      "* Value      : " ^ val_str ^ "\n" ^
      "* Expression : " ^ (show_expr err.err_match_expr) ^ "\n" ^
      "* Expected   : " ^ (show_on_type err.err_match_expected) ^ "\n" ^
      "* Actual     : " ^ (show_on_type err.err_match_actual)
    | Error_value err ->
      let aliases = err.err_value_aliases in
      let value = err.err_value_val in
      let val_str =
        if (List.length aliases) > 0 then
          (alias_str aliases) ^ " = " ^ (show_expr value)
        else
          (show_expr value)
      in
      "* Value      : " ^ val_str ^ "\n" ^
      "* Expression : " ^ (show_expr err.err_value_expr)
  ;;

  let wrap error_list = error_list;;

  let empty = [];;

  let is_empty = List.is_empty;;

  let count error_list = List.length error_list;;

  let to_string error_list =
    let string_list = List.map error_to_string error_list in
    String.join "\n---------------\n" string_list
  ;;
end
;;

let odefa_to_on_type
    (odefa_type : Ast.type_sig)
  : on_type =
  match odefa_type with
  | Ast.Top_type -> TopType
  | Ast.Int_type -> IntType
  | Ast.Bool_type -> BoolType
  | Ast.Fun_type -> FunType
  | Ast.Rec_type lbls ->
    let lbls' =
      lbls
      |> Ast.Ident_set.enum
      |> Enum.map (fun (Ast.Ident id) -> On_ast.Ident id)
      |> On_ast.Ident_set.of_enum
    in
    RecType lbls'
  | Ast.Bottom_type ->
    raise @@ Jhupllib.Utils.Invariant_failure
      (Printf.sprintf "Bottom type not in natodefa")
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
    (odefa_on_maps : On_to_odefa_types.Odefa_natodefa_mappings.t)
    (odefa_err : Error.error)
  : error =
  let open On_to_odefa_types in
  (* Helper functions *)
  let odefa_to_on_expr =
    Odefa_natodefa_mappings.get_natodefa_equivalent_expr odefa_on_maps
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