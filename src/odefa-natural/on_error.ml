open Batteries;;

open Odefa_ast;;
open Odefa_symbolic_interpreter;;

type error_binop = {
  err_binop_expr : On_ast.expr;
}
[@@ deriving show]
;;

type error_match = {
  err_match_expr : On_ast.expr;
}
[@@ deriving show]

type error_value = {
  err_value_expr : On_ast.expr;
}
[@@ deriving show]

type error =
  | Error_binop of error_binop
  | Error_match of error_match
  | Error_value of error_value
[@@ deriving show]
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
  [@@ deriving show]
  ;;

  let _ = show;;

  let error_to_string error =
    match error with
    | Error_binop err ->
      "* Expression : " ^ (On_ast.show_expr err.err_binop_expr)
    | Error_match err ->
      "* Expression : " ^ (On_ast.show_expr err.err_match_expr)
    | Error_value err ->
      "* Expression : " ^ (On_ast.show_expr err.err_value_expr)
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

let odefa_to_natodefa_error
    (odefa_on_maps : On_to_odefa_types.Odefa_natodefa_mappings.t)
    (odefa_err : Error.error)
  : error =
  let odefa_var_to_on_expr = odefa_on_maps.odefa_var_to_natodefa_expr in
  match odefa_err with
  | Error.Error_binop err ->
    let (Clause (Var (v, _), _)) = err.err_binop_clause in
    let on_expr = Ast.Ident_map.find v odefa_var_to_on_expr in
    Error_binop {
      err_binop_expr = on_expr;
    }
  | Error.Error_match err ->
    let (Clause (Var (v, _), _)) = err.err_match_clause in
    let on_expr = Ast.Ident_map.find v odefa_var_to_on_expr in
    Error_match {
      err_match_expr = on_expr;
    }
  | Error.Error_value err ->
    let (Clause (Var (v, _), _)) = err.err_value_clause in
    let on_expr = Ast.Ident_map.find v odefa_var_to_on_expr in
    Error_value {
      err_value_expr = on_expr;
    }
;;