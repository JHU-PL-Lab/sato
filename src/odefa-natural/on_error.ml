open Batteries;;

open Odefa_ast;;
open Odefa_symbolic_interpreter;;

type error_binop = {
  err_binop_expr : On_ast.expr;
}
[@@ deriving show]
;;

type error_match = {
  err_match_aliases : On_ast.ident list;
  err_match_expr : On_ast.expr;
  err_match_value : On_ast.expr;
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
      "* Expression : " ^ (On_ast_pp.show_expr err.err_binop_expr)
    | Error_match err ->
      let alias_str =
        String.join " = "
          @@ List.map On_ast_pp.show_ident err.err_match_aliases
      in
      let value_str = On_ast_pp.show_expr err.err_match_value in
      "* Value      : " ^ alias_str ^ " = " ^ value_str ^"\n" ^
      "* Expression : " ^ (On_ast_pp.show_expr err.err_match_expr)
    | Error_value err ->
      "* Expression : " ^ (On_ast_pp.show_expr err.err_value_expr)
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

(*
let _odefa_to_on_binop
    (expr1 : On_ast.expr)
    (expr2 : On_ast.expr)
    (op : Ast.binary_operator)
  : On_ast.expr =
  match op with
  | Binary_operator_plus
;;
*)
  
let odefa_to_natodefa_error
    (odefa_on_maps : On_to_odefa_types.Odefa_natodefa_mappings.t)
    (odefa_err : Error.error)
  : error =
  let open On_to_odefa_types in
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
  match odefa_err with
  | Error.Error_binop err ->
    begin
      let (Clause (Var (v, _), _)) = err.err_binop_clause in
      Error_binop {
        err_binop_expr = odefa_to_on_expr v;
      }
    end
  | Error.Error_match err ->
    begin
      let aliases = err.err_match_aliases in
      let (aliases', last_var) =
        match List.rev aliases with
        | hd :: tl ->
          (List.rev tl, hd)
        | [] ->
          raise @@
            Jhupllib.Utils.Invariant_failure "Cannot have empty alias list!"
      in
      let (Clause (Var (v, _), _)) = err.err_match_clause in
      Error_match {
        err_match_aliases = odefa_to_on_aliases aliases';
        err_match_expr = odefa_to_on_expr v;
        err_match_value = odefa_to_on_expr last_var
      }
    end
  | Error.Error_value err ->
    begin
      let (Clause (Var (v, _), _)) = err.err_value_clause in
      Error_value {
        err_value_expr = odefa_to_on_expr v;
      }
    end
;;