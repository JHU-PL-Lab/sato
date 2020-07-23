open Batteries;;

open Odefa_ast;;
open Ast;;
open Ast_pp;;

open Constraint;;

type error_binop = {
  err_binop_ident : ident;
  err_binop_operation : binary_operator;
  err_binop_left_val : value_source;
  err_binop_right_val : value_source;
}
[@@ deriving show]
;;


type error_match = {
  err_match_ident : ident;
  err_match_value : value_source;
  err_match_expected_type : type_sig;
  err_match_actual_type : type_sig;
}
[@@ deriving show]
;;

type error =
  | Error_binop of error_binop
  | Error_match of error_match
;;

module type Error_tree = sig
  type t;;
  val singleton : error -> t;;
  val add_and : t -> t -> t;;
  val add_or : t -> t -> t;;
  val tree_from_error_list : t list -> t;;
  val to_string : t -> string;;
  val empty : t;;
  val is_empty : t -> bool;;
end;;

module Error_tree : Error_tree = struct
  type t =
    | Node of t * t
    | Error of error
    | Empty
  ;;

  let singleton error = Error error;;

  let add_and et1 et2 =
    match (et1, et2) with
    | (Empty, Empty) -> Empty
    | (_, Empty) ->  et1
    | (Empty, _) -> et2
    | (_, _) -> Node (et1, et2)
  ;;

  let add_or et1 et2 =
    match (et1, et2) with
    | (Empty, Empty) -> Empty
    | (_, _) -> Node (et1, et2)
  ;;

  let tree_from_error_list err_trees =
    let rec add_to_tree err_trees =
      match err_trees with
      | [err_tree] -> err_tree
      | err_tree :: err_trees' ->
        begin
          let rest_of_tree = add_to_tree err_trees' in
          match err_tree with
          | Empty -> rest_of_tree
          | Node _ | Error _ -> Node (err_tree, rest_of_tree)
        end
      | [] ->
        raise @@
          Jhupllib.Utils.Invariant_failure "No error trees found in list"
    in
    add_to_tree err_trees
  ;;

  let rec flatten_tree error_tree =
    match error_tree with
    | Node (et1, et2) -> (flatten_tree et1) @ (flatten_tree et2)
    | Error error -> [error]
    | Empty -> []
  ;;

  let error_to_string error =
    match error with
    | Error_binop binop_err ->
      begin
        "* Operation : " ^
        (show_value_source binop_err.err_binop_left_val) ^ "\n" ^
        (show_binary_operator binop_err.err_binop_operation) ^ "\n" ^
        (show_value_source binop_err.err_binop_right_val)
      end
    | Error_match match_err ->
      begin
        "* Value    : " ^ (show_value_source match_err.err_match_value) ^ "\n" ^
        "* Expected : " ^ (show_type_sig match_err.err_match_expected_type) ^ "\n" ^
        "* Actual   : " ^ (show_type_sig match_err.err_match_actual_type)
      end
  ;;

  let to_string error_tree =
    let error_list = flatten_tree error_tree in
    let string_list = List.map error_to_string error_list in
    String.join "\n---------------\n" string_list
  ;;
  
  let empty = Empty;;

  let is_empty error_tree =
    match error_tree with
    | Empty -> true
    | Node (_, _) | Error _ -> false
  ;;
end;;