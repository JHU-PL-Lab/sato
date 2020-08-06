open Batteries;;

open Odefa_ast;;
open Ast;;
open Ast_pp;;

open Constraint;;

(* let lazy_logger = Jhupllib.Logger_utils.make_lazy_logger "Symbolic_interpreter.Error";; *)

type error_binop = {
  err_binop_ident : ident;
  err_binop_operation : binary_operator;
  err_binop_left_val : value_source;
  err_binop_right_val : value_source;
}
[@@ deriving eq, show]
;;

type error_match = {
  err_match_aliases : ident list;
  err_match_value : clause;
  err_match_clause : clause;
  err_match_expected_type : type_sig;
  err_match_actual_type : type_sig;
}
[@@ deriving eq, show]
;;

type error =
  | Error_binop of error_binop
  | Error_match of error_match
  [@@ deriving eq, show]
;;

exception Parse_failure of string;;

module type Error_tree = sig
  type t;;
  val empty : t;;
  val is_empty : t -> bool;;
  val singleton : error -> t;;
  val add_and : t -> t -> t;;
  val add_or : t -> t -> t;;
  val tree_from_error_list : t list -> t;;
  val to_string : t -> string;;
  val map : (error -> error) -> t -> t;;
  val mem : error -> t -> bool;;
  val mem_singleton : t -> t -> bool;;
  val count : t -> int;;
end;;

module Error_tree : Error_tree = struct
  type t =
    | Node of t * t
    | Error of error
    | Empty
    [@@ deriving show]
  ;;

  let _ = show;;

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

  let rec _flatten_tree error_tree =
    match error_tree with
    | Node (et1, et2) -> (_flatten_tree et1) @ (_flatten_tree et2)
    | Error error -> [error]
    | Empty -> []
  ;;

  let error_to_string error =
    match error with
    | Error_binop binop_err ->
      begin
        "* Operation : " ^
        (show_value_source binop_err.err_binop_left_val) ^ " " ^
        (show_binary_operator binop_err.err_binop_operation) ^ " " ^
        (show_value_source binop_err.err_binop_right_val)
      end
    | Error_match match_err ->
      begin
        let alias_str =
          let a_chain = match_err.err_match_aliases in
          let a_str = String.join " = " @@ List.map show_ident a_chain in
          if not @@ List.is_empty a_chain then a_str ^ " = " else a_str
        in
        let clause_str =
          match_err.err_match_clause
          (* Delete context stack information for end-user *)
          |> Ast_tools.map_clause_vars (fun (Var (x, _)) -> Var (x, None))
          |> show_clause
        in
        "* Value    : " ^ alias_str ^
          (show_clause match_err.err_match_value) ^ "\n" ^
        "* Clause   : " ^ clause_str ^ "\n" ^
        "* Expected : " ^ (show_type_sig match_err.err_match_expected_type) ^ "\n" ^
        "* Actual   : " ^ (show_type_sig match_err.err_match_actual_type)
      end
  ;;

  let to_string error_tree =
    let error_list = _flatten_tree error_tree in
    let string_list = List.map error_to_string error_list in
    String.join "\n---------------\n" string_list
  ;;
  
  let empty = Empty;;

  let is_empty error_tree =
    match error_tree with
    | Empty -> true
    | Node (_, _) | Error _ -> false
  ;;

  let map fn error_tree =
    let rec walk fn error_tree =
      match error_tree with
      | Node (et1, et2) -> Node (walk fn et1, walk fn et2)
      | Error err -> Error (fn err)
      | Empty -> Empty
    in
    walk fn error_tree
  ;;

  let mem error error_tree =
    let rec walk error_tree error =
      match error_tree with
      | Empty -> false
      | Node (et1, et2) -> (walk et1 error) || (walk et2 error)
      | Error error' -> equal_error error error'
    in
    walk error_tree error
  ;;

  let mem_singleton error_singleton error_tree =
    match error_singleton with
    | Error error -> mem error error_tree
    | Node (_, _) | Empty -> failwith "Not a singleton!"
  ;;

  let count error_tree =
    let rec walk error_tree =
      match error_tree with
      | Empty -> 0
      | Node (et1, et2) -> (walk et1) + (walk et2)
      | Error _ -> 1
    in
    walk error_tree
  ;;
end;;

(* **** String-to-error parsing **** *)

let _parse_aliases alias_str =
  alias_str
  |> Str.split (Str.regexp "[ ]+=[ ]+") 
  |> List.map (fun str -> Ident str)
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
  | "int" | "integer" -> Int_type
  | "bool" | "boolean" -> Bool_type
  | "fun" | "function" -> Fun_type
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
        |> List.map (fun lbl -> Ident lbl)
        |> Ident_set.of_list
      in
      Rec_type lbl_set
    end else begin
      raise @@ Parse_failure "cannot parse type"
    end
;;

let parse_error error_str =
  let args_list =
    error_str
    |> String.trim
    |> String.lchop
    |> String.rchop
    |> Str.split (Str.regexp "\"[ ]*\"")
  in
  match args_list with
  | [error_str; alias_str; val_str; clause_str; expected_str; actual_str]
    when String.equal error_str "match" ->
    begin
      Error_match {
        err_match_aliases = _parse_aliases alias_str;
        err_match_value = _parse_clause val_str;
        err_match_clause = _parse_clause clause_str;
        err_match_expected_type = _parse_type expected_str;
        err_match_actual_type = _parse_type actual_str;
      }
    end
  | _ -> raise @@ Parse_failure "Missing or spurious arguments"
;;