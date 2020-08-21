open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Ast;;

(* open Constraint;; *)

(* let lazy_logger = Jhupllib.Logger_utils.make_lazy_logger "Symbolic_interpreter.Error";; *)

type error_binop = {
  err_binop_clause : clause;
  err_binop_operation : binary_operator;
  err_binop_left_val : clause_body;
  err_binop_right_val : clause_body;
  err_binop_left_aliases : ident list;
  err_binop_right_aliases : ident list;
}
[@@ deriving eq]
;;

type error_match = {
  err_match_aliases : ident list;
  err_match_value : clause_body;
  err_match_clause : clause;
  err_match_expected_type : type_sig;
  err_match_actual_type : type_sig;
}
[@@ deriving eq]
;;

type error_value = {
  err_value_aliases : ident list;
  err_value_val : clause_body;
  err_value_clause : clause;
}
[@@ deriving eq]
;;

type error =
  | Error_binop of error_binop
  | Error_match of error_match
  | Error_value of error_value
  [@@ deriving eq]
;;

(* **** Pretty-print error **** *)

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

exception Parse_failure of string;;

module type Error_tree = sig
  type t;;
  val empty : t;;
  val is_empty : t -> bool;;
  val singleton : error -> t;;
  val add_and : t -> t -> t;;
  val add_or : t -> t -> t;;
  val tree_from_error_list : t list -> t;;
  val flatten_tree : t -> error list;;
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
  ;;

  let singleton error = Error error;;

  (* We need to effective negate the logical operations, according to
     DeMorgan's laws.  (Think negating the predicate of the conditional;
     the the abort clause is in the true branch.) *)

  (* not (x1 and x2) <=> (not x1) or (not x2) *)
  let add_and et1 et2 =
    match (et1, et2) with
    | (Empty, Empty) -> Empty
    | (_, Empty) ->  et1
    | (Empty, _) -> et2
    | (_, _) -> Node (et1, et2)
  ;;

  (* not (x1 or x2) <=> (not x1) and (not x2) *)
  let add_or et1 et2 =
    match (et1, et2) with
    | (Empty, Empty) -> Empty
    | (_, Empty) -> Empty
    | (Empty, _) -> Empty
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

  let to_string error_tree =
    let error_list = _flatten_tree error_tree in
    let string_list = List.map show error_list in
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

(*
let val_source_to_clause_body val_src =
  let open Interpreter_types in
  match val_src with
  | Constraint.Value v ->
    begin
      match v with
      | Constraint.Int n -> Value_body (Value_int n)
      | Constraint.Bool b -> Value_body (Value_bool b)
      | Constraint.Function f -> Value_body (Value_function f)
      | Constraint.Record r ->
        let r' =
          r
          |> Ident_map.enum
          |> Enum.map (fun (lbl, (Symbol (s, _))) -> (lbl, Var (s, None)))
          |> Ident_map.of_enum
        in
        Value_body (Value_record (Record_value r'))
    end
  | Constraint.Binop (x1, op, x2) ->
    let x1' = (fun (Symbol (s1, _)) -> Var (s1, None)) x1 in
    let x2' = (fun (Symbol (s2, _)) -> Var (s2, None)) x2 in
    Binary_operation_body (x1', op, x2')
  | Constraint.Input -> Input_body
  | Constraint.Match (x, p) ->
    let x' = (fun (Symbol (s, _)) -> Var (s, None)) x in
    Match_body (x', p)
  | Constraint.Abort -> Abort_body []
;;
*)

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

let _parse_op op_str =
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

let parse_error error_str =
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
      let (Clause (_, body)) = _parse_clause @@ "dummy = " ^ val_str in
      Error_match {
        err_match_aliases = _parse_aliases alias_str;
        err_match_value = body;
        err_match_clause = _parse_clause clause_str;
        err_match_expected_type = _parse_type expected_str;
        err_match_actual_type = _parse_type actual_str;
      }
    end
  | _ -> raise @@ Parse_failure "Missing or spurious arguments"
;;