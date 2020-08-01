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
  val singleton : error -> t;;
  val is_singleton : t -> bool;;
  val add_and : t -> t -> t;;
  val add_or : t -> t -> t;;
  val tree_from_error_list : t list -> t;;
  val to_string : t -> string;;
  val empty : t;;
  val is_empty : t -> bool;;
  val parse : string -> t;;
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

  let is_singleton error_tree =
    match error_tree with
    | Error _ -> true
    | Node (_, _) | Empty -> false
  ;;

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
        let alias_str =
          let a_chain = match_err.err_match_aliases in
          let a_str = String.join " = " @@ List.map show_ident a_chain in
          if not @@ List.is_empty a_chain then a_str ^ " = " else a_str
          (*
          if List.length alias_chain > 1 then begin
            (show_ident @@ List.first alias_chain) ^ " = " ^
            (show_ident @@ List.last alias_chain)
          end else begin
            (show_ident @@ List.first alias_chain)
          end
          *)
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

  let map fn error_tree =
    let rec walk fn error_tree =
      match error_tree with
      | Node (et1, et2) -> Node (walk fn et1, walk fn et2)
      | Error err -> Error (fn err)
      | Empty -> Empty
    in
    walk fn error_tree
  ;;

  (* The following s-expression code is taken from Martin Josefsson at
     http://www.martinjosefsson.com/parser/compiler/interpreter/programming/language/2019/04/03/Simple-S_expression_parser_in_OCaml.html
     and is used under the MIT license, with some modifications for Str.split_result
  *)

  (* **** Begin s-expression code **** *)

  type s_expression =
    | Atom of string
    | SexpList of s_expression list
  ;;

  type ('i, 'e) parse_result =
    | ParseNext of 'i * 'e
    | ParseOut of 'i
    | ParseEnd
  ;;

  let parse_list iterator parse_s_expressions =
    match parse_s_expressions iterator [] with next_iterator, expressions ->
      ParseNext (next_iterator, SexpList expressions)
  ;;

  let parse_expression (iterator: int * Str.split_result list) parse_s_expressions =
    let index, tokens = iterator in
    if List.length tokens = index then begin
      ParseEnd
    end else begin
      let current_token = List.nth tokens index in
      match current_token with
      | Str.Delim d when String.equal d "[" ->
        parse_list (index + 1, tokens) parse_s_expressions
      | Str.Delim d when String.equal d "]" ->
        ParseOut (index + 1, tokens)
      | Str.Text t -> ParseNext ((index + 1, tokens), Atom t)
      | Str.Delim _ -> raise @@ Parse_failure "unknown delimiter"
    end
  ;;

  let s_expression_of_token_list
    : Str.split_result list -> s_expression =
    fun tokens ->
      let rec parse_s_expressions
          (iterator: int * Str.split_result list)
          (expressions: s_expression list) =
        match parse_expression iterator parse_s_expressions with
        | ParseEnd -> (iterator, List.rev expressions)
        | ParseOut iterator -> (iterator, List.rev expressions)
        | ParseNext (iterator, result) ->
          parse_s_expressions iterator (result :: expressions)
      in
      match parse_s_expressions (0, tokens) [] with
      | _, [first] -> first
      | _, lst -> SexpList lst
  ;;

  (* **** End s-expression code **** *)

  let _parse_alias alias_str = Ident (alias_str);;

  let _parse_clause cl_str =
    let expr_lst =
      try
        Odefa_parser.Parser.parse_expression_string cl_str
      with Odefa_parser.Parser.Parse_error (_, _, _, _) ->
        raise @@ Parse_failure ("cannot parse clause " ^ cl_str)
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

  let _parse_vars_str vars_str =
    let var_strs = Str.split (Str.regexp "[ ]*=[ ]*") vars_str in
    let (alias_strs, clause_str) =
      match List.rev var_strs with
      | hd1 :: hd2 :: tl -> (tl, hd2 ^ "=" ^ hd1)
      | _ -> raise @@ Parse_failure "cannot parse vars"
    in
    (List.map _parse_alias alias_strs, _parse_clause clause_str)
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

  let rec s_expr_to_err_tree s_expr =
    match s_expr with
    | Atom err_str ->
      begin
        let err_str_list =
          err_str
          |> Str.split (Str.regexp "[\"]")
          |> List.map String.trim
          |> List.filter (fun s -> not @@ String.is_empty s)
        in
        match err_str_list with
        | [vars; clause; expected; actual] ->
          let (aliases, val_clause) = _parse_vars_str vars in
          Error (Error_match {
            err_match_aliases = aliases;
            err_match_value = val_clause;
            err_match_clause = _parse_clause clause;
            err_match_expected_type = _parse_type expected;
            err_match_actual_type = _parse_type actual;
          })
        | _ -> raise @@ Parse_failure "missing or spurious match error args"
      end
    | SexpList s_expr_lst ->
      begin
        match s_expr_lst with
        | [] -> Empty
        | [s_expr] -> s_expr_to_err_tree s_expr
        | [s_expr; s_expr'] ->
          Node (s_expr_to_err_tree s_expr, s_expr_to_err_tree s_expr')
        | _ -> raise @@ Parse_failure "sexpr has more than two nodes"
      end
  ;;

  let parse err_str =
    let err_str_tokenized =
      err_str
      |> Str.full_split (Str.regexp "[][]")
      |> List.filter
        (fun token ->
          match token with
          | Str.Text txt ->
            txt
            |> String.trim
            |> (fun s -> not @@ String.is_empty s)
          | Str.Delim _ ->
            true
        )
    in
    let s_expr = s_expression_of_token_list err_str_tokenized in
    let e_tree = s_expr_to_err_tree s_expr in
    e_tree
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