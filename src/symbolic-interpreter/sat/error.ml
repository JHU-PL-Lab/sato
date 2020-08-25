open Batteries;;
open Jhupllib;;

open Odefa_ast;;

module type Error_ident = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Jhupllib.Pp_utils.pretty_printer;;
  val show : t -> string;;
end;;

module type Error_value = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Jhupllib.Pp_utils.pretty_printer;;
  val show : t -> string;;
end;;

module type Error_binop = sig
  type t;;
  val equal : t -> t -> bool;;
end;;

module type Error_clause = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Jhupllib.Pp_utils.pretty_printer;;
  val show : t -> string;;
end;;

module type Error_type = sig
  type t;;
  val equal : t -> t -> bool;;
  val subtype : t -> t -> bool;;
  val pp : t Jhupllib.Pp_utils.pretty_printer;;
  val show : t -> string;;
end;;

module Ident : Error_ident = struct
  type t = Ast.ident;;
  let equal = Ast.equal_ident;;
  let pp = Ast_pp.pp_ident;;
  let show = Ast_pp.show_ident;;
end;;

module Value : Error_value = struct
  type t = Ast.clause_body;;
  let equal = Ast.equal_clause_body;;
  let pp = Ast_pp.pp_clause_body;;
  let show = Ast_pp.show_clause_body;;
end;;

module Binop : Error_binop = struct
  type t = Ast.binary_operator;;
  let equal = Ast.equal_binary_operator;;
end;;

module Clause : Error_clause = struct
  type t = Ast.clause;;
  let equal = Ast.equal_clause;;
  let pp = Ast_pp.pp_clause;;
  let show = Ast_pp.show_clause;;
end;;

module Type : Error_type = struct
  type t = Ast.type_sig;;
  let equal = Ast.equal_type_sig;;
  let subtype = Ast.Type_signature.subtype;;
  let pp = Ast_pp.pp_type_sig;;
  let show = Ast_pp.show_type_sig;;
end;;

module type Error = sig
  module Error_ident : Error_ident;;
  module Error_value : Error_value;;
  module Error_binop : Error_binop;;
  module Error_clause : Error_clause;;
  module Error_type : Error_type;;

  exception Parse_failure of string;;

  type error_binop = {
    err_binop_left_aliases : Error_ident.t list;
    err_binop_right_aliases : Error_ident.t list;
    err_binop_left_val : Error_value.t;
    err_binop_right_val : Error_value.t;
    err_binop_operation : Error_binop.t;
    err_binop_clause : Error_clause.t;
  }

  type error_match = {
    err_match_aliases : Error_ident.t list;
    err_match_val : Error_value.t;
    err_match_expected : Error_type.t;
    err_match_actual : Error_type.t;
    err_match_clause : Error_clause.t;
  }

  type error_value = {
    err_value_aliases : Error_ident.t list;
    err_value_val : Error_value.t;
    err_value_clause : Error_clause.t;
  }

  type t =
    | Error_binop of error_binop
    | Error_match of error_match
    | Error_value of error_value

  val equal : t -> t -> bool;;
  val parse : string -> t;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
end;;

module Error
    (Ident : Error_ident with type t = Ast.ident)
    (Value : Error_value with type t = Ast.clause_body)
    (Binop : Error_binop with type t = Ast.binary_operator)
    (Clause : Error_clause with type t = Ast.clause)
    (Type : Error_type with type t = Ast.type_sig)
  : Error = struct
  module Error_ident = Ident;;
  module Error_value = Value;;
  module Error_binop = Binop;;
  module Error_clause = Clause;;
  module Error_type = Type;;

  exception Parse_failure of string;;

  type error_binop = {
    err_binop_left_aliases : Error_ident.t list;
    err_binop_right_aliases : Error_ident.t list;
    err_binop_left_val : Error_value.t;
    err_binop_right_val : Error_value.t;
    err_binop_operation : Error_binop.t;
    err_binop_clause : Error_clause.t;
  }
  [@@ deriving eq]

  type error_match = {
    err_match_aliases : Error_ident.t list;
    err_match_val : Error_value.t;
    err_match_expected : Error_type.t;
    err_match_actual : Error_type.t;
    err_match_clause : Error_clause.t;
  }
  [@@ deriving eq]

  type error_value = {
    err_value_aliases : Error_ident.t list;
    err_value_val : Error_value.t;
    err_value_clause : Error_clause.t;
  }
  [@@ deriving eq]

  type t =
    | Error_binop of error_binop
    | Error_match of error_match
    | Error_value of error_value
  [@@ deriving eq]

  let equal = equal;;

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
        let Ast.Expr clist = expr in
        match clist with
        | [clause] -> clause
        | _ ->
          raise @@ Parse_failure "expression contains more than one clause"
      end
    | _ -> raise @@ Parse_failure "more than one expression"
  ;;

  let _parse_clause_body clause_body_str =
    let (Ast.Clause (_, body)) =
      _parse_clause @@ "dummy = " ^ clause_body_str
    in
    body
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
        Error_binop {
          err_binop_clause = _parse_clause clause_str;
          err_binop_left_val = _parse_clause_body l_val_str;
          err_binop_right_val = _parse_clause_body r_val_str;
          err_binop_left_aliases = _parse_aliases l_alias_str;
          err_binop_right_aliases = _parse_aliases r_alias_str;
          err_binop_operation = _parse_op op_str;
        }
      end
    | [error_str; alias_str; val_str; clause_str; expected_str; actual_str]
      when String.equal error_str "match" ->
      begin
        Error_match {
          err_match_aliases = _parse_aliases alias_str;
          err_match_val = _parse_clause_body val_str;
          err_match_clause = _parse_clause clause_str;
          err_match_expected = _parse_type expected_str;
          err_match_actual = _parse_type actual_str;
        }
      end
    | [error_str; alias_str; val_str; clause_str]
      when String.equal error_str "value" ->
      begin
        Error_value {
          err_value_aliases = _parse_aliases alias_str;
          err_value_val = _parse_clause_body val_str;
          err_value_clause = _parse_clause clause_str;
        }
      end
    | _ -> raise @@ Parse_failure "Missing or spurious arguments"
  ;;

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
      let value = err.err_match_val in
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
        pp_type_sig err.err_match_expected
    in
    let pp_actual formatter err =
      Format.fprintf formatter
        "@[* Actual   : @[%a@]@]"
        pp_type_sig err.err_match_actual
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


end;;

(* ******************* *)

open Ast;;

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

module type Error_list = sig
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

module Error_list : Error_list = struct
  type t = error list;;

  let singleton error = [error];;

  (* We need to effective negate the logical operations, according to
     DeMorgan's laws.  (Think negating the predicate of the conditional;
     the the abort clause is in the true branch.) *)

  (* not (x1 and x2) <=> (not x1) or (not x2) *)
  let add_and errs_1 errs_2 =
    match (errs_1, errs_2) with
    | ([], []) -> []
    | (_, []) ->  errs_1
    | ([], _) -> errs_2
    | (_, _) -> errs_1 @ errs_2
  ;;

  (* not (x1 or x2) <=> (not x1) and (not x2) *)
  let add_or errs_1 errs_2 =
    match (errs_1, errs_2) with
    | ([], [])
    | (_, [])
    | ([], _) -> []
    | (_, _) -> errs_1 @ errs_2
  ;;

  let tree_from_error_list err_lists =
    List.fold_left
      (fun err_list err -> err @ err_list)
      []
      err_lists
  ;;

  let flatten_tree err_list = err_list;;

  let to_string err_list =
    let error_list = flatten_tree err_list in
    let string_list = List.map show error_list in
    String.join "\n---------------\n" string_list
  ;;
  
  let empty = [];;

  let is_empty error_list =
    match error_list with
    | [] -> true
    | _ -> false
  ;;

  let map = List.map;;

  let mem error error_list =
    List.exists (equal_error error) error_list
  ;;

  let mem_singleton error_singleton error_list =
    match error_singleton with
    | [error] -> mem error error_list
    | _ -> failwith "Not a singleton!"
  ;;

  let count error_list = List.length error_list;;
end;;

(* **** String-to-error parsing **** *)

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
        |> List.map (fun lbl -> Ast.Ident lbl)
        |> Ast.Ident_set.of_list
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
  | [error_str; alias_str; val_str; clause_str]
    when String.equal error_str "value" ->
    begin
      let (Clause (_, body)) = _parse_clause @@ "dummy = " ^ val_str in
      Error_value {
        err_value_aliases = _parse_aliases alias_str;
        err_value_val = body;
        err_value_clause = _parse_clause clause_str;
      }
    end
  | _ -> raise @@ Parse_failure "Missing or spurious arguments"
;;