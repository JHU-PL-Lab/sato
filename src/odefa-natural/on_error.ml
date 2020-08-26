open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_symbolic_interpreter;;

open Error;;

let _parse_expr expr_str =
  let expr_lst =
    try
      On_parse.parse_expression_string expr_str
    with On_parse.Parse_error _ ->
      raise @@ Parse_failure (Printf.sprintf "Cannot parse expr %s" expr_str)
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

module type Error_ident = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val parse : string -> t;;
end;;

module type Error_value = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val parse : string -> t;;
end;;

module type Error_binop = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val parse : string -> t;;
end;;

module type Error_clause = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val parse : string -> t;;
end;;

module type Error_type = sig
  type t;;
  val equal : t -> t -> bool;;
  val subtype : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val parse : string -> t;;
end;;

module Ident : (Error_ident with type t = On_ast.ident) = struct
  type t = On_ast.ident;;
  let equal = On_ast.equal_ident;;
  let pp = On_ast_pp.pp_ident;;
  let show = On_ast_pp.show_ident;;
  let parse s = On_ast.Ident s;;
end;;

module Value : (Error_value with type t = On_ast.expr) = struct
  type t = On_ast.expr;;
  let equal = On_ast.equal_expr;;
  let pp = On_ast_pp.pp_expr;;
  let show = On_ast_pp.show_expr;;
  let parse = _parse_expr;;
end;;

module Binop : (Error_binop with type t = On_ast.expr) = struct
  type t = On_ast.expr;;
  let equal = On_ast.equal_expr;;
  let pp = On_ast_pp.pp_expr;;
  let show = On_ast_pp.show_expr;;
  let parse = _parse_expr;;
end;;

module Clause : (Error_clause with type t = On_ast.expr) = struct
  type t = On_ast.expr;;
  let equal = On_ast.equal_expr;;
  let pp = On_ast_pp.pp_expr;;
  let show = On_ast_pp.show_expr;;
  let parse = _parse_expr;;
end;;

module Type : (Error_type with type t = On_ast.type_sig) = struct
  type t = On_ast.type_sig;;
  let equal = On_ast.equal_type_sig;;
  let subtype _ _ = false;;
  let pp = On_ast_pp.pp_on_type;;
  let show = On_ast_pp.show_on_type;;
  let parse = _parse_type_sig;;
end;;

module On_error = Make(Ident)(Value)(Binop)(Clause)(Type);;

(* **** Odefa to natodefa error translation **** *)

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
    (odefa_err : Error.Odefa_error.t)
  : On_error.t =
  let open Error in
  (* Helper functions *)
  let odefa_to_on_expr =
    On_to_odefa_maps.get_natodefa_equivalent_expr odefa_on_maps
  in
  let odefa_to_on_aliases (aliases : Ast.ident list) : On_ast.ident list =
    aliases
    |> List.filter_map
      (fun alias ->
        match odefa_to_on_expr alias with
        | (On_ast.Var ident) -> Some ident
        | _ -> None
      )
    (* During translation, some odefa vars are assigned to the same natodefa
       vars (namely in var expressions).  The following procedure removes any
       adjacent duplicates from the alias chain. *)
    |> List.fold_left
      (fun deduped_list alias ->
        match List.Exceptionless.hd deduped_list with
        | Some next ->
          let is_next = On_ast.equal_ident next alias in
          if is_next then deduped_list else alias :: deduped_list
        | None ->
          alias :: deduped_list
      )
      []
    |> List.rev
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
  | Odefa_error.Error_binop err ->
    begin
      let l_aliases = err.err_binop_left_aliases in
      let r_aliases = err.err_binop_right_aliases in
      let l_aliases_on = odefa_to_on_aliases l_aliases in
      let r_aliases_on = odefa_to_on_aliases r_aliases in
      let (_, op, _) = err.err_binop_operation in
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
        err_binop_left_val = l_value;
        err_binop_right_val = r_value;
        err_binop_operation = constraint_expr;
        err_binop_clause = odefa_to_on_expr v;
      }
    end
  | Odefa_error.Error_match err ->
    begin
      let aliases = err.err_match_aliases in
      let (Clause (Var (v, _), _)) = err.err_match_clause in
      Error_match {
        err_match_aliases = odefa_to_on_aliases aliases;
        err_match_clause = odefa_to_on_expr v;
        err_match_val = odefa_to_on_value aliases;
        err_match_expected = odefa_to_on_type err.err_match_expected;
        err_match_actual = odefa_to_on_type err.err_match_actual;
      }
    end
  | Odefa_error.Error_value err ->
    begin
      let aliases = err.err_value_aliases in
      let (Clause (Var (v, _), _)) = err.err_value_clause in
      Error_value {
        err_value_aliases = odefa_to_on_aliases aliases;
        err_value_val = odefa_to_on_value aliases;
        err_value_clause = odefa_to_on_expr v;
      }
    end
;;