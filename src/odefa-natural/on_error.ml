open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_symbolic_interpreter;;

(* **** Natodefa module signatures **** *)

module type Error_ident = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

module type Error_value = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

module type Error_binop = sig
  type t;;
  val equal : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

module type Error_type = sig
  type t;;
  val equal : t -> t -> bool;;
  val subtype : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

module type Error_natodefa_type = sig
  type t;;
  val equal : t -> t -> bool;;
  val subtype : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;
(* **** Natodefa modules **** *)

let replace_linebreaks (str : string) : string =
  String.replace_chars
    (function '\n' -> " " | c -> String.of_char c) str
;;

module Ident : (Error_ident with type t = On_ast.ident) = struct
  type t = On_ast.ident;;
  let equal = On_ast.equal_ident;;
  let pp = On_ast_pp.pp_ident;;
  let show = On_ast_pp.show_ident;;
  let to_yojson ident =
    `String (replace_linebreaks @@ show ident);;
end;;

module Value : (Error_value with type t = On_ast.core_natodefa) = struct
  type t = On_ast.core_natodefa;;
  let equal = On_ast.equal_expr;;
  let pp = On_ast_pp.pp_expr;;
  let show = Pp_utils.pp_to_string pp;;
  let to_yojson value =
    `String (replace_linebreaks @@ show value);;
end;;

module Binop : (Error_binop with type t = On_ast.core_natodefa) = struct
  type t = On_ast.core_natodefa;;
  let equal = On_ast.equal_expr;;
  let pp = On_ast_pp.pp_expr;;
  let show = Pp_utils.pp_to_string pp;;
  let to_yojson binop =
    `String (replace_linebreaks @@ show binop);;
end;;

module Type : (Error_type with type t = On_ast.type_sig) = struct
  type t = On_ast.type_sig;;
  let equal = On_ast.equal_type_sig;;
  let subtype _ _ = false;;
  let pp = On_ast_pp.pp_on_type;;
  let show = On_ast_pp.show_on_type;;
  let to_yojson typ =
    `String (replace_linebreaks @@ show typ);;
end;;

module NatodefaType : (Error_natodefa_type with type t = On_ast.syn_type_natodefa) = struct
  type t = On_ast.syn_type_natodefa;;
  let equal = On_ast.equal_expr;;
  let subtype _ _ = false;;
  let pp = On_ast_pp.pp_expr;;
  let show = Pp_utils.pp_to_string On_ast_pp.pp_expr;;
  let to_yojson typ =
    `String (replace_linebreaks @@ show typ);;
end;;

module type Error = sig
  module Error_ident : Error_ident;;
  module Error_value : Error_value;;
  module Error_binop : Error_binop;;
  module Error_type : Error_type;;
  module Error_natodefa_type : Error_natodefa_type;;

  type ident;;
  type value;;
  type binop;;
  type type_sig;;
  type natodefa_type;;

  type error_binop = {
    err_binop_left_aliases : ident list;
    err_binop_right_aliases : ident list;
    err_binop_left_val : value;
    err_binop_right_val : value;
    err_binop_operation : binop;
  }

  type error_match = {
    err_match_aliases : ident list;
    err_match_val : value;
    err_match_expected : type_sig;
    err_match_actual : type_sig;
  }

  type error_value = {
    err_value_aliases : ident list;
    err_value_val : value;
  }

  type error_type = {
    err_type_aliases : ident list;
    err_type_val : value;
    err_type_expected : natodefa_type;
    err_type_actual : natodefa_type;
  }

  type t =
    | Error_binop of error_binop
    | Error_match of error_match
    | Error_value of error_value
    | Error_natodefa_type of error_type

  val equal : t -> t -> bool;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

module Make
    (Ident : Error_ident)
    (Value : Error_value)
    (Binop : Error_binop)
    (PrimitiveType : Error_type)
    (NatodefaType : Error_natodefa_type)
  : (Error
      with type ident := Ident.t
      and type value := Value.t
      and type binop := Binop.t
      and type type_sig := PrimitiveType.t
      and type natodefa_type := NatodefaType.t) = struct

  module Error_ident = Ident;;
  module Error_value = Value;;
  module Error_binop = Binop;;
  module Error_type = PrimitiveType;;
  module Error_natodefa_type = NatodefaType;;

  type error_binop = {
    err_binop_left_aliases : Ident.t list;
    err_binop_right_aliases : Ident.t list;
    err_binop_left_val : Value.t;
    err_binop_right_val : Value.t;
    err_binop_operation : Binop.t;
  }
  [@@ deriving eq, to_yojson]

  type error_match = {
    err_match_aliases : Ident.t list;
    err_match_val : Value.t;
    err_match_expected : PrimitiveType.t;
    err_match_actual : PrimitiveType.t;
  }
  [@@ deriving eq, to_yojson]

  type error_value = {
    err_value_aliases : Ident.t list;
    err_value_val : Value.t;
  }
  [@@ deriving eq, to_yojson]

  type error_type = {
    err_type_aliases : Ident.t list;
    err_type_val : Value.t;
    err_type_expected : NatodefaType.t;
    err_type_actual : NatodefaType.t;
  } 
  [@@ deriving eq, to_yojson]


  type t =
    | Error_binop of error_binop
    | Error_match of error_match
    | Error_value of error_value
    | Error_natodefa_type of error_type
  [@@ deriving eq, to_yojson]

  let equal = equal;;

  let pp_alias_list formatter aliases =
    Pp_utils.pp_concat_sep
      " ="
      (fun formatter x -> Ident.pp formatter x)
      formatter
      (List.enum aliases)
  ;;

  let pp_error_binop formatter err =
    let pp_left_value formatter err =
      let l_aliases = err.err_binop_left_aliases in
      let l_value = err.err_binop_left_val in
      if (List.length l_aliases) > 0 then
        Format.fprintf formatter
          "@[* Left Val   : @[%a@ =@ %a@]@]@,"
          pp_alias_list l_aliases
          Value.pp l_value
      else
        Format.pp_print_string formatter ""
    in
    let pp_right_value formatter err =
      let r_aliases = err.err_binop_right_aliases in
      let r_value = err.err_binop_right_val in
      if (List.length r_aliases) > 0 then
        Format.fprintf formatter
          "@[* Right Val  : @[%a@ =@ %a@]@]@,"
          pp_alias_list r_aliases
          Value.pp r_value
      else
        Format.pp_print_string formatter ""
    in
    let pp_constraint formatter err =
      Format.fprintf formatter
        "@[* Constraint : @[%a@]@]"
        Binop.pp err.err_binop_operation
    in
    Format.fprintf formatter
      "@[<v 0>%a%a%a@]"
      pp_left_value err
      pp_right_value err
      pp_constraint err
  ;;

  let pp_error_match formatter err =
      let pp_value formatter err =
      let aliases = err.err_match_aliases in
      let value = err.err_match_val in
      if not @@ List.is_empty aliases then
        Format.fprintf formatter 
          "@[* Value    : @[%a@ =@ %a@]@]@,"
          pp_alias_list aliases
          Value.pp value
      else
        Format.fprintf formatter 
          "@[* Value    : @[%a@]@]@,"
          Value.pp value
    in
    let pp_expected formatter err =
      Format.fprintf formatter
        "@[* Expected : @[%a@]@]@,"
        PrimitiveType.pp err.err_match_expected
    in
    let pp_actual formatter err =
      Format.fprintf formatter
        "@[* Actual   : @[%a@]@]"
        PrimitiveType.pp err.err_match_actual
    in
    Format.fprintf formatter
      "@[<v 0>%a%a%a@]"
      pp_value err
      pp_expected err
      pp_actual err
  ;;

  let pp_error_value formatter err =
    let pp_value formatter err =
      let aliases = err.err_value_aliases in
      let value = err.err_value_val in
      if not @@ List.is_empty aliases then
        Format.fprintf formatter 
          "@[* Value : @[%a@ =@ %a@]@]"
          pp_alias_list aliases
          Value.pp value
      else
        Format.fprintf formatter 
          "@[* Value : @[%a@]@]"
          Value.pp value
    in
    Format.fprintf formatter
      "@[<v 0>%a@]"
      pp_value err
  ;;

  let pp_error_type formatter err =
    let pp_value formatter err =
    let aliases = err.err_type_aliases in
    let value = err.err_type_val in
    if not @@ List.is_empty aliases then
      Format.fprintf formatter 
        "@[* Value    : @[%a@ =@ %a@]@]@,"
        pp_alias_list aliases
        Value.pp value
    else
      Format.fprintf formatter 
        "@[* Value    : @[%a@]@]@,"
        Value.pp value
    in
    let pp_expected formatter err =
      Format.fprintf formatter
        "@[* Expected : @[%a@]@]@,"
        NatodefaType.pp err.err_type_expected
    in
    let pp_actual formatter err =
      Format.fprintf formatter
        "@[* Actual   : @[%a@]@]"
        NatodefaType.pp err.err_type_actual
    in
    Format.fprintf formatter
      "@[<v 0>%a%a%a@]"
      pp_value err
      pp_expected err
      pp_actual err
  ;;

  let pp formatter error =
    match error with
    | Error_binop err -> pp_error_binop formatter err
    | Error_match err -> pp_error_match formatter err
    | Error_value err -> pp_error_value formatter err
    | Error_natodefa_type err -> pp_error_type formatter err
  ;;

  let show = Pp_utils.pp_to_string pp;;
end;;

module On_error = Make(Ident)(Value)(Binop)(Type)(NatodefaType);;

(* **** Odefa error cleanup **** *)

let odefa_error_remove_instrument_vars
    (odefa_on_maps : On_to_odefa_maps.t)
    (error : Error.Odefa_error.t)
  : Error.Odefa_error.t =
  let remove_instrument_aliases aliases =
    List.filter
      (fun alias ->
        not @@ On_to_odefa_maps.is_var_instrumenting odefa_on_maps alias)
      aliases
  in
  match error with
  | Error_binop err ->
    begin
      let left_aliases' =
        remove_instrument_aliases err.err_binop_left_aliases
      in
      let right_aliases' =
        remove_instrument_aliases err.err_binop_right_aliases
      in
      let (_, op, _) =
        err.err_binop_operation
      in
      let l_operand' =
        match left_aliases' with
        | [] -> err.err_binop_left_val
        | v :: _ -> Ast.Var_body (Var (v, None))
      in
      let r_operand' =
        match right_aliases' with
        | [] -> err.err_binop_right_val
        | v :: _ -> Ast.Var_body (Var (v, None))
      in
      Error_binop {
        err with
        err_binop_left_aliases = left_aliases';
        err_binop_right_aliases = right_aliases';
        err_binop_operation = (l_operand', op, r_operand')
      }
    end
  | Error_match err ->
    begin
      let match_aliases = err.err_match_aliases in
      Error_match {
        err with
        err_match_aliases = remove_instrument_aliases match_aliases;
      }
    end
  | Error_value err ->
    begin
      let aliases = err.err_value_aliases in
      Error_value {
        err with
        err_value_aliases = remove_instrument_aliases aliases;
      }
    end
;;

(* **** Odefa to natodefa error translation **** *)

(* Helper function to remove adjacent duplicate entries in a list (note that
   this does not remove non-adjacent dupes). *)
let deduplicate_list list =
  List.fold_right
    (fun x deduped_list ->
      match List.Exceptionless.hd deduped_list with
      | Some next ->
        let is_next = On_ast.equal_ident next x in
        if is_next then deduped_list else x :: deduped_list
      | None ->
        x :: deduped_list
    )
    list
    []
;;

(* Helper function that returns a natodefa binop, depending on the odefa
   binary operator. *)
let odefa_to_on_binop 
  (odefa_binop : Ast.binary_operator) : (On_ast.core_natodefa -> On_ast.core_natodefa -> On_ast.core_natodefa) =
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
    (ton_on_maps : Ton_to_on_maps.t)
    (err_loc_option : On_ast.sem_type_natodefa option)
    (odefa_err : Error.Odefa_error.t)
  : On_error.t =
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
    |> deduplicate_list
  in
  let odefa_to_on_value (aliases : Ast.ident list) : On_ast.core_natodefa =
    let last_var =
      try
        List.last aliases
      with Invalid_argument _ ->
        raise @@ Jhupllib.Utils.Invariant_failure "Can't have empty alias list!"
    in
    (* let () = print_endline @@ Ast.show_ident last_var in *)
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
    | Ast.Untouched_type s ->
      UntouchedType s
    | Ast.Any_untouched_type ->
      (* TODO: Very cheap hack; need to change this later *)
      UntouchedType "non-parametric type"
    | Ast.Bottom_type ->
      raise @@ Jhupllib.Utils.Invariant_failure
        (Printf.sprintf "Bottom type not in natodefa")
  in
  (* Odefa to natodefa *)
  match odefa_err with
  | Error.Odefa_error.Error_binop err ->
    begin
      let () = print_endline "Natodefa Binop Error!" in
      let l_aliases = err.err_binop_left_aliases in
      let r_aliases = err.err_binop_right_aliases in
      let l_aliases_on = odefa_to_on_aliases l_aliases in
      let r_aliases_on = odefa_to_on_aliases r_aliases in
      let (_, op, _) = err.err_binop_operation in
      let l_value = odefa_to_on_value l_aliases in
      let r_value = odefa_to_on_value r_aliases in
      let constraint_expr =
        let left_expr =
          if List.is_empty l_aliases_on then l_value else
            On_ast.Var (List.hd l_aliases_on)
        in
        let right_expr =
          if List.is_empty r_aliases_on then r_value else
            On_ast.Var (List.hd r_aliases_on)
        in
        odefa_to_on_binop op left_expr right_expr
      in
      Error_binop {
        err_binop_left_aliases = l_aliases_on;
        err_binop_right_aliases = r_aliases_on;
        err_binop_left_val = l_value;
        err_binop_right_val = r_value;
        err_binop_operation = constraint_expr;
      }
    end
  | Error.Odefa_error.Error_match err ->
    begin
      let () = print_endline "Natodefa Match Error!" in
      let aliases = err.err_match_aliases in
      Error_match {
        err_match_aliases = odefa_to_on_aliases aliases;
        err_match_val = odefa_to_on_value aliases;
        err_match_expected = odefa_to_on_type err.err_match_expected;
        err_match_actual = odefa_to_on_type err.err_match_actual;
      }
    end
  | Error.Odefa_error.Error_value err ->
    begin
      let aliases = err.err_value_aliases in
      match err_loc_option with
      | None ->
        let () = print_endline "Natodefa Value Error!" in
        Error_value {
          err_value_aliases = odefa_to_on_aliases aliases;
          err_value_val = odefa_to_on_value aliases;
        }
      | Some err_loc ->
        let () = print_endline "Natodefa Type Error!" in
        let expected_type = Ton_to_on_maps.IntermediateExpr_map.find err_loc ton_on_maps.sem_to_syn in
        Error_natodefa_type {
          err_type_aliases = odefa_to_on_aliases aliases;
          err_type_val = odefa_to_on_value aliases;
          err_type_expected = expected_type;
          err_type_actual = expected_type;
        }
    end
;;