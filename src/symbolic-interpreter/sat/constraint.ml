open Batteries;;
open Jhupllib;;

open Odefa_ast;;

open Ast;;
open Ast_pp;;
open Interpreter_types;;

type symbol_type =
  | IntSymbol
  | BoolSymbol
  | RecordSymbol
  | FunctionSymbol
  | BottomSymbol
[@@deriving eq, ord, to_yojson]
;;

let pp_symbol_type formatter t =
  match t with
  | IntSymbol -> Format.pp_print_string formatter "int"
  | BoolSymbol -> Format.pp_print_string formatter "bool"
  | RecordSymbol -> Format.pp_print_string formatter "record"
  | FunctionSymbol -> Format.pp_print_string formatter "function"
  | BottomSymbol -> Format.pp_print_string formatter "bottom"
;;

let show_symbol_type = Pp_utils.pp_to_string pp_symbol_type;;

(** A representation of runtime values in terms of symbols. *)
type value =
  | Int of int
  | Bool of bool
  | Function of function_value
  | Record of symbol Ident_map.t
[@@deriving eq, ord, to_yojson]
;;

let pp_value formatter v =
  match v with
  | Int n -> Format.pp_print_int formatter n
  | Bool b -> Format.pp_print_bool formatter b
  | Function(Function_value(x,_)) ->
    Format.fprintf formatter "fun %a -> ..." pp_var x
  | Record(m) ->
    Pp_utils.pp_map pp_ident pp_symbol Ident_map.enum formatter m
;;

let show_value = Pp_utils.pp_to_string pp_value;;

type value_def =
  | Value of value
  | Input
  | Binop of symbol * binary_operator * symbol
  | Match of symbol * pattern
  | Abort
[@@ deriving eq, ord, to_yojson]
;;

let pp_value_def formatter val_src =
  match val_src with
  | Value v -> pp_value formatter v
  | Input -> Format.pp_print_string formatter "input"
  | Binop (x1, op, x2) ->
    let (Symbol (i1, _)) = x1 in
    let (Symbol (i2, _)) = x2 in
    Format.fprintf formatter "%a %a %a"
      pp_ident i1 pp_binary_operator op pp_ident i2
  | Match (x, pattern) ->
    let (Symbol (ident, _)) = x in
    Format.fprintf formatter "%a ~ %a"
      pp_ident ident pp_pattern pattern
  | Abort -> Format.pp_print_string formatter "abort"
;;

let show_value_def = Pp_utils.pp_to_string pp_value_def;;

type t =
  | Constraint_value of symbol * value (* x = v *)
  | Constraint_value_clause of symbol * value (* x = v *)
  | Constraint_input of symbol (* x = input *)
  | Constraint_alias of symbol * symbol (* x = x *)
  | Constraint_binop of symbol * symbol * binary_operator * symbol (* x = x + x *)
  | Constraint_projection of symbol * symbol * ident (* x = x.l *)
  | Constraint_match of symbol * symbol * pattern (* x = x ~ p *)
  | Constraint_type of symbol * symbol_type (* x : t *)
  | Constraint_stack of Relative_stack.concrete_stack (* stack = C *)
  | Constraint_abort of symbol (* x = abort *)
[@@deriving eq, ord, to_yojson]
;;

let pp formatter sc =
  match sc with
  | Constraint_value(x,v) ->
    Format.fprintf formatter "%a = %a" pp_symbol x pp_value v
  | Constraint_value_clause(x,v) ->
    Format.fprintf formatter "%a = %a" pp_symbol x pp_value v
  | Constraint_input(x) ->
    Format.fprintf formatter "%a = input" pp_symbol x
  | Constraint_alias(x,x') ->
    Format.fprintf formatter "%a = %a" pp_symbol x pp_symbol x'
  | Constraint_binop(x,x',op,x'') ->
    Format.fprintf formatter "%a = %a %a %a"
      pp_symbol x pp_symbol x' pp_binary_operator op pp_symbol x''
  | Constraint_projection(x,x',lbl) ->
    Format.fprintf formatter "%a = %a.%a"
      pp_symbol x pp_symbol x' pp_ident lbl
  | Constraint_match(x,x',p) ->
    Format.fprintf formatter "%a = %a ~ %a"
      pp_symbol x pp_symbol x' pp_pattern p
  | Constraint_type(x,t) ->
    Format.fprintf formatter "%a ~ %a" pp_symbol x pp_symbol_type t
  | Constraint_stack(s) ->
    Format.fprintf formatter "stack = %a" Relative_stack.pp_concrete_stack s
  | Constraint_abort(x) ->
    Format.fprintf formatter "%a = abort" pp_symbol x
;;

let show = Pp_utils.pp_to_string pp;;

(* Need to create an equivalent internal type for namespacing reasons. *)
type _t = t [@@deriving ord, show, to_yojson];;
module Symbolic_constraint = struct
  type t = _t [@@deriving ord, show, to_yojson];;
end;;

module Set = struct
  module S = BatSet.Make(Symbolic_constraint);;
  include S;;
  include Pp_utils.Set_pp(S)(Symbolic_constraint);;
  include Yojson_utils.Set_to_yojson(S)(Symbolic_constraint);;
end;;

module Map = struct
  module M = BatMap.Make(Symbolic_constraint);;
  include M;;
  include Pp_utils.Map_pp(M)(Symbolic_constraint);;
  include Yojson_utils.Map_to_yojson(M)(Symbolic_constraint);;
end;;
