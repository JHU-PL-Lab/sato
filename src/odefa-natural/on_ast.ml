open Batteries;;
open Jhupllib;;

type label = Label of string [@@deriving eq, ord, show];;

type ident = Ident of string [@@deriving eq, ord, show, to_yojson];;

module Ident =
struct
  type t = ident;;
  let equal = equal_ident;;
  let compare = compare_ident;;
  let pp = pp_ident;;
  let show = show_ident;;
  let to_yojson = ident_to_yojson;;
  let hash = Hashtbl.hash
end;;

module Ident_set = struct
  module M = Set.Make(Ident);;
  include M;;
  include Pp_utils.Set_pp(M)(Ident);;
  include Yojson_utils.Set_to_yojson(M)(Ident);;
end;;

module Ident_map = struct
  module M = Map.Make(Ident);;
  include M;;
  include Pp_utils.Map_pp(M)(Ident);;
  include Yojson_utils.Map_to_yojson(M)(Ident);;
end;;

type variant_label = Variant_label of string [@@deriving eq, ord, show]

type funsig = Funsig of ident * ident list * expr

(* and variant_content = Variant of variant_label * pattern *)

and pattern = AnyPat | IntPat | BoolPat | FunPat
            | RecPat of (ident option) Ident_map.t
            | VariantPat of variant_label * ident
            | VarPat of ident
            | EmptyLstPat | LstDestructPat of ident * ident

and expr =
  | Int of int | Bool of bool
  | Var of ident | Function of ident list * expr
  | Input
  | Appl of expr * expr
  | Let of ident * expr * expr
  | LetRecFun of funsig list * expr | LetFun of funsig * expr
  | Plus of expr * expr | Minus of expr * expr
  | Times of expr * expr | Divide of expr * expr | Modulus of expr * expr
  | Equal of expr * expr | Neq of expr * expr
  | LessThan of expr * expr | Leq of expr * expr
  | GreaterThan of expr * expr | Geq of expr * expr
  | And of expr * expr | Or of expr * expr | Not of expr
  | If of expr * expr * expr
  | Record of expr Ident_map.t | RecordProj of expr * label
  | Match of expr * (pattern * expr) list
  | VariantExpr of variant_label * expr
  | List of expr list | ListCons of expr * expr
  | Assert of expr
[@@deriving eq, ord, show]
;;

module Expr = struct
  type t = expr;;
  let equal = equal_expr;;
  let compare = compare_expr;;
  let show = show_expr;;
end;;

module Expr_map = Map.Make(Expr);;