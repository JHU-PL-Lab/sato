open Batteries;;
open Jhupllib;;

type label = Label of string [@@deriving eq, ord, show, to_yojson];;

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

type variant_label = Variant_label of string [@@deriving eq, ord, show, to_yojson]

type type_sig =
  | TopType
  | IntType
  | BoolType
  | FunType
  | RecType of Ident_set.t
  | ListType
  | VariantType of variant_label
[@@ deriving eq, ord, show, to_yojson]

and type_decl = 
  (* | TypeVar of ident *)
  | TypeInt
  | TypeBool
  | TypeRecord of type_decl Ident_map.t
  | TypeList of type_decl
  | TypeUnion of type_decl * type_decl
  | TypeIntersect of type_decl * type_decl
  | TypeArrow of type_decl * type_decl
  | TypeSet of type_decl * predicate
  (* | TypeRecurse of ident * type_decl *)
[@@ deriving eq, ord, show, to_yojson]

and predicate = Predicate of expr
[@@ deriving eq, ord, show, to_yojson]

and funsig = Funsig of ident * ident list * expr

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
  | LetWithType of ident * expr * expr * type_decl
  | LetRecFunWithType of funsig list * expr * type_decl list
  | LetFunWithType of funsig * expr * type_decl
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
  | Assert of expr | Assume of expr
  | SetCell of expr * expr | GetCell of expr 
  | NewCell of expr
  (* | Protected of expr *)
[@@deriving eq, ord, to_yojson]
;;

type state_mode = Stateful | Stateless;;

type program = Program of expr * state_mode;;

module Expr = struct
  type t = expr;;
  let equal = equal_expr;;
  let compare = compare_expr;;
  let to_yojson = expr_to_yojson;;
end;;

module Pattern = struct
  type t = pattern;;
  let equal = equal_pattern;;
  let compare = compare_pattern;;
  let to_yojson = pattern_to_yojson;;
end;;

(** Takes [expr] as an argument.  Returns the relative precedence of the
    expression.  Higher ints correspond to higher precedences. *)
let expr_precedence expr =
  match expr with
  | Function _ | Let _ | LetFun _ | LetRecFun _ | LetWithType _ | LetFunWithType _ | LetRecFunWithType _ | Match _ -> 0
  | If _ -> 1
  | SetCell _ -> 2
  | Or _ -> 3
  | And _ -> 4
  | Not _ | GetCell _ | NewCell _ -> 5
  | Equal _ | Neq _ | LessThan _ | Leq _ | GreaterThan _ | Geq _ -> 6
  | ListCons _ -> 7
  | Plus _ | Minus _ -> 8
  | Times _ | Divide _ | Modulus _ -> 9
  | Assert _ | Assume _ | VariantExpr _ -> 10
  | Appl _ -> 11
  | RecordProj _ -> 12
  | Int _ | Bool _ | Input | Var _ | List _ | Record _ -> 13
;;

(** Takes expressions [e1] and [e2] as arguments.  Returns 0 if the two
    expressions have equal precedence, a negative int if [e1] has lower
    precedence than [e2], and a positive int if [e1] has higher precedence. *)
let expr_precedence_cmp e1 e2 = (expr_precedence e1) - (expr_precedence e2);;