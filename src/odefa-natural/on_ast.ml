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

(* A tag indicating the constructor can appear only in phase one *)
(* type with_syntactic_type;; *)

(* A tag indicating that the constructor can appear at any phase *)
(* type no_syntactic_type;; *)

type variant_label = Variant_label of string [@@deriving eq, ord, show, to_yojson]

type syntactic_only = [ `Syntactic ]

type 'a syntactic_and_semantic = [< `Syntactic | `Semantic ] as 'a 

type type_sig =
  | TopType
  | IntType
  | BoolType
  | FunType
  | RecType of Ident_set.t
  | ListType
  | VariantType of variant_label
  | UntouchedType of string
  [@@ deriving eq, ord, show, to_yojson]

type pattern = AnyPat | IntPat | BoolPat | FunPat
            | RecPat of (ident option) Ident_map.t
            | StrictRecPat of (ident option) Ident_map.t
            | VariantPat of variant_label * ident
            | VarPat of ident
            | EmptyLstPat | LstDestructPat of ident * ident
            | UntouchedPat of string
            [@@ deriving eq, ord, show, to_yojson]

type predicate = syntactic_only typed_expr

and 'a funsig = Funsig of ident * ident list * 'a typed_expr

and 'a typed_expr =
  | Int : int -> 'a typed_expr 
  | Bool : bool -> 'a typed_expr
  | Var : ident -> 'a typed_expr
  | Function : (ident list * 'a typed_expr) -> 'a typed_expr 
  | Input : 'a typed_expr
  | Appl : ('a typed_expr * 'a typed_expr) -> 'a typed_expr
  | Let : (ident * 'a typed_expr * 'a typed_expr) -> 'a typed_expr
  | LetRecFun : ('a funsig list * 'a typed_expr) -> 'a typed_expr  
  | LetFun : ('a funsig * 'a typed_expr) -> 'a typed_expr  
  | LetWithType : (ident * 'a typed_expr * 'a typed_expr * 'a typed_expr) -> 'a syntactic_and_semantic typed_expr
  | LetRecFunWithType : ('a funsig list * 'a typed_expr * 'a typed_expr list) -> 'a syntactic_and_semantic typed_expr
  | LetFunWithType : ('a funsig * 'a typed_expr * 'a typed_expr) -> 'a syntactic_and_semantic typed_expr
  | Plus : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Minus : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Times : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Divide : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Modulus : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Equal : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Neq : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | LessThan : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Leq : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | GreaterThan : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Geq : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | And : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Or : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Not : 'a typed_expr -> 'a typed_expr 
  | If : ('a typed_expr * 'a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Record : ('a typed_expr Ident_map.t) -> 'a typed_expr 
  | RecordProj : ('a typed_expr * label) -> 'a typed_expr
  | Match : ('a typed_expr * (pattern * 'a typed_expr) list) -> 'a typed_expr
  | VariantExpr : (variant_label * 'a typed_expr) -> 'a typed_expr
  | List : 'a typed_expr list -> 'a typed_expr 
  | ListCons : ('a typed_expr * 'a typed_expr) -> 'a typed_expr 
  | Assert : 'a typed_expr -> 'a typed_expr 
  | Assume : 'a typed_expr -> 'a typed_expr 
  | Untouched : string -> 'a typed_expr
  (* Type expressions *)
  | TypeVar : ident -> syntactic_only typed_expr
  | TypeInt : syntactic_only typed_expr
  | TypeBool : syntactic_only typed_expr
  | TypeRecord : (syntactic_only typed_expr) Ident_map.t -> syntactic_only typed_expr
  | TypeList : syntactic_only typed_expr -> syntactic_only typed_expr
  | TypeArrow : (syntactic_only typed_expr * syntactic_only typed_expr) -> syntactic_only typed_expr
  | TypeArrowD : ((ident * syntactic_only typed_expr) * syntactic_only typed_expr) -> syntactic_only typed_expr
  | TypeSet : (syntactic_only typed_expr) * predicate -> syntactic_only typed_expr
  | TypeUnion : (syntactic_only typed_expr * syntactic_only typed_expr) -> syntactic_only typed_expr
  | TypeIntersect : (syntactic_only typed_expr * syntactic_only typed_expr) -> syntactic_only typed_expr
  | TypeRecurse : (ident * syntactic_only typed_expr) -> syntactic_only typed_expr
  | TypeUntouched : string -> syntactic_only typed_expr

type syn_type_natodefa = syntactic_only typed_expr

type sem_type_natodefa = [ `Semantic ] typed_expr

type core_natodefa = [` Core ] typed_expr

let rec equal_funsig: type a. a funsig -> a funsig -> bool =
        fun (Funsig (id1, params1, fe1)) (Funsig (id2, params2, fe2)) ->
        (id1 = id2) && (List.eq equal_ident params1 params2) && (equal_typed_expr fe1 fe2)

and equal_typed_expr: type a. a typed_expr -> a typed_expr -> bool = 
  fun e1 e2 ->
  match e1, e2 with  
  | Int n1, Int n2 -> n1 = n2 
  (* | Int _, _ -> false *)
  | Bool b1, Bool b2 -> b1 = b2
  (* | Bool _, _ -> false *)
  | Input, Input -> true
  (* | Input, _ -> false *)
  | Var x1, Var x2 -> x1 = x2
  (* | Var _, _ -> false *)
  | List l1, List l2 -> 
    List.eq equal_typed_expr l1 l2
  (* | List _, _ -> false *)
  | Record r1, Record r2 -> 
    Ident_map.equal equal_typed_expr r1 r2
  (* | Record _, _ -> false *)
  | Untouched s1, Untouched s2 -> s1 = s2
  (* | Untouched _, _ -> false *)
  | Function (id_lst1, fun_body1), Function (id_lst2, fun_body2) -> 
    (List.eq equal_ident id_lst1 id_lst2) && (equal_typed_expr fun_body1 fun_body2)
  (* | Function _, _ -> false *)
  | Let (x1, xe1, e1), Let (x2, xe2, e2) ->
    (x1 = x2) && (equal_typed_expr xe1 xe2) && (equal_typed_expr e1 e2)
  (* | Let _, _ -> false *)
  | LetFun (f1, e1), LetFun (f2, e2) -> 
    (equal_funsig f1 f2) && (equal_typed_expr e1 e2)
  (* | LetFun _, _ -> false *)
  | LetRecFun (sig_lst1, e1), LetRecFun (sig_lst2, e2) ->
    (List.eq equal_funsig sig_lst1 sig_lst2) && 
    (equal_typed_expr e1 e2)
  (* | LetRecFun _, _ -> false *)
  | LetWithType (x1, xe1, e1, t1), LetWithType (x2, xe2, e2, t2) ->
    (x1 = x2) && (equal_typed_expr xe1 xe2) && 
    (equal_typed_expr e1 e2) && (equal_typed_expr t1 t2)
  (* | LetWithType _, _ -> false *)
  | LetFunWithType (f1, e1, t1), LetFunWithType (f2, e2, t2) ->
    (equal_funsig f1 f2) && 
    (equal_typed_expr e1 e2) && 
    (equal_typed_expr t1 t2)
  (* | LetFunWithType _, _ -> false *)
  | LetRecFunWithType (sig_lst1, e1, t1), LetRecFunWithType (sig_lst2, e2, t2) ->
    (List.eq equal_funsig sig_lst1 sig_lst2) && 
    (equal_typed_expr e1 e2) && 
    (List.eq equal_typed_expr t1 t2)
  (* | LetRecFunWithType _, _ -> false *)
  | Match (me1, pe_lst1), Match (me2, pe_lst2) ->
    let eq_pe (p1, e1) (p2, e2) = 
      p1 = p2 && equal_typed_expr e1 e2
    in
    (equal_typed_expr me1 me2) && 
    List.eq eq_pe pe_lst1 pe_lst2
  (* | Match _, _ -> false *)
  | If (cond1, tb1, fb1), If (cond2, tb2, fb2) ->
    (equal_typed_expr cond1 cond2) && 
    (equal_typed_expr tb1 tb2) &&
    (equal_typed_expr fb1 fb2)
  (* | If _, _ -> false *)
  | Or (lop1, rop1), Or (lop2, rop2)
  | And (lop1, rop1), And (lop2, rop2)
  | Equal (lop1, rop1), Equal (lop2, rop2)
  | Neq (lop1, rop1), Neq (lop2, rop2)
  | LessThan (lop1, rop1), LessThan (lop2, rop2)
  | Leq (lop1, rop1), Leq (lop2, rop2) 
  | GreaterThan (lop1, rop1), GreaterThan (lop2, rop2)
  | Geq (lop1, rop1), Geq (lop2, rop2)
  | Appl (lop1, rop1), Appl (lop2, rop2)
  | Plus (lop1, rop1), Plus (lop2, rop2)
  | Minus (lop1, rop1), Minus (lop2, rop2)
  | Times (lop1, rop1), Times (lop2, rop2)
  | Divide (lop1, rop1), Divide (lop2, rop2) 
  | Modulus (lop1, rop1), Modulus (lop2, rop2) 
  | ListCons (lop1, rop1), ListCons (lop2, rop2) ->
    (equal_typed_expr lop1 lop2) && 
    (equal_typed_expr rop1 rop2) 
  (* | Or _, _
  | And _, _
  | Equal _, _
  | Neq _, _
  | LessThan _, _
  | Leq _, _ 
  | GreaterThan _, _
  | Geq _, _
  | Appl _, _
  | Plus _, _
  | Minus _, _
  | Times _, _
  | Divide _, _ 
  | Modulus _, _ 
  | ListCons _, _ -> false *)
  | Assert e1, Assert e2
  | Assume e1, Assume e2
  | Not e1, Not e2 ->
    equal_typed_expr e1 e2
  | VariantExpr (l1, e1), VariantExpr (l2, e2) -> 
    (l1 = l2) && (equal_typed_expr e1 e2)
  | RecordProj (e1, l1), RecordProj (e2, l2) -> 
    (l1 = l2) && (equal_typed_expr e1 e2)
  (* Type expressions *)
  | TypeVar x1, TypeVar x2 -> x1 = x2
  | TypeInt, TypeInt | TypeBool, TypeBool -> true 
  | TypeRecord t1, TypeRecord t2 -> 
    Ident_map.equal equal_typed_expr t1 t2
  | TypeList t1, TypeList t2 ->
    equal_typed_expr t1 t2
  | TypeArrow (lt1, rt1), TypeArrow (lt2, rt2) 
  | TypeUnion (lt1, rt1), TypeUnion (lt2, rt2)
  | TypeIntersect (lt1, rt1), TypeUnion (lt2, rt2) 
  | TypeSet (lt1, rt1), TypeSet (lt2, rt2) ->
    (equal_typed_expr lt1 lt2) && (equal_typed_expr rt1 rt2)
  | TypeArrowD ((id1, lt1), rt1), TypeArrowD ((id2, lt2), rt2) ->
    (id1 = id2) &&
    (equal_typed_expr lt1 lt2) && 
    (equal_typed_expr rt1 rt2)
  | TypeRecurse (x1, t1), TypeRecurse (x2, t2) ->
    (x1 = x2) && (t1 = t2)
  | TypeUntouched s1, TypeUntouched s2 -> s1 = s2
  | _ -> false 

let rec compare_funsig: type a. a funsig -> a funsig -> int =
    fun (Funsig (id1, params1, fe1)) (Funsig (id2, params2, fe2)) ->
    (compare id1 id2) + (List.compare compare_ident params1 params2) + (compare_typed_expr fe1 fe2)

and compare_typed_expr : type a. a typed_expr -> a typed_expr -> int = 
  fun e1 e2 ->
    match e1, e2 with  
    | Int n1, Int n2 -> compare n1 n2
    | Bool b1, Bool b2 -> compare b1 b2
    | Input, Input -> 0
    | Var x1, Var x2 -> compare x1 x2
    | List l1, List l2 -> 
      List.compare compare_typed_expr l1 l2
    | Record r1, Record r2 -> 
      Ident_map.compare compare_typed_expr r1 r2
    | Untouched s1, Untouched s2 -> compare s1 s2
    | Function (id_lst1, fun_body1), Function (id_lst2, fun_body2) -> 
      (List.compare compare_ident id_lst1 id_lst2) + (compare_typed_expr fun_body1 fun_body2)
    | Let (x1, xe1, e1), Let (x2, xe2, e2) ->
      (compare x1 x2) + (compare_typed_expr xe1 xe2) + (compare_typed_expr e1 e2)
    | LetFun (f1, e1), LetFun (f2, e2) -> 
      (compare_funsig f1 f2) + (compare_typed_expr e1 e2)
    | LetRecFun (sig_lst1, e1), LetRecFun (sig_lst2, e2) ->
      (List.compare compare_funsig sig_lst1 sig_lst2) + 
      (compare_typed_expr e1 e2)
    | LetWithType (x1, xe1, e1, t1), LetWithType (x2, xe2, e2, t2) ->
      (compare x1 x2) + (compare_typed_expr xe1 xe2) + 
      (compare_typed_expr e1 e2) + (compare_typed_expr t1 t2)
    | LetFunWithType (f1, e1, t1), LetFunWithType (f2, e2, t2) ->
      (compare_funsig f1 f2) + 
      (compare_typed_expr e1 e2) + 
      (compare_typed_expr t1 t2)
    | LetRecFunWithType (sig_lst1, e1, t1), LetRecFunWithType (sig_lst2, e2, t2) ->
      (List.compare compare_funsig sig_lst1 sig_lst2) + 
      (compare_typed_expr e1 e2) + 
      (List.compare compare_typed_expr t1 t2)
    | Match (me1, pe_lst1), Match (me2, pe_lst2) ->
      let compare_pe (p1, e1) (p2, e2) = 
        compare_pattern p1 p2 + compare_typed_expr e1 e2
      in
      (compare_typed_expr me1 me2) + 
      List.compare compare_pe pe_lst1 pe_lst2
    | If (cond1, tb1, fb1), If (cond2, tb2, fb2) ->
      (compare_typed_expr cond1 cond2) + 
      (compare_typed_expr tb1 tb2) +
      (compare_typed_expr fb1 fb2)
    | Or (lop1, rop1), Or (lop2, rop2)
    | And (lop1, rop1), And (lop2, rop2)
    | Equal (lop1, rop1), Equal (lop2, rop2)
    | Neq (lop1, rop1), Neq (lop2, rop2)
    | LessThan (lop1, rop1), LessThan (lop2, rop2)
    | Leq (lop1, rop1), Leq (lop2, rop2) 
    | GreaterThan (lop1, rop1), GreaterThan (lop2, rop2)
    | Geq (lop1, rop1), Geq (lop2, rop2)
    | Appl (lop1, rop1), Appl (lop2, rop2)
    | Plus (lop1, rop1), Plus (lop2, rop2)
    | Minus (lop1, rop1), Minus (lop2, rop2)
    | Times (lop1, rop1), Times (lop2, rop2)
    | Divide (lop1, rop1), Divide (lop2, rop2) 
    | Modulus (lop1, rop1), Modulus (lop2, rop2) 
    | ListCons (lop1, rop1), ListCons (lop2, rop2) ->
      (compare_typed_expr lop1 lop2) + 
      (compare_typed_expr rop1 rop2) 
    | Assert e1, Assert e2
    | Assume e1, Assume e2
    | Not e1, Not e2 ->
      compare_typed_expr e1 e2
    | VariantExpr (l1, e1), VariantExpr (l2, e2) -> 
      (compare l1 l2) + (compare_typed_expr e1 e2)
    | RecordProj (e1, l1), RecordProj (e2, l2) -> 
      (compare l1 l2) + (compare_typed_expr e1 e2)
    (* Type expressions *)
    | TypeVar x1, TypeVar x2 -> compare x1 x2
    | TypeInt, TypeInt | TypeBool, TypeBool -> 0 
    | TypeRecord t1, TypeRecord t2 -> 
      Ident_map.compare compare_typed_expr t1 t2
    | TypeList t1, TypeList t2 ->
      compare_typed_expr t1 t2
    | TypeArrow (lt1, rt1), TypeArrow (lt2, rt2) 
    | TypeUnion (lt1, rt1), TypeUnion (lt2, rt2)
    | TypeIntersect (lt1, rt1), TypeUnion (lt2, rt2) 
    | TypeSet (lt1, rt1), TypeSet (lt2, rt2) ->
      (compare_typed_expr lt1 lt2) + (compare_typed_expr rt1 rt2)
    | TypeArrowD ((id1, lt1), rt1), TypeArrowD ((id2, lt2), rt2) ->
      (compare id1 id2) +
      (compare_typed_expr lt1 lt2) + 
      (compare_typed_expr rt1 rt2)
    | TypeRecurse (x1, t1), TypeRecurse (x2, t2) ->
      (compare x1 x2) + (compare t1 t2)
    | TypeUntouched s1, TypeUntouched s2 -> compare s1 s2
    | _ -> 1

module type Expr = sig
  type t;;
  val equal : t -> t -> bool;;
  val compare : t -> t -> int;;
end;;

module TypedExpr : (Expr with type t = syn_type_natodefa) = struct
  type t = syn_type_natodefa;;
  let equal = equal_typed_expr;;
  let compare = compare_typed_expr;;
end;;

module IntermediateExpr : (Expr with type t = sem_type_natodefa) = struct
  type t = sem_type_natodefa;;
  let equal = equal_typed_expr;;
  let compare = compare_typed_expr;;
end;;

module CoreExpr : (Expr with type t = core_natodefa) = struct
  type t = core_natodefa;;
  let equal = equal_typed_expr;;
  let compare = compare_typed_expr;;
end;;

module Pattern = struct
  type t = pattern;;
  let equal = equal_pattern;;
  let compare = compare_pattern;;
  let to_yojson = pattern_to_yojson;;
end;;

(* Takes [expr] as an argument.  Returns the relative precedence of the
    expression.  Higher ints correspond to higher precedences. *)
let expr_precedence_p1 : type a. a typed_expr -> int =
  fun expr ->
  match expr with
  | Function _ | Let _ | LetFun _ | LetRecFun _ 
  | LetWithType _ | LetFunWithType _ | LetRecFunWithType _ | Match _ -> 0
  | If _ -> 1
  | Or _ -> 2
  | And _ -> 3
  | Not _ -> 4
  | Equal _ | Neq _ | LessThan _ | Leq _ | GreaterThan _ | Geq _ -> 5
  | ListCons _ -> 6
  | Plus _ | Minus _ -> 7
  | Times _ | Divide _ | Modulus _ -> 8
  | Assert _ | Assume _ | VariantExpr _ -> 9
  | Appl _ -> 10
  | RecordProj _ -> 11
  | Int _ | Bool _ | Input | Var _ | List _ | Record _ | Untouched _ -> 12
  (* TODO: For now, all type expressions will have the lowest precedence coz I'm lazy and don't wanna think about it *)
  | TypeVar _ | TypeInt | TypeBool | TypeRecord _ | TypeList _
  | TypeArrow _ | TypeArrowD _ | TypeSet _ | TypeUnion _
  | TypeIntersect _ | TypeRecurse _ | TypeUntouched _ -> 13
;;

(** Takes expressions [e1] and [e2] as arguments.  Returns 0 if the two
    expressions have equal precedence, a negative int if [e1] has lower
    precedence than [e2], and a positive int if [e1] has higher precedence. *)
let expr_precedence_cmp e1 e2 = (expr_precedence_p1 e1) - (expr_precedence_p1 e2);;