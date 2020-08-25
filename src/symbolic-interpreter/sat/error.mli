open Jhupllib;;

open Odefa_ast;;
open Ast;;

exception Parse_failure of string;;

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

module Ident : Error_ident with type t = Ast.ident;;
module Value : Error_value with type t = Ast.clause_body;;
module Binop : Error_binop with type t = (Ast.clause_body * Ast.binary_operator * Ast.clause_body);;
module Clause : Error_clause with type t = Ast.clause;;
module Type : Error_type with type t = Ast.type_sig;;

module type Error = sig
  module Error_ident : Error_ident;;
  module Error_value : Error_value;;
  module Error_binop : Error_binop;;
  module Error_clause : Error_clause;;
  module Error_type : Error_type;;

  type ident;;
  type value;;
  type binop;;
  type clause;;
  type type_sig;;

  type error_binop = {
    (** The alias chain leading up to the left value. *)
    err_binop_left_aliases : ident list;
    (** The alias chain leading up to the right value. *)
    err_binop_right_aliases : ident list;
    (** The value of the left side of the binop. *)
    err_binop_left_val : value;
    (** The value of the right side of the binop. *)
    err_binop_right_val : value;
    (** The operator (e.g. +, -, and, or, ==, etc. *)
    err_binop_operation : binop;
    (** The clause representing the operation being instrumented. *)
    err_binop_clause : clause;
  }

  type error_match = {
    (** The alias chain of the ident begin matched upon. *)
    err_match_aliases : ident list;
    (** The value of the ident that is being matched. *)
    err_match_val : value;
    (** The expected type of the symbol being matched. *)
    err_match_expected : type_sig;
    (** The actual type of the symbol being matched. *)
    err_match_actual : type_sig;
    (** The clause respresenting the operation being instrumented. *)
    err_match_clause : clause;
  }

  type error_value = {
    (** The alias chain defining the boolean value. *)
    err_value_aliases : ident list;
    (** The boolean value (should always be false). *)
    err_value_val : value;
    (** The clause respresenting the operation being instrumented. *)
    err_value_clause : clause;
  }

  type t =
    | Error_binop of error_binop
    | Error_match of error_match
    | Error_value of error_value
  ;;

  val equal : t -> t -> bool;;

  val parse : string -> t;;

  val pp : t Pp_utils.pretty_printer;;

  val show : t -> string;;
end;;

module Make
    (Ident : Error_ident)
    (Value : Error_value)
    (Binop : Error_binop)
    (Clause : Error_clause)
    (Type : Error_type)
  (* : Error;; *)
  : (Error
      with type ident := Ident.t
      and type value := Value.t
      and type binop := Binop.t
      and type clause := Clause.t
      and type type_sig := Type.t)

(* ******************* *)

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

val parse_error : string -> error;;

val show : error -> string;;

module type Error_list = sig
  type t;;

  (** Create a new, empty error tree (i.e. has no errors at all). *)
  val empty : t;;

  (** Returns true if the error tree is empty, false otherwise. *)
  val is_empty : t -> bool;;

  (** Create an error tree that contains a single error leaf node. *)
  val singleton : error -> t;;

  (** Merge two error trees as if they are part of an AND operation.
      In an AND operation, all values must be true for the op to return true.
      Therefore if one error has a false value, the error tree is false. *)
  val add_and : t -> t -> t;;

  (** Merge two error trees as if they are part of an OR operation.
      In an OR operation, only one value needs to be true for the op to be true
      so only when all errors have a false value can the error tree be false. *)
  val add_or : t -> t -> t;;

  (** Create an error tree from a list of error trees (assuming all top-level
      predicates have a false value). *)
  val tree_from_error_list : t list -> t;;

  (** Flattens an error tree into a list structure. *)
  val flatten_tree : t -> error list;;

  (** String representation of the error tree. *)
  val to_string : t -> string;;

  (** Maps a function over the errors in an error tree. *)
  val map : (error -> error) -> t -> t;;

  (** Returns true if an error exists in the error tree, false otherwise. *)
  val mem : error -> t -> bool;;

  (** Same as mem, except that the first argument is a singleton error tree. *)
  val mem_singleton : t -> t -> bool;;

  (** Count the number of errors in the error tree. *)
  val count : t -> int;;
end;;

module Error_list : Error_list;;