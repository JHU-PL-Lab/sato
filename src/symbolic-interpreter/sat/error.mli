open Odefa_ast;;
open Ast;;

open Constraint;;

exception Parse_failure of string;;

type error_binop = {
  (** The identifier of the binop clause. *)
  err_binop_ident : ident;

  (** The operator (e.g. +, -, and, or, ==, etc. *)
  err_binop_operation : binary_operator;

  (** The value of the left side of the binop. *)
  err_binop_left_val : value_source;

  (** The value of the right side of the binop. *)
  err_binop_right_val : value_source;
}
[@@ deriving show]
;;

type error_match = {
  (** The alias chain of the ident begin matched upon. *)
  err_match_aliases : ident list;

  (** The value of the ident that is being matched. *)
  err_match_value : clause;

  (** The clause that is being constrained by the abort's conditional. *)
  err_match_clause : clause;

  (** The expected type, according to the pattern. *)
  err_match_expected_type : type_sig;

  (** The actual type of the symbol being matched. *)
  err_match_actual_type : type_sig;
}
[@@ deriving show]
;;

type error =
  | Error_binop of error_binop
  | Error_match of error_match
;;

module type Error_tree = sig
  type t;;

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

  (** String representation of the error tree. *)
  val to_string : t -> string;;

  (** Create a new, empty error tree (i.e. has no errors at all). *)
  val empty : t;;

  (** Returns true if the error tree is empty, false otherwise. *)
  val is_empty : t -> bool;;

  (** Parses a string into an error tree *)
  val parse : string -> t;;

  (** Maps a function over the errors in an error tree. *)
  val map : (error -> error) -> t -> t;;
end;;

module Error_tree : Error_tree;;