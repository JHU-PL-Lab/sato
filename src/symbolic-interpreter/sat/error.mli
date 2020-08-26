open Jhupllib;;

open Odefa_ast;;

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
module Binop : Error_binop with type t =
  (Ast.clause_body * Ast.binary_operator * Ast.clause_body);;
module Type : Error_type with type t = Ast.type_sig;;

module type Error = sig
  module Error_ident : Error_ident;;
  module Error_value : Error_value;;
  module Error_binop : Error_binop;;
  module Error_type : Error_type;;

  type ident;;
  type value;;
  type binop;;
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
  }

  type error_value = {
    (** The alias chain defining the boolean value. *)
    err_value_aliases : ident list;
    (** The boolean value (should always be false). *)
    err_value_val : value;
  }

  type t =
    | Error_binop of error_binop
    | Error_match of error_match
    | Error_value of error_value
  ;;

  (** Returns true if two errors are equal, false otherwise. *)
  val equal : t -> t -> bool;;

  (** Parse a string into an error.  Used primarily for testing. *)
  val parse : string -> t;;

  (** Pretty-printer for an error. *)
  val pp : t Pp_utils.pretty_printer;;

  (** Show the error as a string. *)
  val show : t -> string;;
end;;

module Make
    (Ident : Error_ident)
    (Value : Error_value)
    (Binop : Error_binop)
    (Type : Error_type)
  : (Error
      with type ident := Ident.t
      and type value := Value.t
      and type binop := Binop.t
      and type type_sig := Type.t)

module Odefa_error
  : (Error
      with type ident := Ident.t
      and type value := Value.t
      and type binop := Binop.t
      and type type_sig := Type.t)
;;