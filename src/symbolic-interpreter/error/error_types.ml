open Odefa_ast;;

type error_binop = {
  (** The clause representing the operation being instrumented. *)
  err_binop_clause : Ast.clause;

  (** The operator (e.g. +, -, and, or, ==, etc. *)
  err_binop_operation : Ast.binary_operator;

  (** The value of the left side of the binop. *)
  err_binop_left_val : Ast.clause_body;

  (** The value of the right side of the binop. *)
  err_binop_right_val : Ast.clause_body;

  (** The alias chain leading up to the left value. *)
  err_binop_left_aliases : Ast.ident list;

  (** The alias chain leading up to the right value. *)
  err_binop_right_aliases : Ast.ident list;
}
[@@ deriving eq]
;;

type error_match = {
  (** The alias chain of the ident begin matched upon. *)
  err_match_aliases : Ast.ident list;

  (** The value of the ident that is being matched. *)
  err_match_value : Ast.clause_body;

  (** The clause respresenting the operation being instrumented. *)
  err_match_clause : Ast.clause;

  (** The expected type, according to the pattern. *)
  err_match_expected_type : Ast.type_sig;

  (** The actual type of the symbol being matched. *)
  err_match_actual_type : Ast.type_sig;
}
[@@ deriving eq]
;;

type error_value = {
  (** The alias chain defining the boolean value. *)
  err_value_aliases : Ast.ident list;

  (** The boolean value (should always be false). *)
  err_value_val : Ast.clause_body;

  (** The clause representing the operation being constrained. *)
  err_value_clause : Ast.clause;
}
[@@ deriving eq]
;;

type error =
  | Error_binop of error_binop
  | Error_match of error_match
  | Error_value of error_value
[@@ deriving eq]
;;