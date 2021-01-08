open Odefa_ast;;
open Odefa_ddpa;;

open Ast;;
open Interpreter_types;;

(** This type describes the information which must be in context during lookup. *)
type lookup_environment = {
  le_cfg : Ddpa_graph.ddpa_graph;
  (** The DDPA CFG to use during lookup. *)

  le_clause_mapping : clause Ident_map.t;
  (** A mapping from identifiers to the concrete clauses which define them. *)

  le_clause_predecessor_mapping : clause Ident_map.t;
  (** A mapping from clauses (represented by the identifier they define) to the
      concrete clauses which appear immediately *before* them.  The first clause
      in each expression does not appear in this map. *)

  le_function_parameter_mapping : function_value Ident_map.t;
  (** A mapping from function parameter variables to the functions which declare
      them. *)

  le_function_return_mapping : function_value Ident_map.t;
  (** A mapping from function return variables to the functions which declare
      them. *)

  le_abort_mapping : abort_value Ident_map.t;
  (** A mapping from abort clause identifiers to identifier information
    associated with the error. *)

  le_first_var : Ident.t;
  (** The identifier which represents the first defined variable in the
      program. *)
}
[@@deriving show]
;;

(** Given a program [expr] and its CFG [ddpa_graph], construct the lookup
    environment *)
val prepare_environment : Ddpa_graph.ddpa_graph -> expr -> lookup_environment;;

(** Given a program [expr], list its instrumenting conditionals (conditionals
    where at least one branch has an abort clause as its return clause) in
    the order it's listed in the program. *)
val list_instrument_conditionals : expr -> ident list;;