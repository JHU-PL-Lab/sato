(** This module defines basic data types used by the symbolic interpreter. *)

open Batteries;;
open Jhupllib;;
open Odefa_ast;;

open Ast;;
open Ast_pp;;
open Pp_utils;;

(* Symbol *)

(** The type of a symbol in the symbolic interpreter.  This is essentially the
    type of a variable using a stack-costack pair rather than a freshening
    stack. *)
type symbol =
  | Symbol of Ident.t * Relative_stack.t
[@@deriving eq, ord, to_yojson]
;;

let pp_symbol : symbol pretty_printer =
  fun formatter symbol ->
  match symbol with
  | Symbol(x,relstack) ->
    pp_ident formatter x;
    Relative_stack.pp formatter relstack;
;;
let show_symbol = pp_to_string pp_symbol;;

module Symbol = struct
  type t = symbol [@@deriving eq, ord, show, to_yojson];;
end;;

module Symbol_set = struct
  module M = Set.Make(Symbol);;
  include M;;
  include Pp_utils.Set_pp(M)(Symbol);;
  include Yojson_utils.Set_to_yojson(M)(Symbol);;
end;;

module Symbol_map = struct
  module M = Map.Make(Symbol);;
  include M;;
  include Pp_utils.Map_pp(M)(Symbol);;
  include Yojson_utils.Map_to_yojson(M)(Symbol);;
end;;

(* Abort info *)

type abort_value = {
  (** The sequence of conditional clauses that, if the false path is always
      taken, lead to this abort point. *)
  abort_conditional_clauses : clause list;

  (** The predicates of the conditional clauses, in the order that the clauses
      are nested. *)
  abort_predicate_idents : ident list;

  (** The return clauses, ie. the last clauses of the expression, of the true
      branches of the conditional clauses. *)
  abort_return_clauses : clause list;
}
[@@ deriving eq, ord, show]
;;