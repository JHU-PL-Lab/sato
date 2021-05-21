(** This module defines basic data types used by the symbolic interpreter. *)

open Batteries;;
open Jhupllib;;
open Odefa_ast;;

open Ast;;
open Ast_pp;;
open Pp_utils;;

(* **** Symbol **** *)

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

(* **** Abort info **** *)

type abort_value = {
  (** The identifier of the conditional clause the abort clause
      is nested in. *)
  abort_conditional_ident : ident;

  (** The predicate of the conditional clauses the abort clause
      is nested in. *)
  abort_predicate_ident : ident;

  (** The branch of the conditional clause that the abort clause
      is nested in. *)
  abort_conditional_branch : bool;
}
[@@ deriving eq, ord, show]
;;

(* **** Lookup stack **** *)

(** The type of elements on a lookup stack. The lookup stack is
    essentially a continuation stack like in DDPA, and for now
    both variable names and labels can appear on the lookup stack *)

type lookup_stack_element = 
  | LookupVar of Ident.t
  | LookupLabel of ident
[@@ deriving eq, ord, show]
;;
(* 
let pp_lookup_stack_element formatter e = 
  match e with
  | LookupVar (Ident x) -> Format.pp_print_string formatter x
  | LookupLabel (Ident l) -> Format.pp_print_string formatter l

let show_lookup_stack_element = pp_to_string pp_lookup_stack_element;; *)
