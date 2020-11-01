open Odefa_ast;;
open Odefa_symbolic_interpreter;;

open Odefa_natural;;

(** Raised when an expected answer fails to parse *)
exception Parse_failure of string;;

(** The interface of a generic answer, i.e. information that can be extracted
    from a run of the demand-driven symbolic evaluator. *)
module type Answer = sig
  (** The type of the answer *)
  type t;;

  (** A function to extract an answer from the result of a symbolic interpreter
      evaluation, given an expression and a particular stop variable. *)
  val answer_from_result :
    int -> Ast.expr -> Ast.ident -> Interpreter.evaluation_result -> t;;

  (** A function to parse an answer from a string. Mostly used for testing. *)
  val answer_from_string : string -> t;;

  (** Set the odefa/natodefa mappings as a global, which will be needed to
      remove any variables added during instrumentation, convert from odefa
      back to natodefa, etc. *)
  val set_odefa_natodefa_map : On_to_odefa_maps.t -> unit;;

  (** Convert the answer into a string. *)
  val show : ?show_steps:bool -> t -> string;;

  (** Count the number of answers in the data structure. *)
  val count : t -> int;;

  (** Number of (valid) answers in the list. *)
  val count_list : t list -> int;;

  (** True if generating an answer from the result is successful, false
      otherwise. *)
  val generation_successful : t -> bool;;

  (** Test to see if an expected answer is included within an answer produced
      by the program.  The expected answer is the first argument while the
      actual answer is the second argument; test_expected returns a boolean. *)
  val test_expected : t -> t -> bool;;

  val to_yojson : t -> Yojson.Safe.t;;
end;;

(** An input sequence for a single program flow of symbolic evaluation. *)
module Input_sequence : Answer;;

(** The type errors encountered for a single program flow of symbolic
    evaluation. *)
module Type_errors : Answer;;

(** The type errors encountered for a single natodefa program flow of
    symbolic evaluation. *)
module Natodefa_type_errors : Answer;;