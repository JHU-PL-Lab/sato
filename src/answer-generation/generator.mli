(**
   This module defines a process for generating test input sequences.
*)

open Odefa_ast;;
open Odefa_ddpa;;
open Odefa_symbolic_interpreter;;

open Generator_answer;;
open Generator_configuration;;

(** The interface of a generic answer generator.  The generator attempts to
    perform demand-driven symbolic interpretation, starting from an inital
    set of parameters, in order to derive answers to a question about the
    program (e.g. Does it have type errors? What input sequences can reach
    a particular variable?). *)
module type Generator = sig
  module Answer : Answer;;

  (** A record of fields that stay constant across multiple generation attempts
      on a single program.  These are stored for reference purposes (i.e. for
      use by auxillary functions), but not updated by the generator itself
      after initialization. *)
  type generator_reference =
    {
      (** The program being analyzed. *)
      gen_program : Ast.expr;

      (** The CFG of the program being analyzed. *)
      gen_cfg : Ddpa_graph.ddpa_graph;

      (** The exploration policy used by the symbolic interpreter. *)
      gen_exploration_policy : Interpreter.exploration_policy;

      (** The maximum number of steps taken by a particular evaluation.
          (A None value means an infinite number of steps can be taken.) *)
      gen_max_steps : int option;

      (** The maximum number of results that can be generated.
          (A None value means an infinite number of results can be generated.) *)
      gen_max_results : int option;
    }
  ;;

  (** Parameters to initialize answer generation. *)
  type generation_parameters = {
    (** Reference information about the program. *)
    gen_reference : generator_reference;

    (** The initial state of the evaluation. *)
    gen_evaluation : Interpreter.evaluation;

    (** The list of target variables (the name comes from the fact that these variables
        are the targets of program flow given a particular input sequence). *)
    gen_target_vars : Ast.ident list;
  }
  ;;

  (** The final result of generation. *)
  type generation_result = {
    (** The list of answers that were discovered during generation. *)
    gen_answers : Answer.t list;

    (** The number of answers discovered during generation (which must always
        be equal to the gen_answers list. *)
    gen_num_answers : int;

    (** Whether all possible evaluations have been exhausted, or if some
        evaluations could have continued if the maximum number of steps was
        not reached. *)
    gen_is_complete : bool;
  }
  ;;

  (** Creates the parameters for answer generation, which the generator will use in
      order to perform DDSE and generate answers.  The given optional integer is
      the maximum number of steps for an evaluation to take, starting from a
      particular variable in the var list (if none is given, generation may run
      forever, as it is non-deterministic).

      If the query is invalid (e.g. the target variable does not appear in the
      expression, or if no target variables are given, an exception is raised
      from the symbolic intepreter of type
      [Odefa_symbolic_interpreter.Interpreter.Invalid_query]. *)
  val create :
    ?exploration_policy:Interpreter.exploration_policy ->
    ?max_steps:(int option) ->
    ?max_results:(int option) ->
    configuration -> Ast.expr -> Ast.ident list -> 
    generation_parameters
  ;;
  
  (** A convenience interface for running answer generation.   This
      routine will use the generator to produce results until either results
      have been provably exhausted or the maximum number of steps has been
      reached for all possible start variables.  In any case, the result will
      provide the total list and number of answers, along with an indication of
      whether more answers can, in theory, be found or not.

      The generation_callback optional parameter provides results in the form
      of this function's returned values but is called as each new result is
      generated. *)
  val generate_answers :
    ?generation_callback:(Answer.t -> int -> unit) ->
    generation_parameters ->
    generation_result
  ;;
  end;;

(** A functor to create an answer generator with the Generator interface. *)
module Make(Answer : Answer) : Generator;;