open Odefa_answer_generation;;
open Odefa_ast;;

open Ast;;

open Sato_types;;

type type_checker_args = {
  args_filename : string;
  args_mode : sato_mode;
  args_target_var : Ident.t option;
  args_generator_configuration : Generator_configuration.configuration;
  args_maximum_steps : int option;
  args_maximum_results : int option;
  args_exploration_policy :
    Odefa_symbolic_interpreter.Interpreter.exploration_policy;
  args_compact_output : bool;
}
;;

(** Parses the command line arguments.  If a parse error occurs, this function
    prints an appropriate error message and terminates the program.  Otherwise,
    the returned values are the generator configuration, the name of the file
    to analyze, and the variable in the program to reach. *)
val parse_args : unit -> type_checker_args;;