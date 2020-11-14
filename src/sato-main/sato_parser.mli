open Odefa_answer_generation;;
open Odefa_ast;;

open Ast;;

type type_checker_args = {
  tc_filename : string;
  tc_mode : Cli_parser.sato_mode;
  tc_target_var : Ident.t option;
  tc_generator_configuration : Generator_configuration.configuration;
  tc_maximum_steps : int option;
  tc_maximum_results : int option;
  tc_exploration_policy :
    Odefa_symbolic_interpreter.Interpreter.exploration_policy;
  tc_compact_output : bool;
}
;;

(** Parses the command line arguments.  If a parse error occurs, this function
    prints an appropriate error message and terminates the program.  Otherwise,
    the returned values are the generator configuration, the name of the file
    to analyze, and the variable in the program to reach. *)
val parse_args : unit -> type_checker_args;;