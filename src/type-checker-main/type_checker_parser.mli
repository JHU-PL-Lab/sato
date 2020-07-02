open Odefa_test_generation;;
open Odefa_ast;;

open Ast;;

type type_checker_args = {
  tc_filename : string;
  tc_target_var : Ident.t;
  tc_debug : bool;
  tc_generator_configuration : Generator_configuration.configuration;
  tc_maximum_steps : int option;
  tc_maximum_results : int option;
  tc_exploration_policy :
    Odefa_symbolic_interpreter.Interpreter.exploration_policy;
}
;;

val parse_args : unit -> type_checker_args;;