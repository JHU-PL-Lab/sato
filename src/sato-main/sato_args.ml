open Batteries;;

open Odefa_ast;;
open Odefa_answer_generation;;
open Odefa_symbolic_interpreter;;

open Ast;;
open Generator_configuration;;

open Sato_cli_parser;;
open Sato_cli_parser_utils;;
open Sato_types;;

type type_checker_args = {
  args_filename : string;
  args_mode : sato_mode;
  args_target_var : Ident.t option;
  args_generator_configuration : Generator_configuration.configuration;
  args_maximum_steps : int option;
  args_maximum_results : int option;
  args_exploration_policy : Interpreter.exploration_policy;
  args_compact_output : bool;
}
;;

let parse_args () : type_checker_args =
  let (parsers, cli_parser) = make_cli_parser Sato_version.version_str in
  (* **** Perform parse **** *)
  try
    let filename = parse_out_filename cli_parser in
    let conf =
          { conf_context_model =
              insist "Context model" parsers.parse_context_stack;
          }
    in
    { args_generator_configuration = conf;
      args_filename = filename;
      args_mode =
        insist "Mode" parsers.parse_mode;
      args_target_var =
        begin
          match parsers.parse_target_point.BatOptParse.Opt.option_get () with
          | Some name -> Some (Ident name)
          | None -> None
        end;
      args_maximum_steps =
        parsers.parse_max_steps.BatOptParse.Opt.option_get ();
      args_maximum_results =
        parsers.parse_max_results.BatOptParse.Opt.option_get ();
      args_exploration_policy =
        insist "Exploration policy" parsers.parse_exploration_policy;
      args_compact_output =
        match (parsers.parse_compact_output.BatOptParse.Opt.option_get ()) with
        | Some b -> b
        | None -> false
    }
  with
  | ParseFailure msg ->
    BatOptParse.OptParser.error cli_parser @@ msg;
    raise @@ Jhupllib.Utils.Invariant_failure
      "BatOptParse.OptParser.error was supposed to terminate the program!"
;;