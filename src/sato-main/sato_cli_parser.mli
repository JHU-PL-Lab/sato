open Odefa_ddpa;;
open Odefa_symbolic_interpreter;;

open Sato_types;;

type parsers =
  { 
    parse_mode : sato_mode BatOptParse.Opt.t;
    parse_context_stack : (module Ddpa_context_stack.Context_stack) BatOptParse.Opt.t;
    parse_target_point : string BatOptParse.Opt.t;
    parse_max_steps : int BatOptParse.Opt.t;
    parse_max_results : int BatOptParse.Opt.t;
    parse_exploration_policy : Interpreter.exploration_policy BatOptParse.Opt.t;
    parse_logging : unit BatOptParse.Opt.t;
    parse_compact_output : bool BatOptParse.Opt.t;
  }
;;

val make_cli_parser : string -> (parsers * BatOptParse.OptParser.t);;