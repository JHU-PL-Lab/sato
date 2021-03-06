open Batteries;;

open Odefa_ddpa;;

open Sato_cli_parser_utils;;
open Sato_types;;

open Odefa_symbolic_interpreter.Interpreter;;

let named_exploration_policies =
  [
    (Explore_breadth_first, "bfs");
    (Explore_smallest_relative_stack_length, "relstack-len");
    (Explore_least_relative_stack_repetition, "relstack-rep");
  ]
;;

type parsers =
  { 
    parse_mode : sato_mode BatOptParse.Opt.t;
    parse_context_stack : (module Ddpa_context_stack.Context_stack) BatOptParse.Opt.t;
    parse_target_point : string BatOptParse.Opt.t;
    parse_max_steps : int BatOptParse.Opt.t;
    parse_max_results : int BatOptParse.Opt.t;
    parse_exploration_policy : exploration_policy BatOptParse.Opt.t;
    parse_logging : unit BatOptParse.Opt.t;
    parse_output_format : output_format BatOptParse.Opt.t;
  }
;;

let make_parsers () : parsers =
  { parse_mode =
      single_value_parser
        ~invalid_value_err_msg:
          (fun _ str ->
            "Could not understand mode: " ^ str ^ ".\n" ^
            "Valid modes are \"error\" and \"input\".")
        "MODE"
        (Some "Specifies the mode of the sato executable: error (default) or input.")
        (Some Type_checking)
        (fun s -> match s with
          | "error" -> Some Type_checking
          | "input" -> Some Test_generation
          | _ -> None
        );
    parse_context_stack =
      select_context_stack_parser ();
    parse_target_point =
      single_value_parser
        "VARIABLE"
        (Some "Specifies the variable to start demand-driven lookup from.")
        None
        Option.some;
    parse_max_steps =
      single_value_parser
        "MAX_STEPS"
        (Some ("Specifies the maximum number of steps to take during computation."))
        None
        (fun x -> try Some(int_of_string x) with | Failure _ -> None);
    parse_max_results =
      single_value_parser
        "MAX_RESULTS"
        (Some ("Specifies the maximum number of results to find during computation."))
        None
        (fun x -> try Some(int_of_string x) with | Failure _ -> None);
    parse_exploration_policy =
      begin
        let named_exploration_policies_str =
          begin
            named_exploration_policies
            |> List.map snd
            |> List.map (fun s -> "* " ^ s)
            |> String.concat "\n "
          end
        in
        single_value_parser
          ~invalid_value_err_msg:
            (fun _ str ->
              "Could not understand exploration policy: " ^ str ^ "\n" ^
              "Valid policies are:\n " ^
              named_exploration_policies_str
            )
          "EXPLORATION_POLICY"
          (Some "Specifies the exploration policy of the evaluation queue.")
          (Some Explore_breadth_first)
          (fun s ->
            try
              Some(List.assoc_inv s named_exploration_policies)
            with
            | Not_found -> None 
          )
        end;
    parse_output_format =
      single_value_parser
        "OUTPUT_FORMAT"
        ~invalid_value_err_msg:(fun _ str ->
          "Cannot understand output format " ^ str ^ ".\n" ^
          "Valid formats are \"default\", \"compact\", and \"json\"")
        (Some "Specifies the output format: default (descriptive output), compact, or JSON\n")
        (Some Standard)
        (function
          | "default" -> Some Standard
          | "compact" -> Some Compact
          | "json" -> Some JSON
          | _ -> None
        );
    parse_logging = logging_option_parser ();
  }
;;

let make_cli_parser version_str =
  let cli_parser =
    BatOptParse.OptParser.make ~version:version_str ()
  in
  let parsers = make_parsers () in
  (* **** Add options **** *)
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'m'
    ~long_name:"mode"
    parsers.parse_mode;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'c'
    ~long_name:"context-stack"
    parsers.parse_context_stack;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'t'
    ~long_name:"target-point"
    parsers.parse_target_point;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'s'
    ~long_name:"maximum-steps"
    parsers.parse_max_steps;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'r'
    ~long_name:"maximum-results"
    parsers.parse_max_results;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'l'
    ~long_name:"log"
    parsers.parse_logging;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'e'
    ~long_name:"exploration-policy"
    parsers.parse_exploration_policy;
  BatOptParse.OptParser.add
    cli_parser
    ~short_name:'f'
    ~long_name:"output-format"
    parsers.parse_output_format;
  (parsers, cli_parser)
;;