open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_natural;;
open Odefa_parser;;

open Odefa_answer_generation;;

let logger = Logger_utils.make_logger "Type_checker";;
let lazy_logger = Logger_utils.make_lazy_logger "Type_checker";;

exception CommandLineParseFailure of string;;
exception TypeCheckComplete;;

exception GenerationComplete;;

module Type_error_generator = Generator.Make(Generator_answer.Type_errors);;
module Ans = Type_error_generator.Answer;;

module Natodefa_type_error_generator = Generator.Make(Generator_answer.Natodefa_type_errors);;
module On_ans = Natodefa_type_error_generator.Answer;;

let print_results (is_completed : bool) (total_errors : int) : unit =
  (* Display number of type errors. *)
  if total_errors = 0 then
    print_endline "No errors found."
  else
    print_endline @@ (string_of_int total_errors) ^ " errors found.";
  (* Display if control flows have been exhausted or not. *)
  if is_completed then
    print_endline "No further control flows exist."
  else
    print_endline "Further control flows may exist."
;;

let run_odefa
    (filename : string)
    (args : Type_checker_parser.type_checker_args) =
  (* Parse AST *)
  try
    let (odefa_ast, on_odefa_maps) =
      Odefa_instrumentation.instrument_odefa
        @@ File.with_file_in filename Parser.parse_program
    in
    Ast_wellformedness.check_wellformed_expr odefa_ast;
    (* Prepare and create generator *)
    Ans.set_odefa_natodefa_map on_odefa_maps;
    let results_remaining = ref args.tc_maximum_results in
    let total_errors = ref 0 in
    let generator =
      Type_error_generator.create
        ~exploration_policy:args.tc_exploration_policy
        args.tc_generator_configuration
        odefa_ast
        args.tc_target_var
    in
    let generation_callback
      (type_errors : Ans.t) (steps: int) : unit =
      let _ = steps in (* Temp *)
      print_endline (Ans.show type_errors);
      flush stdout;
      total_errors := !total_errors + Ans.count type_errors;
      results_remaining := (Option.map (fun n -> n - 1) !results_remaining);
      if !results_remaining = Some 0 then begin
        raise GenerationComplete
      end;
    in
    (* Run generator *)
    try
      let _, generator_opt =
        Type_error_generator.generate_answers
          ~generation_callback:generation_callback
          args.tc_maximum_steps
          generator
      in
      print_results (Option.is_none generator_opt) (!total_errors);
    with GenerationComplete ->
      print_endline "Type errors found; terminating";
  with
  | Sys_error err ->
    begin
      prerr_endline err;
      exit 1
    end
  | Ast_wellformedness.Illformedness_found ills ->
    begin
      print_endline "Program is ill_formed.";
      let print_ill ill =
        print_string "* ";
        print_endline @@ Ast_wellformedness.show_illformedness ill;
      in
      List.iter print_ill ills;
      exit 1
    end
  | Odefa_symbolic_interpreter.Interpreter.Invalid_query msg ->
    prerr_endline msg
;;

let run_natodefa
    (filename : string)
    (args : Type_checker_parser.type_checker_args) =
  try
    (* Parse AST *)
    let natodefa_ast =
      File.with_file_in filename On_parse.parse_program
    in
    let (odefa_ast, on_odefa_maps) =
      On_to_odefa.translate ~is_instrumented:true natodefa_ast
    in
    lazy_logger `debug (fun () ->
      Printf.sprintf "Translated program:\n%s" (Ast_pp.show_expr odefa_ast));
    Ast_wellformedness.check_wellformed_expr odefa_ast;
    (* Prepare and create generator *)
    On_ans.set_odefa_natodefa_map on_odefa_maps;
    let results_remaining = ref args.tc_maximum_results in
    let total_errors = ref 0 in
    let generator =
      Natodefa_type_error_generator.create
        ~exploration_policy:args.tc_exploration_policy
        args.tc_generator_configuration
        odefa_ast
        args.tc_target_var
    in
    let generation_callback
      (type_errors : On_ans.t) (steps: int) : unit =
      let _ = steps in (* Temp *)
      print_endline (On_ans.show type_errors);
      flush stdout;
      total_errors := !total_errors + On_ans.count type_errors;
      results_remaining := (Option.map (fun n -> n - 1) !results_remaining);
      if !results_remaining = Some 0 then begin
        raise GenerationComplete
      end;
    in
    (* Run generator *)
    try
      let _, generator_opt =
        Natodefa_type_error_generator.generate_answers
          ~generation_callback:generation_callback
          args.tc_maximum_steps
          generator
      in
      print_results (Option.is_none generator_opt) (!total_errors);
    with GenerationComplete ->
      print_endline "Type errors found; terminating";
  with
  | Sys_error err ->
    begin
      prerr_endline err;
      exit 1
    end
  | Ast_wellformedness.Illformedness_found ills ->
    begin
      print_endline "Program is ill_formed.";
      let print_ill ill =
        print_string "* ";
        print_endline @@ Ast_wellformedness.show_illformedness ill;
      in
      List.iter print_ill ills;
      exit 1
    end
  | Odefa_symbolic_interpreter.Interpreter.Invalid_query msg ->
    prerr_endline msg


(* TODO: Add variable of operation where type error occured *)
let () =
  let args = Type_checker_parser.parse_args () in
  let filename : string = args.tc_filename in
  let is_natodefa = Filename.extension filename = ".natodefa" in
  let is_odefa = Filename.extension filename = ".odefa" in
  if is_natodefa then
    run_natodefa filename args
  else if is_odefa then
    run_odefa filename args
  else
    raise @@ Invalid_argument "Filetype not supported"
;;