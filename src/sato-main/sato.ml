open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_natural;;
open Odefa_parser;;

open Odefa_answer_generation;;
open Odefa_symbolic_interpreter;;

let logger = Logger_utils.make_logger "Sato";;
let lazy_logger = Logger_utils.make_lazy_logger "Sato";;

exception CommandLineParseFailure of string;;
exception NoOperationsInProgram;;
exception TypeCheckComplete;;

let parse_program
    (args: Sato_parser.type_checker_args) 
  : (Ast.expr * On_to_odefa_maps.t) =
  let filename = args.tc_filename in
  try
    match Filename.extension filename with
    | ".natodefa" ->
      begin
        let natodefa_ast = File.with_file_in filename On_parse.parse_program in
        let (odefa_ast, on_odefa_maps) =
          On_to_odefa.translate natodefa_ast
        in
        Ast_wellformedness.check_wellformed_expr odefa_ast;
        (odefa_ast, on_odefa_maps)
      end
    | ".odefa" ->
      begin
        let pre_inst_ast = File.with_file_in filename Parser.parse_program in
        let (odefa_ast, on_odefa_maps) =
          Odefa_instrumentation.instrument_odefa pre_inst_ast
        in
        Ast_wellformedness.check_wellformed_expr odefa_ast;
        (odefa_ast, on_odefa_maps)
      end
    | _ ->
      raise @@ Invalid_argument
        (Printf.sprintf "Filetype %s not supported" filename)
  with
  | Sys_error msg | Invalid_argument msg ->
    Stdlib.prerr_endline msg;
    Stdlib.exit 1
  | On_parse.Parse_error (_, line, col, token)->
    let msg =
      Printf.sprintf "Invalid token \"%s\" at line %d, column %d" token line col
    in
    Stdlib.prerr_endline msg;
    Stdlib.exit 1
  | Ast_wellformedness.Illformedness_found ills ->
    print_endline "Program is ill-formed.";
    List.iter
      (fun ill ->
        let msg = "* " ^ Ast_wellformedness.show_illformedness ill in
        Stdlib.print_endline msg;)
      ills;
    Stdlib.exit 1
;;

let print_results
    ~(output : unit BatIO.output)
    (answer_name : string)
    (is_completed : bool)
    (total_errors : int)
  : unit =
  (* Display number of type errors. *)
  if total_errors = 0 then
    output_string output
      (Printf.sprintf "No %ss found.\n" answer_name)
  else
    output_string output
      (Printf.sprintf "%d %s%s found.\n"
        total_errors
        answer_name
        (if total_errors = 1 then "" else "s"));
  (* Display if control flows have been exhausted or not. *)
  if is_completed then
    output_string output "No further control flows exist.\n"
  else
    output_string output "Further control flows may exist.\n"
;;

let print_results_compact
    ~(output : unit BatIO.output)
    (is_completed : bool)
    (total_errors : int)
  : unit =
  output_string output (Printf.sprintf "num  : %d\n" total_errors);
  output_string output (Printf.sprintf "more : %b\n" (not is_completed));
;;

let get_target_vars
    (args: Sato_parser.type_checker_args)
    (expr : Ast.expr)
  : Ast.ident list =
  match args.tc_target_var with
  | Some v -> [v]
  | None ->
    begin
      match Interpreter_environment.list_instrument_conditionals expr with
      | [] -> raise NoOperationsInProgram
      | target_list -> target_list
    end
;;

let run_error_check
    ?output:(output=stdout)
    ?show_steps:(show_steps=false)
    (module Error_generator : Generator.Generator)
    (args : Sato_parser.type_checker_args)
    (on_odefa_maps : On_to_odefa_maps.t)
    (expr : Ast.expr)
  : unit =
  let module Ans = Error_generator.Answer in
  Ans.set_odefa_natodefa_map on_odefa_maps;
  try
    (* Prepare and create generator *)
    let target_vars = get_target_vars args expr in
    let gen_params =
      Error_generator.create
        ~exploration_policy:args.tc_exploration_policy
        ~max_steps:args.tc_maximum_steps
        ~max_results:args.tc_maximum_results
        args.tc_generator_configuration
        expr
        target_vars
    in
    let generation_callback
      (type_errors : Ans.t) (_: int) : unit =
      if Ans.generation_successful type_errors then begin
        let str =
          Ans.show ~show_steps ~is_compact:args.tc_compact_output type_errors
        in
        output_string output @@ Printf.sprintf "%s\n" str
      end;
    in
    (* Run generator *)
    let gen_answers =
      Error_generator.generate_answers
        ~generation_callback:generation_callback
        gen_params
    in
    (* Finish generation *)
    let is_complete = gen_answers.gen_is_complete in
    begin
      if args.tc_compact_output then
        print_results_compact ~output is_complete gen_answers.gen_num_answers
      else
        print_results ~output (Ans.description) is_complete gen_answers.gen_num_answers
    end;
    close_out output
  (* Exception for when the user inputs a target var not in the program *)
  with
  | NoOperationsInProgram ->
    print_endline "No error-able operations found; terminating."
  | Interpreter.Invalid_query msg ->
    prerr_endline msg;
    Stdlib.exit 1
;;

(* TODO: Add variable of operation where type error occured *)
let () =
  let args = Sato_parser.parse_args () in
  let (odefa_expr, on_odefa_maps) = parse_program args in
  match args.tc_mode with
  | Type_checking ->
    begin
      let error_generator =
        if On_to_odefa_maps.is_natodefa on_odefa_maps then
          (module Generator.Make(Generator_answer.Natodefa_type_errors)
            : Generator.Generator)
        else
          (module Generator.Make(Generator_answer.Type_errors)
            : Generator.Generator)
      in
      run_error_check error_generator args on_odefa_maps odefa_expr
    end
  | Test_generation ->
    begin
      match args.tc_target_var with
      | None ->
        Stdlib.prerr_endline "This mode requires a target variable; exiting.";
        Stdlib.exit 1
      | Some _ ->
        let input_generator =
          (module Generator.Make(Generator_answer.Input_sequence)
            : Generator.Generator)
        in
        run_error_check input_generator args on_odefa_maps odefa_expr
    end
;;