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
    (args: Sato_args.type_checker_args) 
  : (Ast.expr * On_to_odefa_maps.t) =
  let filename = args.args_filename in
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
    (args: Sato_args.type_checker_args)
    (expr : Ast.expr)
  : Ast.ident list =
  match args.args_target_var with
  | Some v -> [v]
  | None ->
    begin
      match Interpreter_environment.list_instrument_conditionals expr with
      | [] -> raise NoOperationsInProgram
      | target_list -> target_list
    end
;;

let run_generation
    ?output:(output=stdout)
    (module Generator : Generator.Generator)
    (args : Sato_args.type_checker_args)
    (on_odefa_maps : On_to_odefa_maps.t)
    (expr : Ast.expr)
  : unit =
  let module Ans = Generator.Answer in
  Ans.set_odefa_natodefa_map on_odefa_maps;
  try
    (* Prepare and create generator *)
    let target_vars = get_target_vars args expr in
    let gen_params =
      Generator.create
        ~exploration_policy:args.args_exploration_policy
        ~max_steps:args.args_maximum_steps
        ~max_results:args.args_maximum_results
        args.args_generator_configuration
        expr
        target_vars
    in
    (* Mutable list to store JSON output.  Will remain empty if output
       format is "default" or "compact" (i.e. not JSON).*)
    let json_list = ref [] in
    let generation_callback
      (type_errors : Ans.t) : unit =
      if Ans.generation_successful type_errors then begin
        match args.args_output_format with
        | Standard ->
          let str = Ans.show type_errors in
          output_string output @@ Printf.sprintf "%s\n" str
        | Compact ->
          let str = Ans.show_compact type_errors in
          output_string output @@ Printf.sprintf "%s\n" str
        | JSON ->
          json_list := (Ans.to_yojson type_errors) :: !json_list        
      end;
    in
    (* Run generator *)
    let gen_answers =
      Generator.generate_answers
        ~generation_callback:generation_callback
        gen_params
    in
    (* Finish generation *)
    let is_complete = gen_answers.gen_is_complete in
    begin
      match args.args_output_format with
      | Standard ->
        print_results ~output (Ans.description) is_complete gen_answers.gen_num_answers
      | Compact ->
        print_results_compact ~output is_complete gen_answers.gen_num_answers
      | JSON ->
        (`List !json_list)
        |> Yojson.Safe.to_string
        |> Yojson.Safe.prettify
        |> output_string output
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

let () =
  let args = Sato_args.parse_args () in
  let (odefa_expr, on_odefa_maps) = parse_program args in
  match args.args_mode with
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
      run_generation error_generator args on_odefa_maps odefa_expr
    end
  | Test_generation ->
    begin
      match args.args_target_var with
      | None ->
        Stdlib.prerr_endline "This mode requires a target variable; exiting.";
        Stdlib.exit 1
      | Some _ ->
        let input_generator =
          (module Generator.Make(Generator_answer.Input_sequence)
            : Generator.Generator)
        in
        run_generation input_generator args on_odefa_maps odefa_expr
    end
;;