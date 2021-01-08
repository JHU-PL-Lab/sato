open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_natural;;
open Ton_to_on;;

(* open Ast_tools;; *)

open Odefa_answer_generation;;
open Odefa_symbolic_interpreter;;

let logger = Logger_utils.make_logger "Type_verifier";;
let lazy_logger = Logger_utils.make_lazy_logger "Type_verifier";;

exception CommandLineParseFailure of string;;
exception NoOperationsInProgram;;
exception TypeCheckComplete;;

exception GenerationComplete;;

(** Removes from a variable any special symbols introduced by the translation
    process which are not parseable identifiers. *)
let purge_special_symbols (x : Ast.Var.t) : Ast.Var.t =
  let Ast.Var(Ast.Ident(s), fs) = x in
  let s' =
    s
    |> String.replace_chars
      (fun c ->
          match c with
        | '~' -> "___"
        | _ -> String.of_char c
      )
  in
  Ast.Var(Ast.Ident(s'), fs)
;;

let parse_program
    (args: Type_verifier_parser.type_verifier_args) 
  : (Ast.expr * On_to_odefa_maps.t) =
  let filename = args.tc_filename in
  try
    match Filename.extension filename with
    | ".natodefa" ->
      begin
        let natodefa_ast = File.with_file_in filename On_parse.parse_program in
        let (odefa_ast, on_odefa_maps) =
          On_to_odefa.translate (typed_non_to_on natodefa_ast)
        in
        (* print_endline (On_ast_pp.show_expr (typed_non_to_on natodefa_ast)); *)
        (* print_endline (Ast_pp.show_expr @@ map_expr_vars purge_special_symbols odefa_ast); *)
        Ast_wellformedness.check_wellformed_expr odefa_ast;
        (odefa_ast, on_odefa_maps)
      end
    | _ ->
      raise @@ Invalid_argument
        (Printf.sprintf "Filetype %s not supported" filename)
  with
  | Sys_error err ->
    begin
      Stdlib.prerr_endline err;
      Stdlib.exit 1
    end
  | On_parse.Parse_error (_, line, col, token)->
    begin
      Stdlib.prerr_endline
        @@ Printf.sprintf "Invalid token \"%s\" at line %d, column %d" token line col;
      Stdlib.exit 1
    end
  | Ast_wellformedness.Illformedness_found ills ->
    begin
      print_endline "Program is ill-formed.";
      List.iter
        (fun ill ->
            Stdlib.print_string "* ";
            Stdlib.print_endline @@ Ast_wellformedness.show_illformedness ill;
        )
        ills;
      Stdlib.exit 1
    end
;;

let print_results
    (is_completed : bool)
    (total_errors : int)
  : unit =
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


let get_target_vars (expr : Ast.expr) : Ast.ident list =
    match Interpreter_environment.list_instrument_conditionals expr with
    | [] -> raise NoOperationsInProgram
    | target_list -> target_list
;;

let run_error_check
    (module Error_generator : Generator.Generator)
    (args : Type_verifier_parser.type_verifier_args)
    (on_odefa_maps : On_to_odefa_maps.t)
    (expr : Ast.expr)
  : unit =
  let module Ans = Error_generator.Answer in
  Ans.set_odefa_natodefa_map on_odefa_maps;
  try
    (* Prepare and create generator *)
    let target_vars = get_target_vars expr in
    let results_remaining = ref args.tc_maximum_results in
    let total_errors = ref 0 in
    let generator =
      Error_generator.create
        ~exploration_policy:args.tc_exploration_policy
        args.tc_generator_configuration
        expr
        target_vars
    in
    let generation_callback
      (type_errors : Ans.t) (steps: int) : unit =
      let _ = steps in (* Temp *)
      print_endline (Ans.show type_errors);
      print_endline (Printf.sprintf "Found in %d steps" steps);
      print_endline "";
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
        Error_generator.generate_answers
          ~generation_callback:generation_callback
          args.tc_maximum_steps
          generator
      in
      print_results (Option.is_none generator_opt) (!total_errors);
    with GenerationComplete ->
      print_endline "Errors found; terminating";
  (* Exception for when the user inputs a target var not in the program *)
  with
  | NoOperationsInProgram ->
    print_endline "No error-able operations found; terminating."
  | Interpreter.Invalid_query msg ->
    prerr_endline msg
;;

(* TODO: Add variable of operation where type error occured *)
let () =
  let args = Type_verifier_parser.parse_args () in
  let (odefa_expr, on_odefa_maps) = parse_program args in
  let error_generator =
    if On_to_odefa_maps.is_natodefa on_odefa_maps then
      (module Generator.Make(Generator_answer.Natodefa_type_errors)
        : Generator.Generator)
    else
      (module Generator.Make(Generator_answer.Type_errors)
        : Generator.Generator)
  in
  run_error_check error_generator args on_odefa_maps odefa_expr
;;