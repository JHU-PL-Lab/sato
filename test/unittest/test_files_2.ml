open Batteries;;
(* open Jhupllib;; *)
open OUnit2;;

open Odefa_ast;;
open Odefa_natural;;
open Odefa_answer_generation;;
open Odefa_symbolic_interpreter;;

exception File_test_creation_failure of string;;
exception Argument_parse_failure of string;;

type arguments = {
  arg_target_var : Ast.Ident.t option;
  arg_gen_config : Generator_configuration.configuration;
  arg_explore_policy : Interpreter.exploration_policy;
  arg_max_steps : int option;
}
;;

(* **** Global variables **** *)

let target_var_str = "TARGET-VARIABLE";;
let gen_config_str = "GENERATOR-CONFIG";;
let explore_policy_str = "EXPLORATION-POLICY";;
let max_steps_str = "MAX-STEPS";;

let input_root = "test/test-inputs";;
let output_root = "test/test-outputs";;

let parse_arguments filename =
  let module String_map = Map.Make(String) in
  let arg_from_str str =
    let str' = String.trim str in
    if String.starts_with str' "#" then
      str'
      |> (fun s -> String.tail s 1)
      |> String.trim
      |> Option.some
    else None
  in
  let args =
    filename
    |> File.lines_of
    |> Enum.filter_map arg_from_str
    |> Enum.map (String.split ~by:":")
    |> Enum.map (fun (s1, s2) -> (String.trim s1, String.trim s2))
    |> String_map.of_enum
  in
  {
    arg_target_var = begin
      match String_map.Exceptionless.find target_var_str args with
      | Some var_str -> Some (Ident var_str)
      | None -> None
      end;
    arg_gen_config = begin
      { conf_context_model =
        match String_map.Exceptionless.find gen_config_str args with
        | Some name ->
          begin
            match Odefa_toploop.Toploop_utils.stack_from_name name with
            | Some stack -> stack
            | None -> raise @@ Argument_parse_failure "Unknown generator configuration"
          end
        | None ->
          (module Odefa_ddpa.Ddpa_unit_stack.Stack)
      }
      end;
    arg_explore_policy = begin
      match String_map.Exceptionless.find explore_policy_str args with
      | Some str ->
        begin
          match str with
          | "QUEUE" -> Explore_breadth_first
          | "LENGTH_STACK" -> Explore_smallest_relative_stack_length
          | "REPEAT_STACK" -> Explore_least_relative_stack_repetition
          | _ -> raise @@ Argument_parse_failure "Unknown interpreter exploration policy"
        end
      | None -> Explore_breadth_first
      end;
    arg_max_steps = begin
      match String_map.Exceptionless.find max_steps_str args with
      | Some steps_str ->
        begin
        try Some (int_of_string steps_str) with
        | Failure _ -> raise @@ Argument_parse_failure "Non-parseable max steps"
        end
      | None -> (Some 10000)
      end;
  }
;;

let parse_program (file : string) : (Ast.expr * On_to_odefa_maps.t) =
  let (expr, maps) =
    try
      if Filename.extension file = ".natodefa" then begin
        let on_ast = File.with_file_in file On_parse.parse_program in
        On_to_odefa.translate on_ast
      end else begin
        let ast = File.with_file_in file Odefa_parser.Parser.parse_program in
        Odefa_instrumentation.instrument_odefa ast
      end
    with Sys_error err -> raise @@ File_test_creation_failure err
  in
  begin
    try Ast_wellformedness.check_wellformed_expr expr with
    | Ast_wellformedness.Illformedness_found ills ->
      begin
        let ills_msg =
          ills
          |> List.map Ast_wellformedness.show_illformedness
          |> List.map (fun s -> "* " ^ s)
          |> String.join "\n"
        in
        raise @@ File_test_creation_failure
          (Format.sprintf "Program is ill-formed.\n%s" ills_msg)
      end
  end;
  (expr, maps)
;;

let run_type_checker (file : string) : Yojson.Safe.t =
  let args = parse_arguments file in
  let (expr, maps) = parse_program file in
  let m =
    if (Filename.extension file = ".natodefa") then
      (module Generator.Make(Generator_answer.Natodefa_type_errors) : Generator.Generator)
    else
      (module Generator.Make(Generator_answer.Type_errors) : Generator.Generator)
  in
  let module Error_generator = (val m) in
  let module Ans = Error_generator.Answer in
  let () = Ans.set_odefa_natodefa_map maps in
  let target_vars =
    match args.arg_target_var with
    | Some var -> [var]
    | None ->
      begin
        match Interpreter_environment.list_instrument_conditionals expr with
        | [] -> failwith "foo"
        | target_list -> target_list
      end
  in
  let generator =
    Error_generator.create
      ~exploration_policy:args.arg_explore_policy
      args.arg_gen_config
      expr
      target_vars
  in
  let error_list_ref = ref [] in
  let generation_callback
      (type_errors : Ans.t) (_ : int) : unit =
    error_list_ref := type_errors :: !error_list_ref
  in
  let _, _ =
    Error_generator.generate_answers
      ~generation_callback:generation_callback
      args.arg_max_steps
      generator
  in
  let error_list_to_yojson err_list =
    `List (List.map Ans.to_yojson err_list)
  in
  error_list_to_yojson !error_list_ref
;;

let make_test ((in_file, out_file) : (string * string)) =
  try
    let test_thunk =
      (fun _ ->
        let expected = Yojson.Safe.from_file out_file in
        let actual = run_type_checker in_file in
        assert_equal
          ~cmp:Yojson.Safe.equal
          ~printer:Yojson.Safe.pretty_to_string
          expected
          actual)
    in
    in_file >:: test_thunk
  with
  | File_test_creation_failure s ->
    in_file >:: (fun _ -> assert_failure s)
  | Argument_parse_failure s ->
    in_file >:: (fun _ -> assert_failure s)
;;

let make_tests_from_dir dir_name =
  let input_dir = input_root ^ Filename.dir_sep ^ dir_name in
  let output_dir = output_root ^ Filename.dir_sep ^ dir_name in
  if Sys.file_exists input_dir && Sys.file_exists output_dir
    && Sys.is_directory input_dir && Sys.is_directory output_dir then
    input_dir
    |> Sys.files_of
    |> Enum.filter_map
      (fun filename ->
        let in_file = input_dir ^ Filename.dir_sep ^ filename in
        if Sys.is_directory in_file then None
        else if not @@ String.ends_with in_file ".odefa"
              && not @@ String.ends_with in_file ".natodefa" then begin
          None
        end else begin
          let out_file =
            filename
            |> Filename.remove_extension
            |> (fun f -> output_dir ^ Filename.dir_sep ^ f ^ ".json")
          in
          if not @@ Sys.file_exists out_file then
            raise @@ File_test_creation_failure
              (Format.sprintf "No corresponding output file %s" out_file)
          else
            Some (in_file, out_file)
        end
      )
    |> Enum.map make_test
    |> List.of_enum
  else
    raise @@ File_test_creation_failure
      (Format.sprintf "Test file directory %s does not exist" dir_name)
;;

let tests =
  "Test Files" >::: (
    make_tests_from_dir ""
  )
;;