(**
   This test module will load a series of test files from the test sources
   directory and execute them one by one.

   Each file is expected to contain a comment describing the expected test
   result.  The comment should be of one of the following forms:

   - EXPECT-EVALUATE: We expect that the code evaluates to completion.

   - EXPECT-STUCK: We expect that the code gets stuck during evaluation.

   - EXPECT-WELL-FORMED: We expect that the code is well-formed.

   - EXPECT-ILL-FORMED: We expect that the code is not well-formed.

   - EXPECT-ANALYSIS-STACK-IS <stack>: We expect that the context stack is
      <stack>. Options for stack: 0ddpa, 1ddpa, 2ddpa, ddpaNR, none, <n>ddpa.

   - EXPECT-INPUT-IS <inputs>: We expect that the code can successfully process
      the input sequence <inputs>, given as an int list (eg. [0, 1, 2]).

   - EXPECT-ANALYSIS-LOOKUP-FROM-END <var> <type set>: We expect that the
      variable <var> should be one of the types in <type set>.

   - EXPECT-ANALYSIS-INCONSISTENCY-AT <var>: We expect to encounter an
      inconsistency at the variable <var> in DDPA.

   - EXPECT-ANALYSIS-NO-INCONSISTENCIES: We expect to not encounter any
      inconsistency in DDPA.
*)

(* NOTE: This test harness was originally designed to test DDPA and DDSE, and
   was at one point modified to test type checking.  However, due to it
   complexity, we moved to a different test harness in test_sato.ml, and this
   is left as a legacy tester for DDPA.
*)

(* FIXME: purge the term "inconsistency" *)

open Batteries;;
open Jhupllib;;
open OUnit2;;

open Odefa_ast;;
open Odefa_ddpa;;
open Odefa_parser;;
open Odefa_answer_generation;;
open Odefa_toploop;;

open Odefa_natural;;

open Ast;;
open Ast_pp;;
open Ast_wellformedness;;
open Generator_answer;;
open Toploop_options;;
open Toploop_types;;
open Ddpa_abstract_ast;;
open String_utils;;

let lazy_logger = Logger_utils.make_lazy_logger "Test_files";;

exception File_test_creation_failure of string;;

(** Thrown internally when an input generation test can halt generation as all
    sequences have been generated. *)

exception Input_generation_complete;;

module String_map = Map.Make(String);;

module Input_generator = Generator.Make(Input_sequence);;

let string_of_int_list int_list =
  "[" ^ (String.join ", " @@ List.map string_of_int int_list) ^ "]"
;;

let string_of_input_sequence input_sequence =
  Input_generator.Answer.show input_sequence
;;

let string_of_input_sequences input_sequences =
  String.join ", " @@ List.map string_of_input_sequence input_sequences
;;
type test_expectation =
  (* Can the expression successfully evaluate? *)
  | Expect_evaluate
  | Expect_stuck
  (* Is the expression syntactically correct? *)
  | Expect_well_formed
  | Expect_ill_formed
  (* Set the analysis stack, e.g. 0ddpa, 1ddpa, etc. *)
  | Expect_analysis_stack_is of (module Ddpa_context_stack.Context_stack) option
  (* Set the input to feed into the program. *)
  | Expect_input_is of int list
  (* What values does DDPA expect the variable to be? *)
  | Expect_analysis_variable_lookup_from_end of ident * string
  (* Is there an inconsistency? *)
  | Expect_analysis_inconsistency_at of ident
  | Expect_analysis_no_inconsistencies
;;

(* **** Expectation utility functions **** *)

let pp_test_expectation formatter expectation =
  match expectation with
  | Expect_evaluate -> Format.pp_print_string formatter "Expect_evaluate"
  | Expect_stuck -> Format.pp_print_string formatter "Expect_stuck"
  | Expect_well_formed -> Format.pp_print_string formatter "Expect_well_formed"
  | Expect_ill_formed -> Format.pp_print_string formatter "Expect_ill_formed"
  | Expect_analysis_stack_is _ ->
    Format.pp_print_string formatter "Expect_analysis_stack_is(...)"
  | Expect_input_is inputs ->
    Format.fprintf formatter "Expect_int_is %s" (string_of_int_list inputs)
  | Expect_analysis_variable_lookup_from_end(x,expected) ->
    Format.fprintf formatter
      "Expect_analysis_variable_lookup_from_end(%a,\"%s\")"
      pp_ident x expected
  | Expect_analysis_inconsistency_at(x) ->
    Format.fprintf formatter
      "Expect_analysis_inconsistency_at(%a)"
      pp_ident x
  | Expect_analysis_no_inconsistencies ->
    Format.pp_print_string formatter "Expect_analysis_no_inconsistencies"
;;

let name_of_expectation expectation =
  match expectation with
  | Expect_evaluate -> "should evaluate"
  | Expect_stuck -> "should get stuck"
  | Expect_well_formed -> "should be well-formed"
  | Expect_ill_formed -> "should be ill-formed"
  | Expect_analysis_stack_is stack_option ->
    let name =
      match stack_option with
      | Some stack ->
        let module Stack =
          (val stack : Ddpa_context_stack.Context_stack)
        in
        Stack.name
      | None -> "none"
    in
    "should use analysis stack " ^ name
  | Expect_input_is inputs ->
    "should have input " ^ (string_of_int_list inputs)
  | Expect_analysis_variable_lookup_from_end(ident,_) ->
    "should have particular values for variable " ^ (show_ident ident)
  | Expect_analysis_inconsistency_at ident ->
    "should be inconsistent at " ^ show_ident ident
  | Expect_analysis_no_inconsistencies ->
    "should be consistent"
;;

(* **** Expectation parsing **** *)

type expectation_parse =
  | Success of test_expectation
  | Failure of string
;;

exception Expectation_parse_failure of string;;

exception Expectation_not_found;;

type expectation_stack_decision =
  | Default_stack
  | Chosen_stack of (module Ddpa_context_stack.Context_stack) option
;;

let assert_no_args lst =
  if List.is_empty lst
  then ()
  else raise @@ Expectation_parse_failure "expected no arguments"
;;

let assert_one_arg lst =
  match lst with
  | [x] -> x
  | _ ->
    raise @@
    Expectation_parse_failure ("expected one argument; got " ^
                               string_of_int (List.length lst))
;;

let assert_two_args lst =
  match lst with
  | [x;y] -> (x,y)
  | _ ->
    raise @@
    Expectation_parse_failure ("expected two arguments; got " ^
                               string_of_int (List.length lst))
;;

let _parse_analysis_stack_args args_str =
  let args = whitespace_split args_str in
  let name = assert_one_arg args in
  begin
    try
      let stack_module = Toploop_utils.stack_from_name name in
      Expect_analysis_stack_is stack_module
    with
    | Not_found ->
      raise @@ Expectation_parse_failure "invalid stack name"
  end
;;

let _parse_input args_lst =
  match args_lst with
  | [args_str] ->
    begin
      try
        let inputs =
          args_str
          |> whitespace_split
          |> List.map int_of_string
        in
        Expect_input_is inputs
      with Failure _ ->
          raise @@ Expectation_parse_failure
            ("Could not parse input: " ^ args_str)
    end
  | [] ->
    raise @@ Expectation_parse_failure "Missing arguments"
  | _ ->
    raise @@ Expectation_parse_failure "Spurious arguments"
;;

let parse_expectation str =
  try
    let expectation =
      match String_utils.whitespace_split ~max:2 str with
      | "EXPECT-EVALUATE" :: args_part ->
        assert_no_args args_part;
        Expect_evaluate
      | "EXPECT-STUCK" :: args_part ->
        assert_no_args args_part;
        Expect_stuck
      | "EXPECT-WELL-FORMED" :: args_part ->
        assert_no_args args_part;
        Expect_well_formed
      | "EXPECT-ILL-FORMED" :: args_part ->
        assert_no_args args_part;
        Expect_ill_formed
      | "EXPECT-ANALYSIS-STACK-IS" :: args_part ->
        let args_str = String.join "" args_part in
        _parse_analysis_stack_args args_str
      | "EXPECT-INPUT-IS"::args_part ->
        _parse_input args_part
      | "EXPECT-ANALYSIS-LOOKUP-FROM-END" :: args_part ->
        let args_str = String.join "" args_part in
        let args = whitespace_split ~max:2 args_str in
        let (ident_str, pp_expectation) = assert_two_args args in
        let ident = Ident(ident_str) in
        Expect_analysis_variable_lookup_from_end(ident,pp_expectation)
      | "EXPECT-ANALYSIS-INCONSISTENCY-AT" :: args_part ->
        let args_str = String.join "" args_part in
        let args = whitespace_split args_str in
        let call_site = assert_one_arg args in
        Expect_analysis_inconsistency_at (Ident(call_site))
      | "EXPECT-ANALYSIS-NO-INCONSISTENCIES" :: args_part ->
        assert_no_args args_part;
        Expect_analysis_no_inconsistencies
      | _ ->
        raise @@ Expectation_not_found
    in
    Some (Success expectation)
  with
  | Expectation_parse_failure s -> Some (Failure s)
  | Expectation_not_found -> None
;;

(* **** Expectation observation functions **** *)

(* Functions return None if the expectation is satisfied to remove said
   expectation from the list, returns Some to keep it if the expectation
   is irrelevant, and assert_failure is the expectation fails. *)

let observe_evaluated expectation =
  match expectation with
  | Expect_evaluate -> None
  | Expect_stuck ->
    assert_failure @@ "Evaluation completed but was expected to become stuck."
  | _ -> Some expectation
;;

let observe_stuck failure expectation =
  match expectation with
  | Expect_evaluate ->
    assert_failure @@ "Evaluation became stuck: " ^ failure
  | Expect_stuck -> None
  | _ -> Some expectation
;;

let observe_well_formed expectation =
  match expectation with
  | Expect_well_formed -> None
  | Expect_ill_formed ->
    assert_failure @@ "Well-formedness check passed but was expect to fail."
  | _ -> Some expectation
;;

let observe_ill_formed illformednesses expectation =
  match expectation with
  | Expect_well_formed ->
    assert_failure @@ "Expression was unexpectedly ill-formed.  Causes:" ^
                      "\n    * " ^ concat_sep "\n    *"
                        (List.enum @@
                         List.map show_illformedness illformednesses)
  | Expect_ill_formed -> None
  | _ -> Some expectation
;;

let observe_analysis_stack_selection chosen_stack_ref expectation =
  match expectation with
  | Expect_analysis_stack_is module_option ->
    begin
      chosen_stack_ref :=
        begin
          match !chosen_stack_ref with
          | Default_stack -> Chosen_stack module_option
          | Chosen_stack _ ->
            assert_failure @@ "multiple expectations of analysis stack"
        end;
      None
    end
  | _ -> Some expectation
;;

let observe_input_selection input_ref expectation =
  match expectation with
  | Expect_input_is inputs ->
    begin
      input_ref :=
        begin
          match !input_ref with
          | None -> Some inputs
          | Some _ ->
            assert_failure @@ "multiple expectations of input"
        end;
      None
    end
  | _ -> Some expectation
;;


let observe_analysis_variable_lookup_from_end ident repr expectation =
  match expectation with
  | Expect_analysis_variable_lookup_from_end(ident',repr') ->
    if ident = ident'
    then
      begin
        if repr = repr'
        then None
        else assert_failure @@
          Printf.sprintf "for variable %s, expected %s but got %s"
            (show_ident ident) repr' repr
      end
    else Some expectation
  | _ -> Some expectation
;;

let observe_inconsistency inconsistency expectation =
  let site_of_inconsistency =
    let open Toploop_analysis_types in
    match inconsistency with
    | Application_of_non_function (Abs_var ident,_,_,_) -> ident
    | Invalid_binary_operation (Abs_var ident,_,_,_,_,_) -> ident
    | Projection_of_non_record (Abs_var ident,_,_) -> ident
    | Projection_of_absent_label (Abs_var ident,_,_,_) -> ident
  in
  match expectation with
  | Expect_analysis_inconsistency_at expected_site ->
    if site_of_inconsistency = expected_site
    then None
    else Some expectation
  | _ -> Some expectation
;;

let observe_no_inconsistency expectation =
  match expectation with
  | Expect_analysis_no_inconsistencies -> None
  | _ -> Some expectation
;;

(* **** Testing **** *)

(* This routine takes an observation function and applies it to all of the
    not-yet-handled expectations. *)
let _observation filename expectations_left f =
  let exp_l' = List.filter_map f expectations_left in
  lazy_logger `trace (fun () ->
    Printf.sprintf
      "In test for %s, expectations remaining after an observation: %s"
      filename
      (Pp_utils.pp_to_string (Pp_utils.pp_list pp_test_expectation) exp_l'));
  exp_l'
;;

(* This routine detects expectations of a particular form. *)
let _have_expectation expectations_left pred =
  List.exists pred expectations_left
;;

(** Test demand-driven program analysis. *)
let test_ddpa
    (filename : string)
    (expect_left : test_expectation list ref)
    (stack_module_choice : expectation_stack_decision)
    (expr: Ast.expr)
  : unit =
  let observation = _observation filename in
  (* Configure the toploop options *)
  let chosen_module_option =
    match stack_module_choice with
    | Default_stack ->
      Some (module Ddpa_single_element_stack.Stack :
              Ddpa_context_stack.Context_stack)
    | Chosen_stack value -> value
  in
  let variables_to_analyze =
    !expect_left
    |> List.enum
    |> Enum.filter_map
      (function
        | Expect_analysis_variable_lookup_from_end(ident,expected) ->
          Some (ident, expected)
        | _ -> None)
    |> List.of_enum
  in
  let configuration =
    { topconf_context_stack = chosen_module_option;
      topconf_log_prefix = filename ^ "_";
      topconf_ddpa_log_level = None;
      topconf_pdr_log_level = None;
      topconf_pdr_log_deltas = false;
      topconf_graph_log_file_name = "ddpa_test.log.yojson";
      topconf_analyze_vars =
        if variables_to_analyze = []
        then Toploop_option_parsers.Analyze_no_variables
        else
          Toploop_option_parsers.Analyze_specific_variables
            (variables_to_analyze
              |> List.map (fun (Ident s, _) -> (s, None, None)));
      topconf_disable_evaluation =
        not @@ _have_expectation !expect_left
          (function
            | Expect_evaluate -> true
            | Expect_stuck -> true
            | _ -> false);
      topconf_disable_inconsistency_check =
        not @@ _have_expectation !expect_left
          (function
            | Expect_analysis_no_inconsistencies -> true
            | Expect_analysis_inconsistency_at _ -> true
            | _ -> false);
      topconf_disable_analysis = false;
      topconf_report_sizes = false;
      topconf_report_source_statistics = false
    }
  in
  (* Set the inputs we feed into the toploop. *)
  let input_ref = ref None in
  expect_left := observation !expect_left (observe_input_selection input_ref);
  let input_callback =
    match !input_ref with
    | Some inputs ->
      begin
        let buffer = ref inputs in
          (fun () ->
            match !buffer with
            | [] -> failwith "Out of input"
            | head :: tail ->
              buffer := tail;
              head
          )
      end
    | None -> Toploop.default_callbacks.cb_input
  in
  let callbacks =
    { Toploop.default_callbacks with
      cb_input = input_callback
    }
  in
  (* Run the DDPA toploop *)
  lazy_logger `trace (fun () ->
      Printf.sprintf "Test for %s: executing toploop handler" filename);
  let result =
    Toploop.handle_expression
      ~callbacks:callbacks
      configuration
      expr
  in
  lazy_logger `trace (fun () ->
      Printf.sprintf "Test for %s: toploop result was %s"
        filename (Pp_utils.pp_to_string pp_result result));
  (* Report well-formedness or ill-formedness as appropriate. *)
  if result.illformednesses = [] then begin
    expect_left :=
      observation !expect_left observe_well_formed
  end else begin
    expect_left :=
      observation !expect_left (observe_ill_formed result.illformednesses)
  end;
  (* Report each discovered error *)
  List.iter
    (fun error ->
      expect_left := observation !expect_left (observe_inconsistency error)
    )
    result.errors;
  (* If there are no errors, report that. *)
  if result.errors = [] then begin
    expect_left := observation !expect_left observe_no_inconsistency
  end;
  (* Report each resulting variable analysis. *)
  result.analyses
  |> List.iter
    (fun ((varname, _, _), values) ->
      let repr =
        Pp_utils.pp_to_string Ddpa_abstract_ast.Abs_value_set.pp values
      in
      expect_left := observation !expect_left
        (observe_analysis_variable_lookup_from_end (Ident varname) repr)
    );
  (* Now report the result of evaluation. *)
  begin
    match result.evaluation_result with
    | Evaluation_completed _ ->
      expect_left := observation !expect_left observe_evaluated
    | Evaluation_failure failure ->
      expect_left := observation !expect_left (observe_stuck failure)
    | Evaluation_invalidated -> ()
    | Evaluation_disabled -> ()
  end;
;;

let make_test filename expectations =
  let test_name =
    filename ^ ": (" ^ string_of_list name_of_expectation expectations ^ ")"
  in
  (* Create the test in a thunk. *)
  let test_thunk _ =
    lazy_logger `trace (fun () ->
        Printf.sprintf "Performing test for %s with expectations: %s"
          filename
          (Pp_utils.pp_to_string (Pp_utils.pp_list pp_test_expectation)
             expectations)
      );
    (* Using a mutable list of not-yet-handled expectations. *)
    let expectations_left = ref expectations in
    (* Translate code if it's natodefa *)
    let is_natodefa = String.ends_with filename "natodefa" in
    let (i_expr, _) =
      if is_natodefa then begin
        On_to_odefa.translate
          @@ File.with_file_in filename On_parse.parse_program
      end else begin
        Odefa_instrumentation.instrument_odefa
          @@ File.with_file_in filename Parser.parse_program
      end
    in
    (* Decide what kind of analysis to perform. *)
    let module_choice = ref Default_stack in
    let obs = _observation filename in
    expectations_left :=
      obs !expectations_left (observe_analysis_stack_selection module_choice);
    (* Perform tests *)
    try
      test_ddpa filename expectations_left !module_choice i_expr;
    with Ast_wellformedness.Illformedness_found _ -> ();
    (* Now assert that every expectation has been addressed. *)
    match !expectations_left with
    | [] -> ()
    | expectations' ->
      assert_failure @@
        "The following expectations could not be met:" ^ "\n" ^
        "    * " ^
        concat_sep
          "\n    * "
          (List.enum @@ List.map name_of_expectation expectations')
  in
  test_name >:: test_thunk
;;

let make_test_from filename =
  let expectation_from_str str =
    let str' = String.trim str in
       if String.starts_with str' "#"
       then
         let str'' = String.trim @@ String.tail str' 1 in
         match parse_expectation str'' with
         | Some (Success expectation) -> Some(Success expectation)
         | Some (Failure s) -> Some(Failure(
             Printf.sprintf
               "Error parsing expectation:\n        Error: %s\n        Text:  %s"
               s str''))
         | None -> None
       else None
  in
  let expectations =
    filename
    |> File.lines_of
    |> Enum.filter_map expectation_from_str
    |> List.of_enum
  in
  let failures =
    expectations
    |> List.filter_map
      (function
        | Success _ -> None
        | Failure s -> Some s
      )
  in
  match failures with
  | [] ->
    let successes =
      expectations
      |> List.filter_map
        (function
          | Success expectation -> Some expectation
          | Failure _ -> None
        )
    in
    begin
      match successes with
      | [] -> raise (File_test_creation_failure(
          "Could not create test from file " ^ filename ^
          ": no expectations found"))
      | _ ->
        make_test filename successes
    end
  | _ ->
    let message = "Could not create test from file " ^ filename ^ ":" in
    let message' =
      failures
      |> List.fold_left
        (fun msg err -> msg ^ "\n    " ^ err) message
    in
    raise (File_test_creation_failure message')
;;

let wrap_make_test_from filename =
  try
    make_test_from filename
  with
  | File_test_creation_failure s ->
    filename >:: function _ -> assert_failure s
;;

let make_tests_from_dir pathname =
  let legal_exts = [".odefa"; ".natodefa"] in
  if Sys.file_exists pathname && Sys.is_directory pathname
  then
    Sys.files_of pathname
    |> Enum.map (fun f -> pathname ^ Filename.dir_sep ^ f)
    |> Enum.filter (fun f -> not @@ Sys.is_directory f)
    |> Enum.filter (fun f ->
        (List.fold_left
          (fun acc -> fun legal_ext -> acc || (String.ends_with f legal_ext))
          false legal_exts))
    |> Enum.map wrap_make_test_from
    |> List.of_enum
  else
    raise (File_test_creation_failure(
        "Test file directory " ^ pathname ^ " is missing"))
;;

let tests =
  "Test_source_files" >::: (
    make_tests_from_dir "test/test-sources"
    @ make_tests_from_dir "test/test-sources/odefa-basic"
    (* @ make_tests_from_dir "test/test-sources/odefa-fails" *)
    (* @ make_tests_from_dir "test/test-sources/odefa-input" *)
    (* @ make_tests_from_dir "test/test-sources/odefa-stack" *)
    @ make_tests_from_dir "test/test-sources/odefa-types"
    @ make_tests_from_dir "test/test-sources/natodefa-basic"
    @ make_tests_from_dir "test/test-sources/natodefa-types"
    (* @ make_tests_from_dir "test-sources/natodefa-input" *)
  )
;;