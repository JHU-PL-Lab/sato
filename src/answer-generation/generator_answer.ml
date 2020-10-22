open Batteries;;
(* open Jhupllib;; *)

open Odefa_ast;;
open Ast;;

open Odefa_symbolic_interpreter;;
open Odefa_symbolic_interpreter.Interpreter;;

open Odefa_natural;;


exception Parse_failure of string;;

module type Answer = sig
  type t;;
  val answer_from_result : expr -> ident -> evaluation_result -> t;;
  val answer_from_string : string -> t;;
  val set_odefa_natodefa_map : On_to_odefa_maps.t -> unit;;
  val show : t -> string;;
  val count : t -> int;;
  val count_list : t list -> int;;
  val generation_successful : t -> bool;;
  val test_expected : t -> t -> bool;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

(* **** String parsing utilities **** *)

(* Utility to parse int sequences separated by commas. *)
let parse_comma_separated_ints (lst_str : string) : int list =
  let lst_str' =
    if (String.starts_with lst_str "[") &&
         (String.ends_with lst_str "]") then
      lst_str
      |> String.lchop
      |> String.rchop
    else
      lst_str
  in
  let str_lst =
    lst_str'
    |> Str.global_replace (Str.regexp "[ ]*") ""
    |> Str.split (Str.regexp ",")
  in
  try
    List.map int_of_string str_lst
  with Failure _ ->
    raise @@ Parse_failure "Unable to parse int list"
;;

let split_with_regexp (re : Str.regexp) (str : string) : (string * string) =
  if Str.string_match re str 0 then
    let split_pos = Str.match_end () in
    let prefix = String.trim @@ Str.string_before str split_pos in
    let suffix = String.trim @@ Str.string_after str split_pos in
    (prefix, suffix)
  else
    raise @@ Parse_failure "string does not match on regexp"
;;

(* **** String showing utilities **** *)

let show_input_seq (input_seq : int list) =
  "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
;;

(* **** Input sequence **** *)

module Input_sequence : Answer = struct
  type t = int list option
  [@@ deriving to_yojson]
  ;;

  let answer_from_result e x result =
    let (input_seq, error_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
    match error_opt with
    | None -> Some input_seq
    | Some _ -> None
  ;;

  (* String "[ 1, 2, 3 ]" or "1, 2, 3" to input sequence *)
  let answer_from_string arg_str =
    Some (parse_comma_separated_ints arg_str)
  ;;

  (* Unused for input sequence generation. *)
  let set_odefa_natodefa_map (_ : On_to_odefa_maps.t) = ();;

  let show inputs_opt =
    match inputs_opt with
    | Some inputs ->
      "[" ^ (String.join ", " @@ List.map string_of_int inputs) ^ "]"
    | None -> "???"
  ;;

  let count inputs_opt =
    match inputs_opt with
    | Some _ -> 1
    | None -> 0 (* Fail silently *)
  ;;

  let count_list (inputs_opt_lst : t list) =
    inputs_opt_lst
    |> List.filter_map identity
    |> List.length
  ;;

  let generation_successful inputs_opt =
    match inputs_opt with
    | Some _ -> true
    | None -> false
  ;;

  let test_expected expected_inputs actual_inputs =
    expected_inputs = actual_inputs
  ;;
end;;

(* **** Type Errors **** *)

module Type_errors : Answer = struct
  
  type t = {
    err_errors : Error.Odefa_error.t list;
    err_input_seq : int list;
    err_location : Ast.clause option;
  }
  [@@ deriving to_yojson]
  ;;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result e x result : t =
    let (input_seq, error_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
    match !odefa_on_maps_option_ref with
    | Some odefa_on_maps ->
      begin
        match error_opt with
        | Some (error_loc, error_list) ->
          let rm_inst_fn =
            On_error.odefa_error_remove_instrument_vars odefa_on_maps
          in
          let trans_inst_fn =
            On_to_odefa_maps.get_pre_inst_equivalent_clause odefa_on_maps
          in
          {
            err_input_seq = input_seq;
            err_location = Some (trans_inst_fn error_loc);
            err_errors = List.map rm_inst_fn error_list;
          }
        | None ->
          {
            err_input_seq = input_seq;
            err_location = None;
            err_errors = [];
          }
      end
    | None -> failwith "Odefa/natodefa maps were not set!"
  ;;

  (* Ex: [0, 1] "sum = a or z" "a = b" "c = 2" "int" "bool" *)
  let answer_from_string arg_str : t =
    let (input_str, loc_err_str) =
      split_with_regexp (Str.regexp "\\[[^][]*\\]") arg_str
    in
    let (loc_str, error_str) =
      split_with_regexp (Str.regexp "\"[^\"]*\"") loc_err_str
    in
    let loc_str =
      (* Remove quotes *)
      loc_str
      |> String.lchop
      |> String.rchop
    in
    let inputs = parse_comma_separated_ints input_str in
    let location =
      try
        Odefa_parser.Parser.parse_clause_string loc_str
      with Odefa_parser.Parser.Parse_error _ ->
        failwith (Printf.sprintf "Cannot parse clause %s" loc_str)
    in
    let error = Error.Odefa_error.parse error_str in
    {
      err_input_seq = inputs;
      err_location = Some location;
      err_errors = [error];
    }
  ;;

  let set_odefa_natodefa_map odefa_on_maps : unit =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let show (error : t) : string =
    match error.err_location with
    | Some error_loc ->
      "Type errors for:\n" ^
      "- Input sequence  : " ^ (show_input_seq error.err_input_seq) ^ "\n" ^
      "- Found at clause : " ^ (Ast_pp.show_clause error_loc) ^ "\n" ^
      "--------------------\n" ^
      (String.join "\n--------------------\n"
        @@ List.map Error.Odefa_error.show error.err_errors)
    | None -> "** No errors found on this run. **"
  ;;

  let count (errors : t) = List.length errors.err_errors;;

  let count_list error_list =
    error_list
    |> List.map count
    |> List.sum
  ;;

  let generation_successful error =
    match error.err_location with
    | Some _ -> true
    | None -> false
  ;;

  let test_expected (expect_errs : t) (actual_errs : t) =
    let exp_inputs = expect_errs.err_input_seq in
    let act_inputs = actual_errs.err_input_seq in
    let exp_loc = expect_errs.err_location in
    let act_loc = actual_errs.err_location in
    let exp_errors = expect_errs.err_errors in
    let act_errors = expect_errs.err_errors in
    if (exp_inputs <> act_inputs) || (exp_loc <> act_loc) then false else
      begin
        let is_mem err =
          List.exists (Error.Odefa_error.equal err) act_errors
        in
        not @@ List.is_empty (List.filter is_mem exp_errors)
      end
  ;;
end;;

module Natodefa_type_errors : Answer = struct

  type t = {
    err_errors : On_error.On_error.t list;
    err_input_seq : int list;
    err_location : On_ast.expr option;
  }
  [@@ deriving to_yojson]
  ;;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result e x result =
    let (input_seq, error_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
      match !odefa_on_maps_option_ref with
      | Some odefa_on_maps ->
        begin
          match error_opt with
          | Some (error_loc, error_lst) ->
            let on_err_loc =
              On_to_odefa_maps.get_natodefa_equivalent_expr odefa_on_maps error_loc
            in
            let on_err_list =
              List.map (On_error.odefa_to_natodefa_error odefa_on_maps) error_lst
            in
            {
              err_input_seq = input_seq;
              err_location = Some on_err_loc;
              err_errors = on_err_list;
            }
          | None ->
            {
              err_input_seq = input_seq;
              err_location = None;
              err_errors = [];
            }
        end
      | None -> failwith "Odefa/natodefa maps were not set!"
  ;;

  let answer_from_string arg_str =
    let (input_str, loc_err_str) =
      split_with_regexp (Str.regexp "\\[[^][]*\\]") arg_str
    in
    let (loc_str, error_str) =
      split_with_regexp (Str.regexp "\"[^\"]*\"") loc_err_str
    in
    let loc_str =
      (* Remove quotes *)
      loc_str
      |> String.lchop
      |> String.rchop
    in
    let inputs = parse_comma_separated_ints input_str in
    let location = Odefa_natural.On_parse.parse_single_expr_string loc_str in
    let error = On_error.On_error.parse error_str in
    {
      err_input_seq = inputs;
      err_location = Some location;
      err_errors = [error];
    }
  ;;

  let set_odefa_natodefa_map odefa_on_maps =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let show error =
    match error.err_location with
    | Some error_loc ->
      "Type errors for:\n" ^
      "- Input sequence : " ^ (show_input_seq error.err_input_seq) ^ "\n" ^
      "- Found at expr  : " ^ (On_ast_pp.show_expr error_loc) ^ "\n" ^
      "--------------------\n" ^
      (String.join "\n--------------------\n"
        @@ List.map On_error.On_error.show error.err_errors)
    | None -> ""
  ;;

  let count error = List.length error.err_errors;;

  let count_list error_list =
    error_list
    |> List.map count
    |> List.sum
  ;;

  let generation_successful error =
    match error.err_location with
    | Some _ -> true
    | None -> false
  ;;

  let test_expected (expect_errs : t) (actual_errs : t) =
    let exp_inputs = expect_errs.err_input_seq in
    let act_inputs = actual_errs.err_input_seq in
    let exp_loc = expect_errs.err_location in
    let act_loc = actual_errs.err_location in
    let exp_errors = expect_errs.err_errors in
    let act_errors = expect_errs.err_errors in
    if (exp_inputs <> act_inputs) || (exp_loc <> act_loc) then false else
      begin
        let is_mem err =
          List.exists (On_error.On_error.equal err) act_errors
        in
        not @@ List.is_empty (List.filter is_mem exp_errors)
      end
  ;;
end;;