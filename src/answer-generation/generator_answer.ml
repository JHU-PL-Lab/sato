open Batteries;;
(* open Jhupllib;; *)

open Odefa_ast;;
open Ast;;

open Odefa_symbolic_interpreter;;
open Odefa_symbolic_interpreter.Interpreter;;

open Odefa_natural;;


exception Parse_failure;;

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
end;;

(* Utility to parse int sequences separated by commas. *)
let parse_comma_separated_ints lst_str =
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
    raise Parse_failure
;;

(* **** Input sequence **** *)

module Input_sequence : Answer = struct
  type t = int list option;;

  let answer_from_result e x result =
    let (input_seq, error_list) =
      Generator_utils.input_sequence_from_result e x result
    in
    match error_list with
    | [] -> Some input_seq
    | _ -> None
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
  };;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result e x result : t =
    let (input_seq, error_list) =
      Generator_utils.input_sequence_from_result e x result
    in
    match !odefa_on_maps_option_ref with
    | Some odefa_on_maps ->
      let rm_inst_fn =
        On_error.odefa_error_remove_instrument_vars odefa_on_maps
      in
      {
        err_input_seq = input_seq;
        err_errors = List.map rm_inst_fn error_list;
      }
    | None -> failwith "Odefa/natodefa maps were not set!"
  ;;

  (* Ex: [0, 1] : "a = b" "c = 2" "sum = a or z" "int" "bool" *)
  let answer_from_string arg_str : t =
    let (input_str, error_str) =
      arg_str
      |> String.split ~by:":"
      |> (fun (i_str, e_str) -> (String.trim i_str, String.trim e_str))
    in
    let inputs = parse_comma_separated_ints input_str in
    let error = Error.Odefa_error.parse error_str in
    {
      err_input_seq = inputs;
      err_errors = [error];
    }
  ;;

  let set_odefa_natodefa_map odefa_on_maps : unit =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let show_input_seq input_seq =
    "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
  ;;

  let show (error_seq : t) : string =
    if not @@ List.is_empty error_seq.err_errors then begin
      "Type errors for input sequence " ^
      (show_input_seq error_seq.err_input_seq) ^ ":\n" ^
      (String.join "\n-----------------\n"
        @@ List.map Error.Odefa_error.show error_seq.err_errors)
    end else begin
      ""
    end
  ;;

  let count (errors : t) = List.length errors.err_errors;;

  let count_list error_list =
    error_list
    |> List.map count
    |> List.fold_left (fun a x -> x + a) 0
  ;;

  (* Currently always returns true; no mechanism to detect failed answer gen *)
  let generation_successful (_: t) = true;;

  let test_expected (expect_errs : t) (actual_errs : t) =
    let exp_inputs = expect_errs.err_input_seq in
    let act_inputs = actual_errs.err_input_seq in
    let exp_errors = expect_errs.err_errors in
    let act_errors = expect_errs.err_errors in
    if exp_inputs <> act_inputs then false else begin
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
  };;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result e x result =
    let (input_seq, error_list) =
      Generator_utils.input_sequence_from_result e x result
    in
    let on_error_list =
      match !odefa_on_maps_option_ref with
      | Some odefa_on_maps ->
        List.map (On_error.odefa_to_natodefa_error odefa_on_maps) error_list
      | None -> failwith "Odefa/natodefa maps were not set!"
    in
    {
      err_input_seq = input_seq;
      err_errors = on_error_list;
    }
  ;;

  let answer_from_string arg_str =
    let (input_str, error_str) =
      arg_str
      |> String.split ~by:":"
      |> (fun (i_str, e_str) -> (String.trim i_str, String.trim e_str))
    in
    let inputs = parse_comma_separated_ints input_str in
    let error = On_error.On_error.parse error_str in
    {
      err_input_seq = inputs;
      err_errors = [error];
    }
  ;;

  let set_odefa_natodefa_map odefa_on_maps =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let show_input_seq input_seq =
    "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
  ;;

  let show error =
    if not @@ List.is_empty error.err_errors then begin
      "Type errors for input sequence " ^
      (show_input_seq error.err_input_seq) ^ ":\n" ^
      (String.join "\n-----------------\n"
        @@ List.map On_error.On_error.show error.err_errors)
    end else begin
      ""
    end
  ;;

  let count error =
    List.length error.err_errors
  ;;

  let count_list error_list =
    List.fold_left
      (fun acc error -> acc + (count error))
      0
      error_list
  ;;

  let generation_successful _ = true;;

  let test_expected (expect_errs : t) (actual_errs : t) =
    let exp_inputs = expect_errs.err_input_seq in
    let act_inputs = actual_errs.err_input_seq in
    let exp_errors = expect_errs.err_errors in
    let act_errors = expect_errs.err_errors in
    if exp_inputs <> act_inputs then false else begin
      let is_mem err =
        List.exists (On_error.On_error.equal err) act_errors
      in
      not @@ List.is_empty (List.filter is_mem exp_errors)
    end
  ;;
end;;