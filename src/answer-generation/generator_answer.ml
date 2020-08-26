open Batteries;;
(* open Jhupllib;; *)

open Odefa_ast;;
open Ast;;

open Odefa_symbolic_interpreter;;
open Odefa_symbolic_interpreter.Interpreter_types;;
open Odefa_symbolic_interpreter.Interpreter;;

open Odefa_natural;;

(* let lazy_logger = Jhupllib.Logger_utils.make_lazy_logger "Generator_answer";; *)

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
  val test_mem : t list -> t -> bool;;
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
    let (input_seq, ab_symbol_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
    match ab_symbol_opt with
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

  let test_mem input_seq_list input_seq = List.mem input_seq input_seq_list;;
end;;

(* **** Type Errors **** *)

module Type_errors : Answer = struct
  
  type error_seq = {
    err_errors : Error.Odefa_error.t list;
    err_input_seq : int list;
  }
  ;;

  type t = error_seq;;

  let odefa_on_maps_option_ref = ref None;;

  (* Remove variables added during instrumentation *)
  let _remove_instrument_vars
      (odefa_on_maps : On_to_odefa_maps.t)
      (error : t)
    : t =
    let rm_inst_var_fn = On_error.odefa_error_remove_instrument_vars odefa_on_maps in
    let error_list = error.err_errors in
    let error_list' = List.map rm_inst_var_fn error_list in
    {
      error with
      err_errors = error_list';
    }
  ;;

  let answer_from_result e x result =
    let error_list_map = result.er_errors in
    let (input_seq, abort_symb_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
    let error_list =
      match abort_symb_opt with
      | Some abort_symb -> Symbol_map.find abort_symb error_list_map
      | None -> []
    in
    let errs =
      {
        err_input_seq = input_seq;
        err_errors = error_list;
      }
    in
    match !odefa_on_maps_option_ref with
    | Some odefa_on_maps -> _remove_instrument_vars odefa_on_maps errs
    | None -> failwith "Odefa/natodefa maps were not set!"
  ;;

  (* Ex: [0, 1] : "a = b" "c = 2" "sum = a or z" "int" "bool" *)
  let answer_from_string arg_str =
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

  let set_odefa_natodefa_map odefa_on_maps =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let show_input_seq input_seq =
    "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
  ;;

  let show error_seq =
    if not @@ List.is_empty error_seq.err_errors then begin
      "Type errors for input sequence " ^
      (show_input_seq error_seq.err_input_seq) ^ ":\n" ^
      (String.join "\n-----------------\n"
        @@ List.map Error.Odefa_error.show error_seq.err_errors)
    end else begin
      ""
    end
  ;;

  let count errors = List.length  errors.err_errors;;

  let count_list error_list =
    error_list
    |> List.map count
    |> List.fold_left (fun a x -> x + a) 0
  ;;

  (* Currently always returns true; no mechanism to detect failed answer gen *)
  let generation_successful (_: t) = true;;

  (*
  let test_mem (error_list: t list) (error: t) =
    let input_seq = error.err_input_seq in
    let error_lists = error.err_errors in
    let error_assoc_list =
      List.map
        (fun err -> (err.err_input_seq, err.err_errors))
        error_list
    in
    let error_list_list = List.assoc input_seq error_assoc_list in
    match error_lists with
    | [error_list] ->
      error_list_list
      |> List.filter (Error_list.mem_singleton error_list)
      |> List.is_empty
      |> Bool.not
    | _ ->
      failwith "test_mem can only test single error"
  ;;
  *)

  let test_mem _ _ = false;;
end;;

module Natodefa_type_errors : Answer = struct
  type error_seq = {
    err_errors : On_error.On_error.t list;
    err_input_seq : int list;
  }
  ;;

  type t = error_seq;;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result e x result =
    let error_list_map = result.er_errors in
    let (input_seq, abort_symb_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
    match abort_symb_opt with
    | Some abort_symb ->
      begin
        let error_list = Symbol_map.find abort_symb error_list_map in
        match !odefa_on_maps_option_ref with
        | Some odefa_on_maps ->
          let on_error_list =
            List.map (On_error.odefa_to_natodefa_error odefa_on_maps) error_list
          in
          {
            err_input_seq = input_seq;
            err_errors = on_error_list;
          }
        | None ->
          failwith "Odefa/natodefa maps were not set!"
      end
    | None ->
      {
        err_input_seq = input_seq;
        err_errors = [];
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

  (*
  let test_mem (error_list: t list) (error: t) =
    let input_seq = error.err_input_seq in
    let error_lst = error.err_errors in
    let error_assoc_list =
      List.map
        (fun err -> (err.err_input_seq, err.err_errors))
        error_list
    in
    let error_lst' = List.assoc input_seq error_assoc_list in
    On_error.Error_list.mem_singleton error_lst' error_lst
  ;;
  *)

  let test_mem _ _ = false;;
end;;