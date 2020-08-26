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

  (* **** Remove variables added during instrumentation **** *)

  let remove_instrument_vars_error
      (odefa_on_maps : On_to_odefa_maps.t)
      (error : Error.Odefa_error.t)
    : Error.Odefa_error.t =
    match error with
    | Error_binop err ->
      begin
        let binop_cls = err.err_binop_clause in
        let left_aliases = err.err_binop_left_aliases in
        let right_aliases = err.err_binop_right_aliases in
        let (Clause (Var (b_ident, _), _)) = binop_cls in
        let binop_cls' =
          try
            On_to_odefa_maps.get_pre_inst_equivalent_clause
              odefa_on_maps b_ident
          with Not_found ->
            binop_cls
        in
        let left_aliases' =
          List.filter
            (fun a -> not @@
              On_to_odefa_maps.is_var_instrumenting odefa_on_maps a)
            left_aliases
        in
        let right_aliases' =
          List.filter
            (fun a -> not @@
              On_to_odefa_maps.is_var_instrumenting odefa_on_maps a)
            right_aliases
        in
        Error_binop {
          err with
          err_binop_clause = binop_cls';
          err_binop_left_aliases = left_aliases';
          err_binop_right_aliases = right_aliases';
        }
      end
    | Error_match err ->
      begin
        let match_cls = err.err_match_clause in
        let (Clause (Var (v_match, _), _)) = match_cls in
        let match_aliases = err.err_match_aliases in
        let match_aliases' =
          List.filter
            (* Stacks aren't set during instrumenting, so we're safe *)
            (fun a -> not @@
              On_to_odefa_maps.is_var_instrumenting odefa_on_maps a)
            match_aliases
        in
        let match_cls' =
          On_to_odefa_maps.get_pre_inst_equivalent_clause
            odefa_on_maps v_match
        in
        Error_match {
          err with
          err_match_aliases = match_aliases';
          err_match_clause = match_cls';
        }
      end
    | Error_value err ->
      begin
        let aliases = err.err_value_aliases in
        let val_clause = err.err_value_clause in
        let (Clause (Var (x, _), _)) = val_clause in
        let aliases' =
          List.filter
            (fun a -> not @@
              On_to_odefa_maps.is_var_instrumenting odefa_on_maps a)
            aliases
        in
        let clause' =
          On_to_odefa_maps.get_pre_inst_equivalent_clause
            odefa_on_maps x
        in
        Error_value {
          err with
          err_value_aliases = aliases';
          err_value_clause = clause';
        }
      end
  ;;

  let remove_instrument_vars
      (odefa_on_maps : On_to_odefa_maps.t)
      (error : t)
    : t =
    let rm_inst_var_fn = remove_instrument_vars_error odefa_on_maps in
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
    | Some odefa_on_maps -> remove_instrument_vars odefa_on_maps errs
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
    err_errors : On_error.Error_list.t;
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
    let abort_list =
      match abort_symb_opt with
      | Some abort_symb -> [abort_symb]
      | None -> []
    in
    if List.is_empty abort_list then begin
      {
        err_input_seq = input_seq;
        err_errors = On_error.Error_list.empty;
      }
    end else begin
      let abort = List.first abort_list in
      let error_list = Symbol_map.find abort error_list_map in
      match !odefa_on_maps_option_ref with
      | Some odefa_on_maps ->
        let on_error_list =
          List.map (On_error.odefa_to_natodefa_error odefa_on_maps) error_list
        in
        {
          err_input_seq = input_seq;
          err_errors = On_error.Error_list.wrap on_error_list;
        }
      | None ->
        failwith "Odefa/natodefa maps were not set!"
    end
  ;;

  let answer_from_string arg_str =
    let (input_str, error_str) =
      arg_str
      |> String.split ~by:":"
      |> (fun (i_str, e_str) -> (String.trim i_str, String.trim e_str))
    in
    let inputs = parse_comma_separated_ints input_str in
    let error = On_error.parse_error error_str in
    let err_list = On_error.Error_list.wrap [error] in
    {
      err_input_seq = inputs;
      err_errors = err_list;
    }
  ;;

  let set_odefa_natodefa_map odefa_on_maps =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let show_input_seq input_seq =
    "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
  ;;

  let show error =
    if not @@ On_error.Error_list.is_empty error.err_errors then begin
      "Type errors for input sequence " ^
      (show_input_seq error.err_input_seq) ^ ":\n" ^
      (On_error.Error_list.to_string error.err_errors)
    end else begin
      ""
    end
  ;;

  let count error =
    On_error.Error_list.count error.err_errors
  ;;

  let count_list error_list =
    List.fold_left
      (fun acc error -> acc + (count error))
      0
      error_list
  ;;

  let generation_successful _ = true;;

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

end;;