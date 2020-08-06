open Batteries;;
(* open Jhupllib;; *)

open Odefa_ast;;
open Ast;;

open Odefa_symbolic_interpreter.Error;;
open Odefa_symbolic_interpreter.Interpreter_types;;
open Odefa_symbolic_interpreter.Interpreter;;

open Odefa_natural;;
open On_to_odefa_types;;

(* let lazy_logger = Jhupllib.Logger_utils.make_lazy_logger "Generator_answer";; *)

exception Parse_failure;;

module type Answer = sig
  type t;;
  val answer_from_result : expr -> ident -> evaluation_result -> t;;
  val answer_from_string : string -> t;;
  val set_odefa_natodefa_map : Odefa_natodefa_mappings.t -> unit;;
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
    let (input_seq, ab_symb_list) =
      Generator_utils.input_sequence_from_result e x result
    in
    (* lazy_logger `trace (fun () -> "Abort symbols: " ^ (String.join ", " @@ List.map show_symbol ab_symb_list)); *)
    if List.is_empty ab_symb_list then
      Some input_seq
    else
      None
  ;;

  (* String "[ 1, 2, 3 ]" or "1, 2, 3" to input sequence *)
  let answer_from_string arg_str =
    Some (parse_comma_separated_ints arg_str)
  ;;

  (* Unused for input sequence generation. *)
  let set_odefa_natodefa_map (_ : Odefa_natodefa_mappings.t) = ();;

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
    err_errors : Error_tree.t list;
    err_input_seq : int list;
  }
  ;;

  type t = error_seq;;

  let odefa_on_maps_option_ref = ref None;;

  (* **** Remove variables added during instrumentation **** *)

  let remove_instrument_vars_error
      (odefa_on_maps : Odefa_natodefa_mappings.t)
      (error : error)
    : error =
    match error with
    | Error_binop err->
      begin
        let binop_cls = err.err_binop_clause in
        let (Clause (Var (b_ident, _), _)) = binop_cls in
        let binop_cls' =
          try
            Odefa_natodefa_mappings.get_pre_inst_equivalent_clause
              odefa_on_maps b_ident
          with Not_found ->
            binop_cls
        in
        Error_binop {
          err with
          err_binop_clause = binop_cls';
        }
      end
    | Error_match err ->
      begin
        let instrument_vars = odefa_on_maps.odefa_instrument_vars_map in
        let val_cls = err.err_match_value in
        let match_cls = err.err_match_clause in
        let (Clause (Var (v_val, _), _)) = val_cls in
        let (Clause (Var (v_match, _), _)) = match_cls in
        let match_aliases = err.err_match_aliases in
        let (value_cls'', match_aliases') =
          try
            (* Replace the var in the value clause *)
            let val_cls' =
              Odefa_natodefa_mappings.get_pre_inst_equivalent_clause
                odefa_on_maps v_val
            in
            (* Remove extra var from alias chain *)
            let Clause (Var (val_ident', _), _) = val_cls' in
            (val_cls', List.remove match_aliases val_ident')
          with Not_found ->
            (val_cls, match_aliases)
        in
        let match_aliases'' =
          List.filter
            (* Stacks aren't set during instrumenting, so we're safe *)
            (fun a -> not @@ Ident_map.mem a instrument_vars)
            match_aliases'
        in
        let match_cls'' =
          Odefa_natodefa_mappings.get_pre_inst_equivalent_clause
            odefa_on_maps v_match
        in
        Error_match {
          err with
          err_match_aliases = match_aliases'';
          err_match_clause = match_cls'';
          err_match_value = value_cls'';
        }
      end
  ;;

  let remove_instrument_vars
      (odefa_on_maps : Odefa_natodefa_mappings.t)
      (error : t)
    : t =
    let rm_inst_var_fn = remove_instrument_vars_error odefa_on_maps in
    let error_list = error.err_errors in
    let error_list' = List.map (Error_tree.map rm_inst_var_fn) error_list in
    {
      error with
      err_errors = error_list';
    }
  ;;

  let answer_from_result e x result =
    let error_tree_map = result.er_errors in
    let (input_seq, abort_list) =
      Generator_utils.input_sequence_from_result e x result
    in
    (* For now, we only report the error associated with the first we encounter
       on a program path, since (during forward evaluation) only code up to
       that abort is "live;" all code afterwards is "dead" code that is
       unreachable in the non-instrumented code.  In the future we can report
       potential errors in "dead" code as well, but only after we prove
       soundness. *)
    let abort_list_singleton =
      if List.is_empty abort_list then [] else [List.first abort_list]
    in
    let error_tree_list =
      List.fold_right
        (fun abort_symb et_list ->
          let et = Symbol_map.find abort_symb error_tree_map in
          et :: et_list
        )
        abort_list_singleton
        []
    in
    let errs =
      {
        err_input_seq = input_seq;
        err_errors = error_tree_list;
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
    let error = parse_error error_str in
    let err_tree = Error_tree.singleton error in
    {
      err_input_seq = inputs;
      err_errors = [err_tree];
    }
  ;;

  let set_odefa_natodefa_map odefa_on_maps =
    odefa_on_maps_option_ref := Some (odefa_on_maps);;
  ;;

  let show_input_seq input_seq =
    "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
  ;;

  let show error_seq =
    if not @@ List.is_empty error_seq.err_errors then begin
      "Type errors for input sequence " ^
      (show_input_seq error_seq.err_input_seq) ^ ":\n" ^
      (String.join "\n-----------------\n"
        @@ List.map Error_tree.to_string error_seq.err_errors)
    end else begin
      ""
    end
  ;;

  let count errors =
    List.fold_left
      (fun count err_tree -> count + (Error_tree.count err_tree))
      0
      errors.err_errors
  ;;

  let count_list error_list =
    error_list
    |> List.map count
    |> List.fold_left (fun a x -> x + a) 0
  ;;

  (* Currently always returns true; no mechanism to detect failed answer gen *)
  let generation_successful (_: t) = true;;

  let test_mem (error_list: t list) (error: t) =
    let input_seq = error.err_input_seq in
    let error_trees = error.err_errors in
    let error_assoc_list =
      List.map
        (fun err -> (err.err_input_seq, err.err_errors))
        error_list
    in
    let error_tree_list = List.assoc input_seq error_assoc_list in
    match error_trees with
    | [error_tree] ->
      error_tree_list
      |> List.filter (Error_tree.mem_singleton error_tree)
      |> List.is_empty
      |> Bool.not
    | _ ->
      failwith "test_mem can only test single error"
  ;;
end;;

(*
module Natodefa_type_errors : Answer = struct
  type error_seq = {
    err_errors :  list;
    err_input_seq : int list;
  }
  ;;
end;;
*)