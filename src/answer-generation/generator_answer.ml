open Batteries;;
(* open Jhupllib;; *)

open Odefa_ast;;
open Ast;;
(* open Ast_pp;; *)

(* open Odefa_symbolic_interpreter;; *)
open Odefa_symbolic_interpreter.Error;;
open Odefa_symbolic_interpreter.Interpreter_types;;
open Odefa_symbolic_interpreter.Interpreter;;
(* open Odefa_symbolic_interpreter.Solver;; *)

(* open Odefa_symbolic_interpreter.Relative_stack;; *)

(* let lazy_logger = Jhupllib.Logger_utils.make_lazy_logger "Generator_answer";; *)

exception Parse_failure;;

module type Answer = sig
  type t;;
  val answer_from_result : expr -> ident -> evaluation_result -> t;;
  val answer_from_string : string -> t;;
  val show : t -> string;;
  val count : t -> int;;
  val count_list : t list -> int;;
  val generation_successful : t -> bool;;
  val remove_instrument_vars : var Var_map.t -> t -> t;;
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

  let show inputs_opt =
    match inputs_opt with
    | Some inputs ->
      "[" ^ (String.join ", " @@ List.map string_of_int inputs) ^ "]"
    | None -> "???"
  ;;

  (*
  let empty = Some [];;

  let is_empty inputs_opt =
    match inputs_opt with
    | Some inputs -> List.is_empty inputs
    | None -> raise @@ Jhupllib.Utils.Invariant_failure "Undefined"
  *)

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

  let remove_instrument_vars (_ : var Var_map.t) (inputs : t) = inputs;;
end;;

(* **** Type Errors **** *)

module Type_errors : Answer = struct

  type error_seq = {
    err_errors : Error_tree.t list;
    err_input_seq : int list;
  }
  ;;

  type t = error_seq;;

  let answer_from_result e x result =
    let error_tree_map = result.er_errors in
    let (input_seq, abort_list) =
      Generator_utils.input_sequence_from_result e x result
    in
    let error_tree_list =
      List.fold_right
        (fun abort_symb et_list ->
          let et = Symbol_map.find abort_symb error_tree_map in
          et :: et_list
        )
        abort_list
        []
    in
    let errs =
      {
        err_input_seq = input_seq;
        err_errors = error_tree_list;
      }
    in
    errs
  ;;

  let answer_from_string arg_str =
    (* Split on square brackets *)
    let (input_str, errors) = String.split ~by:":" arg_str in
    let (input_str, errors) = (String.trim input_str, String.trim errors) in
    let inputs = parse_comma_separated_ints input_str in
    let err_tree = Error_tree.parse errors in
    {
      err_input_seq = inputs;
      err_errors = [err_tree];
    }
  ;;

  let show_input_seq input_seq =
    "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
  ;;

  let show error_seq =
    if not @@ List.is_empty error_seq.err_errors then begin
      "Type errors for input sequence " ^
      (show_input_seq error_seq.err_input_seq) ^ ":\n" ^
      (String.join "\n-----------------\n" @@ List.map Error_tree.to_string error_seq.err_errors)
    end else begin
      ""
    end
  ;;

  let count errors = List.length errors.err_errors;;

  let count_list error_list =
    error_list
    |> List.map count
    |> List.fold_left (fun a x -> x + a) 0
  ;;

  (* Currently always returns true; no mechanism to detect failed answer gen *)
  let generation_successful (_: t) = true;;

  let remove_instrument_vars_error
      (inst_var_map : var Var_map.t)
      (error : error) =
    match error with
    | Error_binop _ -> error
    | Error_match err ->
      begin
        let (Clause (v_val, b_val)) = err.err_match_value in
        let (Clause (v_match, b_match)) = err.err_match_clause in
        let match_aliases = err.err_match_aliases in
        let (value_cls', match_aliases') =
          try
            (* Replace the var in the value clause and remove extra var in
               alias chain *)
            let v_val' = Var_map.find v_val inst_var_map in
            let Var (v_ident', _) = v_val' in
            (Clause (v_val', b_val), List.remove match_aliases v_ident')
          with Not_found ->
            (Clause (v_val, b_val), match_aliases)
        in
        let match_aliases'' =
          List.filter
            (* Stacks aren't set during instrumenting, so we're safe *)
            (fun a -> not @@ Var_map.mem (Var (a, None)) inst_var_map)
            match_aliases'
        in
        let match_cls' =
          try
            let v_match' = Var_map.find v_match inst_var_map in
            Clause (v_match', b_match)
          with Not_found ->
            Clause (v_match, b_match)
        in
        Error_match {
          err with
          err_match_aliases = match_aliases'';
          err_match_clause = match_cls';
          err_match_value = value_cls';
        }
      end
  ;;

  let remove_instrument_vars
      (inst_var_map : var Var_map.t)
      (error : t) =
    let rm_inst_var_fn = remove_instrument_vars_error inst_var_map in
    let error_list = error.err_errors in
    let error_list' = List.map (Error_tree.map rm_inst_var_fn) error_list in
    {
      error with
      err_errors = error_list';
    }
  ;;
end;;