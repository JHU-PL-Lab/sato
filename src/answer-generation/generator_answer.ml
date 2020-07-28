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

  (*
  let test_str input_list str =
    let i = answer_from_string str in
    List.mem i input_list
  ;;
  *)
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

  let count type_errors = List.length type_errors.err_errors;;

  let count_list type_error_list =
    type_error_list
    |> List.map count
    |> List.fold_left (fun a x -> x + a) 0
  ;;

  (* Currently always returns true; no mechanism to detect failed answer gen *)
  let generation_successful (_: t) = true;;
end;;