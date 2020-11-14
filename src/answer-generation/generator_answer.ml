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
  val description : string;;
  val answer_from_result : int -> expr -> ident -> evaluation_result -> t;;
  val set_odefa_natodefa_map : On_to_odefa_maps.t -> unit;;
  val show : ?show_steps:bool -> ?is_compact:bool -> t -> string;;
  val count : t -> int;;
  val count_list : t list -> int;;
  val generation_successful : t -> bool;;
  val test_expected : t -> t -> bool;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

(* **** String showing utilities **** *)

let show_input_seq (input_seq : int list) =
  "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
;;

(* **** Input sequence **** *)

module Input_sequence : Answer = struct
  (* TODO: Add steps *)
  type t = int list option
  [@@ deriving to_yojson]
  ;;

  let description = "input";;

  let answer_from_result steps e x result =
    let _ = steps in
    let (input_seq, error_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
    match error_opt with
    | None -> Some input_seq
    | Some _ -> None
  ;;

  (* Unused for input sequence generation. *)
  let set_odefa_natodefa_map (_ : On_to_odefa_maps.t) = ();;

  let show ?show_steps:(show_steps=false) ?is_compact:(is_compact=false) inputs_opt =
    let _ = show_steps in
    match inputs_opt with
    | Some inputs ->
      let input_str =
        "[" ^ (String.join ", " @@ List.map string_of_int inputs) ^ "]"
      in
      if is_compact then
        Printf.sprintf "* %s \n" input_str
      else
        (Printf.sprintf "* Input sequence: %s\n" input_str)
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
    err_steps : int;
  }
  [@@ deriving to_yojson]
  ;;

  let description = "error";;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result steps e x result : t =
    let _ = steps in
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
            err_steps = steps;
          }
        | None ->
          {
            err_input_seq = input_seq;
            err_location = None;
            err_errors = [];
            err_steps = steps;
          }
      end
    | None -> failwith "Odefa/natodefa maps were not set!"
  ;;


  let set_odefa_natodefa_map odefa_on_maps : unit =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  (* TODO: Pretty-print *)

  let show ?show_steps:(show_steps=false) ?is_compact:(is_compact=false) (error : t) : string =
    if is_compact then begin
      match error.err_location with
      | Some error_loc ->
        "- err at: " ^ (Ast_pp.show_clause error_loc) ^ "\n"
      | None ->
        "- no errs\n"
    end else begin
      match error.err_location with
      | Some error_loc ->
        "Type errors for:\n" ^
        "- Input sequence  : " ^ (show_input_seq error.err_input_seq) ^ "\n" ^
        "- Found at clause : " ^ (Ast_pp.show_clause error_loc) ^ "\n" ^
        begin
          if show_steps then
            "- Found in steps  : " ^ (string_of_int error.err_steps) ^ "\n"
          else
            ""
        end ^
        "--------------------\n" ^
        (String.join "\n--------------------\n"
          @@ List.map Error.Odefa_error.show error.err_errors)
      | None -> "** No errors found on this run. **"
    end
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
    err_steps : int;
  }
  [@@ deriving to_yojson]
  ;;

  let description = "error";;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result steps e x result =
    let _ = steps in
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
              err_steps = steps;
            }
          | None ->
            {
              err_input_seq = input_seq;
              err_location = None;
              err_errors = [];
              err_steps = steps;
            }
        end
      | None -> failwith "Odefa/natodefa maps were not set!"
  ;;

  let set_odefa_natodefa_map odefa_on_maps =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let show ?show_steps:(show_steps=false) ?is_compact:(is_compact=false) error =
    if is_compact then begin
      match error.err_location with
      | Some error_loc ->
        "- err at: " ^ (On_ast_pp.show_expr error_loc) ^ "\n"
      | None ->
        "- no errs\n"
    end else begin
      match error.err_location with
      | Some error_loc ->
        "Type errors for:\n" ^
        "- Input sequence : " ^ (show_input_seq error.err_input_seq) ^ "\n" ^
        "- Found at expr  : " ^ (On_ast_pp.show_expr error_loc) ^ "\n" ^
        begin
          if show_steps then
            "- Found in steps  : " ^ (string_of_int error.err_steps) ^ "\n"
          else
            ""
        end ^
        "--------------------\n" ^
        (String.join "\n--------------------\n"
          @@ List.map On_error.On_error.show error.err_errors)
      | None -> ""
    end
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