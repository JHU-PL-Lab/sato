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
  val show : ?show_steps:bool -> t -> string;;
  val show_compact : ?show_steps:bool -> t -> string;;
  val count : t -> int;;
  val generation_successful : t -> bool;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

(* **** String showing utilities **** *)

let show_input_seq (input_seq : int list) =
  "[" ^ (String.join ", " @@ List.map string_of_int input_seq) ^ "]"
;;

(* **** Input sequence **** *)

module Input_sequence : Answer = struct
  type t = {
    input_seq : int list option;
    input_steps : int;
  }
  [@@ deriving to_yojson]
  ;;

  let description = "input";;

  let answer_from_result steps e x result =
    let (input_seq, error_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
    match error_opt with
    | None -> { 
        input_seq = Some input_seq;
        input_steps = steps;
      }
    | Some _ -> {
        input_seq = None;
        input_steps = steps;
    }
  ;;

  (* Unused for input sequence generation. *)
  let set_odefa_natodefa_map (_ : On_to_odefa_maps.t) = ();;

  let show ?show_steps:(show_steps=false) inputs =
    let inputs_opt = inputs.input_seq in
    match inputs_opt with
    | Some iseq ->
      let input_str =
        Printf.sprintf
          "* Input sequence: [%s]\n"
          (String.join ", " @@ List.map string_of_int iseq)
      in
      let steps_str =
        if show_steps then
          Printf.sprintf
            "* Found in %d step%s\n"
            inputs.input_steps
            (if inputs.input_steps = 1 then "" else "s")
        else
          ""
      in
      Printf.sprintf "%s%s" input_str steps_str
    | None -> ""
  ;;

  let show_compact ?show_steps:(show_steps=false) inputs =
    let inputs_opt = inputs.input_seq in
    match inputs_opt with
    | Some iseq ->
      let input_str =
        Printf.sprintf "* [%s]" (String.join ", " @@ List.map string_of_int iseq)
      in
      let steps_str =
        if show_steps then Printf.sprintf "(%d stp.)" inputs.input_steps else ""
      in
      Printf.sprintf "%s %s" input_str steps_str
    | None -> ""
  ;;

  let count inputs =
    let inputs_opt = inputs.input_seq in
    match inputs_opt with
    | Some _ -> 1
    | None -> 0 (* Fail silently *)
  ;;

  let generation_successful inputs =
    let inputs_opt = inputs.input_seq in
    match inputs_opt with
    | Some _ -> true
    | None -> false
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

  let show ?show_steps:(show_steps=false) (error : t) : string =
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
    | None -> ""
  ;;

  let show_compact ?show_steps:(_=false) (error : t) : string =
    match error.err_location with
    | Some error_loc ->
      "- err at: " ^ (Ast_pp.show_clause error_loc)
    | None ->
      "- no errs"
  ;;

  let count (errors : t) = List.length errors.err_errors;;

  let generation_successful error =
    match error.err_location with
    | Some _ -> true
    | None -> false
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

  let show ?show_steps:(show_steps=false) error =
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
  ;;

  let show_compact ?show_steps:(_=false) error =
    match error.err_location with
    | Some error_loc ->
      "- err at: " ^ (On_ast_pp.show_expr error_loc) 
    | None ->
      "- no errs"
  ;;

  let count error = List.length error.err_errors;;

  let generation_successful error =
    match error.err_location with
    | Some _ -> true
    | None -> false
  ;;
end;;