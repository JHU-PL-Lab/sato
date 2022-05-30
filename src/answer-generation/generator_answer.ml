open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Ast;;

open Odefa_symbolic_interpreter.Interpreter;;

open Odefa_natural;;


exception Parse_failure of string;;

module type Answer = sig
  type t;;
  val description : string;;
  val answer_from_result : int -> expr -> ident -> evaluation_result -> t;;
  val set_odefa_natodefa_map : On_to_odefa_maps.t -> unit;;
  val show : t -> string;;
  val show_compact : t -> string;;
  val count : t -> int;;
  val generation_successful : t -> bool;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

module type Error_location = sig
  type t;;
  val show : t -> string;;
  val show_brief : t -> string;;
  val to_yojson : t -> Yojson.Safe.t;;
end;;

let replace_linebreaks (str : string) : string =
  String.replace_chars
    (function '\n' -> " " | c -> String.of_char c) str
;;

module Odefa_error_location
  : Error_location with type t = Ast.clause = struct
  type t = Ast.clause;;
  let show = Ast_pp.show_clause;;
  let show_brief = Ast_pp_brief.show_clause;;
  let to_yojson clause =
    `String (replace_linebreaks @@ show clause);;
end;;

module Natodefa_error_location
  : Error_location with type t = On_ast.expr = struct
  type t = On_ast.expr;;
  let show = On_ast_pp.show_expr;;
  let show_brief = On_ast_pp.show_expr;;
  let to_yojson expr =
    `String (replace_linebreaks @@ show expr);;
end;;

(* **** String showing utilities **** *)

let pp_input_sequence formatter (input_seq : int list) =
  Pp_utils.pp_list Format.pp_print_int formatter input_seq
;;

let show_input_sequence : int list -> string =
  Pp_utils.pp_to_string pp_input_sequence
;;

(* **** Input sequence **** *)

module Input_sequence : Answer = struct
  type input_seq_record = {
    input_sequence : int list;
    input_steps : int;
  }
  [@@ deriving to_yojson]
  ;;

  type t = input_seq_record option
  ;;

  let description = "input";;

  let answer_from_result steps e x result =
    let (input_seq, error_opt) =
      Generator_utils.input_sequence_from_result e x result
    in
    match error_opt with
    | None -> Some {
      input_sequence = input_seq;
      input_steps = steps;
    }
    | Some _ -> None
  ;;

  (* Unused for input sequence generation. *)
  let set_odefa_natodefa_map (_ : On_to_odefa_maps.t) = ();;

  let show : t -> string = function
    | Some { input_sequence; input_steps } ->
      (Printf.sprintf "* Input sequence: %s\n" (show_input_sequence input_sequence)) ^
      (Printf.sprintf "* Found in %d step%s\n" input_steps (if input_steps = 1 then "" else "s")) ^
      "--------------------"
    | None -> ""
  ;;

  let show_compact : t -> string = function
    | Some { input_sequence; input_steps } ->
      Printf.sprintf
        "- %s (%d stp.)"
        (show_input_sequence input_sequence)
        input_steps
    | None -> ""
  ;;

  let count : t -> int = function Some _ -> 1 | None -> 0;;

  let generation_successful : t -> bool = Option.is_some;;

  let to_yojson : t -> Yojson.Safe.t = function
    | Some inputs -> input_seq_record_to_yojson inputs
    | None -> `Null
  ;;
end;;

(* **** Type Errors **** *)

module Type_errors : Answer = struct

  type error_record = {
    err_errors : Error.Odefa_error.t list;
    err_input_seq : int list;
    err_location : Odefa_error_location.t;
    err_steps : int;
  }
  [@@ deriving to_yojson]
  ;;

  type t = error_record option
  ;;

  let description = "error";;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result steps e x result : t =
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
          Some {
            err_input_seq = input_seq;
            err_location = trans_inst_fn error_loc;
            err_errors = List.map rm_inst_fn error_list;
            err_steps = steps;
          }
        | None -> None
      end
    | None -> failwith "Odefa/natodefa maps were not set!"
  ;;


  let set_odefa_natodefa_map odefa_on_maps : unit =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  (* TODO: Pretty-print *)

  let show : t -> string = function
    | Some error ->
      "** Type Errors **\n" ^
      (Printf.sprintf "- Input sequence  : %s\n" (show_input_sequence error.err_input_seq)) ^
      (Printf.sprintf "- Found at clause : %s\n" (Odefa_error_location.show error.err_location)) ^
      (Printf.sprintf "- Found in steps  : %s\n" (string_of_int error.err_steps)) ^
      "--------------------\n" ^
      (String.join "\n--------------------\n"
        @@ List.map Error.Odefa_error.show error.err_errors)
    | None -> ""
  ;;

  let show_compact : t -> string = function
    | Some error ->
      "- err at: " ^ (Odefa_error_location.show_brief error.err_location)
    | None ->
      "- no errs"
  ;;

  let count : t -> int = function
    | Some err -> List.length err.err_errors
    | None -> 0;;

  let generation_successful : t -> bool = Option.is_some;;

  let to_yojson : t -> Yojson.Safe.t = function
    | Some err -> error_record_to_yojson err
    | None -> `Null
  ;;
end;;

module Natodefa_type_errors : Answer = struct

  type error_record = {
    err_errors : On_error.On_error.t list;
    err_input_seq : int list;
    err_location : Natodefa_error_location.t;
    err_steps : int;
  }
  [@@ deriving to_yojson]
  ;;

  type t = error_record option;;

  let description = "error";;

  let odefa_on_maps_option_ref = ref None;;

  let answer_from_result steps e x result =
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
            Some {
              err_input_seq = input_seq;
              err_location = on_err_loc;
              err_errors = on_err_list;
              err_steps = steps;
            }
          | None -> None
        end
      | None -> failwith "Odefa/natodefa maps were not set!"
  ;;

  let set_odefa_natodefa_map odefa_on_maps =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let show : t -> string = function
    | Some error ->
      "** Type Errors **\n" ^
      (Printf.sprintf "- Input sequence  : %s\n" (show_input_sequence error.err_input_seq)) ^
      (Printf.sprintf "- Found at clause : %s\n" (Natodefa_error_location.show error.err_location)) ^
      (Printf.sprintf "- Found in steps  : %s\n" (string_of_int error.err_steps)) ^
      "--------------------\n" ^
      (String.join "\n--------------------\n"
        @@ List.map On_error.On_error.show error.err_errors)
    | None -> ""
  ;;

  let show_compact : t -> string = function
    | Some error ->
      "- err at: " ^ (Natodefa_error_location.show_brief error.err_location) 
    | None ->
      "- no errs"
  ;;

  let count : t -> int = function
    | Some err -> List.length err.err_errors
    | None -> 0
  ;;

  let generation_successful : t -> bool = Option.is_some;;

  let to_yojson : t -> Yojson.Safe.t = function
    | Some err -> error_record_to_yojson err
    | None -> `Null
  ;;
end;;