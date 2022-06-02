open Batteries;;
open Jhupllib;;

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
  val set_ton_on_map : Ton_to_on_maps.t option -> unit;;
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
  : Error_location with type t = On_ast.syn_natodefa_edesc = struct
  type t = On_ast.syn_natodefa_edesc;;
  let show = Pp_utils.pp_to_string On_ast_pp.pp_expr_desc;;
  let show_brief = Pp_utils.pp_to_string On_ast_pp.pp_expr_desc;;
  let to_yojson expr = 
    `String (replace_linebreaks @@ show expr);;
end;;

(* **** String showing utilities **** *)

let pp_input_sequence  formatter (input_seq : int list) =
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

  let set_ton_on_map (_ : Ton_to_on_maps.t option) = ();;

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

  let ton_on_maps_option_ref = ref None;;

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

  let set_ton_on_map ton_on_maps : unit =
    ton_on_maps_option_ref := ton_on_maps
  ;;

  (* TODO: Pretty-print *)

  let show : t -> string = function
    | Some error ->
      "** Odefa Type Errors **\n" ^
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

  let ton_on_maps_option_ref = ref None;;

  (* Reporting Natodefa errors. *)
  let answer_from_result steps e x result =
    match (!odefa_on_maps_option_ref, !ton_on_maps_option_ref) with
    | (Some odefa_on_maps, Some ton_on_maps) ->
      begin
        let (input_seq, error_opt, aliases, err_vals_map) =
          Generator_utils.input_sequence_from_result_natodefa e x result odefa_on_maps
        in
        match error_opt with
        | Some (error_loc, error_lst) ->
          (* let () = On_to_odefa_maps.print_natodefa_expr_to_expr odefa_on_maps in *)
          (* TODO (Earl): This probably should be the place to trace all the way
              back to the original, user-written Natodefa code.
              The current issue with how mappings are kept is that the abort vars
              are bound to the "assert false" statements directly. 
              Need to find a way to chain up the assert false to the original point of
              error.
          *)
          let on_err_loc =
            On_to_odefa_maps.get_natodefa_equivalent_expr odefa_on_maps error_loc
          in
          let () = print_endline @@ On_to_odefa.show_expr_desc on_err_loc in
          (* TODO (Earl): This is pretty hacky, but it'll do for now *)
          (* More hack? Returns a pair to indicate whether we're handling type error here? *)
          let err_loc_sem = 
            Ton_to_on_maps.sem_natodefa_from_on_err ton_on_maps on_err_loc
          in
          let actual_err_loc_opt = 
            Ton_to_on_maps.Intermediate_expr_desc_map.find_opt 
            err_loc_sem 
            ton_on_maps.sem_to_syn
          in
          let actual_err_loc = 
            match actual_err_loc_opt with
            | Some l -> l
            | None -> 
              Ton_to_on_maps.syn_natodefa_from_sem_natodefa 
              ton_on_maps 
              err_loc_sem
          in
          (* If type error, pass a special flag to odefa_to_natodefa_error so that it'll handle
              value error differently.
          *)
          let is_type_error = 
            match on_err_loc.body with
            | TypeError _ -> true
            | _ -> false
          in
          let err_loc_option = 
            if is_type_error then Some actual_err_loc else None
          in
          (* let () = print_endline "before printing list!" in *)
          (* let () = print_endline @@ string_of_int @@ List.length error_lst in *)
          (* let () = failwith "SCREAM!" in *)
          let on_err_list =
            let mapper = 
              (On_error.odefa_to_natodefa_error odefa_on_maps ton_on_maps err_loc_option aliases err_vals_map) in 
            (* let () = print_endline "mapper is fine" in *)
            (* let () = print_endline @@ string_of_int (List.length error_lst) in *)
            List.map mapper error_lst
          in
          (* let () = failwith "SCREAM!" in *)
          Some {
            err_input_seq = input_seq;
            err_location = actual_err_loc;
            err_errors = on_err_list;
            err_steps = steps;
          }
        | None -> None
      end
    | None, _ -> failwith "Odefa/natodefa maps were not set!"
    | _, None -> failwith "typed natodefa/natodefa maps were not set!"
  ;;

  let set_odefa_natodefa_map odefa_on_maps =
    odefa_on_maps_option_ref := Some (odefa_on_maps)
  ;;

  let set_ton_on_map ton_on_maps : unit =
    ton_on_maps_option_ref := ton_on_maps
  ;;

  let show : t -> string = function
    | Some error ->
      "** NatOdefa Type Errors **\n" ^
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