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
let parse_comma_seperated_ints lst_str =
  let str_lst =
    lst_str
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
    let arg_str' =
      if (String.starts_with arg_str "[") &&
         (String.ends_with arg_str "]") then
        arg_str
        |> String.lchop
        |> String.rchop
      else
        arg_str
    in
    Some (parse_comma_seperated_ints arg_str')
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
end;;

(* **** Type Errors **** *)

module Type_errors : Answer = struct

  (*
  type type_error = {
    terr_expected_type : type_sig;
    terr_actual_type : type_sig;
    terr_operation : clause;
    terr_var_definition : clause;
  }
  ;;
  *)

  type error_seq = {
    (* err_type_errors : type_error list; *)
    err_errors : Error_tree.t list;
    err_input_seq : int list;
  }
  ;;

  type t = error_seq;;

  (*
  let _val_to_clause_body val_src =
    match val_src with
    | Constraint.Value v ->
      let v' =
        match v with
        | Constraint.Int n -> Value_int n
        | Constraint.Bool b -> Value_bool b
        | Constraint.Function f -> Value_function f
        | Constraint.Record symb_map ->
          begin
            let var_map =
              (* Discard context stack information *)
              Ident_map.map
                (fun (Symbol (id, _)) -> Var (id, None))
                symb_map
            in
            Value_record (Record_value var_map)
          end
      in
      Value_body v'
    | Constraint.Input -> Input_body
    | Constraint.Binop (symb1, op, symb2) ->
      (* Discard context stack information *)
      let Symbol (i1, _) = symb1 in
      let Symbol (i2, _) = symb2 in
      Binary_operation_body (Var (i1, None), op, Var (i2, None))
    | Constraint.Abort -> Abort_body []
  ;;

  let _symb_and_val_to_clause symb val_src =
    let Symbol (ident, _) = symb in (* Discard any context stack info *)
    let variable = Var (ident, None) in
    Clause (variable, _val_to_clause_body val_src)

  *)

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
    {
      err_input_seq = input_seq;
      err_errors = error_tree_list;
    }
  ;;

  (*
  let answer_from_result e x result =
    let solver = result.er_solver in
    let (input_seq, _) =
      Generator_utils.input_sequence_from_result e x result
    in
    let abort_points = result.er_abort_points in
    (* Function to apply to left fold op *)
    let accumulate_type_err accum (ab_symb, ab_info) =
      let Symbol(_, relstack) = ab_symb in
      match ab_info with
      | Type_abort_info type_ab_info ->
        let match_imap = type_ab_info.abort_matches in
        let err_list =
          match_imap
          |> Ident_map.enum
          |> Enum.filter_map
            (fun (ident, _) ->
              let type_err =
                find_type_error solver (Symbol(ident, relstack))
              in
              match type_err with
              | None -> None
              | Some type_err_rec ->
                let terr_symb = type_err_rec.terr_ident in
                let terr_val = type_err_rec.terr_value in
                Some {
                  terr_expected_type = type_err_rec.terr_expected_type;
                  terr_actual_type = type_err_rec.terr_actual_type;
                  terr_operation = type_ab_info.abort_operation;
                  terr_var_definition =_symb_and_val_to_clause terr_symb terr_val;
                }
            )
          |> List.of_enum
        in
        err_list @ accum
      | Match_abort_info _ -> accum (* Not implemented yet! *)
    in
    let type_err_list =
      abort_points
      |> Symbol_map.enum
      |> Enum.fold accumulate_type_err []
    in
    lazy_logger `trace (fun () ->
      Printf.sprintf "Total errors: %d" @@ List.length type_err_list);
    { err_type_errors = type_err_list;
      err_input_seq = input_seq;
    }
  ;;

  *)

  (*
  let _parse_type type_str =
    match type_str with
    | "int" | "integer" -> Int_type
    | "bool" | "boolean" -> Bool_type
    | "fun" | "function" -> Fun_type
    | _ ->
      let is_rec_str =
        Str.string_match (Str.regexp "{.*}") type_str 0 in
      if is_rec_str then begin
        let lbl_set =
          type_str
          |> String.lchop
          |> String.rchop
          |> Str.split (Str.regexp ",")
          |> List.map String.trim
          |> List.map (fun lbl -> Ident lbl)
          |> Ident_set.of_list
        in
        Rec_type lbl_set
      end else begin
        raise Parse_failure
      end
  ;;

  let _parse_clause cl_str =
    let expr_lst =
      try
        Odefa_parser.Parser.parse_expression_string cl_str
      with Odefa_parser.Parser.Parse_error _ ->
        raise Parse_failure
    in
    match expr_lst with
    | [expr] ->
      begin
        let Expr clist = expr in
        match clist with
        | [clause] -> clause
        | _ -> raise Parse_failure
      end
    | _ -> raise Parse_failure
  ;;

  (* [<input-seq>] ["operation" "definition" "expected" "actual"] *)
  let answer_from_string arg_str =
    (* Split on square brackets *)
    let arg_lst = Str.split (Str.regexp "[][]") arg_str in
    match arg_lst with
    | input_str :: type_err_strs ->
      begin
        let inputs = parse_comma_seperated_ints input_str in
        let type_err_strs' =
          (* Remove whitespace-only strings *)
          type_err_strs
          |> List.map String.trim
          |> List.filter (fun s -> (String.length s) > 0)
        in
        let type_errs =
          List.map
            (fun type_err_str ->
              let type_err_props =
                Str.split (Str.regexp "[\"]") type_err_str
                (* Remove whitespace-only strings *)
                |> List.map String.trim
                |> List.filter (fun s -> (String.length s) > 0)
              in
              match type_err_props with
              | [op; def; expected; actual] ->
                {
                  terr_expected_type = _parse_type expected;
                  terr_actual_type = _parse_type actual;
                  terr_operation = _parse_clause op;
                  terr_var_definition = _parse_clause def;
                }
              | _ ->
                raise Parse_failure
            )
            type_err_strs'
          in
          {
            err_type_errors = type_errs;
            err_input_seq = inputs;
          }
      end
    | _ ->
      raise Parse_failure
  ;;
  *)

  let answer_from_string _ =
    { err_errors = [];
      err_input_seq = [];
    }

  (*
  let show error_seq =
    let show_type_error type_error =
      "* Operation  : " ^ (show_clause type_error.terr_operation) ^ "\n" ^
      "* Definition : " ^ (show_clause type_error.terr_var_definition) ^ "\n" ^
      "* Expected   : " ^ (show_type_sig type_error.terr_expected_type) ^ "\n" ^
      "* Actual     : " ^ (show_type_sig type_error.terr_actual_type)
    in
    let show_input_seq inputs =
      "[" ^ (String.join ", " @@ List.map string_of_int inputs) ^ "]"
    in
    if not @@ List.is_empty error_seq.err_type_errors then begin
      ("Type errors for input sequence " ^
      (show_input_seq error_seq.err_input_seq) ^ "\n" ^
      (String.join "\n" (List.map show_type_error error_seq.err_type_errors)))
    end else begin
      "" (* Do not show anything if there are no type errors. *)
    end
  ;;
  *)

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