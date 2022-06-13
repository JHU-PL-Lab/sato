open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_symbolic_interpreter;;
open Interpreter_types;;

open Ast;;
open Odefa_natural;;

let lazy_logger = Logger_utils.make_lazy_logger "Generator_utils";;

exception Halt_execution_as_input_sequence_is_complete;;
exception Halt_execution_as_abort_has_been_encountered;;

(** Computes a relative stack by calculating the difference between two
    (absolute) stacks.  Given a reference point at which to start, this
    function computes the relative stack which will produce the goal. *)
let relativize_stack
    (reference_point : Ident.t list)
    (goal : Ident.t list)
  : Relative_stack.t =
  let insist f x s =
    match f x s with
    | None -> raise @@ Utils.Invariant_failure "insist got None stack"
    | Some s' -> s'
  in
  (* Start by throwing away everything they have in common. *)
  let rec discard_common start finish =
    match start, finish with
    | x :: start', y :: finish' when equal_ident x y ->
      discard_common start' finish'
    | _ -> start, finish
  in
  let start, finish = discard_common reference_point goal in
  (* To get from the start stack to the finish stack, we'll first have to pop
    everything from the start stack and then push everything from the finish
    stack. *)
  let relstack =
    Relative_stack.empty
    |> List.fold_right (flip @@ insist Relative_stack.pop) (List.rev start)
    |> (flip @@ List.fold_left (insist Relative_stack.push)) (List.rev finish)
  in
  relstack
;;

let destructure_var v =
  match v with
  | Var (_, None) ->
    raise @@ Utils.Invariant_failure
      ("Non-freshened variable " ^ (Ast_pp.show_var v))
  | Var (x, Some(Freshening_stack(stack))) -> (x, stack)
;;

let successor_var (e : expr) (x : Ident.t) : Ident.t =
  let rec expr_flatten ((Expr clauses) as expr) : expr list =
    expr ::
    (clauses
     |>
     List.map
       (fun (Clause(_,b)) ->
          match b with
          | Value_body (Value_function(Function_value(_,e))) -> expr_flatten e
          | Value_body _
          | Var_body _
          | Input_body
          | Appl_body (_, _)
          | Match_body (_, _)
          | Projection_body (_, _)
          | Binary_operation_body (_, _, _)
          | Abort_body 
          | Assume_body _ -> []
          | Conditional_body (_, e1, e2) ->
            e1 :: e2 :: expr_flatten e1 @ expr_flatten e2
       )
     |> List.concat
    )
  in
  let map_of_expr =
    expr_flatten e
    |> List.enum
    |> Enum.map
      (fun (Expr clauses) ->
          let c1 = List.enum clauses in
          let c2 = List.enum clauses in
          Enum.drop 1 c2;
          Enum.combine c1 c2
          |> Enum.map
            (fun (Clause(Var(x,_),_),clause) -> (x,clause))
      )
    |> Enum.concat
    |> Ident_map.of_enum
  in
  match Ident_map.Exceptionless.find x map_of_expr with
  | Some (Clause (Var (x', _), _)) -> x'
  | None -> x
;;

(* TODO: Modify this function to check for whether the abort *)
let input_sequence_from_result
    (e : expr)
    (x : Ident.t)
    (result : Interpreter.evaluation_result)
  : (int list * (Ast.ident * Error.Odefa_error.t list) option) =
  match Solver.solve result.er_solver with
  | None ->
    raise @@ Jhupllib_utils.Invariant_failure
      "Attempted to extract input sequence on result with no solution!"
  | Some solution ->
    let (get_value, _) = solution in
    let Concrete_stack stack = result.er_stack in
    let stop_var =
      (* Var(successor_var e x, Some(Freshening_stack(stack))) *)
      Var (x, Some (Freshening_stack stack))
    in
    let (_, stop_stack) = destructure_var stop_var in
    let input_record = ref [] in
    (* Function to call to read from input *)
    let read_from_solver v =
      let (x, stack) = destructure_var v in
      let relstack = relativize_stack stop_stack stack in
      let symbol = Symbol(x, relstack) in
      let value =
        match get_value symbol with
        | None ->
          (* The solver had no value for us.  That means that this variable is
            unconstrained and we are free to pick as we please. *)
          Value_int 0
        | Some value ->
          value
      in
      lazy_logger `trace
        (fun () -> "Reconstructed input: " ^ (Ast_pp.show_value value));
      input_record := value :: !input_record;
      value
    in
    (* Callback function executed on each clause encountered *)
    let stop_at_stop_var (Clause(x, _)) =
      if equal_var x stop_var then
        (* (); *)
        raise Halt_execution_as_input_sequence_is_complete;
    in
    (* Function to record the first abort error encountered *)
    let abort_opt_ref = ref None in
    let record_abort_and_stop (Clause(ab, _)) =
      (* For now, we only report the error associated with the first we find
         on a program path, since (during forward evaluation) only code up to
         that abort is "live;" all code afterwards is "dead" code that is
         unreachable in the non-instrumented code.  In the future we can report
         potential errors in "dead" code as well, but only after we prove
         soundness. *)
      lazy_logger `trace (fun () ->
        Printf.sprintf "Abort at %s" (Ast_pp.show_var ab));
      abort_opt_ref := Some ab;
      raise @@ Halt_execution_as_abort_has_been_encountered
    in
    (* Run the interpreter with the above input source and clause callback *)
    let execute_interpreter () =
      try
        let _ =
          Odefa_interpreter.Interpreter.eval
            ~input_source:read_from_solver
            ~clause_callback:stop_at_stop_var
            ~abort_policy:record_abort_and_stop
            e
        in
        raise @@ Jhupllib.Utils.Invariant_failure
          "evaluation completed without triggering halt exception!"
      with
      | Halt_execution_as_input_sequence_is_complete
      | Halt_execution_as_abort_has_been_encountered -> ()
    in
    let () = execute_interpreter () in
    let input_sequence = List.rev !input_record in
    let input_seq_ints =
      List.map
        (fun value ->
          match value with
          | Value_int n -> n
          | _ ->
            raise @@ Jhupllib.Utils.Not_yet_implemented
              "Cannot presently handle non-integer input!"
        )
        input_sequence
    in
    let abort_var_to_errors abort_var_opt =
      match abort_var_opt with
      | Some ab_var ->
        begin
          let (ab_x, ab_stack) = destructure_var ab_var in
          let relstack = relativize_stack stop_stack ab_stack in
          let ab_symb = Symbol (ab_x, relstack) in
          let abort_info =
            try
              Symbol_map.find ab_symb result.er_aborts
            with Not_found ->
              raise @@ Jhupllib.Utils.Invariant_failure (
                Printf.sprintf "Unknown abort %s encountered in interpreter"
                (show_symbol ab_symb)
              )
          in
          let abort_location = abort_info.abort_conditional_ident in
          let abort_preds = (* TODO: Turn into a singleton *)
            [Symbol (abort_info.abort_predicate_ident, relstack)]
          in
          let get_error_fn = Solver.find_errors result.er_solver in
          let error_list =
            abort_preds
            |> List.map get_error_fn
            |> List.filter (fun l -> not @@ List.is_empty l)
            |> List.flatten
          in
          Some (abort_location, error_list)
        end
      | None -> None
    in
    (input_seq_ints, abort_var_to_errors !abort_opt_ref)
;;

let input_sequence_from_result_natodefa
    (e : expr)
    (x : Ident.t)
    (result : Interpreter.evaluation_result)
    (on_to_odefa_maps : On_to_odefa_maps.t)
  : (int list * (Ast.ident * Error.Odefa_error.t list) option * value On_ast.Ident_map.t) =
  match Solver.solve result.er_solver with
  | None ->
    raise @@ Jhupllib_utils.Invariant_failure
      "Attempted to extract input sequence on result with no solution!"
  | Some solution ->
    let (get_value, _) = solution in
    let Concrete_stack stack = result.er_stack in
    let stop_var =
      (* Var(successor_var e x, Some(Freshening_stack(stack))) *)
      Var (x, Some (Freshening_stack stack))
    in
    let (_, stop_stack) = destructure_var stop_var in
    let input_record = ref [] in
    (* Function to call to read from input *)
    let read_from_solver v =
      let (x, stack) = destructure_var v in
      let relstack = relativize_stack stop_stack stack in
      let symbol = Symbol(x, relstack) in
      let value =
        match get_value symbol with
        | None ->
          (* The solver had no value for us.  That means that this variable is
            unconstrained and we are free to pick as we please. *)
          Value_int 0
        | Some value ->
          value
      in
      lazy_logger `trace
        (fun () -> "Reconstructed input: " ^ (Ast_pp.show_value value));
      input_record := value :: !input_record;
      value
    in
    (* Callback function executed on each clause encountered *)
    let stop_at_stop_var (Clause(x, _)) =
      if equal_var x stop_var then
        (* (); *)
        raise Halt_execution_as_input_sequence_is_complete;
    in
    (* Function to record the first abort error encountered *)
    let abort_opt_ref = ref None in
    let record_abort_and_stop (Clause(ab, _)) =
      (* For now, we only report the error associated with the first we find
         on a program path, since (during forward evaluation) only code up to
         that abort is "live;" all code afterwards is "dead" code that is
         unreachable in the non-instrumented code.  In the future we can report
         potential errors in "dead" code as well, but only after we prove
         soundness. *)
      lazy_logger `trace (fun () ->
        Printf.sprintf "Abort at %s" (Ast_pp.show_var ab));
      abort_opt_ref := Some ab;
      raise @@ Halt_execution_as_abort_has_been_encountered
    in
    (* Run the interpreter with the above input source and clause callback *)
    let execute_interpreter () =
      try
        let _ =
          Odefa_interpreter.Interpreter.eval
            ~input_source:read_from_solver
            ~clause_callback:stop_at_stop_var
            ~abort_policy:record_abort_and_stop
            e
        in
        raise @@ Jhupllib.Utils.Invariant_failure
          "evaluation completed without triggering halt exception!"
      with
      | Halt_execution_as_input_sequence_is_complete
      | Halt_execution_as_abort_has_been_encountered -> ()
    in
    let () = execute_interpreter () in
    let input_sequence = List.rev !input_record in
    let input_seq_ints =
      List.map
        (fun value ->
          match value with
          | Value_int n -> n
          | _ ->
            raise @@ Jhupllib.Utils.Not_yet_implemented
              "Cannot presently handle non-integer input!"
        )
        input_sequence
    in
    let abort_var_to_errors abort_var_opt =
      match abort_var_opt with
      | Some ab_var ->
        begin
          let (ab_x, ab_stack) = destructure_var ab_var in
          let relstack = relativize_stack stop_stack ab_stack in
          let ab_symb = Symbol (ab_x, relstack) in
          let abort_info =
            try
              Symbol_map.find ab_symb result.er_aborts
            with Not_found ->
              raise @@ Jhupllib.Utils.Invariant_failure (
                Printf.sprintf "Unknown abort %s encountered in interpreter"
                (show_symbol ab_symb)
              )
          in
          let abort_location = abort_info.abort_conditional_ident in
          let abort_preds = (* TODO: Turn into a singleton *)
            [Symbol (abort_info.abort_predicate_ident, relstack)]
          in
          let get_error_fn = Solver.find_errors result.er_solver in
          let error_list =
            abort_preds
            |> List.map get_error_fn
            |> List.filter (fun l -> not @@ List.is_empty l)
            |> List.flatten
          in
          Some (abort_location, error_list)
        end
      | None -> None
    in
    let err_vals_map =
      let get_vals_from_solver v = 
        let (x, stack) = destructure_var v in
        let relstack = relativize_stack stop_stack stack in
        let symbol = Symbol(x, relstack) in
        let value =
          match get_value symbol with
          | None ->
            failwith "Should have value in solver!"
          | Some value ->
            value
        in
        value
      in
      let fid_vars_lst = 
        On_ast.Ident_map.bindings @@ 
        On_to_odefa_maps.get_false_id_to_subj_var_mapping on_to_odefa_maps
      in
      List.fold_left 
      (fun acc (k, v) -> 
        On_ast.Ident_map.add k (get_vals_from_solver v) acc) 
      On_ast.Ident_map.empty fid_vars_lst
    in
    (input_seq_ints, abort_var_to_errors !abort_opt_ref, err_vals_map)
;;