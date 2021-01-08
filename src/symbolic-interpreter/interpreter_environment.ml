open Batteries;;
open Jhupllib;;

open Odefa_ast;;
open Odefa_ddpa;;

open Ast;;
open Ast_pp;;
open Interpreter_types;;

let lazy_logger =
  Logger_utils.make_lazy_logger
    "Symbolic_interpreter.Interpreter_environment"
;;

type lookup_environment = {
  le_cfg : Ddpa_graph.ddpa_graph;
  le_clause_mapping : clause Ident_map.t;
  le_clause_predecessor_mapping : clause Ident_map.t;
  le_function_parameter_mapping : function_value Ident_map.t;
  le_function_return_mapping : function_value Ident_map.t;
  le_abort_mapping : abort_value Ident_map.t;
  le_first_var : Ident.t;
}
[@@deriving show]
;;

(* **** Enumerate all functions in a program **** *)

let rec enum_all_functions_in_expr expr : function_value Enum.t =
  let Expr(clauses) = expr in
  Enum.concat @@ Enum.map enum_all_functions_in_clause @@ List.enum clauses

and enum_all_functions_in_clause clause : function_value Enum.t =
  let Clause(_, body) = clause in
  enum_all_functions_in_body body

and enum_all_functions_in_body body : function_value Enum.t =
  match body with
  | Value_body v ->
    enum_all_functions_in_value v
  | Conditional_body (_, e1, e2) ->
    Enum.append
      (enum_all_functions_in_expr e1) (enum_all_functions_in_expr e2)
  | Var_body _
  | Input_body
  | Appl_body (_, _)
  | Binary_operation_body (_, _, _)
  | Match_body (_, _)
  | Projection_body (_, _)
  | Abort_body 
  | Assume_body _ ->
    Enum.empty ()

and enum_all_functions_in_value value : function_value Enum.t =
  match value with
  | Value_function(Function_value(_,e) as f) ->
    Enum.append (Enum.singleton f) @@ enum_all_functions_in_expr e
  | Value_int _ | Value_record _ | Value_bool _ ->
    Enum.empty ()
;;

(* Enumerate all aborts in a program *)

let rec enum_all_aborts_in_expr expr : (ident * abort_value) Enum.t =
  let Expr clauses = expr in
  Enum.concat @@ Enum.map enum_all_aborts_in_clause @@ List.enum clauses

and enum_all_aborts_in_clause clause : (ident * abort_value) Enum.t =
  let Clause (Var (cls_id, _), body) = clause in
  match body with
  | Conditional_body (Var (pred_id, _), e1, e2) ->
    begin
      let enum_ret_abort e branch =
        let Expr(c_list) = e in
        match List.Exceptionless.last c_list with
        | None -> Enum.empty ()
        | Some cls ->
          begin
            match cls with
            | Clause (Var (abort_id, _), Abort_body) ->
              let abort_val = {
                abort_conditional_ident = cls_id;
                abort_predicate_ident = pred_id;
                abort_conditional_branch = branch;
              }
              in
              Enum.singleton (abort_id, abort_val)
            | _ -> Enum.empty ()
          end
      in
      Enum.empty ()
      |> Enum.append (enum_all_aborts_in_expr e1)
      |> Enum.append (enum_ret_abort e1 true)
      |> Enum.append (enum_all_aborts_in_expr e2)
      |> Enum.append (enum_ret_abort e2 false)
    end
  | Value_body v ->
    enum_all_aborts_in_value v
  | Abort_body (* Aborts are enumerated in conditionals *)
  | Assume_body _
  | Var_body _
  | Input_body
  | Appl_body (_, _)
  | Binary_operation_body (_, _, _)
  | Match_body (_, _)
  | Projection_body (_, _) ->
    Enum.empty ()

and enum_all_aborts_in_value value : (ident * abort_value) Enum.t =
  match value with
  | Value_function (Function_value (_, e)) ->
    enum_all_aborts_in_expr e
  | Value_int _ | Value_bool _ | Value_record _ ->
    Enum.empty ()
;;

let prepare_environment
    (cfg : Ddpa_graph.ddpa_graph)
    (e : expr)
  : lookup_environment =
  let (function_parameter_mapping, function_return_mapping) =
    enum_all_functions_in_expr e
    |> Enum.fold
      (fun (pm, rm) (Function_value(Var(param,_), body) as f) ->
        let (Var (retvar, _)) = Ast_tools.retv body in
        let pm' = Ident_map.add param f pm in
        let rm' = Ident_map.add retvar f rm in
        (pm', rm')
      )
      (Ident_map.empty, Ident_map.empty)
  in
  let clause_mapping =
    Ast_tools.clause_mapping e
  in
  let clause_predecessor_mapping =
    Ast_tools.clause_predecessor_mapping e
  in
  let first_var =
    let (Var (x, _)) = Ast_tools.firstv e in x
  in
  let abort_map =
    Ident_map.of_enum @@ enum_all_aborts_in_expr e
  in
  let lookup_env =
    { le_cfg = cfg;
      le_clause_mapping = clause_mapping;
      le_clause_predecessor_mapping = clause_predecessor_mapping;
      le_function_parameter_mapping = function_parameter_mapping;
      le_function_return_mapping = function_return_mapping;
      le_abort_mapping = abort_map;
      le_first_var = first_var;
    }
  in
  lazy_logger `debug (fun () -> Printf.sprintf "Lookup environment:\n%s"
      (show_lookup_environment lookup_env));
  lookup_env
;;

let list_instrument_conditionals (e : expr) : ident list =
  e
  |> enum_all_aborts_in_expr
  |> Enum.map (fun (_, abort_val) -> abort_val.abort_conditional_ident)
  |> List.of_enum
  |> List.rev
;;