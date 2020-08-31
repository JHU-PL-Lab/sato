open Batteries;;
open Jhupllib;;
open Odefa_ast;;
open Odefa_ddpa;;

open Ast;;
open Ast_pp;;
open Ddpa_abstract_ast;;
open Interpreter_types;;
open Logger_utils;;

let lazy_logger = make_lazy_logger "Symbolic_interpreter.Interpreter";;

type exploration_policy =
  | Explore_breadth_first
  | Explore_smallest_relative_stack_length
  | Explore_least_relative_stack_repetition
;;

(** This type describes the information which must be in context during lookup. *)
type lookup_environment = {
  le_cfg : Ddpa_graph.ddpa_graph;
  (** The DDPA CFG to use during lookup. *)

  le_clause_mapping : clause Ident_map.t;
  (** A mapping from identifiers to the concrete clauses which define them. *)

  le_clause_predecessor_mapping : clause Ident_map.t;
  (** A mapping from clauses (represented by the identifier they define) to the
      concrete clauses which appear immediately *before* them.  The first clause
      in each expression does not appear in this map. *)

  le_function_parameter_mapping : function_value Ident_map.t;
  (** A mapping from function parameter variables to the functions which declare
      them. *)

  le_function_return_mapping : function_value Ident_map.t;
  (** A mapping from function return variables to the functions which declare
      them. *)

  le_abort_mapping : abort_value Ident_map.t;
  (** A mapping from abort clause identifiers to identifier information
    associated with the error. *)


  le_first_var : Ident.t;
  (** The identifier which represents the first defined variable in the
      program. *)
}
[@@deriving show]
;;

(* Enumerate all functions in a program *)

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
  | Var_body _
  | Input_body
  | Appl_body (_, _)
  | Binary_operation_body (_, _, _) ->
    Enum.empty ()
  | Conditional_body (_, e1, e2) ->
    Enum.append
      (enum_all_functions_in_expr e1) (enum_all_functions_in_expr e2)
  | Match_body (_, _)
  | Projection_body (_, _)
  | Abort_body _ ->
    Enum.empty ()

and enum_all_functions_in_value value : function_value Enum.t =
  match value with
  | Value_record _ -> Enum.empty ()
  | Value_function(Function_value(_,e) as f) ->
    Enum.append (Enum.singleton f) @@ enum_all_functions_in_expr e
  | Value_int _
  | Value_bool _ -> Enum.empty ()
;;

(* Enumerate all aborts in a program *)

let rec enum_all_aborts_in_expr expr : (ident * var list) Enum.t =
  let Expr clauses = expr in
  Enum.concat @@ Enum.map enum_all_aborts_in_clause @@ List.enum clauses

and enum_all_aborts_in_clause clause : (ident * var list) Enum.t =
  let Clause (Var(ident, _), body) = clause in
  match body with
  | Value_body v ->
    enum_all_aborts_in_value v
  | Conditional_body (_, e1, e2) ->
    Enum.append
      (enum_all_aborts_in_expr e1) (enum_all_aborts_in_expr e2)
  | Abort_body vlist ->
    Enum.singleton (ident, vlist)
  | Var_body _
  | Input_body
  | Appl_body (_, _)
  | Binary_operation_body (_, _, _)
  | Match_body (_, _)
  | Projection_body (_, _) ->
    Enum.empty ()

and enum_all_aborts_in_value value : (ident * var list) Enum.t =
  match value with
  | Value_function (Function_value (_, e)) ->
    enum_all_aborts_in_expr e
  | Value_int _ | Value_bool _ | Value_record _ ->
    Enum.empty ()
;;

(**
   Given a program and its corresponding CFG, constructs an appropriate lookup
   environment.
*)
let prepare_environment
    (cfg : Ddpa_graph.ddpa_graph)
    (e : expr)
  : lookup_environment =
  let (function_parameter_mapping, function_return_mapping) =
    enum_all_functions_in_expr e
    |> Enum.fold
      (fun (pm,rm) (Function_value(Var(p,_),Expr(clss)) as f) ->
         let pm' = Ident_map.add p f pm in
         let retvar =
           clss
           |> List.last
           |> (fun (Clause(Var(r,_),_)) -> r)
         in
         let rm' = Ident_map.add retvar f rm in
         (pm', rm')
      )
      (Ident_map.empty, Ident_map.empty)
  in
  let clause_mapping =
    Ast_tools.flatten e
    |> List.enum
    |> Enum.fold
      (fun map (Clause(Var(x,_),_) as c) ->
         Ident_map.add x c map
      )
      Ident_map.empty
  in
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
          | Abort_body _ -> []
          | Conditional_body (_, e1, e2) ->
            e1 :: e2 :: expr_flatten e1 @ expr_flatten e2
       )
     |> List.concat
    )
  in
  let clause_predecessor_mapping =
    expr_flatten e
    |> List.enum
    |> Enum.map
      (fun (Expr clauses) ->
         let c1 = List.enum clauses in
         let c2 = List.enum clauses in
         Enum.drop 1 c1;
         Enum.combine (c1,c2)
         |> Enum.map
           (fun (Clause(Var(x,_),_),clause) -> (x,clause))
      )
    |> Enum.concat
    |> Ident_map.of_enum
  in
  let first_var =
    e
    |> (fun (Expr cls) -> cls)
    |> List.first
    |> (fun (Clause(Var(x,_),_)) -> x)
  in
  let abort_map =
    enum_all_aborts_in_expr e
    |> Enum.map
        (fun ((abort_ident: ident), (cond_vars : var list)) ->
          let cond_vars = List.rev cond_vars in
          let (cond_idents, cond_clauses) =
            List.fold_left
              (fun (ident_acc, cls_acc) (Var (id, _)) ->
                let cls = Ident_map.find id clause_mapping in
                (id :: ident_acc, cls :: cls_acc))
              ([], [])
              cond_vars
          in
          let pred_idents =
            List.map
              (fun (Clause (x, cls_body)) ->
                match cls_body with
                | Conditional_body (Var (pred, _), _, _) -> pred
                | _ -> raise @@ Utils.Invariant_failure ((show_var x) ^ " is not a conditional!")
              )
              cond_clauses
          in
          let abort_val : abort_value =
            {
              abort_conditional_clauses = cond_clauses;
              abort_conditional_idents = cond_idents;
              abort_predicate_idents = pred_idents;
            }
          in
          (abort_ident, abort_val)
        )
    |> Ident_map.of_enum
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

(* The type of the symbolic interpreter's cache key.  The arguments are the
   lookup stack, the clause identifying the program point at which lookup is
   proceeding, and the relative call stack at this point.
*)
type 'a interpreter_cache_key =
  | Cache_lookup :
      Ident.t list * annotated_clause * Relative_stack.t ->
      (symbol list) interpreter_cache_key
;;

module Interpreter_cache_key
  : Symbolic_monad.Cache_key with type 'a t = 'a interpreter_cache_key =
struct
  type 'a t = 'a interpreter_cache_key;;
  type some_key = Some_key : 'a t -> some_key;;

  let compare : type a b. a t -> b t -> (a, b) Gmap.Order.t = fun k1 k2 ->
    match k1, k2 with
    | Cache_lookup(lookup_stack_1, acl1, relative_stack_1),
      Cache_lookup(lookup_stack_2, acl2, relative_stack_2) ->
      let c = List.compare Ident.compare lookup_stack_1 lookup_stack_2 in
      if c < 0 then Lt else
      if c > 0 then Gt else
        let c = Annotated_clause.compare acl1 acl2 in
        if c < 0 then Lt else
        if c > 0 then Gt else
          let c =
            Relative_stack.compare relative_stack_1 relative_stack_2
          in
          if c < 0 then Lt else
          if c > 0 then Gt else
            Eq
  ;;

  let pp (type a) formatter (key : a t) =
    match key with
    | Cache_lookup(lookup_stack, acl, relative_stack) ->
      Format.fprintf formatter "lookup(%s,%s,%s)"
        (Jhupllib.Pp_utils.pp_to_string
           (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack)
        (show_brief_annotated_clause acl)
        (Relative_stack.show relative_stack)
  ;;

  let show key = Jhupllib.Pp_utils.pp_to_string pp key;;
end;;

module Interpreter_cache_key_smallest_relative_stack_length_ordering = struct
  open Interpreter_cache_key;;
  type t = some_key option;;
  let compare (a : t) (b : t) : int =
    match a, b with
    | None, None -> 0
    | Some _, None -> 1
    | None, Some _ -> -1
    | Some(Some_key(Cache_lookup(_, _, relative_stack_1))),
      Some(Some_key(Cache_lookup(_, _, relative_stack_2))) ->
      Stdlib.compare
        (Relative_stack.length relative_stack_1)
        (Relative_stack.length relative_stack_2)
  ;;
end;;

module Interpreter_cache_key_least_relative_stack_repetition_ordering = struct
  open Interpreter_cache_key;;
  type t = some_key option;;
  let reps (a : t) =
    match a with
    | None -> -1
    | Some(Some_key(Cache_lookup(_, _, relstack))) ->
      let (costk, stk) = Relative_stack.to_lists relstack in
      let occurrences =
        (costk @ stk)
        |> List.fold_left
          (fun a e -> Ident_map.modify_def 0 e (fun n -> n + 1) a)
          Ident_map.empty
      in
      let repetitions =
        occurrences
        |> Ident_map.enum
        |> Enum.map (fun (_,v) -> if v < 2 then 0 else v - 1)
        |> Enum.sum
      in
      repetitions
  ;;
  let compare (a : t) (b : t) : int =
    Stdlib.compare (reps a) (reps b)
  ;;
end;;

type evaluation_result = {
  er_solver : Solver.t;
  er_stack : Relative_stack.concrete_stack;
  er_solution : (symbol -> value option);
  er_aborts : abort_value Symbol_map.t;
};;

exception Invalid_query of string;;

module type Interpreter =
sig
  type evaluation;;
  val start : Ddpa_graph.ddpa_graph -> expr -> ident -> evaluation;;
  val step : evaluation -> evaluation_result list * evaluation option;;
end;;

module Make
    (C : Symbolic_monad.WorkCollection
     with module Work_cache_key = Interpreter_cache_key)
  : Interpreter =
struct
  module M = Symbolic_monad.Make(
    struct
      module Cache_key = Interpreter_cache_key;;
      module Work_collection = C;;
    end);;

  (* **** Console logging operations **** *)

  let _trace_log_zeromsg
      (msg : string)
      (lookup_stack : Ident.t list)
      (relstack : Relative_stack.t)
      (acl0 : annotated_clause)
      (acl1 : annotated_clause)
    : unit =
    lazy_logger `trace (fun () ->
      Printf.sprintf "ZERO (%s) for lookup of\n  %s\n  with stack %s\n  at %s\n  after %s\n"
        msg
        (Jhupllib.Pp_utils.pp_to_string
          (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack)
        (Jhupllib.Pp_utils.pp_to_string Relative_stack.pp relstack)
        (Jhupllib.Pp_utils.pp_to_string pp_brief_annotated_clause acl0)
        (Jhupllib.Pp_utils.pp_to_string pp_brief_annotated_clause acl1)
    )
  ;;

  let _trace_log_lookup
      (lookup_stack : Ident.t list)
      (relstack : Relative_stack.t)
      (acl0 : annotated_clause)
      (acl1 : annotated_clause)
    : unit =
    lazy_logger `trace (fun () ->
      Printf.sprintf
        "Looking up\n  %s\n  with stack %s\n  at %s\n  after %s\n"
        (Jhupllib.Pp_utils.pp_to_string
          (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack)
        (Jhupllib.Pp_utils.pp_to_string Relative_stack.pp relstack)
        (Jhupllib.Pp_utils.pp_to_string pp_brief_annotated_clause acl0)
        (Jhupllib.Pp_utils.pp_to_string pp_brief_annotated_clause acl1)
      )
  ;;

  let _trace_log_recurse
      (lookup_stack' : Ident.t list)
      (relstack' : Relative_stack.t)
      (acl0' : annotated_clause)
    : unit =
    lazy_logger `trace (fun () ->
      Printf.sprintf
        "Recursively looking up\n  %s\n  with stack %s\n  at %s\n"
        (Jhupllib.Pp_utils.pp_to_string
          (Jhupllib.Pp_utils.pp_list pp_ident) lookup_stack')
        (Jhupllib.Pp_utils.pp_to_string Relative_stack.pp relstack')
        (Jhupllib.Pp_utils.pp_to_string pp_brief_annotated_clause acl0')
      )
  ;;

  (* NOTE 1: rather than introducing a "stack=" SAT formula, we instead have
     lookup return a pair.  The "stack=" formula in the spec is a hack to avoid
     dealing with pairs in the lookup definition since the mathematical notation
     is... unpleasant.

     This incurs an obligation: we technically need to show that all of the
     stacks are the same.  In the "stack=" variation, two distinct stacks would
     lead to unsatisfiable formulae; here, if two different stacks are returned,
     we must zero the computation.  Conveniently, however, this never occurs:
     all lookups respect the stack discipline and the function call decision set
     is shared between them.  Therefore, all stacks *will* be the same; we
     needn't verify, which is good because it'd make the code quite a lot
     sloppier.
  *)

  let rec loop mappings map =
   (* If only we could generalize monadic sequencing... *)
    let open M in
    match mappings with
    | [] -> return map
    | hd :: tl ->
      let%bind (k, v) = hd in
      loop tl (Ident_map.add k v map)
  ;;

  (* Add a stack constraint if the lookup has reached the top of the program *)
  let record_stack_constraint
      (env : lookup_environment)
      (lookup_var : Ident.t)
      (relstack : Relative_stack.t)
    : unit M.m =
    let open M in
    if equal_ident lookup_var env.le_first_var then begin
      (* Then we've found the start of the program!  Build an
          appropriate concrete stack. *)
      lazy_logger `trace
        (fun () -> "Top of program reached: recording stack.");
      let concrete_stack = Relative_stack.stackize relstack in
      record_constraint @@ Constraint.Constraint_stack(concrete_stack)
    end else
      return ()
  ;;

  let rec rule_computations
      (env : lookup_environment)
      (lookup_stack : Ident.t list)
      (acl0 : annotated_clause)
      (acl1 : annotated_clause)
      (relstack : Relative_stack.t)
    : (symbol list) M.m list =
    let open M in
    let recurse = recurse env in
    let trace_rule name x : unit =
      lazy_logger `trace (fun () ->
        Printf.sprintf "Performing %s rule lookup on %s" name (show_ident x)
      )
    in
    let rule_list = [
      (* ### Value Discovery rule ### *)
      begin
        (* Lookup stack must be a singleton *)
        let%orzero [lookup_var] = lookup_stack in
        (* This must be a value assignment clause defining that variable. *)
        let%orzero Unannotated_clause(
            Abs_clause (Abs_var x, Abs_value_body _)) = acl1
        in
        [%guard equal_ident x lookup_var];
        (* Report Value Discovery rule lookup *)
        trace_rule "Value Discovery" x;
        (* Get the value v assigned here. *)
        let%orzero (Clause (_, Value_body(v))) =
          Ident_map.find x env.le_clause_mapping
        in
        (* Induce the resulting formula *)
        let lookup_symbol = Symbol (lookup_var, relstack) in
        let%bind constraint_value =
          match v with
          | Value_record (Record_value m) ->
            (* The variables in m are unfreshened and local to this context.
                We can look up each of their corresponding symbols and then
                put them in a new dictionary for the constraint. *)
            let mappings =
              m
              |> Ident_map.enum
              |> Enum.map
                (fun (lbl, Var(x,_)) ->
                  let%bind symbol_list = recurse [x] acl1 relstack in
                  let%orzero [symbol] = symbol_list in
                  return (lbl, symbol)
                )
              |> List.of_enum
            in
            let%bind record_map = loop mappings Ident_map.empty in
            return @@ Constraint.Record record_map
          | Value_function f -> return @@ Constraint.Function f
          | Value_int n -> return @@ Constraint.Int n
          | Value_bool b -> return @@ Constraint.Bool b
        in
        let%bind () = record_constraint @@
          Constraint.Constraint_value_clause(lookup_symbol, constraint_value)
        in
        (* If we're at the top of the program, we should record a stack
            constraint. *)
        let%bind () =
          record_stack_constraint env lookup_var relstack
        in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Value Discovery rule discovered that %s = %s"
            (show_symbol lookup_symbol) (show_value v));
        return [lookup_symbol]
      end;

      (* ### Input rule ### *)
      begin
        (* Lookup stack must be a singleton *)
        let%orzero [lookup_var] = lookup_stack in
        (* This must be an input clause defining that variable. *)
        let%orzero Unannotated_clause(
            Abs_clause (Abs_var x, Abs_input_body)) = acl1
        in
        [%guard equal_ident x lookup_var];
        (* Report Input rule lookup *)
        trace_rule "Input" x;
        (* Induce the resulting formula *)
        let lookup_symbol = Symbol (lookup_var, relstack) in
        let%bind () = record_constraint @@
          Constraint.Constraint_input lookup_symbol
        in
        (* If we're at the top of the program, we should record a stack
            constraint. *)
        let%bind () = record_stack_constraint env lookup_var relstack
        in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Input rule discovered that %s = input"
            (show_symbol lookup_symbol));
        return [lookup_symbol]
      end;

      (* ### Binop rule ### *)
      begin
        (* Lookup stack needs to be a singleton, since no binop returns
           function values (which are the only valid non-bottom elements) *)
        let%orzero [lookup_var] = lookup_stack in
        (* This must be a binary operator clause assigning to that variable. *)
        let%orzero Unannotated_clause(
            Abs_clause (Abs_var x,
              Abs_binary_operation_body (Abs_var x', op, Abs_var x''))) =
          acl1
        in
        [%guard equal_ident x lookup_var];
        (* Report Binop rule lookup *)
        trace_rule "Binop" x;
        (* Look up operand variables *)
        let%bind symbol_list_1 = recurse [x'] acl1 relstack in
        let%bind symbol_list_2 = recurse [x''] acl1 relstack in
        let%orzero [symbol_1] = symbol_list_1 in
        let%orzero [symbol_2] = symbol_list_2 in
        (* Add binop constraint *)
        let lookup_symbol = Symbol(lookup_var, relstack) in
        let%bind () = record_constraint @@
          Constraint.Constraint_binop (lookup_symbol, symbol_1, op, symbol_2)
        in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Binop rule discovered that %s = %s %s %s"
            (show_symbol lookup_symbol)
            (show_symbol symbol_1)
            (show_binary_operator op)
            (show_symbol symbol_2));
        return [lookup_symbol]
      end;

      (* Pattern Matching *)
      begin
        (* Grab variable from lookup stack *)
        let%orzero lookup_var :: lookup_stack' = lookup_stack in
        (* This must be a pattern match clause *)
        let%orzero Unannotated_clause(
            Abs_clause(Abs_var x, Abs_match_body(Abs_var x', pattern))) = acl1
        in
        [%guard equal_ident x lookup_var];
        (* Report Pattern Match rule lookup *)
        trace_rule "Pattern Match" x;
        (* Look up the symbol that is being matched upon *)
        let%bind symbol_list = recurse (x' :: lookup_stack') acl1 relstack in
        let%orzero pat_symbol :: symbol_list' = symbol_list in
        (* Record the constraint associated with the pattern match *)
        let lookup_symbol = Symbol(lookup_var, relstack) in
        let%bind () = record_constraint @@
          Constraint_match(lookup_symbol, pat_symbol, pattern)
        in
        (* And we are done *)
        lazy_logger `trace (fun () ->
          Printf.sprintf "Pattern Match rule completed on %s = %s ~ %s"
            (show_symbol lookup_symbol)
            (show_symbol pat_symbol)
            (show_pattern pattern));
        return (lookup_symbol :: symbol_list')
      end;

      (* ### Value Discard rule ### *)
      begin
        (* Lookup stack must NOT be a singleton *)
        (* TODO: verify that this still has the desired intent.  What if
            query_element isn't a variable? *)
        let%orzero lookup_var :: query_element :: lookup_stack' =
          lookup_stack
        in
        (* This must be a value assignment clause defining that variable. *)
        let%orzero Unannotated_clause(
            Abs_clause (Abs_var x, Abs_value_body _)) = acl1
        in
        [%guard equal_ident x lookup_var];
        (* Report Value Discard rule lookup *)
        trace_rule "Value Discard" x;
        (* We found the variable, so toss it and keep going. *)
        let%bind symbol_list = recurse (query_element :: lookup_stack') acl1 relstack in
        let lookup_symbol = Symbol(lookup_var, relstack) in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Value Discard rule discards %s"
            (show_symbol lookup_symbol));
        return (lookup_symbol :: symbol_list)
      end;

      (* ### Alias rule ### *)
      begin
        (* Grab variable from lookup stack *)
        let%orzero lookup_var :: lookup_stack' = lookup_stack in
        (* This must be an alias clause defining that variable. *)
        let%orzero Unannotated_clause(
            Abs_clause (Abs_var x, Abs_var_body(Abs_var x'))) =
          acl1
        in
        [%guard equal_ident x lookup_var];
        (* Report Alias rule lookup *)
        trace_rule "Alias" x;
        (* Look for the alias now. *)
        let%bind symbol_list = recurse (x' :: lookup_stack') acl1 relstack in
        let%orzero alias_symbol :: symbol_list' = symbol_list in
        (* Add the alias constraint *)
        let lookup_symbol = Symbol (x, relstack) in
        (* Return the alias. *)
        lazy_logger `trace (fun () ->
          Printf.sprintf "Alias rule discovered that %s = %s"
            (show_symbol lookup_symbol) (show_symbol alias_symbol));
        let%bind () = record_constraint @@
          Constraint.Constraint_alias (lookup_symbol, alias_symbol)
        in
        return (lookup_symbol :: symbol_list')
      end;

      (* ### Function Enter Parameter rule ### *)
      begin
        (* Grab variable from lookup stack *)
        let%orzero lookup_var :: lookup_stack' = lookup_stack in
        (* This must be a binding enter clause which defines our lookup
            variable. *)
        let%orzero Binding_enter_clause(Abs_var x, Abs_var x', c) = acl1 in
        [%guard equal_ident lookup_var x];
        (* Report Function Enter Parameter rule lookup *)
        trace_rule "Function Enter Parameter" x;
        (* Build the popped relative stack. *)
        let%orzero Abs_clause (Abs_var xr, Abs_appl_body (Abs_var xf,_)) = c in
        let%orzero Some relstack' = Relative_stack.pop relstack xr in
        (* Record this wiring decision. *)
        let cc = Ident_map.find xr env.le_clause_mapping in
        let%bind () = record_decision relstack x cc x' in
        (* Look up the definition of the function. *)
        let%bind fun_symbol_list = recurse [xf] acl1 relstack' in
        let%orzero [function_symbol] = fun_symbol_list in
        (* Require this function be assigned to that variable. *)
        let fv = Ident_map.find x env.le_function_parameter_mapping in
        let%bind () = record_constraint @@
          Constraint.Constraint_value (function_symbol, Constraint.Function fv)
        in
        (* Proceed to look up the argument in the calling context. *)
        let%bind symbol_list = recurse (x' :: lookup_stack') acl1 relstack' in
        let%orzero arg_symbol :: symbol_list' = symbol_list in
        (* Alias the function parameter to the application argument *)
        let lookup_symbol = Symbol (lookup_var, relstack) in
        lazy_logger `trace (fun () ->
            Printf.sprintf "Function Enter Parameter rule discovers %s = %s"
              (show_symbol lookup_symbol) (show_symbol arg_symbol));
        let%bind () = record_constraint @@
          Constraint.Constraint_alias (lookup_symbol, arg_symbol)
        in
        return (lookup_symbol :: symbol_list')
      end;

      (* ### Function Enter Non-Local rule ### *)
      begin
        (* Grab variable from lookup stack *)
        let%orzero x :: lookup_stack' = lookup_stack in
        (* This must be a binding enter clause which DOES NOT define our
            lookup variable. *)
        let%orzero Binding_enter_clause (Abs_var x'', Abs_var x', c) = acl1 in
        [%guard not @@ equal_ident x x''];
        (* Report Function Enter Non-Local rule lookup *)
        trace_rule "Function Enter Non-Local" x;
        (* Build the popped relative stack. *)
        let%orzero Abs_clause(Abs_var xr, Abs_appl_body (Abs_var xf, _)) = c in
        let%orzero Some relstack' = Relative_stack.pop relstack xr in
        (* Record this wiring decision. *)
        let cc = Ident_map.find xr env.le_clause_mapping in
        let%bind () = record_decision relstack x'' cc x' in
        (* Look up the definition of the function. *)
        let%bind fun_symbol_list = recurse [xf] acl1 relstack' in
        let%orzero [function_symbol] = fun_symbol_list in
        (* Require this function be assigned to that variable. *)
        let fv = Ident_map.find x'' env.le_function_parameter_mapping in
        let%bind () = record_constraint @@
          Constraint.Constraint_value (function_symbol, Constraint.Function fv)
        in
        (* Proceed to look up the variable in the context of the function's
            definition. *)
        let%bind symbol_list = recurse (xf :: x :: lookup_stack') acl1 relstack' in
        let%orzero _ :: ret_symbol :: symbol_list' = symbol_list in
        (* Add alias constraints (as symbols have different relative stacks *)
        let lookup_symbol = Symbol (x, relstack) in
        let%bind () = record_constraint @@
          Constraint.Constraint_alias (lookup_symbol, ret_symbol)
        in
        (* And we are done. *)
        lazy_logger `trace (fun () ->
          Printf.sprintf "Function Enter Non-Local rule discovers %s = %s"
            (show_symbol lookup_symbol) (show_symbol ret_symbol));
        return (lookup_symbol :: symbol_list')
      end;

      (* ### Function Exit rule ### *)
      begin
        (* Grab variable from lookup stack *)
        let%orzero lookup_var :: lookup_stack' = lookup_stack in
        (* This must be a binding exit clause which defines our lookup
            variable. *)
        (* x = function ident, x' = return variable *)
        let%orzero Binding_exit_clause (Abs_var x, Abs_var x', c) = acl1 in
        [%guard equal_ident x lookup_var];
        (* Report Function Exit rule lookup *)
        trace_rule "Function Exit" x;
        (* Look up the definition point of the function. *)
        let%orzero Abs_clause (Abs_var xr, Abs_appl_body(Abs_var xf, _)) = c in
        let%bind fun_symbol_list =
          recurse [xf] (Unannotated_clause(c)) relstack
        in
        let%orzero [function_symbol] = fun_symbol_list in
        (* Require this function be assigned to that variable. *)
        let fv = Ident_map.find x' env.le_function_return_mapping in
        let%bind () = record_constraint @@
          Constraint.Constraint_value (function_symbol, Constraint.Function fv)
        in
        (* Proceed to look up the value returned by the function. *)
        let%orzero Some relstack' = Relative_stack.push relstack xr in
        let%bind symbol_list = recurse (x' :: lookup_stack') acl1 relstack' in
        let%orzero ret_symbol :: symbol_list' = symbol_list in
        (* Alias the call site with the return symbol *)
        let lookup_symbol = Symbol (lookup_var, relstack) in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Function Exit rule discovers %s = %s"
            (show_symbol lookup_symbol) (show_symbol ret_symbol));
        let%bind () = record_constraint @@
          Constraint.Constraint_alias (lookup_symbol, ret_symbol)
        in
        return (lookup_symbol :: symbol_list')
      end;

      (* ### Skip rule ### *)
      begin
        (* Grab variable from lookup stack *)
        let%orzero lookup_var :: _ = lookup_stack in
        (* This must be a variable we AREN'T looking for. *)
        let%orzero Unannotated_clause (Abs_clause (Abs_var x'', _)) = acl1 in
        [%guard not @@ equal_ident x'' lookup_var ];
        (* Report Skip rule lookup *)
        trace_rule "Skip" lookup_var;
        (* Even if we're not looking for it, it has to be defined! *)
        let%bind aux_symbol_list = recurse [x''] acl0 relstack in
        let%orzero [aux_symbol] = aux_symbol_list in
        let%bind symbol_list = recurse lookup_stack acl1 relstack in
        let%orzero ret_symbol :: symbol_list' = symbol_list in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Skip rule returns %s, skips %s"
            (show_symbol ret_symbol) (show_symbol aux_symbol));
        return (ret_symbol :: symbol_list')
      end;

      (* ### Conditional Top rule ### *)
      begin
        let%orzero lookup_var :: _ = lookup_stack in
        (* This must be a non-binding enter wiring node for a conditional. *)
        let%orzero Nonbinding_enter_clause (av, c) = acl1 in
        let%orzero Abs_clause(_, Abs_conditional_body(Abs_var x1, _, _)) = c in
        (* Report Conditional Top rule lookup *)
        trace_rule "Conditional Top" lookup_var;
        (* Look up the subject symbol. *)
        let%bind pred_symbol =
          recurse [x1] (Unannotated_clause c) relstack
        in
        let%orzero [pred_symbol] = pred_symbol in
        (* Require that it has the same value as the wiring node. *)
        let%orzero Abs_value_bool b = av in
        let%bind () = record_constraint @@
          Constraint.Constraint_value(pred_symbol, Constraint.Bool b)
        in
        (* Proceed by moving through the wiring node. *)
        let%bind symbol_list = recurse lookup_stack acl1 relstack in
        let%orzero ret_symbol :: symbol_list' = symbol_list in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Conditional Top rule returns %s"
            (show_symbol ret_symbol));
        return (ret_symbol :: symbol_list')
      end;

      (* ### Conditional Bottom - True rule ### *)
      begin
        (* Grab variable from lookup stack *)
        let%orzero lookup_var :: lookup_stack' = lookup_stack in
        (* This must be a binding exit clause which defines our lookup
            variable. *)
        let%orzero Binding_exit_clause (Abs_var x, Abs_var x', c) = acl1 in
        [%guard equal_ident x lookup_var];
        (* Ensure that we're considering the true branch *)
        let%orzero Abs_clause(_, Abs_conditional_body(Abs_var x1, e1, _)) = c in
        let Abs_var e1ret = Ddpa_utils.retv e1 in
        [%guard equal_ident x' e1ret];
        (* Report Conditional Bottom - True rule lookup *)
        trace_rule "Conditional Bottom - True" lookup_var;
        (* Look up the predicate and ensure it is true *)
        let%bind pred_symbol_list =
          recurse [x1] (Unannotated_clause c) relstack
        in
        let%orzero [pred_symbol] = pred_symbol_list in
        let%bind () = record_constraint @@
          Constraint.Constraint_value (pred_symbol, Constraint.Bool true)
        in
        (* Proceed to look up the value returned by this branch. *)
        let%bind symbol_list = recurse (x' :: lookup_stack') acl1 relstack in
        let%orzero ret_symbol :: symbol_list' = symbol_list in
        (* Alias the call site with the return symbol *)
        let lookup_symbol = Symbol (x, relstack) in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Conditional Bottom - True rule returns %s = %s"
            (show_symbol lookup_symbol) (show_symbol ret_symbol));
        let%bind () = record_constraint @@
          Constraint.Constraint_alias (lookup_symbol, ret_symbol)
        in
        return (lookup_symbol :: symbol_list')
      end;

      (* ### Conditional Bottom - False (Non-Abort) rule ### *)
      begin
        (* Grab variable from lookup stack *)
        let%orzero lookup_var :: lookup_stack' = lookup_stack in
        (* This must be a binding exit clause which defines our lookup
            variable. *)
        let%orzero Binding_exit_clause (Abs_var x, Abs_var x', c) = acl1 in
        [%guard equal_ident x lookup_var];
        (* Ensure that we're considering the false branch *)
        let%orzero Abs_clause(_, Abs_conditional_body(Abs_var x1, _, e2)) = c in
        let Abs_clause (Abs_var e2ret, e2cls) = Ddpa_utils.retcls e2 in
        [%guard equal_ident x' e2ret];
        let _ = e2cls in
        (* Ensure we're not considering abort clauses *)
        [%guard (match e2cls with Abs_abort_body _ -> false | _ -> true)];
        (* Report Conditional Bottom - False (Non-abort) rule lookup *)
        trace_rule "Conditional Bottom - False (Non-Abort)" lookup_var;
        (* Look up the predicate and ensure it is false *)
        let%bind pred_symbol_list =
          recurse [x1] (Unannotated_clause c) relstack
        in
        let%orzero [pred_symbol] = pred_symbol_list in
        let%bind () = record_constraint @@
          Constraint.Constraint_value(pred_symbol, Constraint.Bool false)
        in
        (* Proceed to look up the value returned by this branch. *)
        let%bind symbol_list = recurse (x' :: lookup_stack') acl1 relstack in
        let%orzero ret_symbol :: symbol_list' = symbol_list in
        (* Alias the call site with the return symbol *)
        let lookup_symbol = Symbol (x, relstack) in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Conditional Bottom - False (Non-Abort) rule returns %s = %s"
            (show_symbol lookup_symbol) (show_symbol ret_symbol));
        let%bind () = record_constraint @@
          Constraint.Constraint_alias (lookup_symbol, ret_symbol)
        in
        return (lookup_symbol :: symbol_list')
      end;

      (* ### Conditional Bottom - False (Abort) rule ### *)
      begin
        (* Grab variable from lookup stack, which must be a singleton *)
        let%orzero [lookup_var] = lookup_stack in
        (* This must be a binding exit clause which defines our lookup
            variable. *)
        let%orzero Binding_exit_clause (Abs_var x, Abs_var x', c) = acl1 in
        [%guard equal_ident x lookup_var];
        (* Ensure that we're considering the false branch *)
        let%orzero Abs_clause(_, Abs_conditional_body(Abs_var x1, _, e2)) = c in
        let Abs_clause (Abs_var e2ret, e2cls) = Ddpa_utils.retcls e2 in
        [%guard equal_ident x' e2ret];
        (* Ensure we're only considering abort clauses *)
        let%orzero Abs_abort_body _ = e2cls in        
        (* Report Conditional Bottom - False (Non-abort) rule lookup *)
        trace_rule "Conditional Bottom - False (Abort)" lookup_var;
        (* Look up the predicate and ensure it is false *)
        let%bind pred_symbol_list =
          recurse [x1] (Unannotated_clause c) relstack
        in
        let%orzero [pred_symbol] = pred_symbol_list in
        let%bind () = record_constraint @@
          Constraint.Constraint_value(pred_symbol, Constraint.Bool false)
        in
        (* Proceed to look up the first value in the program. *)
        let%bind symbol_list = recurse [env.le_first_var] acl1 relstack in
        let%orzero [_] = symbol_list in
        (* Add the abort to the log *)
        let abort_symbol = Symbol (e2ret, relstack) in
        let abort_value = Ident_map.find e2ret env.le_abort_mapping in
        let%bind () = record_abort_point abort_symbol abort_value in
        let%bind () = record_constraint @@ Constraint_abort(abort_symbol) in
        (* Alias the call site with the return symbol *)
        let lookup_symbol = Symbol (x, relstack) in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Conditional Bottom - False (Abort) rule returns %s"
            (show_symbol lookup_symbol));
        return [lookup_symbol]
      end;

      (* Record Projection *)
      begin
        (* Don't process the record projection unless we're ready to move
            on: we need a variable on top of the stack. *)
        let%orzero lookup_var :: lookup_stack' = lookup_stack in
        (* This must be a record projection clause which defines our
            variable. *)
        let%orzero Unannotated_clause(
            Abs_clause (Abs_var x, Abs_projection_body(Abs_var x', lbl))) =
          acl1
        in
        [%guard equal_ident x lookup_var];
        (* Report Record Projection rule lookup *)
        trace_rule "Record Projection" lookup_var;
        (* Look up the record itself and identify the symbol it uses. *)
        (* We ignore the stacks here intentionally; see note 1 above. *)
        let%bind symbol_list = recurse (x' :: lookup_stack') acl1 relstack in
        let%orzero record_symbol :: symbol_list' = symbol_list in
        (* Now record the constraint that the lookup variable must be the
            projection of the label from that record. *)
        let lookup_symbol = Symbol (lookup_var, relstack) in
        let%bind () = record_constraint @@
          Constraint_projection (lookup_symbol, record_symbol, lbl)
        in
        (* And we're finished. *)
        lazy_logger `trace (fun () ->
          Printf.sprintf "Record Projection rule completed on %s = %s.%s"
            (show_symbol lookup_symbol)
            (show_symbol record_symbol)
            (show_ident lbl));
        return (lookup_symbol :: symbol_list')
      end;

      (*
      (* Abort (not a written rule) *)
      begin
        (* Obtain lookup stack (the lookup var itself becomes unimportant) *)
        let%orzero _ :: lookup_stack' = lookup_stack in
        [%guard List.is_empty lookup_stack'];
        (* This must be an abort clause *)
        let%orzero Unannotated_clause(
            Abs_clause (Abs_var x, Abs_abort_body _)) = acl1
        in
        (* Report Abort rule lookup *)
        trace_rule "Abort" x;
        let abort_symbol = Symbol(x, relstack) in
        (* TODO: Take care of any uncaught exceptions? *)
        (* Look up the first variable of the program *)
        let abort_value = Ident_map.find x env.le_abort_mapping in
        let lookup_var = env.le_first_var in
        let new_lookup_stack = lookup_var :: lookup_stack' in
        let%bind symbol_list = recurse new_lookup_stack acl1 relstack in
        (* Record the abort point and the abort constraint *)
        let%bind () = record_abort_point abort_symbol abort_value in
        let%bind () = record_constraint @@ Constraint_abort(abort_symbol) in
        (* And we are done *)
        lazy_logger `trace (fun () ->
          Printf.sprintf "Abort rule completed on %s = abort"
            (show_symbol abort_symbol));
        (* TODO: Replace with mathematically sound return value *)
        return (List.make (List.length symbol_list) abort_symbol)
      end;
      *)

      (* Start-of-block and end-of-block handling (not actually a rule) *)
      (
        let%orzero (Start_clause _ | End_clause _) = acl1 in
        recurse lookup_stack acl1 relstack
      )
    ]
    in
    rule_list

  and recurse
      (env : lookup_environment)
      (lookup_stack' : Ident.t list)
      (acl0' : annotated_clause)
      (relstack' : Relative_stack.t)
    : (symbol list) M.m =
    let open M in
    _trace_log_recurse lookup_stack' relstack' acl0';
    (* check_formulae @@ *)
    let mon_val = lookup env lookup_stack' acl0' relstack' in
    let cache_key = Cache_lookup (lookup_stack', acl0', relstack') in
    cache cache_key mon_val

  and lookup
      (env : lookup_environment)
      (lookup_stack : Ident.t list)
      (acl0 : annotated_clause)
      (relstack : Relative_stack.t)
    : (symbol list) M.m =
    let open M in
    let%bind acl1 = pick @@ Ddpa_graph.preds acl0 env.le_cfg in
    let%bind () = pause () in
    _trace_log_lookup lookup_stack relstack acl0 acl1;
    let rule_list = rule_computations env lookup_stack acl0 acl1 relstack in
    let%bind mon = pick @@ List.enum rule_list in
    mon
  ;;

  type evaluation = Evaluation of unit M.evaluation;;

  let start
      (cfg : Ddpa_graph.ddpa_graph)
      (e : expr)
      (program_point : ident)
    : evaluation =
    let open M in
    let env = prepare_environment cfg e in
    let initial_lookup_var = env.le_first_var in
    let acl =
      try
        Unannotated_clause (
          Ddpa_graph.lift_clause
            @@ Ident_map.find program_point env.le_clause_mapping)
      with
      | Not_found ->
        raise @@ Invalid_query (
          Printf.sprintf "Variable %s is not defined"
            (show_ident program_point)
        )
    in
    let m : unit m =
      (* At top level, we don't actually need the returned symbol; we just want
         the concrete stack it produces.  The symbol is only used to generate
         formulae, which we'll get from the completed computations. *)
      let%bind _ =
        lookup env [initial_lookup_var] acl Relative_stack.empty
      in
      return ()
    in
    let m_eval = start m in
    Evaluation(m_eval)
  ;;

  (* Helper function that returns Some (evaluation_result) if we have a valid
     value and stack constraint, None otherwise. *)
  let _process_eval_result eval_result =
    match Solver.solve eval_result.M.er_solver with
    | Some (_, None) ->
      raise @@ Jhupllib.Utils.Invariant_failure
        "no stack constraint in solution!"
    | Some (get_value, Some stack) ->
      begin
        lazy_logger `debug (fun () ->
            Printf.sprintf
              "Discovered answer of stack %s and formulae:\n%s"
              (Relative_stack.show_concrete_stack stack)
              (Solver.show eval_result.M.er_solver)
          )
      end;
      let solver = eval_result.M.er_solver in
      let errors = eval_result.M.er_abort_points in
      Some {
        er_solver = solver;
        er_stack = stack;
        er_solution = get_value;
        er_aborts = errors;
      }
    | None ->
      begin
        lazy_logger `debug (fun () ->
            Printf.sprintf
              "Dismissed answer with unsolvable formulae:\n%s"
              (Solver.show eval_result.M.er_solver)
          )
      end;
      None
  ;;

  let step (x : evaluation) : evaluation_result list * evaluation option =
    let Evaluation(evaluation) = x in
    let results, evaluation' =
      M.step ?show_value:(Some(fun _ -> "unit")) evaluation
    in
    let results' =
      Enum.filter_map _process_eval_result results
    in
    let eval_opt =
      if M.is_complete evaluation' then None else Some(Evaluation(evaluation'))
    in
    (List.of_enum results', eval_opt)
  ;;
end;;

type evaluation =
    Evaluation : ('a -> (evaluation_result list * 'a option)) * 'a -> evaluation
;;

module QueueInterpreter =
  Make(Symbolic_monad.QueueWorkCollection(Interpreter_cache_key))
;;

module SmallestRelativeStackLengthInterpreter =
  Make(Symbolic_monad.CacheKeyPriorityQueueWorkCollection
         (Interpreter_cache_key)
         (Interpreter_cache_key_smallest_relative_stack_length_ordering))
;;

module LeastRelativeStackRepetitionInterpreter =
  Make(Symbolic_monad.CacheKeyPriorityQueueWorkCollection
         (Interpreter_cache_key)
         (Interpreter_cache_key_least_relative_stack_repetition_ordering))
;;

let start
    ?exploration_policy:(exploration_policy=Explore_breadth_first)
    (cfg : Ddpa_graph.ddpa_graph) (e : expr) (x : ident)
  : evaluation =
  match exploration_policy with
  | Explore_breadth_first ->
    let e = QueueInterpreter.start cfg e x in
    Evaluation(QueueInterpreter.step, e)
  | Explore_smallest_relative_stack_length ->
    let e = SmallestRelativeStackLengthInterpreter.start cfg e x in
    Evaluation(SmallestRelativeStackLengthInterpreter.step, e)
  | Explore_least_relative_stack_repetition ->
    let e = LeastRelativeStackRepetitionInterpreter.start cfg e x in
    Evaluation(LeastRelativeStackRepetitionInterpreter.step, e)
;;

let step (x : evaluation) : evaluation_result list * evaluation option =
  let Evaluation(stepper,e) = x in
  let (results, e'opt) = stepper e in
  match e'opt with
  | None -> (results, None)
  | Some e' -> (results, Some(Evaluation(stepper, e')))
;;