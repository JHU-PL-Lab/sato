open Batteries;;

open Ast;;

(** Returns a list of all clauses that occur in expression, deeply traversing
    the syntax tree. *)
let rec flatten (Expr clauses) =
  match clauses with
  | [] ->
    []
  | ((Clause(_, Value_body(Value_function(Function_value(_, function_body)))))
     as clause) :: rest_clauses ->
    clause :: flatten function_body @ flatten (Expr rest_clauses)
  | ((Clause(_, Conditional_body(_, match_body, antimatch_body)))
     as clause) :: rest_clauses ->
    clause ::
    flatten match_body @
    flatten antimatch_body @
    flatten (Expr rest_clauses)
  | clause :: rest_clauses ->
    clause :: flatten (Expr rest_clauses)
;;

(** Returns a list of clauses that occur in the immediate block, shallowly
    traversing the syntax tree and inlining conditionals only. *)
let rec flatten_immediate_block (Expr clauses) =
  match clauses with
  | [] ->
    []
  | ((Clause (_, Conditional_body(_, match_body, antimatch_body)))
     as clause) :: rest_clauses ->
    clause :: flatten_immediate_block match_body @ flatten_immediate_block antimatch_body @ flatten_immediate_block (Expr rest_clauses)
  | clause :: rest_clauses ->
    clause :: flatten_immediate_block (Expr rest_clauses)
;;

(** Returns the set of immediate variable bindings that occur in expression,
    shallowly traversing the syntax tree. *)
let defined_variables (Expr clauses) =
  clauses
  |> List.map (fun (Clause (bound_variable, _)) -> bound_variable)
  |> Var_set.of_list
;;

(** Returns a list of all variable bindings that occur in expression, including
    repeated ones, deeply traversing the syntax tree. *)
let bindings_with_repetition expression =
  flatten expression
  |> List.map
    (
      function
      | Clause (bound_variable,
                Value_body (Value_function (Function_value (
                    formal_parameter, _)))) ->
        [bound_variable; formal_parameter]
      | Clause (bound_variable, _) ->
        [bound_variable]
    )
  |> List.flatten
;;

(** Returns the set of variable bindings that occur in expression, deeply
    traversing the syntax tree. *)
let bindings expression =
  Var_set.of_list @@ bindings_with_repetition expression
;;

(** Returns the set of variables that have use occurrences in expression, deeply
    traversing the syntax tree. *)
let use_occurrences expression =
  flatten expression
  |> List.map (
    fun (Clause (_, clause_body)) ->
      match clause_body with
      | Value_body _
      | Input_body ->
        Var_set.empty
      | Var_body variable ->
        Var_set.singleton variable
      | Appl_body (function_, actual_parameter) ->
        Var_set.of_list [function_; actual_parameter]
      | Conditional_body (subject, _, _) ->
        Var_set.singleton subject
      | Match_body (subject, _) ->
        Var_set.singleton subject
      | Projection_body(subject, _) ->
        Var_set.singleton subject
      | Binary_operation_body (left_operand, _, right_operand) ->
        Var_set.of_list [left_operand; right_operand]
      | Abort_body vlist -> Var_set.of_list vlist
  )
  |> List.fold_left Var_set.union Var_set.empty
;;

(** Returns the set of bindings repeated in expression, deeply traversing the
    syntax tree. *)
let non_unique_bindings expression =
  bindings_with_repetition expression
  |> List.group compare_var
  |> List.filter_map (
    fun group ->
      if List.length group > 1 then
        Some (List.first group)
      else
        None
  )
  |> Var_set.of_list
;;

(* Check variable scope *)

let _bind_filter bound site_x vars =
  vars
  |> List.filter (fun x -> not @@ Ident_set.mem x bound)
  |> List.map (fun x -> (site_x, x))
;;

let rec check_scope_expr
    (bound : Ident_set.t) (e : expr)
  : (ident * ident) list =
  let Expr(cls) = e in
  snd @@
  List.fold_left
    (fun (bound',result) clause ->
       let result' = result @ check_scope_clause bound' clause in
       let Clause(Var(x,_),_) = clause in
       let bound'' = Ident_set.add x bound' in
       (bound'', result')
    )
    (bound, [])
    cls

and check_scope_clause
    (bound : Ident_set.t) (c : clause)
  : (ident * ident) list =
  let Clause(Var(site_x,_),b) = c in
  check_scope_clause_body bound site_x b

and check_scope_clause_body
    (bound : Ident_set.t) (site_x : ident) (b : clause_body)
  : (ident * ident) list =
  match b with
  | Value_body v ->
    begin
      match v with
      | Value_function(Function_value(Var(x',_),e)) ->
        check_scope_expr (Ident_set.add x' bound) e
      | _ ->
        []
    end
  | Var_body (Var(x,_)) -> _bind_filter bound site_x [x]
  | Input_body -> []
  | Appl_body (Var(x1,_),Var(x2,_)) -> _bind_filter bound site_x [x1;x2]
  | Conditional_body (Var(x,_), e1, e2) ->
    _bind_filter bound site_x [x] @
    check_scope_expr bound e1 @
    check_scope_expr bound e2
  | Match_body (Var(x,_), _) -> _bind_filter bound site_x [x]
  | Projection_body (Var(x,_), _) -> _bind_filter bound site_x [x]
  | Binary_operation_body (Var(x1,_), _, Var(x2,_)) ->
    _bind_filter bound site_x [x1;x2]
  | Abort_body _ -> [] (* Variables in abort bodies are treated separately *)
;;

(** Returns a list of pairs of variables. The pair represents a violation on the
    concept of scope, i.e., a variable used that was not in scope. The first
    variable is the program point in which the violation occurred, the second
    variable is the one that was not in scope. *)
let scope_violations expression =
  check_scope_expr Ident_set.empty expression
  |> List.map (fun (i1,i2) -> (Var(i1,None)),Var(i2,None))
;;

(* Abort variable well-formedness *)

(* An abort clause's variable list is considered valid if the nesting
   conditionals' identifier variables are found in the list, in order
   of nesting. *)
let abort_var_list_valid cond_list abort_list =
  let rec v_list_eq c_list v_list =
    match c_list, v_list with
    | id1 :: tl1, id2 :: tl2 ->
      if Ident.equal id1 id2 then
        v_list_eq tl1 tl2
      else
        v_list_eq tl1 v_list
    | [], (id2 :: _) -> Some id2
    | _, [] -> None
  in
  v_list_eq cond_list abort_list
;;

let rec check_abort_vars_in_expr
    (cond_idents : Ident.t list) (e : expr)
  : (ident * ident) list =
  let Expr(clauses) = e in
  List.fold_left
    (fun results clause ->
       results @ check_abort_vars_in_clause cond_idents clause
    )
    []
    clauses

and check_abort_vars_in_clause
    (cond_idents : Ident.t list) (cls : clause)
  : (ident * ident) list =
  let (Clause (Var (site_x, _), body)) = cls in
  match body with
  | Abort_body v_list ->
    begin
      let i_list = List.map (fun (Var (id, _)) -> id) v_list in
      match abort_var_list_valid cond_idents i_list with
      | Some id -> [(site_x, id)]
      | None -> []
    end
  | Conditional_body (_, e1, e2) ->
    begin
      let cond_idents' = site_x :: cond_idents in
      check_abort_vars_in_expr cond_idents' e1 @
      check_abort_vars_in_expr cond_idents' e2
    end
  | Value_body v ->
    begin
      match v with
      | Value_function (Function_value (_, e)) ->
        check_abort_vars_in_expr cond_idents e
      | _ -> []
    end
  | _ -> []
;;

let cond_scope_violations expression =
  check_abort_vars_in_expr [] expression
  |> List.map (fun (i1,i2) -> (Var (i1,None)), Var (i2,None))
;;

(* Record label duplication check *)

(* This separator functions separately from the usual separator "~" used
   in natodefa translation, instrumentation, etc.  Note the triple tildes
   used; otherwise labels like "~empty" will be incorrectly flagged as
   duplicates. *)
let sep = "~~~";;

let create_duplicate_label_list (label_list : ident list) =
  let str_list =
    List.map
      (fun (Ident l) ->
        match String.Exceptionless.split ~by:sep l with
        | Some (l', _) -> l'
        | None -> l
      )
      label_list
  in
  let dup_list =
    str_list
    |> List.filter
      (fun l -> (List.length @@ List.filter (String.equal l) str_list) > 1)
    |> List.unique
    |> List.map (fun l -> Ident l)
  in
  dup_list
;;

let rec non_unique_record_labels_expr (e : expr)
  : (var * ident list) list =
  let Expr(clauses) = e in
  List.fold_left
    (fun dup_lst clause ->
      let new_dups = non_unique_record_labels_clause clause in
      dup_lst @ new_dups)
    []
    clauses

and non_unique_record_labels_clause (clause : clause)
  : (var * ident list) list =
  let Clause (var, body) = clause in
  match body with
  | Value_body value ->
    begin
      match value with
      | Value_record (Record_value record) ->
        let dup_list =
          record
          |> Ident_map.keys
          |> List.of_enum
          |> create_duplicate_label_list
        in
        if List.length dup_list > 0 then [(var, dup_list)] else []
      | Value_function (Function_value (_, e)) ->
        non_unique_record_labels_expr e
      | _ -> []
    end
  | Conditional_body (_, e1, e2) ->
    let dups_1 = non_unique_record_labels_expr e1 in
    let dups_2 = non_unique_record_labels_expr e2 in
    dups_1 @ dups_2
  | Match_body (_, pat) ->
    begin
      match pat with
      | Rec_pattern lbl_set ->
        let dup_list =
          lbl_set
          |> Ident_set.elements
          |> create_duplicate_label_list
        in
        if List.length dup_list > 0 then [(var, dup_list)] else []
      | _ -> []
    end
  | _ -> []
;;

let record_label_duplications expression =
  non_unique_record_labels_expr expression
;;

(** Returns the last defined variable in a list of clauses. *)
let rv (cs : clause list) : Var.t =
  let Clause(x,_) = List.last cs in x
;;

(** Returns the last defined variable in an expression. *)
let retv (e : expr) : Var.t =
  let Expr(cs) = e in rv cs
;;

(** Homomorphically maps all variables in an expression. *)
let rec map_expr_vars (fn : Var.t -> Var.t) (e : expr) : expr =
  let Expr(cls) = e in Expr(List.map (map_clause_vars fn) cls)

and map_clause_vars (fn : Var.t -> Var.t) (c : clause) : clause =
  let Clause(x,b) = c in Clause(fn x, map_clause_body_vars fn b)

and map_clause_body_vars (fn : Var.t -> Var.t) (b : clause_body)
  : clause_body =
  match (b : clause_body) with
  | Value_body v -> Value_body (map_value_vars fn v)
  | Var_body x -> Var_body (fn x)
  | Input_body -> Input_body
  | Appl_body (x1,x2) -> Appl_body(fn x1, fn x2)
  | Conditional_body (x, e1, e2) ->
    Conditional_body (fn x, map_expr_vars fn e1, map_expr_vars fn e2)
  | Match_body(x, p) ->
    Match_body(fn x, p)
  | Projection_body(x, l) ->
    Projection_body(fn x, l)
  | Binary_operation_body (x1, op, x2) ->
    Binary_operation_body (fn x1, op, fn x2)
  | Abort_body vlist -> Abort_body (List.map fn vlist)

and map_value_vars (fn : Var.t -> Var.t) (v : value) : value =
  match (v : value) with
  | Value_record(Record_value m) ->
    Value_record(Record_value(Ident_map.map fn m))
  | Value_function f -> Value_function(map_function_vars fn f)
  | Value_int _ -> v
  | Value_bool _ -> v

and map_function_vars (fn : Var.t -> Var.t) (f : function_value)
  : function_value =
  let Function_value(x,e) = f in
  Function_value(fn x, map_expr_vars fn e)
;;

(** Mostly-homomorphically operates on every subexpression of an expression.
    Expressions are modified in a bottom-up fashion. *)
let rec transform_exprs_in_expr (fn : expr -> expr) (e : expr) : expr =
  let Expr(cls) = e in
  fn @@ Expr(List.map (transform_exprs_in_clause fn) cls)

and transform_exprs_in_clause (fn : expr -> expr) (c : clause) : clause =
  let Clause(x,b) = c in Clause(x, transform_exprs_in_clause_body fn b)

and transform_exprs_in_clause_body (fn : expr -> expr) (body : clause_body)
  : clause_body =
  match (body : clause_body) with
  | Value_body v -> Value_body (transform_exprs_in_value fn v)
  | Var_body _ -> body
  | Input_body -> body
  | Appl_body (_, _) -> body
  | Conditional_body (x, e1, e2) ->
    Conditional_body (x,
                      transform_exprs_in_expr fn e1,
                      transform_exprs_in_expr fn e2)
  | Match_body(x, p) ->
    Match_body(x, p)
  | Projection_body (_, _) -> body
  | Binary_operation_body (_, _, _) -> body
  | Abort_body _ -> body

and transform_exprs_in_value (fn : expr -> expr) (v : value) : value =
  match (v : value) with
  | Value_record _ -> v
  | Value_function f -> Value_function(transform_exprs_in_function fn f)
  | Value_int _ -> v
  | Value_bool _ -> v

and transform_exprs_in_function (fn : expr -> expr) (fv : function_value)
  : function_value =
  let Function_value(x,e) = fv in
  Function_value(x, transform_exprs_in_expr fn e)
;;
