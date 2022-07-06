open Batteries;;
open Jhupllib;;
open Logger_utils;;

open Odefa_ast;;

open Ast;;
open Constraint;;
open Interpreter_types;;
open Symbol_cache;;

let lazy_logger = make_lazy_logger "Solver";;

type contradiction =
  | StackContradiction of
      Relative_stack.concrete_stack * Relative_stack.concrete_stack
  | TypeContradiction of
      symbol * Constraint.symbol_type * Constraint.symbol_type
  | ValueContradiction of symbol * value * value
  | ValueDefinitionContradiction of symbol * value_def * value_def
  | ProjectionContradiction of symbol * symbol * ident
  | MatchContradiction of symbol * symbol * pattern
;;

exception Contradiction of contradiction;;

module Symbol_to_symbol_multimap = Jhupllib.Multimap.Make(Symbol)(Symbol);;

module Symbol_and_ident =
struct
  type t = symbol * ident [@@deriving ord];;
end;;

module Symbol_to_symbol_and_ident_multimap =
  Jhupllib.Multimap.Make(Symbol)(Symbol_and_ident)
;;

type t =
  { (** The set of all constraints in the solver. *)
    constraints : Constraint.Set.t;

    (** An index of all alias constraints for a particular symbol.  As a given
        symbol may be aliased to many other symbols, this is a multimap. *)
    (* alias_constraints_by_symbol : Symbol_to_symbol_multimap.t; *)

    (** An index of alias constraints, from symbols that identify an alias
        clause to the predecessor symbols they are aliasing.  Since a symbol
        cannot alias multiple predecessor symbols (as that will cause a
        duplicate variable binding), this is a map. *)
    alias_constraints_by_symbol : symbol Symbol_map.t;

    (** An index of all value constraints by symbol.  As values are unique and
        no symbol may be constrained to multiple different values, this is a
        map. *)
    value_constraints_by_symbol : value Symbol_map.t;

    (** An index of all value definition constraints by symbol, in which a "value
        definition" is the clause that assigns a value to a symbol.  Since each
        symbol is alphatized and maps exactly to one clause, this is a map. *)
    value_def_constraints_by_symbol : value_def Symbol_map.t;

    (** An index of all record projection constraints over the record symbol.
        As a given record symbol may be projected many times (and the results
        assigned to many symbols), this is a multimap.  Note: Unlike all other
        symbol maps, the record symbol, not the symbol identifying the clause,
        is the key of the map. *)
    projection_constraints_by_record_symbol : Symbol_to_symbol_and_ident_multimap.t;

    (** An index of all symbol type constraints.  Because each symbol must have
        exactly one type, this is a map. *)
    type_constraints_by_symbol : symbol_type Symbol_map.t;

    (** The unique stack constraint which may appear in this solver.  Only one
        stack constraint may appear in any particular solver because all stack
        constraints contradict with one another. *)
    stack_constraint : Relative_stack.concrete_stack option;
  }
;;

type solution =
  (symbol -> Ast.value option) * Relative_stack.concrete_stack option
;;

let empty =
  { constraints = Constraint.Set.empty;
    alias_constraints_by_symbol = Symbol_map.empty;
    value_constraints_by_symbol = Symbol_map.empty;
    value_def_constraints_by_symbol = Symbol_map.empty;
    projection_constraints_by_record_symbol =
      Symbol_to_symbol_and_ident_multimap.empty;
    type_constraints_by_symbol = Symbol_map.empty;
    stack_constraint = None;
  }
;;

(* **** Output functions **** *)

let pp formatter solver =
  Constraint.Set.pp formatter solver.constraints
;;

let show solver = Pp_utils.pp_to_string pp solver;;

(* **** Helper functions **** *)

let _binop_types (op : binary_operator)
  : symbol_type * symbol_type * symbol_type =
  match op with
  | Binary_operator_plus
  | Binary_operator_minus
  | Binary_operator_times
  | Binary_operator_divide
  | Binary_operator_modulus -> (IntSymbol, IntSymbol, IntSymbol)
  | Binary_operator_less_than
  | Binary_operator_less_than_or_equal_to
  | Binary_operator_equal_to
  | Binary_operator_not_equal_to -> (IntSymbol, IntSymbol, BoolSymbol)
  | Binary_operator_and
  | Binary_operator_or
  | Binary_operator_xnor
  | Binary_operator_xor -> (BoolSymbol, BoolSymbol, BoolSymbol)
;;

(* TODO: This is probably the function we want to look at - EW *)
let rec _construct_alias_chain solver symbol : ident list =
  let Symbol (x, _) = symbol in
  let alias_opt =
    Symbol_map.Exceptionless.find symbol solver.alias_constraints_by_symbol
  in
  match alias_opt with
  | Some symbol' ->
    (* We want the alias chain to only record chains of distinct symbols *)
    let Symbol (x', _) = symbol' in
    if not @@ equal_ident x x' then
      x :: _construct_alias_chain solver symbol'
    else
      _construct_alias_chain solver symbol'
  | None -> [x]
;;

(* let _alias_chain_from_symbol symbols : ident list = 
  symbols
  |> List.map (fun (Symbol (x, _)) -> x)
  |> List.unique
;; *)

let rec _construct_symbol_chain solver symbol : symbol list =
  let alias_opt =
    Symbol_map.Exceptionless.find symbol solver.alias_constraints_by_symbol
  in
  match alias_opt with
  | Some symbol' ->
    (* We want the alias chain to only record chains of distinct symbols *)
    symbol :: _construct_symbol_chain solver symbol'
  | None -> [symbol]
;;

let _get_symbol_type solver symbol : symbol_type option =
  Symbol_map.Exceptionless.find symbol solver.type_constraints_by_symbol
;;

let _get_type solver symbol : type_sig =
  let symb_type =
    match _get_symbol_type solver symbol with
    | Some st -> st
    | None ->
      raise @@ Utils.Invariant_failure
        (Printf.sprintf "symbol %s not found in type constraint set!"
          (show_symbol symbol))
  in
  match symb_type with
  | BottomSymbol -> Bottom_type
  | IntSymbol -> Int_type
  | BoolSymbol -> Bool_type
  | FunctionSymbol -> Fun_type
  | RecordSymbol ->
    let rec_val =
      try 
        Symbol_map.find symbol solver.value_constraints_by_symbol
      with Not_found ->
        raise @@ Utils.Invariant_failure
          (Printf.sprintf "Symbol %s not found in value constraint set"
            (show_symbol symbol))
    in
    let rec_lbls =
      match rec_val with
      | Record rmap ->
        rmap
        |> Ident_map.keys
        |> Ident_set.of_enum
      | _ ->
        raise @@ Utils.Invariant_failure
          (Printf.sprintf "Value %s incorrectly typed as record"
            (show_value rec_val))
    in
    Rec_type rec_lbls
  | UntouchedSymbol ->
    let untouched_val =
      try 
        Symbol_map.find symbol solver.value_constraints_by_symbol
      with Not_found ->
        raise @@ Utils.Invariant_failure
          (Printf.sprintf "Symbol %s not found in value constraint set"
            (show_symbol symbol))
    in
    match untouched_val with
    | Untouched t -> Untouched_type t
    | _ ->
      raise @@ Utils.Invariant_failure
        (Printf.sprintf "Value %s incorrectly typed as untouched!"
          (show_value untouched_val))
;;

let _get_value_def solver symbol : value_def option =
  Symbol_map.Exceptionless.find symbol solver.value_def_constraints_by_symbol
;;

let _symbolic_to_concrete_value (val_src : value_def) : clause_body =
  match val_src with
  | Constraint.Value v ->
    begin
    match v with
    | Int n -> Value_body (Value_int n)
    | Bool b -> Value_body (Value_bool b)
    | Function f -> Value_body (Value_function f)
    | Record r ->
      (* Eliminate relative stack info *)
      let r' =
        r
        |> Ident_map.enum
        |> Enum.map (fun (lbl, (Symbol (x, _))) -> (lbl, Var (x, None)))
        |> Ident_map.of_enum
      in
      Value_body (Value_record (Record_value r'))
    | Untouched s -> Value_body (Value_untouched s)
    end
  | Constraint.Input -> Input_body
  | Constraint.Binop (x1, op, x2) ->
    let (Symbol (i1, _)) = x1 in
    let (Symbol (i2, _)) = x2 in
    Binary_operation_body (Var(i1, None), op, Var(i2, None))
  | Constraint.Match (x', pattern) ->
    let (Symbol (id, _)) = x' in
    Match_body (Var(id, None), pattern)
  | Constraint.Abort -> Abort_body
;;

(* **** Constraint set operations **** *)

let _check_value_def_constraints solver x vdef : unit =
  let vdef_map = solver.value_def_constraints_by_symbol in
  match Symbol_map.Exceptionless.find x vdef_map with
  | None -> ();
  | Some vdef' ->
    if not (equal_value_def vdef vdef') then
      raise @@ Contradiction(ValueDefinitionContradiction(x, vdef, vdef'))
;;

let rec _add_constraints_and_close
    (constraints : Constraint.Set.t) (solver : t)
  : t =
  if Constraint.Set.is_empty constraints then solver else
    let (c, constraints') = Constraint.Set.pop constraints in
    if Constraint.Set.mem c solver.constraints then
      _add_constraints_and_close constraints' solver
    else
      let new_solver : t =
        match c with
        | Constraint_value(x, v) ->
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            value_constraints_by_symbol =
              begin
                begin
                  match Symbol_map.Exceptionless.find x
                          solver.value_constraints_by_symbol with
                  | None -> ();
                  | Some v' ->
                    if not (equal_value v v') then
                      raise @@ Contradiction(ValueContradiction(x,v,v'))
                end;
                Symbol_map.add x v solver.value_constraints_by_symbol
              end;
          }
        | Constraint_value_clause(x, v) ->
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            value_def_constraints_by_symbol =
              begin
                let vdef = Constraint.Value v in
                _check_value_def_constraints solver x vdef;
                Symbol_map.add x vdef solver.value_def_constraints_by_symbol;
              end
            }
        | Constraint_input(x) ->
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            value_def_constraints_by_symbol =
              begin
                let vdef = Constraint.Input in
                _check_value_def_constraints solver x vdef;
                Symbol_map.add x vdef solver.value_def_constraints_by_symbol;
              end
          }
        | Constraint_alias(x1, x2) ->
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            alias_constraints_by_symbol =
              if (x1 = x2) 
              then solver.alias_constraints_by_symbol 
              else
                Symbol_map.add x1 x2 solver.alias_constraints_by_symbol
          }
        | Constraint_binop (x1, x2, op, x3) ->
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            value_def_constraints_by_symbol =
              begin
                let vdef = Constraint.Binop (x2, op, x3) in
                _check_value_def_constraints solver x1 vdef;
                Symbol_map.add x1 vdef solver.value_def_constraints_by_symbol;
              end
          }
        | Constraint_projection(x1, x2, lbl) ->
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            projection_constraints_by_record_symbol =
              Symbol_to_symbol_and_ident_multimap.add x2 (x1,lbl)
                solver.projection_constraints_by_record_symbol
          }
        | Constraint_match(x1, x2, p) ->
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            value_def_constraints_by_symbol =
              begin
                let vdef = Constraint.Match (x2, p) in
                _check_value_def_constraints solver x1 vdef;
                Symbol_map.add x1 vdef solver.value_def_constraints_by_symbol;
              end
          }
        | Constraint_type(x,t) ->
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            type_constraints_by_symbol =
              begin
                begin
                  match Symbol_map.Exceptionless.find x
                          solver.type_constraints_by_symbol with
                  | None -> ();
                  | Some t' ->
                    if not (equal_symbol_type t t') then
                      raise @@ Contradiction(TypeContradiction(x,t,t'))
                end;
                Symbol_map.add x t solver.type_constraints_by_symbol;
              end;
          }
        | Constraint_stack(s) ->
          begin
            match solver.stack_constraint with
            | Some s' ->
              begin
                if Relative_stack.equal_concrete_stack s s' then
                  ()
                else
                  raise @@ Contradiction(StackContradiction(s,s'))
              end;
            | None -> ()
          end;
          { solver with
            constraints = Constraint.Set.add c solver.constraints;
            stack_constraint = Some s;
          }
        | Constraint_abort x ->
          begin
            { solver with
              constraints = Constraint.Set.add c solver.constraints;
              value_def_constraints_by_symbol =
                begin
                  let vdef = Constraint.Abort in
                  _check_value_def_constraints solver x vdef;
                  Symbol_map.add x vdef solver.value_def_constraints_by_symbol;
                end
            }
          end;
      in
      let new_constraints : Constraint.Set.t =
        match c with
        | Constraint_value(x, v) ->
          (* TODO: Maybe add a second check for pattern match contradictions, 
             just like with record projection. *)
          begin
            let projection_constraints =
              match v with
              | Record m ->
                solver.projection_constraints_by_record_symbol
                |> Symbol_to_symbol_and_ident_multimap.find x
                |> Enum.map
                  (fun (x',lbl) ->
                    match Ident_map.Exceptionless.find lbl m with
                    | None ->
                      (* This means that we have two constraints.  One is a
                         record value assignment and the other is a projection
                         from that record.  But the projection is for a label
                         that the record doesn't have.  Contradiction! *)
                      raise @@ Contradiction(ProjectionContradiction(x',x,lbl))
                    | Some x'' ->
                      Constraint_alias(x',x'')
                  )
              | Int _ | Bool _ | Function _ | Untouched _ ->
                Enum.empty ()
            in
            let type_constraints =
              let t =
                match v with
                | Int _ -> IntSymbol
                | Bool _ -> BoolSymbol
                | Record _ -> RecordSymbol
                | Function _ -> FunctionSymbol
                | Untouched _ -> UntouchedSymbol
              in
              Enum.singleton (Constraint_type(x,t))
            in
            Constraint.Set.of_enum
              @@ Enum.append projection_constraints type_constraints
          end
        | Constraint_value_clause(x, v) ->
          Constraint.Set.singleton @@ Constraint_value(x, v)
        | Constraint_input(x) ->
          Constraint.Set.singleton @@ Constraint_type(x, IntSymbol)
        | Constraint_alias(x, x') ->
          begin
            let value_constraints =
              match Symbol_map.Exceptionless.find x'
                      solver.value_constraints_by_symbol with
              | None -> Enum.empty ()
              | Some v -> Enum.singleton @@ Constraint_value(x, v)
            in
            let value_def_constraints =
              match Symbol_map.Exceptionless.find x'
                      solver.value_def_constraints_by_symbol with
              | None -> Enum.empty ()
              | Some (Constraint.Value v) ->
                Enum.singleton @@ Constraint_value_clause (x, v)
              | Some (Constraint.Input) ->
                Enum.singleton @@ Constraint_input x
              | Some (Constraint.Binop (s1, op, s2)) ->
                Enum.singleton @@ Constraint_binop (x, s1, op, s2)
              | Some (Constraint.Match (s, p)) ->
                Enum.singleton @@ Constraint_match (x, s, p)
              | Some (Constraint.Abort) ->
                Enum.singleton @@ Constraint_abort x
            in
            Constraint.Set.of_enum
              @@ Enum.append value_constraints value_def_constraints
          end
        | Constraint_binop(x, x', op, x'') ->
          begin
            let (tLeft,tRight,tOut) = _binop_types op in
            Constraint.Set.of_enum @@ List.enum @@
            [
              Constraint_type (x,tOut);
              Constraint_type (x',tLeft);
              Constraint_type (x'',tRight);
            ]
          end
        | Constraint_projection(x, x', lbl) ->
          begin
            let new_const =
              Constraint.Set.singleton @@ Constraint_type (x', RecordSymbol)
            in
            let record_val =
              Symbol_map.Exceptionless.find x'
                solver.value_constraints_by_symbol
            in
            match record_val with
            | None -> new_const
            | Some(Int _ | Bool _ | Function _ | Untouched _) -> new_const
            | Some(Record record_body) ->
              match Ident_map.Exceptionless.find lbl record_body with
              | None ->
                (* This means that we have two constraints.  One is a
                   record value assignment and the other is a projection
                   from that record.  But the projection is for a label
                   that the record doesn't have.  Contradiction! *)
                raise @@ Contradiction(ProjectionContradiction(x,x',lbl))
              | Some x'' ->
                Constraint.Set.add (Constraint_alias(x,x'')) new_const
          end
        | Constraint_match(x, x', pat) ->
          begin
            match pat with
            | Any_pattern ->
              begin
                (* TODO: Should we also look up x' here as well? *)
                Constraint.Set.singleton @@ Constraint_value(x, Bool(true))
              end
            | Int_pattern ->
              begin
                let typ = Symbol_map.Exceptionless.find x'
                  solver.type_constraints_by_symbol in
                match typ with
                | Some (IntSymbol) ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(true))
                | Some _ ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | None ->
                  Constraint.Set.empty
              end
            | Bool_pattern ->
              begin
                let typ = Symbol_map.Exceptionless.find x'
                  solver.type_constraints_by_symbol in
                match typ with
                | Some (BoolSymbol) ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(true))
                | Some _ ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | None ->
                  Constraint.Set.empty
              end
            | Fun_pattern ->
              begin
                let typ = Symbol_map.Exceptionless.find x'
                  solver.type_constraints_by_symbol in
                match typ with
                | Some (FunctionSymbol) ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(true))
                | Some _ ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | None ->
                  Constraint.Set.empty
              end
            | Rec_pattern record_pattern ->
              begin
                let record_val = Symbol_map.Exceptionless.find x'
                  solver.value_constraints_by_symbol
                in
                match record_val with
                | Some(Record record_body) ->
                  let record_lbls =
                    record_body
                    |> Ident_map.keys
                    |> Ident_set.of_enum
                  in
                  if Ident_set.subset record_pattern record_lbls then
                    Constraint.Set.singleton @@ Constraint_value(x, Bool(true))
                  else
                    Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | Some _ ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | None ->
                  Constraint.Set.empty
              end
            | Strict_rec_pattern record_pattern ->
              begin
                let record_val = Symbol_map.Exceptionless.find x'
                  solver.value_constraints_by_symbol
                in
                match record_val with
                | Some(Record record_body) ->
                  let record_lbls =
                    record_body
                    |> Ident_map.keys
                    |> Ident_set.of_enum
                  in
                  if Ident_set.equal record_pattern record_lbls then
                    Constraint.Set.singleton @@ Constraint_value(x, Bool(true))
                  else
                    Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | Some _ ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | None ->
                  Constraint.Set.empty
              end
            | Untouched_pattern s ->
              begin
                let untouched_val = Symbol_map.Exceptionless.find x'
                  solver.value_constraints_by_symbol
                in
                match untouched_val with
                | Some(Untouched s') ->
                  if (s = s') then
                    Constraint.Set.singleton @@ Constraint_value(x, Bool(true))
                  else
                    Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | Some _ ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | None ->
                  Constraint.Set.empty
              end
            | Any_untouched_pattern ->
              begin
                let untouched_val = Symbol_map.Exceptionless.find x'
                  solver.value_constraints_by_symbol
                in
                match untouched_val with
                | Some(Untouched _) ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(true))
                | Some _ ->
                  Constraint.Set.singleton @@ Constraint_value(x, Bool(false))
                | None ->
                  Constraint.Set.empty
              end
          end
        | Constraint_type (_,_) ->
          Constraint.Set.empty
        | Constraint_stack _ ->
          Constraint.Set.empty
        | Constraint_abort ab ->
          Constraint.Set.singleton @@ Constraint_type(ab, BottomSymbol)
      in
      _add_constraints_and_close
        (Constraint.Set.union new_constraints constraints) new_solver
;;

let add c solver =
  _add_constraints_and_close (Constraint.Set.singleton c) solver
;;

let singleton c = add c empty;;

let union s1 s2 =
  let (smaller, larger) =
    if Constraint.Set.cardinal s1.constraints <
       Constraint.Set.cardinal s2.constraints then
      (s1,s2)
    else
      (s2,s1)
  in
  _add_constraints_and_close smaller.constraints larger
;;

(* **** Constraint set solving (feat. Z3) **** *)

let z3_expr_of_symbol
    (ctx : Z3.context)
    (symbol_cache : symbol_cache)
    (solver : t)
    (symbol : symbol)
  : Z3.Expr.expr option =
  let z3symbol = define_symbol symbol_cache symbol in
  match _get_symbol_type solver symbol with
  | Some IntSymbol -> Some(Z3.Arithmetic.Integer.mk_const ctx z3symbol)
  | Some BoolSymbol -> Some(Z3.Boolean.mk_const ctx z3symbol)
  | Some FunctionSymbol -> None
  | Some RecordSymbol -> None
  | Some BottomSymbol -> None
  (* 
     TODO: This is temporary; I'm assuming all the logic related to type checking
           untouched can be achieved in this mini-solver without having to call
           upon Z3. (Earl)
  *)
  | Some UntouchedSymbol -> None 
  | None -> None
;;

let z3_expr_of_value
    (ctx : Z3.context)
    (value : Constraint.value)
  : Z3.Expr.expr option =
  (match value with
   | Constraint.Int n -> Some(Z3.Arithmetic.Integer.mk_numeral_i ctx n)
   | Constraint.Bool b -> Some(Z3.Boolean.mk_val ctx b)
   | Constraint.Function _ -> None
   | Constraint.Record _ -> None
   | Constraint.Untouched _ -> None
  )
;;

let z3_fn_of_operator
    (ctx : Z3.context)
    (operator : binary_operator)
  : (Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr) option =
  let z3_listop_to_binop f =
    fun arg1 arg2 -> f ctx [arg1;arg2]
  in
  let z3_negate_binop f =
    fun arg1 arg2 -> Z3.Boolean.mk_not ctx (f ctx arg1 arg2)
  in
  match operator with
  | Binary_operator_plus -> Some(z3_listop_to_binop Z3.Arithmetic.mk_add)
  | Binary_operator_minus -> Some(z3_listop_to_binop Z3.Arithmetic.mk_sub)
  | Binary_operator_times -> Some(z3_listop_to_binop Z3.Arithmetic.mk_mul)
  | Binary_operator_divide -> Some(Z3.Arithmetic.mk_div ctx)
  | Binary_operator_modulus -> Some(Z3.Arithmetic.Integer.mk_mod ctx)
  | Binary_operator_less_than -> Some(Z3.Arithmetic.mk_lt ctx)
  | Binary_operator_less_than_or_equal_to -> Some(Z3.Arithmetic.mk_le ctx)
  | Binary_operator_equal_to -> Some(Z3.Boolean.mk_eq ctx)
  | Binary_operator_not_equal_to -> Some(z3_negate_binop Z3.Boolean.mk_eq)
  | Binary_operator_and -> Some(z3_listop_to_binop Z3.Boolean.mk_and)
  | Binary_operator_or -> Some(z3_listop_to_binop Z3.Boolean.mk_or)
  | Binary_operator_xor -> Some(Z3.Boolean.mk_xor ctx)
  | Binary_operator_xnor -> Some(z3_negate_binop Z3.Boolean.mk_xor)
;;

let z3_constraint_of_constraint
    (ctx : Z3.context)
    (symbol_cache : symbol_cache)
    (solver : t)
    (c : Constraint.t)
  : (Z3.Expr.expr list) option =
  let open Option.Monad in
  let translate_symbol symbol =
    z3_expr_of_symbol ctx symbol_cache solver symbol
  in
  let translate_value value =
    z3_expr_of_value ctx value
  in
  match c with
  | Constraint_value(x,v) ->
    let%bind z3x = translate_symbol x in
    let%bind z3v = translate_value v in
    Some([Z3.Boolean.mk_eq ctx z3x z3v])
  | Constraint_alias(x1,x2) ->
    let%bind z3x1 = translate_symbol x1 in
    let%bind z3x2 = translate_symbol x2 in
    Some([Z3.Boolean.mk_eq ctx z3x1 z3x2])
  | Constraint_binop(x1,x2,op,x3) ->
    let%bind fn = z3_fn_of_operator ctx op in
    let%bind z3x1 = translate_symbol x1 in
    let%bind z3x2 = translate_symbol x2 in
    let%bind z3x3 = translate_symbol x3 in
    let binary_c = Z3.Boolean.mk_eq ctx z3x1 (fn z3x2 z3x3) in
    ( match op with
      | Binary_operator_divide
      | Binary_operator_modulus -> (
          let%bind z3zero = translate_value (Int(0)) in
          let is_zero = Z3.Boolean.mk_eq ctx z3x3 z3zero in
          let not_zero = Z3.Boolean.mk_not ctx is_zero in
          Some([binary_c; not_zero]))
      | _ -> Some ([binary_c]) )
  | Constraint_value_clause _ ->
    None
  | Constraint_input _ ->
    None
  | Constraint_match _ ->
    None
  | Constraint_projection _ ->
    None
  | Constraint_type _ ->
    None
  | Constraint_stack _ ->
    None
  | Constraint_abort _ ->
    None
;;

let solve (solver : t) : solution option =
  let ctx = Z3.mk_context [] in
  let z3 = Z3.Solver.mk_solver ctx None in
  let symbol_cache = new_symbol_cache ctx in
  let z3constraints =
    solver.constraints
    |> Constraint.Set.enum
    |> Enum.filter_map (z3_constraint_of_constraint ctx symbol_cache solver)
    |> List.of_enum
    |> List.concat
  in
  Z3.Solver.add z3 z3constraints;
  match Z3.Solver.check z3 [] with
  | Z3.Solver.SATISFIABLE ->
    begin
      match Z3.Solver.get_model z3 with
      | None ->
        raise @@ Jhupllib.Utils.Invariant_failure
          "Z3 reports no model for a checked formula set"
      | Some model ->
        let get_value symbol =
          match z3_expr_of_symbol ctx symbol_cache solver symbol with
          | None -> None
          | Some expr ->
            begin
              match _get_symbol_type solver symbol with
              | Some IntSymbol ->
                begin
                  match Z3.Model.eval model expr true with
                  | None -> None
                  | Some expr' ->
                    (* Z3 documents a get_int function, but the latest on OPAM
                       doesn't seem to have it defined. *)
                    let n = Z3.Arithmetic.Integer.get_big_int expr' in
                    Some(Value_int(Big_int_Z.int_of_big_int n))
                end
              | Some BoolSymbol ->
                begin
                  match Z3.Model.eval model expr true with
                  | None -> None
                  | Some expr' ->
                    begin
                      match Z3.Boolean.get_bool_value expr' with
                      | Z3enums.L_TRUE -> Some(Value_bool true)
                      | Z3enums.L_FALSE -> Some(Value_bool false)
                      | Z3enums.L_UNDEF ->
                        raise @@ Jhupllib.Utils.Not_yet_implemented "L_UNDEF"
                    end
                end
              | Some FunctionSymbol -> None
              | Some RecordSymbol ->
                (* TODO: Think about how we can implement this *)
                (* TODO: look up the corresponding record *)
                raise @@ Jhupllib_utils.Not_yet_implemented "solution for record"
              | Some UntouchedSymbol ->
                begin
                let untouched_val =
                  try 
                    Symbol_map.find symbol solver.value_constraints_by_symbol
                  with Not_found ->
                    raise @@ Utils.Invariant_failure
                      (Printf.sprintf "Symbol %s not found in value constraint set"
                        (show_symbol symbol))
                in
                match untouched_val with
                | Untouched t -> Some (Value_untouched t)
                | _ ->
                  raise @@ Utils.Invariant_failure
                    (Printf.sprintf "Value %s incorrectly typed as untouched!"
                      (show_value untouched_val))
                end
              | Some BottomSymbol -> None
              | None -> None
            end
        in
        Some(get_value, solver.stack_constraint)
    end
  | Z3.Solver.UNSATISFIABLE ->
    (* Return no dictionary. *)
    None
  | Z3.Solver.UNKNOWN ->
    failwith @@ Printf.sprintf "Unknown result in solve: %s"
      (Z3.Solver.get_reason_unknown z3)
;;

let solvable solver =
  Option.is_some @@ solve solver
;;

(* **** Error finding **** *)

(* We need to effectively negate the logical operations, according to
   DeMorgan's laws.  (Think negating the predicate of the conditional;
   then the abort clause would be in the true branch.) 
    - And: not (x1 and x2) <=> (not x1) or (not x2)
    - Or: not (x1 or x2) <=> (not x1) and (not x2)
*)

(** Merge two error trees as if they are part of an AND operation.
    In an AND operation, all values must be true for the op to return true.
    Therefore if one error has a false value, the error tree is false. *)
let add_and errs_1 errs_2 : Error.Odefa_error.t list =
  match (errs_1, errs_2) with
  | ([], []) -> []
  | (_, []) ->  errs_1
  | ([], _) -> errs_2
  | (_, _) -> errs_1 @ errs_2
;;

(** Merge two error trees as if they are part of an OR operation.
    In an OR operation, only one value needs to be true for the op to be true
    so only when all errors have a false value can the error tree be false. *)
let add_or errs_1 errs_2 : Error.Odefa_error.t list =
  match (errs_1, errs_2) with
  | ([], [])
  | (_, [])
  | ([], _) -> []
  | (_, _) -> errs_1 @ errs_2
;;

let rec find_errors solver symbol =
  let open Error in
  (* Get values *)
  let value_def_opt = _get_value_def solver symbol in
  (* Match on values *)
  match value_def_opt with
  | Some (Constraint.Binop (s1, op, s2)) ->
    begin
      lazy_logger `trace (fun () ->
        Printf.sprintf "Binary operation on symbol %s" (show_symbol symbol));
      match op with
      | Binary_operator_and ->
        let et1 = find_errors solver s1 in
        let et2 = find_errors solver s2 in
        add_and et1 et2
      | Binary_operator_or ->
        let et1 = find_errors solver s1 in
        let et2 = find_errors solver s2 in
        add_or et1 et2
      | Binary_operator_xnor
      | Binary_operator_xor
      | Binary_operator_plus
      | Binary_operator_minus
      | Binary_operator_times
      | Binary_operator_divide
      | Binary_operator_modulus
      | Binary_operator_less_than
      | Binary_operator_less_than_or_equal_to
      | Binary_operator_equal_to
      | Binary_operator_not_equal_to ->
        let l_aliases = _construct_alias_chain solver s1 in
        let r_aliases = _construct_alias_chain solver s2 in
        let l_val =
          match _get_value_def solver s1 with
            | Some vs -> _symbolic_to_concrete_value vs
            | None -> raise Not_found
        in
        let r_val =
            match _get_value_def solver s2 with
            | Some vs -> _symbolic_to_concrete_value vs
            | None -> raise Not_found
        in
        let l_operand =
          if List.is_empty l_aliases then l_val else
            Ast.Var_body (Var (List.first l_aliases, None))
        in
        let r_operand =
          if List.is_empty r_aliases then r_val else
            Ast.Var_body (Var (List.first r_aliases, None))
        in
        let binop_error =  Odefa_error.Error_binop {
          err_binop_left_val = l_val;
          err_binop_right_val = r_val;
          err_binop_left_aliases = l_aliases;
          err_binop_right_aliases = r_aliases;
          err_binop_operation = (l_operand, op, r_operand);
        }
        in
        lazy_logger `trace (fun () ->
          Printf.sprintf "Binop error:\n%s" (Odefa_error.show binop_error));
        List.singleton binop_error
    end
  | Some (Constraint.Match (match_symb, pattern)) ->
    begin
      lazy_logger `trace (fun () ->
        Printf.sprintf "Pattern match on symbol %s" (show_symbol symbol));
      let match_aliases =
        _construct_alias_chain solver match_symb
      in
      let match_value =
        match Symbol_map.Exceptionless.find symbol
            solver.value_constraints_by_symbol with
        | Some v -> v
        | None ->
          raise @@ Utils.Invariant_failure
            (Printf.sprintf "Pattern match at %s did not produce a value"
            (show_symbol symbol))
      in
      match match_value with
      | Constraint.Bool false ->
        let expected_type =
          match pattern with
          | Int_pattern -> Int_type
          | Bool_pattern -> Bool_type
          | Fun_pattern -> Fun_type
          | Rec_pattern labels -> Rec_type labels
          | Strict_rec_pattern labels -> Rec_type labels
          | Any_pattern -> Top_type
          | Untouched_pattern s -> Untouched_type s
          | Any_untouched_pattern -> Any_untouched_type
        in
        let actual_type = _get_type solver match_symb in
        let match_val_source =
          match _get_value_def solver match_symb with
          | Some vs -> _symbolic_to_concrete_value vs
          | None -> raise @@ Utils.Invariant_failure
            (Printf.sprintf "%s has no value in constraint set!"
              (show_symbol match_symb))
        in
        if not (Ast.Type_signature.subtype actual_type expected_type) then begin
          let match_error = Odefa_error.Error_match {
            err_match_aliases = match_aliases;
            err_match_val = match_val_source;
            err_match_expected = expected_type;
            err_match_actual = actual_type;
          }
          in
          lazy_logger `trace (fun () ->
            Printf.sprintf "Match error:\n%s" (Odefa_error.show match_error));
          List.singleton match_error
        end else begin
          []
        end
      | Constraint.Bool true ->
        (* The special case where the constraint is true 
           and an error occurs; we need to make sure that untouched matches are the 
           only type error that falls into this category.
        *)
        (* NOTE: The above statement is not true. If we have bool + 1, the find_error
           will go down to check the isInt 1 and the constraint will be satisfied.
        *)
        let polymorphism_error =
          match pattern with
          | Any_untouched_pattern -> true
          | Int_pattern | Bool_pattern | Fun_pattern 
          | Rec_pattern _ | Strict_rec_pattern _
          | Any_pattern | Untouched_pattern _-> 
            false
        in
        if polymorphism_error 
        then
          let expected_type = Any_untouched_type in
          let actual_type = _get_type solver match_symb in
          let match_val_source =
            match _get_value_def solver match_symb with
            | Some vs -> _symbolic_to_concrete_value vs
            | None -> raise @@ Utils.Invariant_failure
              (Printf.sprintf "%s has no value in constraint set!"
                (show_symbol match_symb))
          in
          let match_error = Odefa_error.Error_match {
              err_match_aliases = match_aliases;
              err_match_val = match_val_source;
              err_match_expected = expected_type;
              err_match_actual = actual_type;
          }
          in
          lazy_logger `trace (fun () ->
            Printf.sprintf "Match error:\n%s" (Odefa_error.show match_error));
          List.singleton match_error
        else []
      | _ ->
        raise @@ Utils.Invariant_failure
          (Printf.sprintf "%s is not a boolean value" (show_symbol symbol))
    end
  (* Note (Earl): We probably need another value to represent actual type errors;
     right now it's confusing asserts with the type errors. 
  *)
  | Some (Constraint.Value v) ->
    begin
      match v with
      | Bool b ->
        if b then [] else
          let alias_chain = _construct_symbol_chain solver symbol in
          (* let () = print_endline "----------" in
          let () = List.iter (fun s -> print_endline @@ show_symbol s) alias_chain in 
          let () = print_endline "----------" in *)
          let value_error = Odefa_error.Error_value {
            err_value_aliases = alias_chain;
            err_value_val = Value_body (Value_bool b);
          }
          in
          lazy_logger `trace (fun () ->
            Printf.sprintf "Value error:\n%s" (Odefa_error.show value_error));
          List.singleton value_error
      | _ ->
        raise @@ Utils.Invariant_failure
          (Printf.sprintf "Error list on %s has non-boolean values"
            (show_symbol symbol))
    end
  | Some (Constraint.Input) ->
    raise @@ Utils.Invariant_failure
      (Printf.sprintf "Error on %s has non-boolean value"
            (show_symbol symbol))
  | Some (Constraint.Abort) ->
    raise @@ Utils.Invariant_failure
      (Printf.sprintf "Error on %s has abort value"
        (show_symbol symbol))
  | None ->
    raise @@ Utils.Invariant_failure
      (Printf.sprintf "%s has no value definition" (show_symbol symbol))
;;

(* **** Other functions **** *)

let enum solver = Constraint.Set.enum solver.constraints;;

let of_enum constraints = Enum.fold (flip add) empty constraints;;

let iter fn solver = Constraint.Set.iter fn solver.constraints;;