open Jhupllib;;

open Odefa_ast;;

module Odefa_natodefa_mappings : sig
  type t = {
    (** A set of odefa variables that were added during instrumentation
        (as opposed to being in the original code or added during pre-
        instrumentation translation).  The instrumentation variable
        is the key; the value is the pre-instrumentation variable
        it aliases.  Note that the value is an Option; it is none if
        the variable has no associated pre-instrumentation alias (namely
        if it was added as a pattern match conditional var). *)
    odefa_instrument_vars_map : (Ast.ident option) Ast.Ident_map.t;

    (** Mapping between variables that were added during instrumentation
        with the variables whose clauses the instrumenting clause is
        constraining.  This is mainly used to obtain the operation that
        an instrumenting conditional is constrianing. *)
    odefa_pre_instrument_clause_mapping : Ast.clause Ast.Ident_map.t;

    (** Mapping between an odefa variable to the natodefa expr that the
        odefa variable was derived from. *)
    odefa_var_to_natodefa_expr : On_ast.expr Ast.Ident_map.t;

    (** Mapping between two natodefa expressions.  Used to create a
        mapping of natodefa lists and variants with their record
        equivalents as their keys. *)
    natodefa_expr_to_expr : On_ast.expr On_ast.Expr_map.t;
  }
  [@@ deriving eq, ord]
  ;;

  val empty : t;;

  val add_odefa_instrument_var : t -> Ast.ident -> Ast.ident option -> t;;

  val add_odefa_var_clause_mapping : t -> Ast.ident -> Ast.clause -> t;;

  val add_odefa_var_on_expr_mapping : t -> Ast.ident -> On_ast.expr -> t;;

  val add_on_expr_to_expr_mapping : t -> On_ast.expr -> On_ast.expr -> t;;

  (** Get an odefa clause that existed before the odefa program was
      instrumented.  If the odefa var was added during type instrumentation,
      it will return the clause representing the constrained operation.
      If the var was added before, it will return the clause it identified
      before instrumentation. *)
  val get_pre_inst_equivalent_clause : t -> Ast.ident -> Ast.clause;;

  val get_natodefa_equivalent_expr : t -> Ast.ident -> On_ast.expr;;

end = struct
  type t = {
    odefa_instrument_vars_map : (Ast.ident option) Ast.Ident_map.t;
    odefa_pre_instrument_clause_mapping : Ast.clause Ast.Ident_map.t;
    odefa_var_to_natodefa_expr : On_ast.expr Ast.Ident_map.t;
    natodefa_expr_to_expr : On_ast.expr On_ast.Expr_map.t;
  }
  [@@ deriving eq, ord]
  ;;

  let empty = {
    odefa_instrument_vars_map = Ast.Ident_map.empty;
    odefa_pre_instrument_clause_mapping = Ast.Ident_map.empty;
    odefa_var_to_natodefa_expr = Ast.Ident_map.empty;
    natodefa_expr_to_expr = On_ast.Expr_map.empty;
  }
  ;;

  let add_odefa_instrument_var mappings inst_ident ident_opt =
    let instrument_set = mappings.odefa_instrument_vars_map in
    { mappings with
      odefa_instrument_vars_map =
        Ast.Ident_map.add inst_ident ident_opt instrument_set;
    }
  ;;

  let add_odefa_var_clause_mapping mappings var_ident clause =
    let instrument_map = mappings.odefa_pre_instrument_clause_mapping in
    { mappings with
      odefa_pre_instrument_clause_mapping =
        Ast.Ident_map.add var_ident clause instrument_map;
    }
  ;;

  let add_odefa_var_on_expr_mapping mappings odefa_ident on_expr =
    let natodefa_map = mappings.odefa_var_to_natodefa_expr in
    { mappings with
      odefa_var_to_natodefa_expr =
        Ast.Ident_map.add odefa_ident on_expr natodefa_map;
    }
  ;;
  let add_on_expr_to_expr_mapping mappings expr1 expr2 =
    let natodefa_expr_map = mappings.natodefa_expr_to_expr in
    { mappings with
      natodefa_expr_to_expr =
        On_ast.Expr_map.add expr1 expr2 natodefa_expr_map;
    }

  let get_pre_inst_equivalent_clause mappings odefa_ident =
    let inst_map = mappings.odefa_instrument_vars_map in
    let clause_map = mappings.odefa_pre_instrument_clause_mapping in
    (* Get pre-instrument var from instrument var *)
    let odefa_ident' =
      match Ast.Ident_map.Exceptionless.find odefa_ident inst_map with
      | Some (Some pre_inst_ident) -> pre_inst_ident
      | Some (None) | None -> odefa_ident
    in
    (* Get clause from var *)
    match Ast.Ident_map.Exceptionless.find odefa_ident' clause_map with
    | Some clause -> clause
    | None ->
      raise @@ Utils.Invariant_failure
        (Printf.sprintf
          "%s should have associated clause!"
          (Ast.show_ident odefa_ident))
  ;;

  let get_natodefa_equivalent_expr mappings odefa_ident =
    let inst_map = mappings.odefa_instrument_vars_map in
    let odefa_on_map = mappings.odefa_var_to_natodefa_expr in
    let on_expr_map = mappings.natodefa_expr_to_expr in
    (* Get pre-instrument var *)
    let odefa_ident' =
      match Ast.Ident_map.Exceptionless.find odefa_ident inst_map with
      | Some (Some pre_inst_ident) -> pre_inst_ident
      | Some (None) | None -> odefa_ident
    in
    (* Get natodefa expr from odefa var *)
    let natodefa_expr =
      try Ast.Ident_map.find odefa_ident' odefa_on_map with
      | Not_found ->
        raise @@ Utils.Invariant_failure
          (Printf.sprintf
            "variable %s not associated with natodefa expr"
            (Ast.show_ident odefa_ident'))
    in
    (* Get any original natodefa exprs *)
    match On_ast.Expr_map.Exceptionless.find natodefa_expr on_expr_map with
    | Some natodefa_expr' -> natodefa_expr'
    | None -> natodefa_expr
  ;;
end;;