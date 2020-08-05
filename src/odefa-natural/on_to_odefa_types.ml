open Odefa_ast;;

module Odefa_natodefa_mappings : sig
  type t = {
    (** Mapping between variables that were added during instrumentation
        with the variables whose clauses the instrumenting clause is
        constraining.  This is mainly used to obtain the operation that
        an instrumenting conditional is constrianing. *)
    odefa_pre_instrument_clause_mapping : Ast.clause Ast.Ident_map.t;

    (** Mapping between an odefa variable to the natodefa expr that the
        odefa variable was derived from. *)
    odefa_var_to_natodefa_expr : On_ast.expr Ast.Ident_map.t;
  }
  [@@ deriving eq, ord]
  ;;

  val empty : t;;

  val add_var_clause_mapping : t -> Ast.ident -> Ast.clause -> t;;

  val add_natodefa_mapping : t -> Ast.ident -> On_ast.expr -> t;;

  (* val get_pre_instrumented : t -> Ast.ident -> Ast.clause;; *)

  (* val get_natodefa_expr : t -> Ast.ident -> On_ast.expr;; *)

end = struct
  type t = {
    odefa_pre_instrument_clause_mapping : Ast.clause Ast.Ident_map.t;
    odefa_var_to_natodefa_expr : On_ast.expr Ast.Ident_map.t;
  }
  [@@ deriving eq, ord]
  ;;

  let empty = {
    odefa_pre_instrument_clause_mapping = Ast.Ident_map.empty;
    odefa_var_to_natodefa_expr = Ast.Ident_map.empty;
  }
  ;;

  let add_var_clause_mapping mappings inst_ident pre_inst_clause =
    let instrument_map = mappings.odefa_pre_instrument_clause_mapping in
    { mappings with
      odefa_pre_instrument_clause_mapping =
        Ast.Ident_map.add inst_ident pre_inst_clause instrument_map;
    }
  ;;

  (*
  let get_pre_instrumented mappings inst_ident =
    let instrument_map = mappings.odefa_pre_instrument_clause_mapping in
    Ast.Ident_map.find_default inst_ident inst_ident instrument_map
  ;;
  *)

  let add_natodefa_mapping mappings odefa_ident on_expr =
    let natodefa_map = mappings.odefa_var_to_natodefa_expr in
    { mappings with
      odefa_var_to_natodefa_expr =
        Ast.Ident_map.add odefa_ident on_expr natodefa_map;
    }
  ;;

  (*
  let get_natodefa_expr mappings odefa_ident =
    let natodefa_map = mappings.odefa_var_to_natodefa_expr in
    try
      Ast.Ident_map.find odefa_ident natodefa_map
    with Not_found ->
      (* If the variable is not in the mapping, it's probably because it was
         originally in the natodefa code. *)
      let (Ast.Ident id) = odefa_ident in
      On_ast.Var (Ident id)
  ;;
  *)
end;;