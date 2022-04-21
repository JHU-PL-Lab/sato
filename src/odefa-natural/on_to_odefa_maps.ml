open Batteries;;
open Jhupllib;;

open Odefa_ast;;

(* let lazy_logger = Logger_utils.make_lazy_logger "On_to_odefa_types";; *)

module Expr = struct
  include On_ast.CoreExpr;;
  let pp = On_ast_pp.pp_expr;;
end;;

module Expr_map = struct
  module M = Map.Make(Expr);;
  include M;;
  include Pp_utils.Map_pp(M)(Expr);;
end;;

module On_labels_map = struct
  module M = Map.Make(On_ast.Ident_set);;
  include M;;
  include Pp_utils.Map_pp(M)(On_ast.Ident_set);;
end;;

module Odefa_clause = struct
  type t = Ast.clause;;
  let pp = Ast_pp.pp_clause;;
end;;

type t = {

  (** True if the mapping was created during natodefa-to-odefa
      translation, false otherwise (e.g. after instrumenting on
      odefa code). *)
  is_natodefa : bool;

  (** A set of odefa variables that were added during instrumentation
      (as opposed to being in the original code or added during pre-
      instrumentation translation).  The instrumentation variable
      is the key; the value is the pre-instrumentation variable
      it aliases.  Note that the value is an Option; it is none if
      the variable has no associated pre-instrumentation alias (namely
      if it was added as a pattern match conditional var). *)
  odefa_instrument_vars_map : (Ast.Ident.t option) Ast.Ident_map.t;

  (** Mapping between variables that were added during instrumentation
      with the variables whose clauses the instrumenting clause is
      constraining.  This is mainly used to obtain the operation that
      an instrumenting conditional is constrianing. *)
  odefa_pre_instrument_clause_mapping : Odefa_clause.t Ast.Ident_map.t;

  (** Mapping between an odefa variable to the natodefa expr that the
      odefa variable was derived from. *)
  odefa_var_to_natodefa_expr : Expr.t Ast.Ident_map.t;

  (** Mapping between two natodefa expressions.  Used to create a
      mapping of natodefa lists and variants with their record
      equivalents as their keys, as well as mappings between let recs and
      their desugared versions. *)
  natodefa_expr_to_expr : Expr.t Expr_map.t;

  (** Mapping between two natodefa idents.  Used to create a mapping from
      post- to pre-alphatization variables. *)
  natodefa_var_to_var : On_ast.Ident.t On_ast.Ident_map.t;

  (** Mapping between sets of natodefa idents and natodefa type sigs.  Used to
      determine if a record was originally a list, variant, or record, depending
      on its labels. *)
  natodefa_idents_to_types : On_ast.type_sig On_labels_map.t;
}
[@@ deriving show]
;;

let print_natodefa_expr_to_expr mappings = 
  let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in
  let () = Expr_map.iter 
    (fun k v -> 
      let () = print_endline @@ "Key: " ^ show_expr k in
      let () = print_endline @@ "Value: " ^ show_expr v in
      ()) mappings.natodefa_expr_to_expr
  in
  ()

let empty is_natodefa = {
  is_natodefa = is_natodefa;
  odefa_instrument_vars_map = Ast.Ident_map.empty;
  odefa_pre_instrument_clause_mapping = Ast.Ident_map.empty;
  odefa_var_to_natodefa_expr = Ast.Ident_map.empty;
  natodefa_expr_to_expr = Expr_map.empty;
  natodefa_var_to_var = On_ast.Ident_map.empty;
  natodefa_idents_to_types = On_labels_map.empty;
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
  (* let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in *)
  let natodefa_expr_map = mappings.natodefa_expr_to_expr in
  let add' k v m = 
    if Expr_map.mem k m then 
      (* let () = print_endline @@ "--------------" in
      let () = print_endline @@ "Mapping already exists: " in
      let () = print_endline @@ show_expr k in
      let () = print_endline @@ show_expr (Expr_map.find k m) in
      let () = print_endline @@ "--------------" in *)
      m
    else 
      (* let () = print_endline @@ "--------------" in
      let () = print_endline @@ "Adding Mapping: " in
      let () = print_endline @@ show_expr k in
      let () = print_endline @@ show_expr v in
      let () = print_endline @@ "--------------" in *)
      Expr_map.add k v m 
  in
  { mappings with
    natodefa_expr_to_expr =
      add' expr1 expr2 natodefa_expr_map;
  }
;;

let add_on_var_to_var_mapping mappings var1 var2 =
  let natodefa_var_map = mappings.natodefa_var_to_var in
  { mappings with
    natodefa_var_to_var =
      On_ast.Ident_map.add var1 var2 natodefa_var_map
  }
;;

let add_on_idents_to_type_mapping mappings idents type_sig =
  let natodefa_idents_type_map = mappings.natodefa_idents_to_types in
  { mappings with
    natodefa_idents_to_types =
      On_labels_map.add idents type_sig natodefa_idents_type_map
  }
;;

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
    raise @@ Invalid_argument
      (Printf.sprintf
        "%s needs to have an associated clause."
        (Ast.show_ident odefa_ident))
;;


(* Note (Earl): The problem is with this function. It is trying to reconstruct 
   the original AST, but we have a match in a let rec that's transformed 
   separately, and we can only reconstruct one at a time. This causes us to
   chase our tail around like a stupid dog.
 *)
(** Helper function to recursively map natodefa expressions according to
    the expression-to-expression mapping (eg. records to lists or variants).
    We need a custom transformer function, rather than the one in utils, 
    because we need to first transform the expression, then recurse (whereas
    transform_expr and transform_expr_m do the other way around). *)
let rec on_expr_transformer transformer (expr : On_ast.core_natodefa) =
  (* let () = print_endline @@ "--------------" in *)
  (* let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in *)
  (* let () = print_endline @@ "Expression in on expr transformer" in *)
  (* let () = print_endline @@ show_expr expr in  *)
  let open On_ast in
  (* let () = print_endline @@ "==>" in *)
  let recurse = on_expr_transformer transformer in
  let expr' = transformer expr in
  (* let () = print_endline @@ "Expression' in on expr transformer" in
  let () = print_endline @@ show_expr expr' in
  let () = print_endline @@ "--------------" in *)
  match expr' with
  | Int _ | Bool _ | Var _ | Input | Untouched _ | TypeError _ -> expr'
  | Record record ->
    let record' =
      record
      |> On_ast.Ident_map.enum
      |> Enum.map (fun (lbl, e) -> (lbl, new_expr_desc @@ recurse e.body))
      |> On_ast.Ident_map.of_enum
    in
    Record record'
  | Match (e, pat_e_lst) ->
    (* let () = print_endline "in match" in *)
    let pat_e_lst' =
      List.map (fun (pat, e') -> 
        (* let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in
        let () = print_endline "********************" in
        let () = print_endline @@ "This is in Match" in
        let () = print_endline @@ show_pattern pat in
        let () = print_endline " -> " in
        let () = print_endline @@ show_expr e' in
        let () = print_endline " =====> " in
        let () = print_endline @@ show_expr (recurse e') in
        let () = print_endline "********************" in *)
        (pat, new_expr_desc @@ recurse e'.body)) pat_e_lst
    in
    let e' = new_expr_desc @@ recurse e.body in
    Match (e', pat_e_lst')
  | Function (id_lst, e) -> 
    let e_body = e.body in
    let e' = new_expr_desc @@ recurse e_body in
    Function (id_lst, e')
  | Appl (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Appl (e1', e2') 
  | Let (id, e1, e2) -> 
    (* let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in
    let () = print_endline "********************" in
    let () = print_endline @@ "This is in Let" in
    let () = print_endline @@ show_ident id in
    let () = print_endline " = " in
    let () = print_endline @@ show_expr e1 in
    let () = print_endline " =====> " in
    let () = print_endline @@ show_expr (recurse e1) in
    let () = print_endline "********************" in *)
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Let (id, e1', e2')
  | LetFun (fs, e) ->
    let Funsig (fs_ident, fs_args, e_body) = fs in
    (* let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in
    let () = print_endline "********************" in
    let () = print_endline @@ "This is in LetFun" in
    let () = print_endline @@ show_ident fs_ident in
    let () = print_endline " = " in
    let () = print_endline @@ show_expr e_body in
    let () = print_endline " =====> " in
    let () = print_endline @@ show_expr (recurse e_body) in
    let () = print_endline "********************" in *)
    let e_body_body = e_body.body in
    let e_body' = new_expr_desc @@ recurse e_body_body in
    let fs' = Funsig (fs_ident, fs_args, e_body') in
    let e_body = e.body in
    let e' = new_expr_desc @@ recurse e_body in
    LetFun (fs', e')
  | LetRecFun (fs_lst, e) ->
    (* let () = print_endline "in LetRecFun case" in *)
    (* let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in *)
    (* let () = print_endline @@ show_expr expr' in *)
    (* let () = print_endline @@ show_expr e in *)
    (* let () = print_endline "Pre list map in LRF case" in *)
    let fs_lst' =
      List.map
        (fun (Funsig (id, args, e')) -> 
          (* let () = print_endline @@ show_expr e' in *)
          let ep_body = e'.body in
          let e'' = new_expr_desc @@ recurse ep_body in
          Funsig (id, args, e''))
        fs_lst
    in
    (* let () = print_endline "Post list map in LRF case" in *)
    let e_body = e.body in
    let e' = new_expr_desc @@ recurse e_body in
    LetRecFun (fs_lst', e')
  | Plus (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Plus (e1', e2') 
  | Minus (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Minus (e1', e2') 
  | Times (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Times (e1', e2') 
  | Divide (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Divide (e1', e2') 
  | Modulus (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Modulus (e1', e2') 
  | Equal (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Equal (e1', e2') 
  | Neq (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Neq (e1', e2') 
  | LessThan (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    LessThan (e1', e2') 
  | Leq (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Leq (e1', e2') 
  | GreaterThan (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    GreaterThan (e1', e2') 
  | Geq (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Geq (e1', e2') 
  | And (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    And (e1', e2') 
  | Or (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    Or (e1', e2') 
  | Not e -> 
    let e_body = e.body in
    let e' = new_expr_desc @@ e_body in
    Not e'
  | If (e1, e2, e3) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e3_body = e3.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    let e3' = new_expr_desc @@ e3_body in
    If (e1', e2', e3') 
  | RecordProj (e, lbl) -> 
    let e_body = e.body in
    let e' = new_expr_desc @@ e_body in
    RecordProj (e', lbl)
  | VariantExpr (vlbl, e) ->
    let e_body = e.body in
    let e' = new_expr_desc @@ e_body in
    VariantExpr (vlbl, e')
  | List (e_lst) ->
    let e_lst' = 
      List.map (fun ed -> new_expr_desc @@ recurse ed.body) e_lst
    in 
    List e_lst'
  | ListCons (e1, e2) -> 
    let e1_body = e1.body in
    let e2_body = e2.body in
    let e1' = new_expr_desc @@ e1_body in
    let e2' = new_expr_desc @@ e2_body in
    ListCons (e1', e2') 
  | Assert e -> 
    let e_body = e.body in
    let e' = new_expr_desc @@ e_body in
    Assert e'
  | Assume e -> 
    let e_body = e.body in
    let e' = new_expr_desc @@ e_body in
    Assume e'
;;

let get_natodefa_equivalent_expr mappings odefa_ident =
  (* let () = print_endline "In get_natodefa_equivalent_expr" in *)
  let inst_map = mappings.odefa_instrument_vars_map in
  let odefa_on_map = mappings.odefa_var_to_natodefa_expr in
  let on_expr_map = mappings.natodefa_expr_to_expr in
  let on_ident_map = mappings.natodefa_var_to_var in
  (* Get pre-instrument var *)
  let odefa_ident' =
    match Ast.Ident_map.Exceptionless.find odefa_ident inst_map with
    | Some (Some pre_inst_ident) -> pre_inst_ident
    | Some (None) | None -> odefa_ident
  in
  (* let () = print_endline "pre-natodefa_expr" in *)
  (* Get natodefa expr from odefa var *)
  let natodefa_expr =
    try
      Ast.Ident_map.find odefa_ident' odefa_on_map
    with Not_found ->
      raise @@ Invalid_argument
        (Printf.sprintf
          "variable %s is not associated with any natodefa expr."
          (Ast.show_ident odefa_ident'))
  in
  (* Get any original natodefa exprs *)
  (* let () = print_endline "on_expr_transform" in *)
  let on_expr_transform (expr : On_ast.core_natodefa) =
    (* let () = print_natodefa_expr_to_expr mappings in *)
    match Expr_map.Exceptionless.find expr on_expr_map with
    | Some expr' -> 
      (* let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in
      let () = print_endline "------------------------" in
      let () = print_endline @@ show_expr expr in
      let () = print_endline @@ " maps to " in 
      let () = print_endline @@ show_expr expr' in
      let () = print_endline "------------------------" in *)
      expr'
    | None -> expr
  in
  (* let () = print_endline "pre-on_ident_transform" in *)
  let on_ident_transform (expr : On_ast.core_natodefa) =
    let open On_ast in
    let find_ident ident =
      Ident_map.find_default ident ident on_ident_map
    in
    let transform_funsig funsig =
      let (Funsig (fun_ident, arg_ident_list, body)) = funsig in
      let fun_ident' = find_ident fun_ident in
      let arg_ident_list' = List.map find_ident arg_ident_list in
      Funsig (fun_ident', arg_ident_list', body)
    in
    match expr with
    | Var ident -> Var (find_ident ident)
    | Function (ident_list, body) ->
      Function (List.map find_ident ident_list, body)
    | Let (ident, e1, e2) -> Let (find_ident ident, e1, e2)
    | LetFun (funsig, e) ->
      LetFun (transform_funsig funsig, e)
    | LetRecFun (funsig_list, e) ->
      LetRecFun (List.map transform_funsig funsig_list, e)
    | Match (e, pat_e_list) ->
      let transform_pattern pat =
        match pat with
        | RecPat record ->
          let record' =
            record
            |> Ident_map.enum
            |> Enum.map
              (fun (lbl, x_opt) ->
                match x_opt with
                | Some x -> (lbl, Some (find_ident x))
                | None -> (lbl, None)
              )
            |> Ident_map.of_enum
          in
          RecPat record'
        | StrictRecPat record ->
          let record' =
            record
            |> Ident_map.enum
            |> Enum.map
              (fun (lbl, x_opt) ->
                match x_opt with
                | Some x -> (lbl, Some (find_ident x))
                | None -> (lbl, None)
              )
            |> Ident_map.of_enum
          in
          StrictRecPat record'
        | VariantPat (vlbl, x) ->
          VariantPat (vlbl, find_ident x)
        | VarPat x ->
          VarPat (find_ident x)
        | LstDestructPat (x1, x2) ->
          LstDestructPat (find_ident x1, find_ident x2)
        | AnyPat | IntPat | BoolPat | FunPat | EmptyLstPat | UntouchedPat _ -> pat
      in
      let pat_e_list' =
        List.map
          (fun (pat, match_expr) -> 
            (* let show_expr = Pp_utils.pp_to_string On_ast_pp.pp_expr in *)
            (* let () = print_endline @@ show_expr match_expr in *)
            (transform_pattern pat, match_expr))
          pat_e_list
      in
      Match (e, pat_e_list')
    | _ -> expr
  in
  (* let () = print_endline "pre-pipe" in *)
  natodefa_expr
  |> on_expr_transformer on_ident_transform
  |> 
  (* let () = print_endline "2nd pipe" in  *)
  let res = on_expr_transformer on_expr_transform in
  (* let res = on_expr_transform in *)
  (* let () = print_endline "3rd pipe" in  *)
  (* let () = print_endline "Finished get_natodefa_equivalent_expr" in *)
  res
;;

let get_type_from_idents mappings odefa_idents =
  let on_idents =
    odefa_idents
    |> Ast.Ident_set.enum
    |> Enum.map (fun (Ast.Ident lbl) -> On_ast.Ident lbl)
    |> On_ast.Ident_set.of_enum
  in
  let on_idents_type_map = mappings.natodefa_idents_to_types in
  match On_labels_map.Exceptionless.find on_idents on_idents_type_map with
  | Some typ -> typ
  | None -> RecType on_idents
;;

let is_natodefa mappings = mappings.is_natodefa;;

let is_var_instrumenting mappings odefa_ident =
  let inst_map = mappings.odefa_instrument_vars_map in
  Ast.Ident_map.mem odefa_ident inst_map
;;