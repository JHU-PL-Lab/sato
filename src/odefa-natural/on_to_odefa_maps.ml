open Batteries;;
open Jhupllib;;

open Odefa_ast;;

(* let lazy_logger = Logger_utils.make_lazy_logger "On_to_odefa_types";; *)

module Expr_desc = struct
  include On_ast.Core_expr_desc;;
  let pp = On_ast_pp.pp_expr_desc;;
end;;

module Expr_desc_map = struct
  module M = Map.Make(Expr_desc);;
  include M;;
  include Pp_utils.Map_pp(M)(Expr_desc);;
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
  odefa_var_to_natodefa_expr : Expr_desc.t Ast.Ident_map.t;

  (** Mapping between two natodefa expressions.  Used to create a
      mapping of natodefa lists and variants with their record
      equivalents as their keys, as well as mappings between let recs and
      their desugared versions. *)
  natodefa_expr_to_expr : Expr_desc.t Expr_desc_map.t;

  (** Mapping between two natodefa idents.  Used to create a mapping from
      post- to pre-alphatization variables. *)
  natodefa_var_to_var : On_ast.Ident.t On_ast.Ident_map.t;

  (** Mapping between sets of natodefa idents and natodefa type sigs.  Used to
      determine if a record was originally a list, variant, or record, depending
      on its labels. *)
  natodefa_idents_to_types : On_ast.type_sig On_labels_map.t;

  match_ident_to_subj_var : Ast.var Ast.Ident_map.t;

  false_id_to_subj_var : Ast.var On_ast.Ident_map.t;
  
}

[@@ deriving show]
;;

let show_expr_desc = Pp_utils.pp_to_string On_ast_pp.pp_expr_desc;;

let print_natodefa_expr_to_expr mappings = 
  let () = Expr_desc_map.iter 
    (fun k v -> 
      let () = print_endline @@ "Key: " ^ show_expr_desc k in
      let () = print_endline @@ "Value: " ^ show_expr_desc v in
      ()) mappings.natodefa_expr_to_expr
  in
  ()

let empty is_natodefa = {
  is_natodefa = is_natodefa;
  odefa_instrument_vars_map = Ast.Ident_map.empty;
  odefa_pre_instrument_clause_mapping = Ast.Ident_map.empty;
  odefa_var_to_natodefa_expr = Ast.Ident_map.empty;
  natodefa_expr_to_expr = Expr_desc_map.empty;
  natodefa_var_to_var = On_ast.Ident_map.empty;
  natodefa_idents_to_types = On_labels_map.empty;
  match_ident_to_subj_var = Ast.Ident_map.empty;
  false_id_to_subj_var = On_ast.Ident_map.empty;
  (* abort_mapping = Ast.Ident_map.empty; *)
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
    if Expr_desc_map.mem k m then 
      m
    else 
      Expr_desc_map.add k v m 
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

let add_match_id_to_subj_var_mapping mappings m_id subj_var = 
  let match_id_subj_map = mappings.match_ident_to_subj_var in
  { mappings with
  match_ident_to_subj_var =
      Ast.Ident_map.add m_id subj_var match_id_subj_map
  }

let add_false_id_to_subj_var_mapping mappings f_id subj_var = 
  let false_subj_map = mappings.false_id_to_subj_var in
  { mappings with
    false_id_to_subj_var =
      On_ast.Ident_map.add f_id subj_var false_subj_map
  }

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
let rec on_expr_transformer 
  (transformer : On_ast.core_natodefa_edesc -> On_ast.core_natodefa_edesc) 
  (e_desc : On_ast.core_natodefa_edesc) =
  let open On_ast in
  let (recurse : core_natodefa_edesc -> core_natodefa_edesc) = on_expr_transformer transformer in
  let e_desc' = transformer e_desc in
  let expr' = e_desc'.body in
  (* NOTE: Here we require the invariant that the transformer will
     make sure the transformed expression match the og_tag
  *)
  let og_tag = e_desc.tag in
  let body' = 
    match expr' with
    | Int _ | Bool _ | Var _ | Input | Untouched _ | TypeError _ -> 
      expr'
    | Record record ->
      let record' =
        record
        |> On_ast.Ident_map.enum
        |> Enum.map (fun (lbl, e) -> (lbl, recurse e))
        |> On_ast.Ident_map.of_enum
      in
      Record record'
    | Match (e, pat_e_lst) ->
      let pat_e_lst' =
        List.map (fun (pat, e) -> (pat, recurse e)) pat_e_lst
      in
      Match (recurse e, pat_e_lst')
    | Function (id_lst, e) -> Function (id_lst, recurse e)
    | Appl (e1, e2) -> Appl (recurse e1, recurse e2)
    | Let (id, e1, e2) -> Let (id, recurse e1, recurse e2)
    | LetFun (fs, e) ->
      let Funsig (fs_ident, fs_args, e_body) = fs in
      let fs' = Funsig (fs_ident, fs_args, recurse e_body) in
      LetFun (fs', recurse e)
    | LetRecFun (fs_lst, e) ->
      let fs_lst' =
        List.map
          (fun (Funsig (id, args, e')) -> Funsig (id, args, recurse e'))
          fs_lst
      in
      LetRecFun (fs_lst', recurse e)
    | Plus (e1, e2) -> Plus (recurse e1, recurse e2)
    | Minus (e1, e2) -> Minus (recurse e1, recurse e2)
    | Times (e1, e2) -> Times (recurse e1, recurse e2)
    | Divide (e1, e2) -> Divide (recurse e1, recurse e2)
    | Modulus (e1, e2) -> Modulus (recurse e1, recurse e2)
    | Equal (e1, e2) -> Equal (recurse e1, recurse e2)
    | Neq (e1, e2) -> Neq (recurse e1, recurse e2)
    | LessThan (e1, e2) -> LessThan (recurse e1, recurse e2)
    | Leq (e1, e2) -> Leq (recurse e1, recurse e2)
    | GreaterThan (e1, e2) -> GreaterThan (recurse e1, recurse e2)
    | Geq (e1, e2) -> Geq (recurse e1, recurse e2)
    | And (e1, e2) -> And (recurse e1, recurse e2)
    | Or (e1, e2) -> Or (recurse e1, recurse e2)
    | Not e -> Not (recurse e)
    | If (e1, e2, e3) -> If (recurse e1, recurse e2, recurse e3)
    | RecordProj (e, lbl) -> RecordProj (recurse e, lbl)
    | VariantExpr (vlbl, e) -> VariantExpr (vlbl, recurse e)
    | List (e_lst) -> List (List.map recurse e_lst)
    | ListCons (e1, e2) -> ListCons (recurse e1, recurse e2)
    | Assert e -> Assert (recurse e)
    | Assume e -> Assume (recurse e)
  in
  {tag = og_tag; body = body'}
;;

let get_natodefa_equivalent_expr on_mappings odefa_ident =
  let inst_map = on_mappings.odefa_instrument_vars_map in
  let odefa_on_map = on_mappings.odefa_var_to_natodefa_expr in
  let on_expr_map = on_mappings.natodefa_expr_to_expr in
  let on_ident_map = on_mappings.natodefa_var_to_var in
  (* Get pre-instrument var *)
  let odefa_ident' =
    match Ast.Ident_map.Exceptionless.find odefa_ident inst_map with
    | Some (Some pre_inst_ident) -> pre_inst_ident
    | Some (None) | None -> odefa_ident
  in
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
  (* Get any original core natodefa exprs *)
  let get_core_natodefa (expr : On_ast.core_natodefa_edesc) =
    match Expr_desc_map.Exceptionless.find expr on_expr_map with
    | Some expr' -> 
      expr'
    | None -> expr
  in
  let on_ident_transform 
      (e_desc : On_ast.core_natodefa_edesc) : On_ast.core_natodefa_edesc =
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
    let expr = e_desc.body in
    let og_tag = e_desc.tag in
    let expr' = 
      match expr with
      | Var ident -> Var (find_ident ident)
      | Function (ident_list, body) ->
        Function (List.map find_ident ident_list, body)
      | Let (ident, e1, e2) ->
        Let (find_ident ident, e1, e2)
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
              (transform_pattern pat, match_expr))
            pat_e_list
        in
        Match (e, pat_e_list')
      | _ -> expr
    in
    {tag = og_tag; body = expr'}
  in
  natodefa_expr
  |> on_expr_transformer on_ident_transform
  |> on_expr_transformer get_core_natodefa
;;

let odefa_to_on_aliases on_mappings aliases =
  let odefa_to_on_expr x =
    get_natodefa_equivalent_expr on_mappings x
  in
  aliases
  |> List.filter_map
    (fun alias ->
      let e_desc = odefa_to_on_expr alias in
      (* let () = print_endline "----" in
      let () = print_endline @@ show_expr_desc e_desc in
      let () = print_endline "----" in *)
      match (e_desc.body) with
      | (On_ast.Var _) | TypeError _ -> Some e_desc
      | _ -> None
    )
  (* During translation, some odefa vars are assigned to the same natodefa
     vars (namely in var expressions).  The following procedure removes any
     adjacent duplicates from the alias chain. *)
  (* |> fun l ->
     let () = print_endline "----" in
     let () = 
       List.iter (fun elm -> print_endline @@ show_expr_desc elm) l
     in 
     let () = print_endline "----" in
     l *)
  |> List.unique
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

let get_false_id_to_subj_var_mapping mappings = 
  mappings.false_id_to_subj_var
;;

let get_odefa_subj_var_from_natodefa_expr mappings (expr : On_ast.core_natodefa_edesc) =
  (* Getting the desugared version of core nat expression *)
  let desugared_core = 
    (* let () = print_endline @@ "This is the transformed expr" in
    let () = print_endline @@ show_expr_desc expr in *)
    let find_key_by_value v = 
      Expr_desc_map.fold
      (fun desugared sugared acc -> 
        (* let () = print_endline "----------------------" in *)
        (* let () = print_endline @@ "This is the value in the dictionary: " in *)
        (* let () = print_endline @@ show_expr_desc sugared in *)
        (* let () = print_endline @@ "This is the key in the dictionary: " in *)
        (* let () = print_endline @@ show_expr_desc desugared in *)
        (* let () = print_endline "----------------------" in *)
        if (sugared = v) then Some desugared else acc)
      mappings.natodefa_expr_to_expr None 
    in
    let rec loop edesc = 
      let edesc_opt' = find_key_by_value edesc in
      match edesc_opt' with
      | None -> edesc
      | Some edesc' -> loop edesc'
    in
    loop expr
  in
  (* TODO: Getting the alphatization version is still wrong :( *)
  (* Getting the alphatized version *)
  let on_ident_transform 
    (e_desc : On_ast.core_natodefa_edesc) : On_ast.core_natodefa_edesc =
  let open On_ast in
  let find_ident ident =
    Ident_map.fold 
    (fun renamed og_name acc ->
      if (og_name = ident) then renamed else acc  
    ) mappings.natodefa_var_to_var ident
  in
  let transform_funsig funsig =
    let (Funsig (fun_ident, arg_ident_list, body)) = funsig in
    let fun_ident' = find_ident fun_ident in
    let arg_ident_list' = List.map find_ident arg_ident_list in
    Funsig (fun_ident', arg_ident_list', body)
  in
  let expr = e_desc.body in
  let og_tag = e_desc.tag in
  let expr' = 
    match expr with
    | Var ident -> Var (find_ident ident)
    | Function (ident_list, body) ->
      Function (List.map find_ident ident_list, body)
    | Let (ident, e1, e2) ->
      Let (find_ident ident, e1, e2)
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
            (transform_pattern pat, match_expr))
          pat_e_list
      in
      Match (e, pat_e_list')
    | _ -> expr
  in
  {tag = og_tag; body = expr'}
  in
  let alphatized = 
    on_expr_transformer on_ident_transform desugared_core
    (* actual_expr *)
  in
  let odefa_var_opt = 
    (* let () = print_endline @@ "This is the original expr" in
    let () = print_endline @@ show_expr_desc alphatized in *)
    Ast.Ident_map.fold
    (fun odefa_var core_expr acc -> 
      (* let () = print_endline @@ "This is the value in the dictionary: " in
      let () = print_endline @@ show_expr_desc core_expr in *)
      if (core_expr = alphatized) then Some odefa_var else acc) 
    mappings.odefa_var_to_natodefa_expr None
  in
  match odefa_var_opt with
  | None -> failwith "Should have found an answer here!"
  | Some x ->
    (* let () = print_endline @@ "This is the original ident" in *)
    (* let () = print_endline @@ Ast_pp.show_ident x in *)
    let subj_var = 
      Ast.Ident_map.find x mappings.match_ident_to_subj_var
    in
    subj_var
;;

let get_odefa_var_opt_from_natodefa_expr mappings (expr : On_ast.core_natodefa_edesc) =
  (* Getting the desugared version of core nat expression *)
  let desugared_core = 
    (* let () = print_endline @@ "This is the transformed expr" in
    let () = print_endline @@ show_expr_desc expr in *)
    let find_key_by_value v = 
      Expr_desc_map.fold
      (fun desugared sugared acc -> 
        (* let () = print_endline "----------------------" in *)
        (* let () = print_endline @@ "This is the value in the dictionary: " in *)
        (* let () = print_endline @@ show_expr_desc sugared in *)
        (* let () = print_endline @@ "This is the key in the dictionary: " in *)
        (* let () = print_endline @@ show_expr_desc desugared in *)
        (* let () = print_endline "----------------------" in *)
        if (sugared = v) then Some desugared else acc)
      mappings.natodefa_expr_to_expr None 
    in
    let rec loop edesc = 
      let edesc_opt' = find_key_by_value edesc in
      match edesc_opt' with
      | None -> edesc
      | Some edesc' -> loop edesc'
    in
    loop expr
  in
  (* TODO: Getting the alphatization version is still wrong :( *)
  (* Getting the alphatized version *)
  let on_ident_transform 
    (e_desc : On_ast.core_natodefa_edesc) : On_ast.core_natodefa_edesc =
  let open On_ast in
  let find_ident ident =
    Ident_map.fold 
    (fun renamed og_name acc ->
      if (og_name = ident) then renamed else acc  
    ) mappings.natodefa_var_to_var ident
  in
  let transform_funsig funsig =
    let (Funsig (fun_ident, arg_ident_list, body)) = funsig in
    let fun_ident' = find_ident fun_ident in
    let arg_ident_list' = List.map find_ident arg_ident_list in
    Funsig (fun_ident', arg_ident_list', body)
  in
  let expr = e_desc.body in
  let og_tag = e_desc.tag in
  let expr' = 
    match expr with
    | Var ident -> Var (find_ident ident)
    | Function (ident_list, body) ->
      Function (List.map find_ident ident_list, body)
    | Let (ident, e1, e2) ->
      Let (find_ident ident, e1, e2)
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
            (transform_pattern pat, match_expr))
          pat_e_list
      in
      Match (e, pat_e_list')
    | _ -> expr
  in
  {tag = og_tag; body = expr'}
  in
  let alphatized = 
    on_expr_transformer on_ident_transform desugared_core
    (* actual_expr *)
  in
  let odefa_var_opt = 
    (* let () = print_endline @@ "This is the original expr" in
    let () = print_endline @@ show_expr_desc alphatized in *)
    Ast.Ident_map.fold
    (fun odefa_var core_expr acc -> 
      (* let () = print_endline @@ "This is the value in the dictionary: " in
      let () = print_endline @@ show_expr_desc core_expr in *)
      if (core_expr = alphatized) then Some (Ast.Var (odefa_var, None)) else acc) 
    mappings.odefa_var_to_natodefa_expr None
  in
  odefa_var_opt
;;
