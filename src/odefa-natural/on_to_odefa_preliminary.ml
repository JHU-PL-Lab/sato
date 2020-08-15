open Batteries;;
open Jhupllib;;

open On_ast;;
open On_to_odefa_monad;;

open TranslationMonad;;

let lazy_logger = Logger_utils.make_lazy_logger "On_to_odefa_preliminary";;

let _lbl_m name =
  let%bind freshness = freshness_string in
  return @@ Ident (freshness ^ name)
;;

let lbl_empty_m : Ident.t m = _lbl_m "empty";;
let lbl_head_m : Ident.t m = _lbl_m "head";;
let lbl_cons_m : Ident.t m = _lbl_m "cons";;
let lbl_tail_m : Ident.t m = _lbl_m "tail";;
let lbl_variant_m (s : string) : Ident.t m = _lbl_m ("variant_" ^ s);;
let lbl_value_m : Ident.t m = _lbl_m "value";;

let list_expr_to_record recurse (expr_lst : expr list) =
  (* Record labels *)
  let%bind lbl_empty = lbl_empty_m in
  let%bind lbl_head = lbl_head_m in
  let%bind lbl_tail = lbl_tail_m in
  (* Add appropriate types *)
  let empty_list_lbls = Ident_set.singleton lbl_empty in
  let nonempty_list_lbls =
    Ident_set.empty
    |> Ident_set.add lbl_head
    |> Ident_set.add lbl_tail
  in
  let lst_type = On_to_odefa_types.ListType in
  let%bind () = add_natodefa_type_mapping empty_list_lbls lst_type in
  let%bind () = add_natodefa_type_mapping nonempty_list_lbls lst_type in
  (* Make record *)
  let list_maker element acc =
    let%bind clean_elm = recurse element in
    let new_map =
      Ident_map.empty
      |> Ident_map.add lbl_head clean_elm
      |> Ident_map.add lbl_tail acc
    in
    return @@ Record new_map
  in
  let empty_rec =
    Record (Ident_map.add lbl_empty (Record Ident_map.empty) Ident_map.empty)
  in
  let%bind record_equivalent =
    list_fold_right_m list_maker expr_lst empty_rec
  in
  return record_equivalent
;;

(* Here  we "cons" the expression with the list during natodefa-to-odefa translation. 
    Simple, but can introduce pitfalls such as:
    - How do we know if what we are consing to is not a list? How do we typecheck?
    - What if we wish to lazily cons, eg. as part of a freeze Fun x -> x :: [y]
  The latter question should be a non-issue due to the encoding, however. - KQ
*)
let list_cons_expr_to_record recurse (expr : expr) (list_expr : expr) =
  (* Record labels *)
  (* Note: We need to add extra cons label to distinguish list cons from regular
     lists *)
  let%bind lbl_head = lbl_head_m in
  let%bind lbl_cons = lbl_cons_m in
  let%bind lbl_tail = lbl_tail_m in
  (* Add appropriate types *)
  let lst_lbls =
    Ident_set.empty
    |> Ident_set.add lbl_head
    |> Ident_set.add lbl_cons
    |> Ident_set.add lbl_tail
  in
  let%bind () =
    add_natodefa_type_mapping lst_lbls On_to_odefa_types.ListType
  in
  (* Recurse over inner expr *)
  let%bind clean_expr = recurse expr in
  let%bind record_list = recurse list_expr in
  (* Make record *)
  let new_map =
    Ident_map.empty
    |> Ident_map.add lbl_head clean_expr
    |> Ident_map.add lbl_tail record_list
    |> Ident_map.add lbl_cons (Record Ident_map.empty)
  in
  let record_equivalent = Record new_map in
  return record_equivalent
;;

(* This function takes a Variant expression and converts it into a
   Record expression. *)
let variant_expr_to_record recurse
    (v_label : variant_label)
    (v_expr : expr)
  : expr m =
  (* Record labels *)
  let Variant_label v_name = v_label in
  let%bind lbl_variant = lbl_variant_m v_name in
  let%bind lbl_value = lbl_value_m in
  (* Add appropriate types *)
  let variant_lbl_set =
    Ident_set.empty
    |> Ident_set.add lbl_variant
    |> Ident_set.add lbl_value
  in
  let variant_typ = On_to_odefa_types.VariantType v_label in
  let%bind () = add_natodefa_type_mapping variant_lbl_set variant_typ in
  (* Recurse over inner expr *)
  let%bind encoded_v_expr = recurse v_expr in
  (* Make record *)
  let empty_rec = Record (Ident_map.empty) in
  let map_with_label =
    Ident_map.add lbl_variant empty_rec Ident_map.empty
  in
  let res_map = Ident_map.add lbl_value encoded_v_expr map_with_label in
  let res_record = Record (res_map) in
  return res_record
;;

let encode_pattern (pattern : pattern) : pattern m =
  match pattern with
  (* Encode list patterns *)
  | EmptyLstPat ->
    (* The empty list is encoded as {~empty = {}}
       The corresponding pattern is {~empty = None} *)
    let%bind lbl_empty = lbl_empty_m in
    let%bind () =
      add_natodefa_type_mapping
        (Ident_set.singleton lbl_empty)
        (On_to_odefa_types.ListType)
    in
    let empty_rec = Ident_map.add lbl_empty None Ident_map.empty in
    let empty_rec_pat = RecPat empty_rec in
    let%bind () = add_natodefa_pattern_mapping empty_rec_pat pattern in
    return empty_rec_pat
  | LstDestructPat (hd_var, tl_var) ->
    let%bind lbl_head = lbl_head_m in
    let%bind lbl_tail = lbl_tail_m in
    let%bind () =
      add_natodefa_type_mapping
        (Ident_set.empty |> Ident_set.add lbl_head |> Ident_set.add lbl_tail)
        (On_to_odefa_types.ListType)
    in
    let new_lbls =
      Ident_map.empty
      |> Ident_map.add lbl_head @@ Some hd_var
      |> Ident_map.add lbl_tail @@ Some tl_var
    in
    let new_pattern = RecPat new_lbls in
    let%bind () = add_natodefa_pattern_mapping new_pattern pattern in
    return new_pattern
  (* Encode variant patterns *)
  | VariantPat (v_label, v_var) ->
    let Variant_label (v_name) = v_label in
    let%bind variant_lbl = lbl_variant_m v_name in
    let%bind value_lbl = lbl_value_m in
    let%bind () =
      add_natodefa_type_mapping
        (Ident_set.empty |> Ident_set.add variant_lbl |> Ident_set.add value_lbl)
        (On_to_odefa_types.VariantType v_label)
    in
    let record =
      Ident_map.empty
      |> Ident_map.add variant_lbl None
      |> Ident_map.add value_lbl (Some v_var)
    in
    let new_pattern = RecPat record in
    let%bind () = add_natodefa_pattern_mapping new_pattern pattern in
    return new_pattern
  (* All other patterns: don't encode *)
  | AnyPat | IntPat | BoolPat | FunPat | RecPat _ | VarPat _ ->
    return pattern
;;

let encode_match_exprs recurse
    (match_expr : expr)
    (pat_expr_lst : (pattern * expr) list) =
  (* Transform first expression *)
  let%bind new_match_expr = recurse match_expr in
  (* Transform pattern-expression pairs *)
  let pat_expr_list_changer pat_expr_tuple =
  let (curr_pat, curr_expr) = pat_expr_tuple in
  let%bind new_pat = encode_pattern curr_pat in
  let%bind new_expr = recurse curr_expr in
    return (new_pat, new_expr)
  in
  let%bind new_pat_expr_lst =
    sequence @@ List.map pat_expr_list_changer pat_expr_lst
  in
  (* Return final match expression *)
  return @@ Match (new_match_expr, new_pat_expr_lst)
;;

(** Transform a let rec expression into one that uses functions.
    E.g. let rec f n = ... in f 10
    becomes
      let f = fun f' a ->
        let f = f' f' in
        ...
      in
      let f'' = f f in f'' 10
    E.g. let rec f a = ... with g b = ... in f 10
    becomes
      let f = fun f' g' a ->
        let f'' = f' f' g' in
        let g'' = g' f' g' in
        ...
      in
      let g = fun f' g' b ->
        let f'' = f' f' g' in
        let g'' = g' f' g' in
        ...
      in
      let f''' = f'' f'' g'' in
      let g''' = g'' f'' g'' in
      f''' 10
*)
let letrec_expr_to_fun recurse fun_sig_list rec_expr =
  (* Translate inner expression *)
  let%bind transformed_rec_expr = recurse rec_expr in
  (* Come up with new names for functions *)
  let original_names =
    List.map (fun (Funsig (id, _, _)) -> id) fun_sig_list
  in
  let%bind new_names =
    sequence @@ List.map
      (fun (Ident old_name) ->
        let%bind new_name = fresh_name old_name in
        return @@ Ident new_name
      )
      original_names
  in
  let name_pairs = List.combine original_names new_names in
  (* Create repeated function applications, eg. f g h ... *)
  let%bind appls_for_funs =
    list_fold_left_m
      (fun appl_dict base_fun ->
        let (original_fun_name, new_fun_name) = base_fun in
        let sub_appl =
          List.fold_left
            (fun acc fun_name -> Appl(acc, Var (fun_name)))
            (Var (new_fun_name))
            new_names
        in
        return @@ Ident_map.add original_fun_name sub_appl appl_dict
      )
      Ident_map.empty
      name_pairs
  in
  (* Create let fun expressions *)
  let lt_maker_fun fun_name acc =
      let cur_appl_expr = Ident_map.find fun_name appls_for_funs in
      Let (fun_name, cur_appl_expr, acc)
  in
  let transformed_outer_expr =
    List.fold_right lt_maker_fun original_names transformed_rec_expr
  in
  let sig_name_pairs = List.combine fun_sig_list new_names in
  (* Final expression *)
  let%bind ret_expr =
    list_fold_right_m
      (fun (fun_sig, fun_new_name) acc ->
        let (Funsig (_, param_list, cur_f_expr)) = fun_sig in
        let%bind transformed_cur_f_expr = recurse cur_f_expr in
        let new_param_list = new_names @ param_list in
        let new_fun_expr =
          List.fold_right lt_maker_fun original_names transformed_cur_f_expr
        in
        let new_fun = Function (new_param_list, new_fun_expr) in
        return @@ Let (fun_new_name, new_fun, acc)
      )
      sig_name_pairs
      transformed_outer_expr
  in
  return ret_expr
;;

let preliminary_encode_expr (e : expr) : expr m =
  let transformer recurse expr =
    match expr with
    | List e_lst ->
      let%bind expr' = list_expr_to_record recurse e_lst in
      let%bind () = add_natodefa_expr_mapping expr' expr in
      return expr'
    | ListCons (e, e_lst) ->
      let%bind expr' = list_cons_expr_to_record recurse e e_lst in
      let%bind () = add_natodefa_expr_mapping expr' expr in
      return expr'
    | VariantExpr (lbl, e') ->
      let%bind expr' = variant_expr_to_record recurse lbl e' in
      let%bind () = add_natodefa_expr_mapping expr' expr in
      return expr'
    | Match (match_e, pat_e_lst) ->
      let%bind expr' = encode_match_exprs recurse match_e pat_e_lst in
      let%bind () = add_natodefa_expr_mapping expr' expr in
      return expr'
    | LetRecFun (fun_sig_list, rec_e) ->
      let%bind expr' = letrec_expr_to_fun recurse fun_sig_list rec_e in
      let%bind () = add_natodefa_expr_mapping expr' expr in
      return expr'
    | _ -> return expr
  in
  m_transform_expr transformer e
;;