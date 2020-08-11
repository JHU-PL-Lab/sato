open Batteries;;
(* open Jhupllib; *)

open On_ast;;
open Translator_utils;;

open TranslationMonad;;

let _lbl_m name =
  let%bind freshness = freshness_string in
  return @@ Ident (freshness ^ name)
;;

(* Note: We have two labels in order to distinguish between list heads that
   were added via consing from heads that were originally part of lists. *)

let lbl_empty_m : Ident.t m = _lbl_m "empty";;
let lbl_head_m : Ident.t m = _lbl_m "head";;
let lbl_head_cons_m : Ident.t m = _lbl_m "head_cons";;
let lbl_tail_m : Ident.t m = _lbl_m "tail";;
let lbl_variant_m (s : string) : Ident.t m = _lbl_m ("variant_" ^ s);;
let lbl_value_m : Ident.t m = _lbl_m "value";;

(* This function encodes all list-related patterns with record patterns *)
let rec encode_list_pattern (pat : pattern) : pattern m =
  match pat with
  | EmptyLstPat ->
    (* The empty list is encoded as {~empty = {}}
       The corresponding pattern is {~empty = None} *)
    let%bind lbl_empty = lbl_empty_m in
    let empty_rec = Ident_map.add lbl_empty None Ident_map.empty in
    return @@ RecPat (empty_rec)
  | LstDestructPat (hd_var, tl_var) ->
    let%bind lbl_head = lbl_head_m in
    let%bind lbl_tail = lbl_tail_m in
    let new_pat =
      Ident_map.empty
      |> Ident_map.add lbl_head @@ Some hd_var
      |> Ident_map.add lbl_tail @@ Some tl_var
    in
    return @@ RecPat (new_pat)
  | _ ->
    return pat
;;

(* This function transforms all lists in the expression to records. *)
let list_transform (e : expr) : expr m =
  let%bind lbl_empty = lbl_empty_m in
  let%bind lbl_head = lbl_head_m in
  let%bind lbl_head_cons = lbl_head_cons_m in
  let%bind lbl_tail = lbl_tail_m in
  let transformer recurse e =
    match e with
    | List expr_list ->
      let list_maker element acc =
        let%bind clean_elm = recurse element in
        let new_map =
          Ident_map.empty
          |> Ident_map.add lbl_head clean_elm
          |> Ident_map.add lbl_tail acc
        in
        return @@ Record new_map
      in
      let empty_rec = Record Ident_map.empty in
      let empty_rec' =
        Record (Ident_map.add lbl_empty empty_rec Ident_map.empty)
      in
      let%bind record_equivalent =
        list_fold_right_m list_maker expr_list empty_rec'
      in
      let%bind () = add_natodefa_expr_mapping record_equivalent e in
      return record_equivalent
    (* Here  we "cons" the expression with the list during natodefa-to-odefa translation. 
       Simple, but can introduce pitfalls such as:
       - How do we know if what we are consing to is not a list? How do we typecheck?
       - What if we wish to lazily cons, eg. as part of a freeze Fun x -> x :: [y]
      The latter question should be a non-issue due to the encoding, however. - KQ
    *)
    | ListCons (expr, expr_list) ->
      let%bind clean_expr = recurse expr in
      let%bind record_list = recurse expr_list in
      let new_map =
        Ident_map.empty
        |> Ident_map.add lbl_head_cons clean_expr
        |> Ident_map.add lbl_tail record_list
      in
      let record_equivalent = Record new_map in
      let%bind () = add_natodefa_expr_mapping record_equivalent e in
      return record_equivalent
    | Match (match_expr, pat_expr_list) ->
      let%bind new_match_e = recurse match_expr in
      (* routine to pass into List.map... *)
      let pat_expr_list_changer pat_expr_tuple =
        let (curr_pat, curr_expr) = pat_expr_tuple in
        let%bind new_pat = encode_list_pattern curr_pat in
        let%bind new_expr = recurse curr_expr in
        return (new_pat, new_expr)
      in
      let%bind new_pat_expr_list =
        sequence @@ List.map pat_expr_list_changer pat_expr_list
      in
      let new_expr = Match (new_match_e, new_pat_expr_list) in
      let%bind () = add_natodefa_expr_mapping new_expr e in
      return @@ new_expr
    | _ ->
      return e
  in
  m_transform_expr transformer e
;;

(* This function takes a Variant expression and converts it into a
   Record expression. *)
let variant_expr_to_record recurse
    (v_label : variant_label)
    (v_expr : expr)
  : expr m =
  let Variant_label v_name = v_label in
  let%bind variant_ident = lbl_variant_m v_name in
  let empty_rec = Record (Ident_map.empty) in
  let map_with_label =
    Ident_map.add variant_ident empty_rec Ident_map.empty
  in
  let%bind encoded_v_expr = recurse v_expr in
  let%bind lbl_value = lbl_value_m in
  let res_map = Ident_map.add lbl_value encoded_v_expr map_with_label in
  let res_record = Record (res_map) in
  return res_record
;;

(* Function that takes a pattern and, if it's a Variant pattern,
   converts it to a Record pattern. *)
let encode_variant_pattern (p : pattern) : pattern m =
  match p with
  | VariantPat (v_label, v_var) ->
    let Variant_label (v_name) = v_label in
    let%bind variant_ident = lbl_variant_m v_name in
    let new_pattern =
      Ident_map.add variant_ident (Some v_var) Ident_map.empty
    in
    return @@ RecPat (new_pattern)
  | _ ->
    return p
;;

(* Overall Function that takes an expression and converts all of the Variant
   expressions and patterns within it to Record expressions and patterns. *)
let encode_variant (e : expr) : expr m =
  let transformer recurse e =
    match e with
    | VariantExpr (lbl, e') ->
      let%bind record_equivalent = variant_expr_to_record recurse lbl e' in
      let%bind () = add_natodefa_expr_mapping record_equivalent e in
      return record_equivalent
    | Match (match_e, pat_expr_list) ->
      let%bind new_match_e = recurse match_e in
      (* routine to pass into List.map to edit all of the pattern/expression
         tuples. *)
      let pat_expr_list_changer pat_expr_tuple =
        let (curr_pat, curr_expr) = pat_expr_tuple in
        let%bind new_pat = encode_variant_pattern curr_pat in
        let%bind new_expr = recurse curr_expr in
        return (new_pat, new_expr)
      in
      let%bind new_pat_expr_list =
        sequence @@ List.map pat_expr_list_changer pat_expr_list
      in
      let new_expr = Match (new_match_e, new_pat_expr_list) in
      let%bind () = add_natodefa_expr_mapping new_expr e in
      return new_expr
    | _ ->
      return e
  in
  m_transform_expr transformer e
;;