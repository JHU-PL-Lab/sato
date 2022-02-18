open Batteries;;

open On_ast;;
(* open Ton_to_on_maps;; *)
open Ton_to_on_monad;;

open TonTranslationMonad;;

let transform_funsig 
  (f : 'a expr -> 'b expr m) 
  (Funsig (fun_name, params, e) : 'a funsig) 
  : 'b funsig m
  = 
  let%bind e' = f e in
  return @@ Funsig (fun_name, params, e')
;;
(* Phase one of transformation: turning all syntactic types into its
   semantic correspondence.
   i.e. int -> { generator = fun _ -> input, 
               , checker = fun e -> isInt e
               }
*)
(* Each false is a potential place for type error.
   Issue: There are cases (i.e. union type) where the boolean value
   is used to check which side of the union we're on. So they're not necessarily 
   all errors.

   What if each "false" is different?

   We might need to bind the semantic pairs themselves as well--need to
   connect the syntactic type with the pair so that when we project from
   them, we can keep track of what type it's supposed to be.
    --> This will get us the original type.

   How do we keep track of the fail & the original type's relationship?

*)
let rec semantic_type_of (t : syn_type_natodefa) : sem_type_natodefa m =
  match t with
  | TypeVar tvar -> return @@ Appl (Var tvar, Var tvar)
  | TypeInt ->
    let generator =
      Function ([Ident "~null"], Input)
    in
    let%bind checker =
      let%bind expr_id = fresh_ident "expr" in 
      let%bind fail_id = fresh_ident "fail" in
      let check_cls = 
        Function ([expr_id], 
          Match (Var expr_id, 
                [(IntPat, Bool true); (AnyPat, Var fail_id)]))
      in
      let fail_cls = Let (fail_id, Bool false, check_cls) in
      return @@ fail_cls
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  | TypeBool ->
    let generator =
      Function ([Ident "~null"], Geq (Input, Int 0))
    in
    let%bind checker =
      let%bind expr_id = fresh_ident "expr" in 
      let%bind fail_id = fresh_ident "fail" in
      let check_cls = 
        Function ([expr_id], 
          Match (Var expr_id, 
                [(BoolPat, Bool true); (AnyPat, Var fail_id)]))
      in
      let fail_cls = Let (fail_id, Bool false, check_cls) in
      return @@ fail_cls
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  | TypeRecord r ->
    let%bind generator = 
      let all_bindings = Ident_map.bindings r in
      let empty_record = Ident_map.empty in
      let mapper (lbl, lbl_type) = 
        let (Ident lbl_str) = lbl in 
        let%bind lbl_var = fresh_ident lbl_str in
        return @@ (lbl, lbl_var, lbl_type)
      in
      let%bind lbl_to_var = 
        all_bindings
        |> List.map mapper
        |> sequence
      in
      let folder acc (lbl, lbl_var, _) = 
        return @@ Ident_map.add lbl (Var lbl_var) acc      
      in
      let%bind res_record = 
        list_fold_left_m 
          folder
          empty_record lbl_to_var 
      in
      let folder' acc (_, lbl_var, cur_t) = 
        let%bind gc_pair = semantic_type_of cur_t in
        return @@ 
          Let (lbl_var, 
               Appl (RecordProj (gc_pair, Label "generator"), Int 0), 
               acc) 
      in
      let%bind rec_input = fresh_ident "rec_input" in
      let base_acc = Let (rec_input, Record res_record, Var rec_input) in
      let%bind gen_expr = list_fold_left_m folder' base_acc lbl_to_var in
      return @@ Function ([Ident "~null"], gen_expr)
    in
    let%bind checker = 
      let all_bindings = Ident_map.bindings r in
      let all_keys = Enum.map (fun k -> (k, None)) (Ident_map.keys r) in
      let type_dict = Ident_map.of_enum all_keys in
      let%bind lbl_check_id = fresh_ident "lbl_check" in
      let%bind expr_id = fresh_ident "expr" in
      let fold_fun acc (Ident lbl, t) = 
        let%bind cur_gc_pair = semantic_type_of t in
        return @@
        Let (lbl_check_id, 
              Appl (RecordProj (cur_gc_pair, Label "checker"), RecordProj (Var expr_id, Label lbl)), 
              And (Var lbl_check_id, acc))
      in
      let (Ident first_lbl, first_type) = List.hd all_bindings in
      let%bind gc_pair_fst = semantic_type_of first_type in
      let init_acc = Appl (RecordProj (gc_pair_fst, Label "checker"), RecordProj (Var expr_id, Label first_lbl)) in
      let%bind fun_body = list_fold_left_m fold_fun init_acc (List.tl all_bindings) in
      let match_body = Match (Var expr_id, 
                              [(StrictRecPat type_dict, fun_body); 
                              (AnyPat, Bool false)]) in
      return @@Function ([expr_id], match_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  | TypeList l ->
    let%bind gc_pair = semantic_type_of l in
    let%bind generator = 
      let%bind len_id = fresh_ident "len" in
      let%bind list_id = fresh_ident "list" in
      let%bind maker_id = fresh_ident "list_maker" in
      let%bind elm_id = fresh_ident "elm" in
      let recur_call = 
        Let (elm_id, 
             Appl (RecordProj (gc_pair, Label "generator"), Int 0), 
             ListCons (Var elm_id, Appl (Var maker_id, Minus (Var len_id, Int 1)))) 
      in
      let list_maker = If (Equal (Var len_id, Int 0), List [], recur_call) in
      let list_maker_fun = Funsig (maker_id, [len_id], list_maker) in
      let inner_let = Let (list_id, Appl (Var maker_id, Var len_id), Var list_id) in
      let list_len = Let (len_id, Input, inner_let) in
      let gen_expr = LetRecFun ([list_maker_fun], list_len) in
      return @@ Function ([Ident "~null"], gen_expr)
    in
    let%bind checker = 
      let%bind test_fun_id = fresh_ident "test_fun" in
      let%bind test_list_id = fresh_ident "test_list" in
      let%bind elm_check_id = fresh_ident "elm_check" in
      let test_fun = 
        Match (Var test_list_id, 
               [(EmptyLstPat, Bool true); 
                (LstDestructPat 
                  (Ident "hd", Ident "tl"), 
                  (Let (elm_check_id, 
                        Appl (RecordProj (gc_pair, Label "checker"), Var (Ident "hd")), 
                        And (Var elm_check_id, Appl (Var test_fun_id, Var (Ident "tl"))))))
               ]) in
      let check_fun = Funsig (test_fun_id, [test_list_id], test_fun) in
      let%bind expr_id = fresh_ident "expr" in
      let fun_body = LetRecFun ([check_fun], Appl (Var test_fun_id, Var expr_id)) in
      let match_body = Match (Var expr_id, 
                              [(EmptyLstPat, Bool true); 
                               (LstDestructPat (Ident "~underscore", Ident "~underscore"), fun_body);
                               (AnyPat, Bool false)
                              ]) 
      in
      return @@ Function ([expr_id], match_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  | TypeArrow (t1, t2) ->
    let%bind gc_pair_dom = semantic_type_of t1 in
    let%bind gc_pair_cod = semantic_type_of t2 in
    let%bind generator = 
      let%bind arg_assume = fresh_ident "arg_assume" in
      let inner_expr = If (Appl (RecordProj (gc_pair_dom, Label "checker"), Var arg_assume), 
                           Appl (RecordProj (gc_pair_cod, Label "generator"), Int 0), 
                           Assert (Bool false)) in 
      let gen_expr = Function ([arg_assume], inner_expr) in
      return @@ Function ([Ident "~null"], gen_expr)
    in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let%bind arg_assert = fresh_ident "arg_assert" in
      let fun_body = Let (arg_assert, 
                          Appl (RecordProj (gc_pair_dom, Label "generator"), Int 0), 
                          Appl (RecordProj (gc_pair_cod, Label "checker"), Appl (Var expr_id, Var arg_assert))) in
      return @@ Function ([expr_id], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  | TypeArrowD ((x1, t1), t2) ->
    let%bind gc_pair_dom = semantic_type_of t1 in
    let%bind generator = 
      let%bind arg_assume = fresh_ident "arg_assume" in
      let%bind gc_pair_cod = semantic_type_of t2 in
      let gc_pair_cod' = Appl (Function ([x1], gc_pair_cod), (Var arg_assume)) in
      let inner_expr = If (Appl (RecordProj (gc_pair_dom, Label "checker"), Var arg_assume), 
                            Appl (RecordProj (gc_pair_cod', Label "generator"), Int 0), 
                            Assert (Bool false)) in 
      let gen_expr = Function ([arg_assume], inner_expr) in
      return @@ Function ([Ident "~null"], gen_expr)
    in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let%bind arg_assert = fresh_ident "arg_assert" in
      let%bind gc_pair_cod = semantic_type_of t2 in
      let gc_pair_cod' = Appl (Function ([x1], gc_pair_cod), (Var arg_assert)) in
      let fun_body = Let (arg_assert, 
                          Appl (RecordProj (gc_pair_dom, Label "generator"), Int 0), 
                          Appl (RecordProj (gc_pair_cod', Label "checker"), Appl (Var expr_id, Var arg_assert))) in
      return @@ Function ([expr_id], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  | TypeSet (t, p) ->
    let%bind gc_pair = semantic_type_of t in
    let%bind p' = semantic_type_of p in
    let%bind generator = 
      let%bind candidate = fresh_ident "candidate" in
      let pred_check = If (Appl (p', Var candidate), Var candidate, Assume (Bool false)) in
      let gen_expr = Let (candidate, 
                          Appl (RecordProj (gc_pair, Label "generator"), Int 0), 
                          pred_check) in
      return @@ Function ([Ident "~null"], gen_expr)
    in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let fun_body = If (Appl (RecordProj (gc_pair, Label "checker"), Var expr_id), 
                         Appl (p', Var expr_id), Bool false) in
      return @@ Function ([expr_id], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    let%bind gc_pair_pred = semantic_type_of (TypeArrow (t, TypeBool)) in
    let%bind  check_pred_id = fresh_ident "check_pred" in
    let pred_cond = If (Var check_pred_id, Record rec_map, Assert (Bool false)) in
    let check_pred = Let (check_pred_id,
                          Appl (RecordProj (gc_pair_pred, Label "checker"), p'),
                          pred_cond)
    in
    return @@ check_pred
  | TypeUnion (t1, t2) ->
    let%bind gc_pair1 = semantic_type_of t1 in
    let%bind gc_pair2 = semantic_type_of t2 in
    let%bind generator = 
      let%bind select_int = fresh_ident "select_int" in
      let branch = If (Geq (Var select_int, Int 0), 
                        Appl (RecordProj (gc_pair1, Label "generator"), Int 0), 
                        Appl (RecordProj (gc_pair2, Label "generator"), Int 0)) in
      let gen_expr = Let (select_int, Input, branch) in
      return @@ Function ([Ident "~null"], gen_expr)
    in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let%bind select_int = fresh_ident "select_int" in
      let checker1 = If (Appl (RecordProj (gc_pair1, Label "checker"), Var expr_id), 
                         Bool true, 
                         Appl (RecordProj (gc_pair2, Label "checker"), Var expr_id)) in
      let checker2 = If (Appl (RecordProj (gc_pair2, Label "checker"), Var expr_id), 
                         Bool true, 
                         Appl (RecordProj (gc_pair1, Label "checker"), Var expr_id)) in
      let branch = If (Geq (Var select_int, Int 0), checker1, checker2) in
      let fun_body = Let (select_int, Input, branch) in
      return @@ Function ([expr_id], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  | TypeIntersect (t1, t2) -> 
    let%bind gc_pair1 = semantic_type_of t1 in
    let%bind gc_pair2 = semantic_type_of t2 in
    let%bind generator = 
      let%bind candidate_var = fresh_ident "candidate" in
      let validate = If (Appl (RecordProj (gc_pair2, Label "checker"), (Var candidate_var)), 
                         Var candidate_var, 
                         Assume (Bool false)) in
      let gen_expr = Let (candidate_var, 
                          Appl (RecordProj (gc_pair1, Label "generator"), Int 0), 
                          validate) in
      return @@ Function ([Ident "~null"], gen_expr)
    in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let fun_body = If (Appl (RecordProj (gc_pair1, Label "checker"), Var expr_id), 
                         Appl (RecordProj (gc_pair2, Label "checker"), Var expr_id), 
                         Bool false) in
      return @@ Function ([expr_id], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  | TypeRecurse (t_var, t') ->
    let%bind gc_pair = semantic_type_of t' in
    let%bind primer_id = fresh_ident "primer" in
    return @@ Let (primer_id, Function ([t_var], gc_pair), Appl (Var primer_id, Var primer_id))
  | TypeUntouched t ->
    let generator = 
      Function ([Ident "~null"], Untouched t)
    in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      return @@ Function ([expr_id], Match (Var expr_id, [(UntouchedPat t, Bool true); (AnyPat, Bool false)]))
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    return @@ Record rec_map
  (* These are constant functions that only modify the types *)
  | Int n -> return @@ Int n
  | Bool b -> return @@ Bool b
  | Var x -> return @@ Var x
  | Input -> return @@ Input
  | Untouched s -> return @@ Untouched s
  | TypeError x -> return @@ TypeError x
  (* All other expressions are homomorphic *)
  | Function (id_lst, f_expr) -> 
    let%bind f_expr' = semantic_type_of f_expr in
    return @@ Function (id_lst, f_expr')
  | Appl (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Appl (e1', e2')
  | Let (x, e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Let (x, e1', e2')
  | LetRecFun (sig_lst, e) ->
    begin
      let%bind sig_lst' = 
        sig_lst 
        |> List.map (transform_funsig semantic_type_of) 
        |> sequence 
      in 
      let%bind e' = semantic_type_of e in
      return @@ LetRecFun (sig_lst', e')
    end
  | LetFun (fun_sig, e) ->
    begin
      let%bind fun_sig' = 
        fun_sig
        |> transform_funsig semantic_type_of
      in
      let%bind e' = semantic_type_of e in
      return @@ LetFun (fun_sig', e')
    end
  | LetWithType (x, e1, e2, t) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let%bind t' = semantic_type_of t in
    let%bind () = add_sem_to_syn_mapping (Var x) t in
    return @@ LetWithType (x, e1', e2', t')
  | LetRecFunWithType (sig_lst, e, t_lst) ->
    begin
      let sig_t_lst = List.combine sig_lst t_lst in
      let%bind () = sig_t_lst
        |> list_fold_left_m 
           (fun () (Funsig (f, _, _), f_t) -> add_sem_to_syn_mapping (Var f) f_t)
           ()
      in
      let%bind sig_lst' = 
        sig_lst
        |> List.map (transform_funsig semantic_type_of)
        |> sequence
      in
      let%bind t_lst' =
        t_lst 
        |> List.map semantic_type_of
        |> sequence
      in 
      let%bind e' = semantic_type_of e in
      return @@ LetRecFunWithType (sig_lst', e', t_lst')
    end
  | LetFunWithType (fun_sig, e, t) -> 
    begin
      let Funsig (f, _, _) = fun_sig in
      let%bind () = add_sem_to_syn_mapping (Var f) t in
      let%bind fun_sig' = 
        fun_sig 
        |> transform_funsig semantic_type_of
      in
      let%bind e' = semantic_type_of e in
      let%bind t' = semantic_type_of t in
      return @@ LetFunWithType (fun_sig', e', t')
    end
  | Plus (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Plus (e1', e2')
  | Minus (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Minus (e1', e2')
  | Times (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Times (e1', e2')
  | Divide (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Divide (e1', e2')
  | Modulus (e1, e2) ->
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Modulus (e1', e2')
  | Equal (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Equal (e1', e2')
  | Neq (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Neq (e1', e2')
  | LessThan (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ LessThan (e1', e2')
  | Leq (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Leq (e1', e2')
  | GreaterThan (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ GreaterThan (e1', e2')
  | Geq (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Geq (e1', e2')
  | And (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ And (e1', e2')
  | Or (e1, e2) ->
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ Or (e1', e2')
  | Not e -> 
    let%bind e' = semantic_type_of e in
    return @@ Not e'
  | If (e1, e2, e3) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let%bind e3' = semantic_type_of e3 in
    return @@ If (e1', e2', e3')
  | Record m -> 
    let%bind m' = (ident_map_map_m (fun e -> semantic_type_of e) m) in
    return @@ Record m'
  | RecordProj (e, l) ->
    let%bind e' = semantic_type_of e in  
    return @@ RecordProj (e', l)
  | Match (e, pattern_expr_lst) ->
    let%bind e' = semantic_type_of e in
    let mapper (pat, expr) =
      let%bind expr' = semantic_type_of expr in 
      return @@ (pat, expr') 
    in
    let%bind pattern_expr_lst' = 
      pattern_expr_lst
      |> List.map mapper 
      |> sequence
    in
    return @@ Match (e', pattern_expr_lst')
  | VariantExpr (lbl, e) -> 
    let%bind e' = semantic_type_of e in  
    return @@ VariantExpr (lbl, e')
  | List expr_lst -> 
    let%bind expr_lst' = 
      expr_lst
      |> List.map semantic_type_of
      |> sequence
    in
    return @@ List expr_lst'
  | ListCons (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    return @@ ListCons (e1', e2')
  | Assert e ->
    let%bind e' = semantic_type_of e in 
    return @@ Assert e'
  | Assume e -> 
    let%bind e' = semantic_type_of e in 
    return @@ Assume e'

(* Phase two of the transformation: erasing all type signatures from 
   the code. By the end of this phase, there should no longer be any
   (x : tau) present in the AST.
 *)
(* Note (Earl): Will have to have a separate variable for each "assert false".
   Can't tell the origin of error otherwise.
*)
and typed_non_to_on (e : sem_type_natodefa) : core_natodefa m = 
  match e with
  | Int n -> return @@ Int n
  | Bool b -> return @@ Bool b
  | Var x -> return @@ Var x
  | Input -> return @@ Input
  | Untouched s -> return @@ Untouched s
  (* TODO (Earl): Come back to here to add mappings to dictionary *)
  | TypeError x -> return @@ TypeError x
  | Function (id_lst, e) -> 
    let%bind e' = typed_non_to_on e in
    return @@ Function (id_lst, e')
  | Appl (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Appl (e1', e2') 
  | Let (x, e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Let (x, e1', e2')
  | LetRecFun (sig_lst, e) ->
    begin
      let%bind sig_lst' = 
        sig_lst
        |> List.map (transform_funsig typed_non_to_on)
        |> sequence
      in
      let%bind e' = typed_non_to_on e in
      return @@ LetRecFun (sig_lst', e')
    end
  | LetFun (fun_sig, e) ->
    begin
      let%bind sig' = 
        fun_sig  
        |> (transform_funsig typed_non_to_on) 
      in
      let%bind e' = typed_non_to_on e in
      return @@ LetFun (sig', e')
    end
  | LetWithType (x, e1, e2, type_decl) ->
    begin
      let%bind type_decl' = typed_non_to_on type_decl in
      let%bind e1' = typed_non_to_on e1 in
      let%bind e2' = typed_non_to_on e2 in
      let%bind check_res = fresh_ident "check_res" in
      let%bind () = add_error_to_natodefa_mapping check_res (Var x) in
      let res_cls = If (Var check_res, e2', TypeError check_res) in
      let check_cls = 
        Let (check_res, Appl (RecordProj (type_decl', Label "checker"), Var x), res_cls) in
      return @@ Let (x, e1', check_cls)
    end
  | LetRecFunWithType (sig_lst, e, type_decl_lst) ->
    begin
      let fun_names = List.map (fun (Funsig (id, _, _)) -> id) sig_lst in
      let combined_lst = List.combine fun_names type_decl_lst in
      let folder (f, t) acc = 
        let%bind t' = typed_non_to_on t in
        let%bind check_res = fresh_ident "check_res" in
        let%bind () = add_error_to_natodefa_mapping check_res (Var f) in
        let res_cls = If (Var check_res, acc, TypeError check_res) in
        let check_cls = 
          Let (check_res, Appl (RecordProj (t', Label "checker"), Var f), res_cls) in
        return check_cls
      in
      let%bind test_exprs = 
        let%bind e' = typed_non_to_on e in
        list_fold_right_m folder combined_lst e' 
      in
      let%bind sig_lst' = 
        sig_lst
        |> List.map (transform_funsig typed_non_to_on)
        |> sequence 
      in
      return @@ LetRecFun (sig_lst', test_exprs)
    end
  | LetFunWithType ((Funsig (f, _, _) as fun_sig), e, type_decl) ->
    begin
      let%bind type_decl' = typed_non_to_on type_decl in
      let%bind e' = typed_non_to_on e in 
      let%bind check_res = fresh_ident "check_res" in
      let%bind () = add_error_to_natodefa_mapping check_res (Var f) in
      let res_cls = If (Var check_res, e', TypeError check_res) in
      let check_cls = 
        Let (check_res, Appl (RecordProj (type_decl', Label "checker"), Var f), res_cls) 
      in
      let%bind fun_sig' = (transform_funsig typed_non_to_on) fun_sig in
      return @@ LetFun (fun_sig', check_cls)
    end
  | Plus (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Plus (e1', e2') 
  | Minus (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Minus (e1', e2') 
  | Times (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Times (e1', e2') 
  | Divide (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Divide (e1', e2') 
  | Modulus (e1, e2) ->
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Modulus (e1', e2') 
  | Equal (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Equal (e1', e2') 
  | Neq (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Neq (e1', e2') 
  | LessThan (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ LessThan (e1', e2') 
  | Leq (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Leq (e1', e2') 
  | GreaterThan (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ GreaterThan (e1', e2') 
  | Geq (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Geq (e1', e2') 
  | And (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ And (e1', e2') 
  | Or (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ Or (e1', e2') 
  | Not e ->
    let%bind e' = typed_non_to_on e in
    return @@ Not e'
  | If (e1, e2, e3) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let%bind e3' = typed_non_to_on e3 in
    return @@ If (e1', e2', e3') 
  | Record m -> 
    let%bind m' = ident_map_map_m (fun e -> typed_non_to_on e) m in
    return @@ Record m' 
  | RecordProj (e, l) -> 
    let%bind e' = typed_non_to_on e in
    return @@ RecordProj (e', l)
  | Match (e, pattern_expr_lst) ->
    let%bind e' = typed_non_to_on e in
    let mapper (pat, expr) =
      let%bind expr' = typed_non_to_on expr in
      return @@ (pat, expr') 
    in
    let%bind pattern_expr_lst' = 
      pattern_expr_lst
      |> List.map mapper
      |> sequence 
    in
    return @@ Match (e', pattern_expr_lst')
  | VariantExpr (lbl, e) -> 
    let%bind e' = typed_non_to_on e in
    return @@ VariantExpr (lbl, e')
  | List expr_lst -> 
    let%bind expr_lst' = 
      expr_lst
      |> List.map typed_non_to_on
      |> sequence
    in
    return @@ List expr_lst'
  | ListCons (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    return @@ ListCons (e1', e2') 
  | Assert e -> 
    let%bind e' = typed_non_to_on e in
    return @@ Assert e'
  | Assume e -> 
    let%bind e' = typed_non_to_on e in
    return @@ Assume e'

let transform_natodefa (e : syn_type_natodefa) : (core_natodefa * Ton_to_on_maps.t) = 
  let transformed_expr : (core_natodefa * Ton_to_on_maps.t) m =
    let%bind e' = 
      return e 
      >>= semantic_type_of
      >>= typed_non_to_on
    in
    let%bind ton_on_map = ton_to_on_maps in
    return (e', ton_on_map)
  in
  run (new_translation_context ()) transformed_expr