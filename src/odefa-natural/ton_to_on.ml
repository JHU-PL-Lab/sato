open Batteries;;
open Jhupllib;;

open On_ast;;
(* open Ton_to_on_maps;; *)
open Ton_to_on_monad;;

open TonTranslationMonad;;

let lazy_logger = Logger_utils.make_lazy_logger "Ton_to_on";;

let transform_funsig 
  (f : 'a expr_desc -> 'b expr_desc m) 
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

   Need a new data type: 
   Use an alist
   [('a expr, ident list)]

   At every semantic_type_of_call, we should return an alist representing
   a walk down the tree with a list of ident associated with each node.

   Keep a list of walk down the type tree, with each node having a unique index
   A map from unique index to points of error

*)

let rec semantic_type_of (e_desc : syntactic_only expr_desc) : semantic_only expr_desc m =
  let t = e_desc.body in
  let tag = e_desc.tag in
  match t with
  | TypeVar tvar -> 
    let res = 
      new_expr_desc @@ Appl (new_expr_desc (Var tvar), new_expr_desc (Var tvar))
    in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeInt ->
    let generator =
      Function ([Ident "~null"], new_expr_desc Input)
    in
    let%bind expr_id = fresh_ident "expr" in 
    let%bind fail_id = fresh_ident "fail" in
    let (fail_pat_cls : sem_natodefa_edesc) = new_expr_desc @@ Var fail_id in
    let match_edesc = 
      new_expr_desc @@
      Match (new_expr_desc (Var expr_id), 
            [(IntPat, new_expr_desc @@ Bool true); 
             (AnyPat, fail_pat_cls)])
    in
    let%bind checker =
      let check_cls = 
        Function ([expr_id], match_edesc)
      in
      let fail_cls = 
        Let (fail_id, new_expr_desc @@ Bool false, new_expr_desc @@ check_cls) 
      in
      (* Adding error point to tag mapping *)
      let%bind () = add_error_to_tag_mapping fail_pat_cls tag in
      let%bind () = add_match_to_error_mapping match_edesc.tag fail_pat_cls in
      return @@ fail_cls
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeBool ->
    let generator =
      Function ([Ident "~null"], 
                new_expr_desc @@ 
                  Geq (new_expr_desc Input, new_expr_desc @@ Int 0))
    in
    let%bind expr_id = fresh_ident "expr" in 
    let%bind fail_id = fresh_ident "fail" in
    let (fail_pat_cls : sem_natodefa_edesc) = new_expr_desc @@ Var fail_id in
    let match_edesc = 
      new_expr_desc @@
      Match (new_expr_desc (Var expr_id), 
            [(BoolPat, new_expr_desc @@ Bool true); 
             (AnyPat, fail_pat_cls)])
    in
    let%bind checker =
      let check_cls = 
        Function ([expr_id], match_edesc)
      in
      let fail_cls = 
        Let (fail_id, new_expr_desc @@ Bool false, new_expr_desc @@ check_cls) 
      in
      let%bind () = add_error_to_tag_mapping fail_pat_cls tag in
      let%bind () = add_match_to_error_mapping match_edesc.tag fail_pat_cls in
      return @@ fail_cls
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
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
        return @@ Ident_map.add lbl (new_expr_desc @@ Var lbl_var) acc      
      in
      let%bind res_record = 
        list_fold_left_m 
          folder
          empty_record lbl_to_var 
      in
      let folder' acc (_, lbl_var, cur_t) = 
        (* TODO: Might want to add an old -> new mapping here *)
        let%bind gc_pair = semantic_type_of cur_t in
        let res = new_expr_desc @@
          Let (lbl_var, 
               new_expr_desc @@
               Appl (
                new_expr_desc @@ 
                  RecordProj (gc_pair, Label "generator"), 
                new_expr_desc @@ Int 0), 
               acc) 
        in return res 
      in
      let%bind rec_input = fresh_ident "rec_input" in
      let base_acc = 
        new_expr_desc @@
        Let (rec_input, 
             new_expr_desc @@ Record res_record, 
             new_expr_desc @@ Var rec_input) 
      in
      let%bind gen_expr = list_fold_left_m folder' base_acc lbl_to_var in
      return @@ Function ([Ident "~null"], gen_expr)
    in
    let%bind checker = 
      let all_bindings = List.rev @@ Ident_map.bindings r in
      let all_keys = Enum.map (fun k -> (k, None)) (Ident_map.keys r) in
      let type_dict = Ident_map.of_enum all_keys in
      let%bind expr_id = fresh_ident "expr" in
      let fold_fun expr_a (Ident lbl, t) = 
        let%bind lbl_check_id = fresh_ident "lbl_check" in
        (* TODO: Might want to add an old -> new mapping here *)
        let%bind cur_gc_pair = semantic_type_of t in
        return @@
        (Let (lbl_check_id, 
              new_expr_desc @@
              Appl (
                new_expr_desc @@ 
                RecordProj (cur_gc_pair, Label "checker"), 
                new_expr_desc @@ 
                RecordProj (new_expr_desc @@ Var expr_id, Label lbl)),
              new_expr_desc @@ 
              If (new_expr_desc @@ Var lbl_check_id, 
                  new_expr_desc @@ expr_a, 
                  new_expr_desc @@ Var lbl_check_id)))
      in
      let (Ident first_lbl, first_type) = List.hd all_bindings in
      let%bind lbl_check_fst = fresh_ident "lbl_check" in
      let%bind gc_pair_fst = 
        (* TODO: Might want to add an old -> new mapping here *)
        semantic_type_of first_type
      in
      let init_acc = 
        Let (lbl_check_fst, 
            new_expr_desc @@ 
            Appl (
              new_expr_desc @@ 
              RecordProj (gc_pair_fst, Label "checker"), 
              new_expr_desc @@ 
              RecordProj (new_expr_desc @@ Var expr_id, Label first_lbl)), 
            new_expr_desc @@
            Var lbl_check_fst)
      in
      let%bind fun_body = 
        list_fold_left_m fold_fun init_acc (List.tl all_bindings) 
      in
      let%bind rec_check_id = fresh_ident "rec_check" in
      let%bind rec_fail_id = fresh_ident "rec_fail" in
      let match_body = Match (new_expr_desc @@ Var expr_id, 
                              [(StrictRecPat type_dict, new_expr_desc fun_body); 
                              (AnyPat, new_expr_desc @@ Var rec_fail_id)]) in
      let check_cls = 
        Let (rec_check_id, 
             new_expr_desc @@ match_body, 
             new_expr_desc @@ Var rec_check_id) 
      in
      let fail_cls = 
        Let (rec_fail_id, 
             new_expr_desc @@ Bool false,
             new_expr_desc @@ check_cls) 
      in
      (* TODO: May only need to record [rec_check_id; rec_fail_id] here;
               since rec_check should be an alias of one of its label
               check in cases of failure.
       *)
      return @@ 
        Function ([expr_id], new_expr_desc fail_cls)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeList l ->
    (* TODO: Might need the tag here as well; add mapping*)
    let%bind gc_pair_g = semantic_type_of l in
    let%bind generator = 
      let%bind len_id = fresh_ident "len" in
      let%bind list_id = fresh_ident "list" in
      let%bind maker_id = fresh_ident "list_maker" in
      let%bind elm_id = fresh_ident "elm" in
      let recur_call = 
        Let (elm_id, 
              new_expr_desc @@
              Appl (
                new_expr_desc @@
                RecordProj (gc_pair_g, Label "generator"), 
                new_expr_desc @@
                Int 0), 
              new_expr_desc @@
              ListCons (new_expr_desc @@ Var elm_id, 
                        new_expr_desc @@
                        Appl (
                          new_expr_desc @@ Var maker_id, 
                          new_expr_desc @@ 
                            Minus (new_expr_desc @@ Var len_id, 
                                   new_expr_desc @@ Int 1)))) 
      in
      let list_maker = 
        If (new_expr_desc @@ 
            Equal (new_expr_desc @@ Var len_id, 
                   new_expr_desc @@ Int 0), 
            new_expr_desc @@ List [], 
            new_expr_desc @@ recur_call) 
      in
      let list_maker_fun = 
        Funsig (maker_id, [len_id], new_expr_desc @@ list_maker) 
      in
      let inner_let = 
          Let (list_id, 
            new_expr_desc @@ 
            Appl (new_expr_desc @@ Var maker_id, new_expr_desc @@ Var len_id), 
            new_expr_desc @@
            Var list_id) 
      in
      let list_len = 
        Let (len_id, new_expr_desc Input, new_expr_desc inner_let) 
      in
      let gen_expr = 
        LetRecFun ([list_maker_fun], new_expr_desc list_len) 
      in
      return @@ Function ([Ident "~null"], new_expr_desc gen_expr)
    in
    let%bind test_fun_id = fresh_ident "test_fun" in
    let%bind test_list_id = fresh_ident "test_list" in
    let%bind elm_check_id = fresh_ident "elm_check" in
    let%bind expr_id = fresh_ident "expr" in
    let%bind lst_check_fail = fresh_ident "lst_fail" in
    let%bind elm_check_let = fresh_ident "lst_check" in
    let%bind gc_pair_c = semantic_type_of l in
    let%bind checker = 
    let test_fun = 
      Match (
        new_expr_desc @@
        Var test_list_id, 
        [(EmptyLstPat, new_expr_desc @@ Bool true); 
         (LstDestructPat 
           (Ident "hd", Ident "tl"), 
           new_expr_desc @@
           (Let (elm_check_id, 
              new_expr_desc @@
              Appl (
                new_expr_desc @@
                RecordProj (gc_pair_c, Label "checker"), 
                new_expr_desc @@ Var (Ident "hd")), 
              new_expr_desc @@
              If (new_expr_desc @@ Var elm_check_id, 
                new_expr_desc @@ 
                Appl (new_expr_desc @@ Var test_fun_id, 
                      new_expr_desc @@ Var (Ident "tl")), 
                new_expr_desc @@ Var elm_check_id))))
        ]) in
    let check_fun = 
      Funsig (test_fun_id, [test_list_id], new_expr_desc test_fun) 
    in
    let check_cls = 
      Let (elm_check_let, 
           new_expr_desc @@ 
             Appl (new_expr_desc @@ Var test_fun_id, 
                   new_expr_desc @@ Var expr_id), 
           new_expr_desc @@ Var elm_check_let)
    in
    let fun_body = LetRecFun ([check_fun], new_expr_desc check_cls) in
    let match_body = 
      Match (new_expr_desc @@ Var expr_id, 
             [(EmptyLstPat, new_expr_desc @@ Bool true); 
              (LstDestructPat 
                (Ident "~underscore", Ident "~underscore2"), 
                new_expr_desc @@ fun_body);
              (AnyPat, new_expr_desc @@ Var lst_check_fail)
             ]) 
    in
    let lst_fail = 
      Let (lst_check_fail, 
           new_expr_desc @@ Bool false, 
           new_expr_desc match_body) 
    in
    return @@ Function ([expr_id], new_expr_desc lst_fail)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeArrow (t1, t2) ->
    (* TODO: Mapping *)
    let%bind gc_pair_dom_gen = semantic_type_of t1 in
    let%bind gc_pair_cod_gen = semantic_type_of t2 in
    let%bind generator = 
      let%bind arg_assume = fresh_ident "arg_assume" in
      let inner_expr = 
        If (new_expr_desc @@
          Appl (new_expr_desc @@ 
            RecordProj (gc_pair_dom_gen, Label "checker"), 
              new_expr_desc @@ Var arg_assume), 
          new_expr_desc @@
          Appl (new_expr_desc @@ 
            RecordProj (gc_pair_cod_gen, Label "generator"), 
              new_expr_desc @@ Int 0), 
          new_expr_desc @@ 
            Assert (new_expr_desc @@ Bool false)) in 
      let gen_expr = Function ([arg_assume], new_expr_desc inner_expr) in
      return @@ Function ([Ident "~null"], new_expr_desc gen_expr)
    in
    let%bind expr_id = fresh_ident "expr" in
    let%bind arg_assert = fresh_ident "arg_assert" in
    let%bind codom_check_id = fresh_ident "codom_check" in
    let%bind gc_pair_dom_check = semantic_type_of t1 in
    let%bind gc_pair_cod_check = semantic_type_of t2 in
    let%bind checker = 
      let codom_check = 
        Let (codom_check_id, 
          new_expr_desc @@
          Appl (new_expr_desc @@
            RecordProj (gc_pair_cod_check, Label "checker"), 
          new_expr_desc @@
          Appl (new_expr_desc @@ Var expr_id, new_expr_desc @@ Var arg_assert)), 
          new_expr_desc @@ 
          Var codom_check_id)
      in
      let fun_body =
        Let (arg_assert, 
             new_expr_desc @@ 
             Appl (new_expr_desc @@ 
              RecordProj (gc_pair_dom_check, Label "generator"), 
                new_expr_desc @@ Int 0), 
             new_expr_desc codom_check) in
      return @@ Function ([expr_id], new_expr_desc fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeArrowD ((x1, t1), t2) ->
    (* TODO: Mapping *)
    let%bind gc_pair_dom_g = semantic_type_of t1 in
    let%bind gc_pair_cod_g = semantic_type_of t2 in
    let mk_gc_pair_cod cod arg = 
      Appl (new_expr_desc @@ 
        Function ([x1], cod), new_expr_desc @@ Var arg) 
    in
    let%bind generator = 
      let%bind arg_assume = fresh_ident "arg_assume" in
      let inner_expr = 
        If (new_expr_desc @@
            Appl (new_expr_desc @@
              RecordProj (gc_pair_dom_g, Label "checker"), 
                new_expr_desc @@ Var arg_assume), 
            new_expr_desc @@
            Appl (new_expr_desc @@ 
              RecordProj (new_expr_desc @@ 
                mk_gc_pair_cod gc_pair_cod_g arg_assume, Label "generator"), 
              new_expr_desc @@ Int 0), 
            new_expr_desc @@ Assert (new_expr_desc @@ Bool false)) in 
      let gen_expr = Function ([arg_assume], new_expr_desc inner_expr) in
      return @@ Function ([Ident "~null"], new_expr_desc gen_expr)
    in
    let%bind codom_check_id = fresh_ident "codom_check" in
    let%bind gc_pair_dom_c = semantic_type_of t1 in
    let%bind gc_pair_cod_c = semantic_type_of t2 in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let%bind arg_assert = fresh_ident "arg_assert" in
      let gc_pair_cod' = 
        Appl (new_expr_desc @@
          Function ([x1], new_expr_desc (mk_gc_pair_cod gc_pair_cod_c arg_assert)), 
          new_expr_desc @@ Var arg_assert) 
      in
      let codom_check = 
        Let (codom_check_id, 
          new_expr_desc @@ 
          Appl (new_expr_desc @@ 
            RecordProj (new_expr_desc gc_pair_cod', Label "checker"), 
            new_expr_desc @@ 
            Appl (new_expr_desc @@ Var expr_id, new_expr_desc @@ Var arg_assert)), 
          new_expr_desc @@
          Var codom_check_id)
      in
      let fun_body = 
        Let (arg_assert, 
             new_expr_desc @@
             Appl (new_expr_desc @@
               RecordProj (gc_pair_dom_c, Label "generator"), 
               new_expr_desc @@ Int 0), 
             new_expr_desc codom_check) in
      return @@ Function ([expr_id], new_expr_desc fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeSet (t, p) ->
    let%bind gc_pair = semantic_type_of t in
    let%bind p' = semantic_type_of p in
    let%bind generator = 
      let%bind candidate = fresh_ident "candidate" in
      let pred_check = 
        If (new_expr_desc @@ 
          Appl (p', new_expr_desc @@ Var candidate), 
          new_expr_desc @@ Var candidate, 
          new_expr_desc @@ Assume (new_expr_desc @@ Bool false)) 
      in
      let gen_expr = Let (candidate, 
                          new_expr_desc @@ 
                          Appl (new_expr_desc @@ 
                            RecordProj 
                              (gc_pair, 
                               Label "generator"), 
                            new_expr_desc @@ Int 0), 
                          new_expr_desc @@ pred_check) in
      return @@ Function ([Ident "~null"], new_expr_desc gen_expr)
    in
    let%bind pred_check_id = fresh_ident "pred_check" in
    let%bind t_check_id = fresh_ident "t_check" in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      (* TODO: Need a false signifier here to link the predicate check failure
         to its corresponding program point. *)
      let check_pred = 
        Let (pred_check_id, 
             new_expr_desc @@ 
             Appl (p', new_expr_desc @@ Var expr_id),
             new_expr_desc @@ Var pred_check_id)
      in
      let check_type_body = 
        If (new_expr_desc @@ 
            Appl (new_expr_desc @@
                  RecordProj (gc_pair, Label "checker"), 
                  new_expr_desc @@ Var expr_id),
            new_expr_desc @@ check_pred,
            new_expr_desc @@ 
            Appl (new_expr_desc @@ 
                  RecordProj (gc_pair, Label "checker"), 
                  new_expr_desc @@ Var expr_id))
      in
      let check_type = 
        Let (t_check_id, 
             new_expr_desc @@ Bool false, 
             new_expr_desc check_type_body)
      in
      return @@ Function ([expr_id], new_expr_desc check_type)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    (* TODO: To reduce complexity, remove pred-checking for now *)
    (* let%bind gc_pair_pred = semantic_type_of (TypeArrow (t, TypeBool)) in
    let%bind check_pred_id = fresh_ident "check_pred" in
    let pred_cond = If (Var check_pred_id, Record rec_map, Assert (Bool false)) in
    let check_pred = Let (check_pred_id,
                          Appl (RecordProj (gc_pair_pred, Label "checker"), p'),
                          pred_cond)
    in *)
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeUnion (t1, t2) ->
    let%bind gc_pair1 = semantic_type_of t1 in
    let%bind gc_pair2 = semantic_type_of t2 in
    let%bind generator = 
      let%bind select_int = fresh_ident "select_int" in
      let branch = If (new_expr_desc @@ 
                       Geq (new_expr_desc @@ 
                            Var select_int, 
                            new_expr_desc @@ Int 0), 
                       new_expr_desc @@ 
                       Appl (new_expr_desc @@ 
                         RecordProj (gc_pair1, Label "generator"), 
                         new_expr_desc @@ Int 0), 
                       new_expr_desc @@ 
                       Appl (new_expr_desc @@ 
                             RecordProj 
                              (gc_pair2, Label "generator"), 
                              new_expr_desc @@ Int 0)) in
      let gen_expr = 
        Let (select_int, new_expr_desc Input, new_expr_desc branch) 
      in
      return @@ Function ([Ident "~null"], new_expr_desc gen_expr)
    in
    let%bind fail_id = fresh_ident "fail" in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let%bind select_int = fresh_ident "select_int" in
      let checker1_inner = 
        If (new_expr_desc @@ 
            Appl (new_expr_desc @@ 
                  RecordProj (gc_pair2, Label "checker"), 
                  new_expr_desc @@ Var expr_id),
            new_expr_desc @@ Bool true,
            new_expr_desc @@ Var fail_id)
      in
      let checker1 = 
        If (new_expr_desc @@ 
            Appl (new_expr_desc @@ 
                  RecordProj (gc_pair1, Label "checker"), 
                  new_expr_desc @@ Var expr_id), 
            new_expr_desc @@ Bool true, 
            new_expr_desc @@ checker1_inner) 
      in
      let checker2_inner = 
        If (new_expr_desc @@ 
            Appl (new_expr_desc @@ 
              RecordProj (gc_pair1, Label "checker"), 
              new_expr_desc @@ Var expr_id),
            new_expr_desc @@ Bool true,
            new_expr_desc @@ Var fail_id)
      in
      let checker2 = 
        If (new_expr_desc @@ 
            Appl (new_expr_desc @@ 
                  RecordProj (gc_pair2, Label "checker"), 
                  new_expr_desc @@ Var expr_id), 
            new_expr_desc @@ Bool true, 
            new_expr_desc @@ checker2_inner) 
      in
      let branch = 
        If (new_expr_desc @@
            Geq (new_expr_desc @@ Var select_int, 
                 new_expr_desc @@ Int 0), 
            new_expr_desc @@ checker1, 
            new_expr_desc @@ checker2) in
      let fail_def = 
        Let (fail_id, new_expr_desc @@ Bool false, new_expr_desc branch) in
      let fun_body = 
        Let (select_int, new_expr_desc Input, new_expr_desc fail_def) 
      in
      return @@ Function ([expr_id], new_expr_desc fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeIntersect (t1, t2) -> 
    let%bind gc_pair1 = semantic_type_of t1 in
    let%bind gc_pair2 = semantic_type_of t2 in
    let%bind generator = 
      let%bind candidate_var = fresh_ident "candidate" in
      let validate = 
        If (new_expr_desc @@ 
            Appl (new_expr_desc @@ 
              RecordProj (gc_pair2, Label "checker"), 
              new_expr_desc @@ (Var candidate_var)), 
            new_expr_desc @@ Var candidate_var, 
            new_expr_desc @@ Assume (new_expr_desc @@ Bool false)) 
      in
      let gen_expr = 
        Let (candidate_var, 
             new_expr_desc @@ 
             Appl (new_expr_desc @@ 
               RecordProj (gc_pair1, Label "generator"), 
               new_expr_desc @@ Int 0), 
             new_expr_desc @@ validate) 
      in
      return @@ Function ([Ident "~null"], new_expr_desc gen_expr)
    in
    let%bind fail_id = fresh_ident "fail" in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let fun_body_inner = 
        If (new_expr_desc @@ Var fail_id,
            new_expr_desc @@ 
            Appl (new_expr_desc @@ 
              RecordProj (gc_pair2, Label "checker"), 
              new_expr_desc @@ Var expr_id), 
            new_expr_desc @@ Var fail_id) 
      in
      let fun_body = 
        Let (fail_id, 
             new_expr_desc @@ 
             Appl (new_expr_desc @@ 
               RecordProj (gc_pair1, Label "checker"), 
               new_expr_desc @@ Var expr_id), 
             new_expr_desc @@ fun_body_inner)
      in
      return @@ Function ([expr_id], new_expr_desc fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeRecurse (t_var, t') ->
    let%bind gc_pair = semantic_type_of t' in
    let%bind primer_id = fresh_ident "primer" in
    let res = 
      new_expr_desc @@ Let (primer_id, 
                    new_expr_desc @@ Function ([t_var], gc_pair), 
                    new_expr_desc @@ 
                    Appl (new_expr_desc @@ Var primer_id, 
                      new_expr_desc @@ Var primer_id))
    in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeUntouched t' ->
    let generator = 
      Function ([Ident "~null"], new_expr_desc @@ Untouched t')
    in
    let%bind fail_id = fresh_ident "fail" in
    let%bind checker = 
      let%bind expr_id = fresh_ident "expr" in
      let check_body = 
        Function ([expr_id], 
          new_expr_desc @@ 
          Match (new_expr_desc @@ Var expr_id, 
                [(UntouchedPat t', new_expr_desc @@ Bool true); 
                (AnyPat, new_expr_desc @@ Var fail_id)]))
      in
      return @@ 
        Let (fail_id, new_expr_desc @@ Bool false, new_expr_desc check_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") (new_expr_desc generator)
      |> Ident_map.add (Ident "checker") (new_expr_desc checker)
    in
    let res = new_expr_desc @@ Record rec_map in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  (* These are constant functions that only modify the types *)
  | Int n -> 
    let res = new_expr_desc @@ Int n in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Bool b -> 
    let res = new_expr_desc @@ Bool b in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Var x -> 
    let res = new_expr_desc @@ Var x in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Input -> 
    let res = new_expr_desc @@ Input in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Untouched s ->
    let res = new_expr_desc @@ Untouched s in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | TypeError x -> 
    let res = new_expr_desc @@ TypeError x in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  (* All other expressions are homomorphic *)
  | Function (id_lst, f_expr) -> 
    let%bind f_expr' = semantic_type_of f_expr in
    let res = new_expr_desc @@ Function (id_lst, f_expr') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Appl (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Appl (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Let (x, e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Let (x, e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | LetRecFun (sig_lst, e) ->
    begin
      let%bind sig_lst' = 
        sig_lst 
        |> List.map (transform_funsig semantic_type_of) 
        |> sequence 
      in 
      let%bind e' = semantic_type_of e in
      let res = new_expr_desc @@ LetRecFun (sig_lst', e') in
      let%bind () = add_sem_to_syn_mapping res e_desc in
      return res
    end
  | LetFun (fun_sig, e) ->
    begin
      let%bind fun_sig' = 
        fun_sig
        |> transform_funsig semantic_type_of
      in
      let%bind e' = semantic_type_of e in
      let res = new_expr_desc @@ LetFun (fun_sig', e') in
      let%bind () = add_sem_to_syn_mapping res e_desc in
      return res
    end
  | LetWithType (x, e1, e2, t) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let%bind t' = semantic_type_of t in
    let res = new_expr_desc @@ LetWithType (x, e1', e2', t') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    (* let%bind () = add_natodefa_expr_error_structure_mapping (Var x) ? in *)
    return res
  | LetRecFunWithType (sig_lst, e, t_lst) ->
    begin
      (* let sig_t_lst = List.combine sig_lst t_lst in *)
      (* let%bind () = sig_t_lst
        |> list_fold_left_m 
           (fun () (Funsig (f, _, _), f_t) -> 
              add_sem_to_syn_mapping (new_expr_desc @@ Var f) f_t)
           ()
      in *)
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
      let res = 
        new_expr_desc @@ 
          LetRecFunWithType (sig_lst', e', t_lst')
      in
      let%bind () = add_sem_to_syn_mapping res e_desc in
      return res
    end
  | LetFunWithType (fun_sig, e, t) -> 
    begin
      let%bind fun_sig' = 
        fun_sig 
        |> transform_funsig semantic_type_of
      in
      let%bind e' = semantic_type_of e in
      let%bind t' = semantic_type_of t in
      let res = 
        new_expr_desc @@ LetFunWithType (fun_sig', e', t')
      in
      let%bind () = add_sem_to_syn_mapping res e_desc in
      return res
    end
  | Plus (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Plus (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Minus (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Minus (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Times (e1, e2) ->
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Times (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Divide (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Divide (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Modulus (e1, e2) ->
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Modulus (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Equal (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Equal (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Neq (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Neq (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | LessThan (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ LessThan (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Leq (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Leq (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | GreaterThan (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ GreaterThan (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Geq (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Geq (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | And (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ And (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Or (e1, e2) ->
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ Or (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Not e -> 
    let%bind e' = semantic_type_of e in
    let res = new_expr_desc @@ Not e' in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | If (e1, e2, e3) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let%bind e3' = semantic_type_of e3 in
    let res = new_expr_desc @@ If (e1', e2', e3') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Record m -> 
    let%bind m' = ident_map_map_m semantic_type_of m in
    let res = new_expr_desc @@ Record m' in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | RecordProj (e, l) ->
    let%bind e' = semantic_type_of e in
    let res = new_expr_desc @@ RecordProj (e', l) in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
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
    let res = new_expr_desc @@ Match (e', pattern_expr_lst') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | VariantExpr (lbl, e) -> 
    let%bind e' = semantic_type_of e in
    let res = new_expr_desc @@ VariantExpr (lbl, e') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | List expr_lst -> 
    let%bind expr_lst' = 
      expr_lst
      |> List.map semantic_type_of
      |> sequence
    in
    let res = new_expr_desc @@ List expr_lst' in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | ListCons (e1, e2) -> 
    let%bind e1' = semantic_type_of e1 in
    let%bind e2' = semantic_type_of e2 in
    let res = new_expr_desc @@ ListCons (e1', e2') in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Assert e ->
    let%bind e' = semantic_type_of e in
    let res = new_expr_desc @@ Assert e' in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res
  | Assume e -> 
    let%bind e' = semantic_type_of e in
    let res = new_expr_desc @@ Assume e' in
    let%bind () = add_sem_to_syn_mapping res e_desc in
    return res

(* Phase two of the transformation: erasing all type signatures from 
   the code. By the end of this phase, there should no longer be any
   (x : tau) present in the AST.
 *)
(* Note (Earl): Will have to have a separate variable for each "assert false".
   Can't tell the origin of error otherwise.
*)
and typed_non_to_on (e_desc : semantic_only expr_desc) : core_only expr_desc m = 
  let e = e_desc.body in
  let _tag = e_desc.tag in
  match e with
  | Int n -> 
    let res = new_expr_desc @@ Int n in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Bool b -> 
    let res = new_expr_desc @@ Bool b in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Var x -> 
    let res = new_expr_desc @@ Var x in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Input -> 
    let res = new_expr_desc @@ Input in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Untouched s -> 
    let res = new_expr_desc @@ Untouched s in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  (* TODO (Earl): Come back to here to add mappings to dictionary *)
  | TypeError x -> 
    let res = new_expr_desc @@ TypeError x in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Function (id_lst, e) -> 
    let%bind e' = typed_non_to_on e in
    let res = new_expr_desc @@ Function (id_lst, e') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Appl (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Appl (e1', e2') in 
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Let (x, e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Let (x, e1', e2') in 
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | LetRecFun (sig_lst, e) ->
    begin
      let%bind sig_lst' = 
        sig_lst
        |> List.map (transform_funsig typed_non_to_on)
        |> sequence
      in
      let%bind e' = typed_non_to_on e in
      let res = new_expr_desc @@ LetRecFun (sig_lst', e') in
      let%bind () = add_core_to_sem_mapping res e_desc in
      return res
    end
  | LetFun (fun_sig, e) ->
    begin
      let%bind sig' = 
        fun_sig  
        |> (transform_funsig typed_non_to_on) 
      in
      let%bind e' = typed_non_to_on e in
      let res = new_expr_desc @@ LetFun (sig', e') in
      let%bind () = add_core_to_sem_mapping res e_desc in
      return res
    end
  | LetWithType (x, e1, e2, type_decl) ->
    begin
      let%bind type_decl' = typed_non_to_on type_decl in
      let%bind e1' = typed_non_to_on e1 in
      let%bind e2' = typed_non_to_on e2 in
      let%bind check_res = fresh_ident "check_res" in
      let%bind () = add_error_to_natodefa_mapping check_res e_desc in
      let res_cls = 
        If (new_expr_desc @@ Var check_res, 
            e2', 
            new_expr_desc @@ TypeError check_res) 
      in
      let check_cls = 
        Let (check_res, 
             new_expr_desc @@ 
             Appl (new_expr_desc @@ 
               RecordProj (type_decl', Label "checker"), 
               new_expr_desc @@ Var x), 
             new_expr_desc @@ res_cls) 
      in
      let res =
        new_expr_desc @@ Let (x, e1', new_expr_desc check_cls)
      in
      let%bind () = add_core_to_sem_mapping res e_desc in
      return res
    end
  | LetRecFunWithType (sig_lst, e, type_decl_lst) ->
    begin
      let fun_names = List.map (fun (Funsig (id, _, _)) -> id) sig_lst in
      let combined_lst = List.combine fun_names type_decl_lst in
      let folder (f, t) acc = 
        let%bind t' = typed_non_to_on t in
        let%bind check_res = fresh_ident "check_res" in
        let%bind () = add_error_to_natodefa_mapping check_res e_desc in
        let res_cls = 
          If (new_expr_desc @@ Var check_res, 
              acc, 
              new_expr_desc@@ TypeError check_res) 
        in
        let check_cls = 
          Let (check_res, 
               new_expr_desc @@ 
               Appl (new_expr_desc @@ 
                 RecordProj (t', Label "checker"), 
                 new_expr_desc @@ Var f), 
               new_expr_desc res_cls) 
        in
        return @@ new_expr_desc @@ check_cls
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
      let res =
        new_expr_desc @@ LetRecFun (sig_lst', test_exprs)
      in
      let%bind () = add_core_to_sem_mapping res e_desc in
      return res
    end
  | LetFunWithType ((Funsig (f, _, _) as fun_sig), e, type_decl) ->
    begin
      let%bind type_decl' = typed_non_to_on type_decl in
      let%bind e' = typed_non_to_on e in 
      let%bind check_res = fresh_ident "check_res" in
      let%bind () = add_error_to_natodefa_mapping check_res e_desc in
      let res_cls = 
        If (new_expr_desc @@ Var check_res, 
            e', 
            new_expr_desc @@ TypeError check_res) 
      in
      let check_cls = 
        Let (check_res, 
             new_expr_desc @@ 
             Appl (new_expr_desc @@ 
               RecordProj (type_decl', Label "checker"), 
               new_expr_desc @@ Var f), 
             new_expr_desc res_cls) 
      in
      let%bind fun_sig' = (transform_funsig typed_non_to_on) fun_sig in
      let res =  
        new_expr_desc @@ LetFun (fun_sig', new_expr_desc check_cls)
      in
      let%bind () = add_core_to_sem_mapping res e_desc in
      return res
    end
  | Plus (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Plus (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res 
  | Minus (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Minus (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res 
  | Times (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Times (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res 
  | Divide (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Divide (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res 
  | Modulus (e1, e2) ->
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Modulus (e1', e2') in 
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Equal (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Equal (e1', e2') in 
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Neq (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Neq (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | LessThan (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ LessThan (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res  
  | Leq (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Leq (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res 
  | GreaterThan (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ GreaterThan (e1', e2') in 
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Geq (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Geq (e1', e2') in 
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | And (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ And (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res 
  | Or (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ Or (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Not e ->
    let%bind e' = typed_non_to_on e in
    let res = new_expr_desc @@ Not e' in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | If (e1, e2, e3) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let%bind e3' = typed_non_to_on e3 in
    let res = new_expr_desc @@ If (e1', e2', e3') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res 
  | Record m -> 
    let%bind m' = ident_map_map_m (fun e -> typed_non_to_on e) m in
    let res = new_expr_desc @@ Record m' in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | RecordProj (e, l) -> 
    let%bind e' = typed_non_to_on e in
    let res = new_expr_desc @@ RecordProj (e', l) in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
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
    let res =
      new_expr_desc @@ 
      Match (e', pattern_expr_lst')
    in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | VariantExpr (lbl, e) -> 
    let%bind e' = typed_non_to_on e in
    let res = new_expr_desc @@ VariantExpr (lbl, e') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | List expr_lst -> 
    let%bind expr_lst' = 
      expr_lst
      |> List.map typed_non_to_on
      |> sequence
    in
    let res = new_expr_desc @@ List expr_lst' in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | ListCons (e1, e2) -> 
    let%bind e1' = typed_non_to_on e1 in
    let%bind e2' = typed_non_to_on e2 in
    let res = new_expr_desc @@ ListCons (e1', e2') in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res 
  | Assert e -> 
    let%bind e' = typed_non_to_on e in
    let res = new_expr_desc @@ Assert e' in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res
  | Assume e -> 
    let%bind e' = typed_non_to_on e in
    let res = new_expr_desc @@ Assume e' in
    let%bind () = add_core_to_sem_mapping res e_desc in
    return res

let debug_transform_ton
  (trans_name : string)
  (transform : 'a expr_desc -> 'b expr_desc m)
  (e : 'a expr_desc)
  : 'b expr_desc m =
  let%bind e' = transform e in
  lazy_logger `debug (fun () ->
    Printf.sprintf "Result of %s:\n%s" trans_name (Pp_utils.pp_to_string On_ast_pp.pp_expr e'.body));
  return e'
;;

let transform_natodefa (e : syn_type_natodefa) : (core_natodefa_edesc * Ton_to_on_maps.t) = 
  let transformed_expr : (core_natodefa_edesc * Ton_to_on_maps.t) m =
    let%bind e' = 
      return (new_expr_desc e) 
      >>= debug_transform_ton "initial" (fun e -> return e)
      >>= debug_transform_ton "typed natodefa phase one" semantic_type_of
      >>= debug_transform_ton "typed natodefa phase two" typed_non_to_on
    in
    let%bind ton_on_map = ton_to_on_maps in
    return (e', ton_on_map)
  in
  run (new_translation_context ()) transformed_expr