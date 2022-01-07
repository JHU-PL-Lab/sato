open Batteries;;

open On_ast;;

let counter = ref 0;;


(* TODO: We need two versions of transform_funsig because the types are 
   different. I wonder if there's a way to simplify it? *)
let transform_funsig 
  (f : 'a typed_expr -> 'b typed_expr) 
  (Funsig (fun_name, params, e) : 'a funsig) 
  = 
  Funsig (fun_name, params, f e)

(* Phase one of transformation: turning all syntactic types into its
   semantic correspondence.
   i.e. int -> { generator = fun _ -> input, 
               , checker = fun e -> isInt e
               }
*)
let rec semantic_type_of (t : syn_type_natodefa) : sem_type_natodefa =
  match t with
  | TypeVar tvar -> Appl (Var tvar, Var tvar)
  | TypeInt ->
    let generator =
      let int_input = Ident ("~int_input" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let gen_expr = Let (int_input, Input, Var int_input) in
      Function ([Ident "~null"], gen_expr)
    in
    let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
    let checker = 
      Function ([Ident exp_str], Match (Var (Ident exp_str), [(IntPat, Bool true); (AnyPat, Bool false)]))
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeBool ->
    let generator =
      let raw_input = Ident ("~raw_input" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let bool_input = Ident ("~bool_input" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let get_raw = Let (raw_input, Input, Var raw_input) in
      let gen_expr = Let (bool_input, Geq (get_raw, Int 0), Var bool_input) in
      Function ([Ident "~null"], gen_expr)
    in
    let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
    let checker = 
      Function ([Ident exp_str], Match (Var (Ident exp_str), [(BoolPat, Bool true); (AnyPat, Bool false)]))
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeRecord r ->
    let generator = 
      let all_bindings = Ident_map.bindings r in
      let empty_record = Ident_map.empty in
      let lbl_to_var = List.map 
        (fun ((Ident lbl_str) as lbl, lbl_type) -> 
          let lbl_var = Ident ("~" ^ lbl_str ^ string_of_int (counter := !counter + 1 ; !counter)) in
          (lbl, lbl_var, lbl_type)) all_bindings 
      in
      let res_record = List.fold_left 
          (fun acc (lbl, lbl_var, _) -> Ident_map.add lbl (Var lbl_var) acc) 
          empty_record lbl_to_var 
      in
      let fold_fun acc (_, lbl_var, cur_t) = 
        let gc_pair = semantic_type_of cur_t in
        Let (lbl_var, 
             Appl (RecordProj (gc_pair, Label "generator"), Int 0), 
             acc) 
      in
      let rec_input = Ident ("~rec_input" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let base_acc = Let (rec_input, Record res_record, Var rec_input) in
      let gen_expr = List.fold_left fold_fun base_acc lbl_to_var in
      Function ([Ident "~null"], gen_expr)
    in
    let checker = 
      let all_bindings = Ident_map.bindings r in
      let all_keys = Enum.map (fun k -> (k, None)) (Ident_map.keys r) in
      let type_dict = Ident_map.of_enum all_keys in
      let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
      let fold_fun acc (Ident lbl, t) = 
        let gc_pair = semantic_type_of t in
        Let (dummy_var, 
              Appl (RecordProj (gc_pair, Label "checker"), RecordProj (Var (Ident exp_str), Label lbl)), 
              And (Var dummy_var, acc))
      in
      let (Ident first_lbl, first_type) = List.hd all_bindings in
      let gc_pair = semantic_type_of first_type in
      let init_acc = Appl (RecordProj (gc_pair, Label "checker"), RecordProj (Var (Ident exp_str), Label first_lbl)) in
      let fun_body = List.fold_left fold_fun init_acc (List.tl all_bindings) in
      let match_body = Match (Var (Ident exp_str), 
                              [(StrictRecPat type_dict, fun_body); 
                              (AnyPat, Bool false)]) in
      Function ([Ident exp_str], match_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeList l ->
    let gc_pair = semantic_type_of l in
    let generator = 
      let len_var = Ident ("~len" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let list_var = Ident ("~list" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let maker_var = Ident ("~list_maker" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let elm_var = Ident ("~elm" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let recur_call = 
        Let (elm_var, 
             Appl (RecordProj (gc_pair, Label "generator"), Int 0), 
             ListCons (Var elm_var, Appl (Var maker_var, Minus (Var len_var, Int 1)))) 
      in
      let list_maker = If (Equal (Var len_var, Int 0), List [], recur_call) in
      let list_maker_fun = Funsig (maker_var, [len_var], list_maker) in
      let inner_let = Let (list_var, Appl (Var maker_var, Var len_var), Var list_var) in
      let list_len = Let (len_var, Input, inner_let) in
      let gen_expr = LetRecFun ([list_maker_fun], list_len) in
      Function ([Ident "~null"], gen_expr)
    in
    let checker = 
      let test_fun_name = Ident ("~testFun" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let test_list = Ident ("~testList" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let test_fun = 
        Match (Var test_list, 
               [(EmptyLstPat, Bool true); 
                (LstDestructPat 
                  (Ident "hd", Ident "tl"), 
                  (Let (dummy_var, 
                        Appl (RecordProj (gc_pair, Label "checker"), Var (Ident "hd")), 
                        And (Var dummy_var, Appl (Var test_fun_name, Var (Ident "tl"))))))
               ]) in
      let check_fun = Funsig (test_fun_name, [test_list], test_fun) in
      let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
      let fun_body = LetRecFun ([check_fun], Appl (Var test_fun_name, Var (Ident exp_str))) in
      let match_body = Match (Var (Ident exp_str), 
                              [(EmptyLstPat, Bool true); 
                               (LstDestructPat (Ident "~dummy1", Ident "~dummy2"), fun_body);
                               (AnyPat, Bool false)
                              ]) 
      in
      Function ([Ident exp_str], match_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeArrow (t1, t2) ->
    let gc_pair1 = semantic_type_of t1 in
    let gc_pair2 = semantic_type_of t2 in
    let generator = 
      let arg_assume = Ident ("~arg_assume" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let inner_expr = If (Appl (RecordProj (gc_pair1, Label "checker"), Var arg_assume), 
                           Appl (RecordProj (gc_pair2, Label "generator"), Int 0), 
                           Assert (Bool false)) in 
      let gen_expr = Function ([arg_assume], inner_expr) in
      Function ([Ident "~null"], gen_expr)
    in
    let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
    let checker = 
      let arg_assert = Ident ("~arg_assert" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let fun_body = Let (arg_assert, 
                          Appl (RecordProj (gc_pair1, Label "generator"), Int 0), 
                          Appl (RecordProj (gc_pair2, Label "checker"), Appl (Var (Ident exp_str), Var arg_assert))) in
      Function ([Ident exp_str], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeArrowD ((x1, t1), t2) ->
    let gc_pair1 = semantic_type_of t1 in
    let generator = 
      let arg_assume = Ident ("~arg_assume" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let gc_pair2 = Appl (Function ([x1], semantic_type_of t2), (Var arg_assume)) in
      let inner_expr = If (Appl (RecordProj (gc_pair1, Label "checker"), Var arg_assume), 
                            Appl (RecordProj (gc_pair2, Label "generator"), Int 0), 
                            Assert (Bool false)) in 
      let gen_expr = Function ([arg_assume], inner_expr) in
      Function ([Ident "~null"], gen_expr)
    in
    let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
    let checker = 
      let arg_assert = Ident ("~arg_assert" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let gc_pair2 = Appl (Function ([x1], semantic_type_of t2), (Var arg_assert)) in
      let fun_body = Let (arg_assert, 
                          Appl (RecordProj (gc_pair1, Label "generator"), Int 0), 
                          Appl (RecordProj (gc_pair2, Label "checker"), Appl (Var (Ident exp_str), Var arg_assert))) in
      Function ([Ident exp_str], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeSet (t, p) ->
    let gc_pair = semantic_type_of t in
    let p' = semantic_type_of p in
    let generator = 
      let candidate = Ident ("~candidate" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let pred_check = If (Appl (p', Var candidate), Var candidate, Assume (Bool false)) in
      let gen_expr = Let (candidate, 
                          Appl (RecordProj (gc_pair, Label "generator"), Int 0), 
                          pred_check) in
      Function ([Ident "~null"], gen_expr)
    in
    let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
    let checker = 
      let fun_body = If (Appl (RecordProj (gc_pair, Label "checker"), Var (Ident exp_str)), 
                         Appl (p', Var (Ident exp_str)), Bool false) in
      Function ([Ident exp_str], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    let gc_pair_pred = semantic_type_of (TypeArrow (t, TypeBool)) in
    let check_pred_id = Ident ("~check_pred" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let pred_cond = If (Var check_pred_id, Record rec_map, Assert (Bool false)) in
    let check_pred = Let (check_pred_id,
                          Appl (RecordProj (gc_pair_pred, Label "checker"), p'),
                          pred_cond)
    in
    check_pred
  | TypeUnion (t1, t2) ->
    let gc_pair1 = semantic_type_of t1 in
    let gc_pair2 = semantic_type_of t2 in
    let generator = 
      let select_int = Ident ("~select_int" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let branch = If (Geq (Var select_int, Int 0), 
                        Appl (RecordProj (gc_pair1, Label "generator"), Int 0), 
                        Appl (RecordProj (gc_pair2, Label "generator"), Int 0)) in
      let gen_expr = Let (select_int, Input, branch) in
      Function ([Ident "~null"], gen_expr)
    in
    let checker = 
      let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
      let select_int = Ident ("~select_int" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let checker1 = If (Appl (RecordProj (gc_pair1, Label "checker"), Var (Ident exp_str)), Bool true, Appl (RecordProj (gc_pair2, Label "checker"), Var (Ident exp_str))) in
      let checker2 = If (Appl (RecordProj (gc_pair2, Label "checker"), Var (Ident exp_str)), Bool true, Appl (RecordProj (gc_pair1, Label "checker"), Var (Ident exp_str))) in
      let branch = If (Geq (Var select_int, Int 0), checker1, checker2) in
      let fun_body = Let (select_int, Input, branch) in
      Function ([Ident exp_str], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeIntersect (t1, t2) -> 
    let gc_pair1 = semantic_type_of t1 in
    let gc_pair2 = semantic_type_of t2 in
    let generator = 
      let candidate_var = Ident ("~candidate" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let validate = If (Appl (RecordProj (gc_pair2, Label "checker"), (Var candidate_var)), 
                         Var candidate_var, 
                         Assume (Bool false)) in
      let gen_expr = Let (candidate_var, 
                          Appl (RecordProj (gc_pair1, Label "generator"), Int 0), 
                          validate) in
      Function ([Ident "~null"], gen_expr)
    in
    let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
    let checker = 
      let fun_body = If (Appl (RecordProj (gc_pair1, Label "checker"), Var (Ident exp_str)), 
                         Appl (RecordProj (gc_pair2, Label "checker"), Var (Ident exp_str)), 
                         Bool false) in
      Function ([Ident exp_str], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeRecurse (t_var, t') ->
    let gc_pair = semantic_type_of t' in
    let self_var = Ident "primer" in
    Let (self_var, Function ([t_var], gc_pair), Appl (Var self_var, Var self_var))
  | TypeUntouched t ->
    let generator = 
      Function ([Ident "~null"], Untouched t)
    in
    let exp_str = "exp" ^ string_of_int (counter := !counter + 1 ; !counter) in
    let checker = 
      Function ([Ident exp_str], Match (Var (Ident exp_str), [(UntouchedPat t, Bool true); (AnyPat, Bool false)]))
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  (* These are constant functions that only modify the types *)
  | Int n -> Int n
  | Bool b -> Bool b
  | Var x -> Var x
  | Input -> Input
  | Untouched s -> Untouched s
  (* All other expressions are homomorphic *)
  | Function (id_lst, f_expr) -> Function (id_lst, semantic_type_of f_expr)
  | Appl (e1, e2) -> Appl (semantic_type_of e1, semantic_type_of e2) 
  | Let (x, e1, e2) -> Let (x, semantic_type_of e1, semantic_type_of e2)
  | LetRecFun (sig_lst, e) ->
    begin
      let sig_lst' = List.map (transform_funsig semantic_type_of) sig_lst in 
      LetRecFun (sig_lst', semantic_type_of e)
    end
  | LetFun (fun_sig, e) ->
    begin
      let fun_sig' = (transform_funsig semantic_type_of) fun_sig in
      LetFun (fun_sig', semantic_type_of e)
    end
  | LetWithType (x, e1, e2, t) -> 
    LetWithType (x, semantic_type_of e1, semantic_type_of e2, semantic_type_of t)
  | LetRecFunWithType (sig_lst, e, t_lst) ->
    begin
      let sig_lst' = List.map (transform_funsig semantic_type_of) sig_lst in
      let t_lst' = List.map semantic_type_of t_lst in 
      LetRecFunWithType (sig_lst', semantic_type_of e, t_lst')
    end
  | LetFunWithType (fun_sig, e, t) -> 
    begin
      let fun_sig' = (transform_funsig semantic_type_of) fun_sig in
      LetFunWithType (fun_sig', semantic_type_of e, semantic_type_of t)
    end
  | Plus (e1, e2) -> Plus (semantic_type_of e1, semantic_type_of e2)
  | Minus (e1, e2) -> Minus (semantic_type_of e1, semantic_type_of e2)
  | Times (e1, e2) -> Times (semantic_type_of e1, semantic_type_of e2)
  | Divide (e1, e2) -> Divide (semantic_type_of e1, semantic_type_of e2)
  | Modulus (e1, e2) -> Modulus (semantic_type_of e1, semantic_type_of e2)
  | Equal (e1, e2) -> Equal (semantic_type_of e1, semantic_type_of e2)
  | Neq (e1, e2) -> Neq (semantic_type_of e1, semantic_type_of e2)
  | LessThan (e1, e2) -> LessThan (semantic_type_of e1, semantic_type_of e2)
  | Leq (e1, e2) -> Leq (semantic_type_of e1, semantic_type_of e2)
  | GreaterThan (e1, e2) -> GreaterThan (semantic_type_of e1, semantic_type_of e2)
  | Geq (e1, e2) -> Geq (semantic_type_of e1, semantic_type_of e2)
  | And (e1, e2) -> And (semantic_type_of e1, semantic_type_of e2)
  | Or (e1, e2) -> Or (semantic_type_of e1, semantic_type_of e2)
  | Not e -> Not (semantic_type_of e)
  | If (e1, e2, e3) -> 
    If (semantic_type_of e1, semantic_type_of e2, semantic_type_of e3)  
  | Record m -> Record (Ident_map.map (fun e -> semantic_type_of e) m)
  | RecordProj (e, l) -> RecordProj (semantic_type_of e, l)
  | Match (e, pattern_expr_lst) ->
    let e' = semantic_type_of e in
    let pattern_expr_lst' = List.map (fun (pat, expr) -> (pat, semantic_type_of expr)) pattern_expr_lst in
    Match (e', pattern_expr_lst')
  | VariantExpr (lbl, e) -> VariantExpr (lbl, semantic_type_of e)
  | List expr_lst -> List (List.map semantic_type_of expr_lst)
  | ListCons (e1, e2) -> ListCons (semantic_type_of e1, semantic_type_of e2)
  | Assert e -> Assert (semantic_type_of e)
  | Assume e -> Assume (semantic_type_of e)

(* Phase two of the transformation: erasing all type signatures from 
   the code. By the end of this phase, there should no longer be any
   (x : tau) present in the AST.
 *)
and typed_non_to_on (e : sem_type_natodefa) : core_natodefa = 
  match e with
  | Int n -> Int n
  | Bool b -> Bool b
  | Var x -> Var x
  | Input -> Input
  | Untouched s -> Untouched s
  | Function (id_lst, e) -> Function (id_lst, typed_non_to_on e)
  | Appl (e1, e2) -> Appl (typed_non_to_on e1, typed_non_to_on e2) 
  | Let (x, e1, e2) -> Let (x, typed_non_to_on e1, typed_non_to_on e2)
  | LetRecFun (sig_lst, e) ->
    begin
      let sig_lst' = List.map (transform_funsig typed_non_to_on) sig_lst in 
      LetRecFun (sig_lst', typed_non_to_on e)
    end
  | LetFun (fun_sig, e) ->
    begin
      let sig' = (transform_funsig typed_non_to_on) fun_sig in
      LetFun (sig', typed_non_to_on e)
    end
  | LetWithType (x, e1, e2, type_decl) ->
    begin
      let type_decl' = typed_non_to_on type_decl in
      let (e1' : core_natodefa) = typed_non_to_on e1 in
      let (e2' : core_natodefa) = typed_non_to_on e2 in
      let test_expr = 
        If (Appl (RecordProj (type_decl', Label "checker"), Var x), 
            e2', 
            Assert (Bool false)) 
      in
      Let (x, e1', test_expr)
    end
  | LetRecFunWithType (sig_lst, e, type_decl_lst) ->
    begin
      let fun_names = List.map (fun (Funsig (id, _, _)) -> Var id) sig_lst in
      let combined_lst = List.combine fun_names type_decl_lst in
      let folder (f, t) acc = 
        let t' = typed_non_to_on t in
        If (Appl (RecordProj (t', Label "checker"), f), acc, Assert (Bool false))
      in
      let test_exprs = 
        List.fold_right folder combined_lst (typed_non_to_on e) 
      in
      let sig_lst' = List.map (transform_funsig typed_non_to_on) sig_lst in
      LetRecFun (sig_lst', test_exprs)
    end
  | LetFunWithType ((Funsig (f, _, _) as fun_sig), e, type_decl) ->
    begin
      let type_decl' = typed_non_to_on type_decl in
      let test_expr = 
        If (Appl (RecordProj (type_decl', Label "checker"), Var f), 
            typed_non_to_on e, 
            Assert (Bool false)) in
      let fun_sig' = (transform_funsig typed_non_to_on) fun_sig in
      LetFun (fun_sig', test_expr)
    end
  | Plus (e1, e2) -> Plus (typed_non_to_on e1, typed_non_to_on e2)
  | Minus (e1, e2) -> Minus (typed_non_to_on e1, typed_non_to_on e2)
  | Times (e1, e2) -> Times (typed_non_to_on e1, typed_non_to_on e2)
  | Divide (e1, e2) -> Divide (typed_non_to_on e1, typed_non_to_on e2)
  | Modulus (e1, e2) -> Modulus (typed_non_to_on e1, typed_non_to_on e2)
  | Equal (e1, e2) -> Equal (typed_non_to_on e1, typed_non_to_on e2)
  | Neq (e1, e2) -> Neq (typed_non_to_on e1, typed_non_to_on e2)
  | LessThan (e1, e2) -> LessThan (typed_non_to_on e1, typed_non_to_on e2)
  | Leq (e1, e2) -> Leq (typed_non_to_on e1, typed_non_to_on e2)
  | GreaterThan (e1, e2) -> GreaterThan (typed_non_to_on e1, typed_non_to_on e2)
  | Geq (e1, e2) -> Geq (typed_non_to_on e1, typed_non_to_on e2)
  | And (e1, e2) -> And (typed_non_to_on e1, typed_non_to_on e2)
  | Or (e1, e2) -> Or (typed_non_to_on e1, typed_non_to_on e2)
  | Not e -> Not (typed_non_to_on e)
  | If (e1, e2, e3) -> If (typed_non_to_on e1, typed_non_to_on e2, typed_non_to_on e3)
  | Record m -> Record (Ident_map.map (fun e -> typed_non_to_on e) m)
  | RecordProj (e, l) -> RecordProj (typed_non_to_on e, l)
  | Match (e, pattern_expr_lst) ->
    let e' = typed_non_to_on e in
    let pattern_expr_lst' = List.map (fun (pat, expr) -> (pat, typed_non_to_on expr)) pattern_expr_lst in
    Match (e', pattern_expr_lst')
  | VariantExpr (lbl, e) -> VariantExpr (lbl, typed_non_to_on e)
  | List expr_lst -> List (List.map typed_non_to_on expr_lst)
  | ListCons (e1, e2) -> ListCons (typed_non_to_on e1, typed_non_to_on e2)
  | Assert e -> Assert (typed_non_to_on e)
  | Assume e -> Assume (typed_non_to_on e)