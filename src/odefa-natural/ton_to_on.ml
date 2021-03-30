open Batteries;;

open On_ast;;

type semantic_type = expr

let counter = ref 0;;

(* May be needed in the future *)
(* let rec subs (var_replace : ident) (concrete_type : type_decl) (og_type : type_decl) : type_decl = 
  match og_type with
  | TypeInt | TypeBool -> og_type 
  | TypeVar v -> 
    if (var_replace == v) then concrete_type else og_type
  | TypeRecord tmap -> TypeRecord (Ident_map.map (subs var_replace concrete_type) tmap)
  | TypeList t -> TypeList (subs var_replace concrete_type t)
  | TypeUnion (t1, t2) -> TypeUnion (subs var_replace concrete_type t1, subs var_replace concrete_type t2)
  | TypeIntersect (t1, t2) -> TypeIntersect (subs var_replace concrete_type t1, subs var_replace concrete_type t2)
  | TypeArrow (t1, t2) -> TypeArrow (subs var_replace concrete_type t1, subs var_replace concrete_type t2)
  | TypeSet (t, p) -> TypeSet (subs var_replace concrete_type t, p)
  | TypeRecurse (t_var', t) ->
    if (t_var == t_var') then og_type else TypeRecurse (t_var', subs var_replace concrete_type t)
in *)

(* TODO: Maybe add annotation on the surface level language so that we can avoid certain type checking in sato *)

(* TODO: Finish the semantic translation of types *)
let rec semantic_pair_of (t : type_decl) : semantic_type =
  match t with
  | TypeVar t_var -> Appl (Var t_var, Var t_var)
  | TypeInt ->
    let generator =
      let int_input = Ident ("~int_input" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let gen_expr = Let (int_input, Input, Var int_input) in
      Function ([Ident "~null"], gen_expr)
    in
    let checker = 
      Function ([Ident "exp"], Match (Var (Ident "exp"), [(IntPat, Bool true); (AnyPat, Bool false)]))
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
    let checker = 
      Function ([Ident "exp"], Match (Var (Ident "exp"), [(BoolPat, Bool true); (AnyPat, Bool false)]))
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
        let gc_pair = semantic_pair_of cur_t in
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
      let fold_fun acc (Ident lbl, t) = 
        let gc_pair = semantic_pair_of t in
        Let (dummy_var, 
              Appl (RecordProj (gc_pair, Label "checker"), RecordProj (Var (Ident "exp"), Label lbl)), 
              acc)
      in
      let (Ident first_lbl, first_type) = List.hd all_bindings in
      let gc_pair = semantic_pair_of first_type in
      let init_acc = Appl (RecordProj (gc_pair, Label "checker"), RecordProj (Var (Ident "exp"), Label first_lbl)) in
      let fun_body = List.fold_left fold_fun init_acc (List.tl all_bindings) in
      let match_body = Match (Var (Ident "exp"), 
                              [(RecPat type_dict, fun_body); 
                              (AnyPat, Bool false)]) in
      Function ([Ident "exp"], match_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeList l ->
    let gc_pair = semantic_pair_of l in
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
                  (Let (dummy_var, Appl (RecordProj (gc_pair, Label "checker"), Var (Ident "hd")), Appl (Var test_fun_name, Var (Ident "tl")))))
               ]) in
      let check_fun = Funsig (test_fun_name, [test_list], test_fun) in
      let fun_body = LetRecFun ([check_fun], Appl (Var test_fun_name, Var (Ident "exp"))) in
      let match_body = Match (Var (Ident "exp"), 
                              [(EmptyLstPat, Bool true); 
                               (LstDestructPat (Ident "~dummy1", Ident "~dummy2"), fun_body);
                               (AnyPat, Bool false)
                              ]) 
      in
      Function ([Ident "exp"], match_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeUnion (t1, t2) ->
    let gc_pair1 = semantic_pair_of t1 in
    let gc_pair2 = semantic_pair_of t2 in
    let generator = 
      let select_int = Ident ("~select_int" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let branch = If (Geq (Var select_int, Int 0), 
                       Appl (RecordProj (gc_pair1, Label "generator"), Int 0), 
                       Appl (RecordProj (gc_pair2, Label "generator"), Int 0)) in
      let gen_expr = Let (select_int, Input, branch) in
      Function ([Ident "~null"], gen_expr)
    in
    let checker = 
      (* let select_int = Ident ("~select_int" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let gate = Ident ("~gate"^ string_of_int (counter := !counter + 1 ; !counter)) in
      let check1 = Appl (RecordProj (gc_pair1, Label "checker"), Var (Ident "exp")) in
      let check2 = Appl (RecordProj (gc_pair2, Label "checker"), Var (Ident "exp")) in
      let assume1 = Let (gate, Assume (check1), check1) in
      let assume2 = Let (gate, Assume (check2), check2) in
      let checker1 = If (assume1, Bool true, assume2) in
      let checker2 = If (assume2, Bool true, assume1) in
      let branch = If (Geq (Var select_int, Int 0), checker1, checker2) in
      let fun_body = Let (select_int, Input, branch) in
      Function ([Ident "exp"], fun_body) *)
      let select_int = Ident ("~select_int" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let checker1 = If (Appl (RecordProj (gc_pair1, Label "checker"), Var (Ident "exp")), Bool true, Appl (RecordProj (gc_pair2, Label "checker"), Var (Ident "exp"))) in
      let checker2 = If (Appl (RecordProj (gc_pair2, Label "checker"), Var (Ident "exp")), Bool true, Appl (RecordProj (gc_pair1, Label "checker"), Var (Ident "exp"))) in
      let branch = If (Geq (Var select_int, Int 0), checker1, checker2) in
      let fun_body = Let (select_int, Input, branch) in
      Function ([Ident "exp"], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeArrow (t1, t2) ->
    let gc_pair1 = semantic_pair_of t1 in
    let gc_pair2 = semantic_pair_of t2 in
    let generator = 
      let arg_assume = Ident ("~arg_assume" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let inner_expr = If (Appl (RecordProj (gc_pair1, Label "checker"), Var arg_assume), 
                           Appl (RecordProj (gc_pair2, Label "generator"), Int 0), 
                           Assert (Bool false)) in 
      let gen_expr = Function ([arg_assume], inner_expr) in
      Function ([Ident "~null"], gen_expr)
    in
    let checker = 
      let arg_assert = Ident ("~arg_assert" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let fun_body = Let (arg_assert, 
                          Appl (RecordProj (gc_pair1, Label "generator"), Int 0), 
                          Appl (RecordProj (gc_pair2, Label "checker"), Appl (Var (Ident "exp"), Var arg_assert))) in
      Function ([Ident "exp"], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeSet (t, Predicate p) ->
    let gc_pair = semantic_pair_of t in
    let generator = 
      let candidate = Ident ("~candidate" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let pred_check = If (Appl (p, Var candidate), Var candidate, Assume (Bool false)) in
      let gen_expr = Let (candidate, 
                          Appl (RecordProj (gc_pair, Label "generator"), Int 0), 
                          pred_check) in
      Function ([Ident "~null"], gen_expr)
    in
    let checker = 
      let fun_body = If (Appl (RecordProj (gc_pair, Label "checker"), Var (Ident "exp")), 
                         Appl (p, Var (Ident "exp")), Bool false) in
      Function ([Ident "exp"], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeIntersect (t1, t2) -> 
    let gc_pair1 = semantic_pair_of t1 in
    let gc_pair2 = semantic_pair_of t2 in
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
    let checker = 
      let fun_body = If (Appl (RecordProj (gc_pair1, Label "checker"), Var (Ident "exp")), 
                         Appl (RecordProj (gc_pair2, Label "checker"), Var (Ident "exp")), 
                         Bool false) in
      Function ([Ident "exp"], fun_body)
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    Record rec_map
  | TypeRecurse (Ident t_var, t') ->
    let rec rename_tree (old_var : ident) (new_var : ident) (og_type : type_decl) : type_decl = 
      match og_type with
      | TypeInt | TypeBool -> og_type 
      | TypeVar v -> 
        if (old_var = v) then TypeVar new_var else og_type
      | TypeRecord tmap -> TypeRecord (Ident_map.map (rename_tree old_var new_var) tmap)
      | TypeList lt -> TypeList (rename_tree old_var new_var lt)
      | TypeUnion (t1, t2) -> TypeUnion (rename_tree old_var new_var t1, rename_tree old_var new_var t2)
      | TypeIntersect (t1, t2) -> TypeIntersect (rename_tree old_var new_var t1, rename_tree old_var new_var t2)
      | TypeArrow (t1, t2) -> TypeArrow (rename_tree old_var new_var t1, rename_tree old_var new_var t2)
      | TypeSet (st, p) -> TypeSet (rename_tree old_var new_var st, p)
      | TypeRecurse (t_var', rt) ->
        if (old_var == t_var') then TypeRecurse (new_var, rename_tree old_var new_var rt) else TypeRecurse (t_var', rename_tree old_var new_var rt)
    in
    let fresh_type_var = Ident ("self_" ^ t_var ^ string_of_int (counter := !counter + 1 ; !counter)) in
    (* let _  = print_endline ("******" ^ show_type_decl t' ^ "******") in *)
    (* let _ = print_endline ("****** This is old_var: " ^ t_var ^ "******") in *)
    let new_decl = rename_tree (Ident t_var) fresh_type_var t' in
    (* let _  = print_endline ("******" ^ show_type_decl new_decl ^ "******") in *)
    let gc_pair = semantic_pair_of new_decl in
    let generator = 
      Function ([Ident "~null"], RecordProj (gc_pair, Label "generator"))
    in 
    let checker = 
      Function ([Ident "exp"], Appl (RecordProj (gc_pair, Label "checker"), Var (Ident "exp")))
    in
    let rec_map = 
      Ident_map.empty
      |> Ident_map.add (Ident "generator") generator
      |> Ident_map.add (Ident "checker") checker
    in
    let primer_var = Ident "primer" in
    Let (primer_var, Function ([fresh_type_var], Record rec_map), Appl (Var primer_var, Var primer_var))

(* TODO: Use the checker/generator pair to perform the checking, which should make things simpler *)
let rec typed_non_to_on (e : expr) : expr = 
  match e with
  | Int _ | Bool _ | Var _ | Input -> e
  | Function (id_lst, e) -> Function (id_lst, typed_non_to_on e)
  | Appl (e1, e2) -> Appl (typed_non_to_on e1, typed_non_to_on e2) 
  | Let (x, e1, e2) -> Let (x, typed_non_to_on e1, typed_non_to_on e2)
  | LetRecFun (sig_lst, e) ->
    begin
      let sig_lst' = List.map transform_funsig sig_lst in 
      LetRecFun (sig_lst', typed_non_to_on e)
    end
  | LetFun (fun_sig, e) ->
    begin
      let sig' = transform_funsig fun_sig in
      LetFun (sig', typed_non_to_on e)
    end
  | LetWithType (x, e1, e2, type_decl) ->
    begin
      let gc_pair = semantic_pair_of type_decl in
      let test_expr = If (Appl (RecordProj (gc_pair, Label "checker"), Var x), Bool true, Assert (Bool false)) in
      let test_ident = Ident ("~test_expr" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let test_let = Let (test_ident, test_expr, (typed_non_to_on e2)) in
      Let (x, e1, test_let)
    end
  | LetRecFunWithType (sig_lst, e, type_decl_lst) ->
    begin
      let fun_names = List.map (fun (Funsig (id, _, _)) -> Var id) sig_lst in
      let combined_lst = List.combine fun_names type_decl_lst in
      let test_exprs = List.map 
        (fun (f, t) -> 
          let gc_pair = semantic_pair_of t in 
          Appl (RecordProj (gc_pair, Label "checker"), f)) 
          combined_lst in
      let test_ident = Ident ("~test_expr" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let test_lets = List.fold_right 
        (fun cur_elm cur_acc -> Let (test_ident, cur_elm, cur_acc)) test_exprs (typed_non_to_on e)
      in
      let sig_lst' = List.map transform_funsig sig_lst in
      LetRecFun (sig_lst', test_lets)
    end
  | LetFunWithType ((Funsig (f, _, _) as fun_sig), e, type_decl) ->
    begin
      let gc_pair = semantic_pair_of type_decl in
      let test_expr = If (Appl (RecordProj (gc_pair, Label "checker"), Var f), Bool true, Assert (Bool false)) in
      let test_ident = Ident ("~test_expr" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let test_let = Let (test_ident, test_expr, (typed_non_to_on e)) in
      let fun_sig' = transform_funsig fun_sig in
      LetFun (fun_sig', test_let)
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

and transform_funsig (Funsig (fun_name, params, e)) = 
    Funsig (fun_name, params, typed_non_to_on e)