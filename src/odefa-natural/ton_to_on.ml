open Batteries;;

open On_ast;;

let counter = ref 0;;

let isInt (e : expr) : expr = 
  Match (e, [(IntPat, Bool true); (AnyPat, Assert (Bool false))])
;;

let isBool (e : expr) : expr = 
  Match (e, [(BoolPat, Bool true); (AnyPat, Assert (Bool false))])
;;

let is_int_with_pred (e : expr) (p : predicate) : expr = 
  let Predicate pred = p in
  Match (e, [(IntPat, Assert (Appl (pred, e))); (AnyPat, Assert (Bool false))])
;;

let is_bool_with_pred (e : expr) (p : predicate) : expr = 
  let Predicate pred = p in
  Match (e, [(BoolPat, Assert (Appl (pred, e))); (AnyPat, Assert (Bool false))])
;;

let rec isRecord (r : type_decl Ident_map.t) (e : expr) : expr = 
  let all_bindings = Ident_map.bindings r in
  let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let fold_fun acc (Ident lbl, t) = Let (dummy_var, generate_assert t (RecordProj (e, Label lbl)), acc) in
  let (Ident first_lbl, first_type) = List.hd all_bindings in
  List.fold_left fold_fun (generate_assert first_type (RecordProj (e, Label first_lbl))) (List.tl all_bindings)

and isList (t : type_decl) (e : expr) : expr =
  let test_fun_name = Ident ("~testFun" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let test_list = Ident ("~testList" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let test_fun = Match (Var test_list, [(EmptyLstPat, Bool true); (LstDestructPat (Ident "hd", Ident "tl"), (Let (dummy_var, generate_assert t (Var (Ident "hd")), Appl (Var test_fun_name, Var (Ident "tl")))))]) in
  let check_fun = Funsig (test_fun_name, [test_list], test_fun) in
  LetRecFun ([check_fun], Appl (Var test_fun_name, e))

and is_record_with_pred (r : type_decl Ident_map.t) (e : expr) (p : predicate) : expr = 
  let Predicate pred = p in
  let all_bindings = Ident_map.bindings r in
  let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let fold_fun (Ident lbl, t) acc = Let (dummy_var, generate_assert t (RecordProj (e, Label lbl)), acc) in
  List.fold_right fold_fun all_bindings (Assert (Appl (pred, e))) 
  
and is_list_with_pred (t : type_decl) (e : expr) (p : predicate) : expr =
  let Predicate pred = p in
  let test_fun_name = Ident ("~testFun" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let test_list = Ident ("~testList" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let list_valid = Ident ("~listValid" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let test_fun = Match (Var test_list, [(EmptyLstPat, Bool true); (LstDestructPat (Ident "hd", Ident "tl"), (Let (dummy_var, generate_assert t (Var (Ident "hd")), Appl (Var test_fun_name, Var (Ident "tl")))))]) in
  let check_fun = Funsig (test_fun_name, [test_list], test_fun) in
  LetRecFun ([check_fun], Let (list_valid, Appl (Var test_fun_name, e), Assert  (Appl (pred, e))))

and generate_assume (t : type_decl) : expr =
  match t with
  (* TODO: Implement the input type according to the type *)
  | FirstOrderType (TypeDefinition (t', p_option)) ->
    begin
      match t' with
      | TypeInt -> 
        begin
          if (Option.is_some p_option) 
          then
            let Predicate p = Option.get p_option in
            let raw_input = Ident ("~rawInput" ^ string_of_int (counter := !counter + 1 ; !counter)) in
            let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
            let inner_let = Let (dummy_var, Assume (Appl (p, (Var raw_input))), Var raw_input) in
            Let (raw_input, Input, inner_let)
          else
            Input
        end
      | TypeBool -> 
        let raw_input = Ident ("~rawInput" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let bool_input = Ident ("~boolInput" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let end_expr = 
          if (Option.is_some p_option)
          then 
            let Predicate p = Option.get p_option in
            Let (dummy_var, Assume (Appl (p, Var bool_input)), Var bool_input)
          else Var bool_input
        in
        let inner_let = Let (bool_input, Geq (Var raw_input, Int 0), end_expr) in
        Let (raw_input, Input, inner_let)
      | TypeRecord r ->
        let all_bindings = Ident_map.bindings r in
        let empty_record = Ident_map.empty in
        let lbl_to_var = List.map 
          (fun ((Ident lbl_str) as lbl, lbl_type) -> 
            let lbl_var = Ident ("~" ^ lbl_str ^ string_of_int (counter := !counter + 1 ; !counter)) in
            (lbl, lbl_var, lbl_type)) all_bindings 
        in
        let res_record = List.fold_left (fun acc (lbl, lbl_var, _) -> Ident_map.add lbl (Var lbl_var) acc) empty_record lbl_to_var 
        in
        let fold_fun acc (_, lbl_var, cur_t) = Let (lbl_var, generate_assume cur_t, acc) in
        let rec_input = Ident ("~rec_input" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let end_expr = 
          if (Option.is_some p_option)
          then
            let Predicate p = Option.get p_option in 
            Let (dummy_var,  Assume (Appl (p, Var rec_input)), Var rec_input)
          else Var rec_input
        in
        let base_acc = Let (rec_input, Record res_record, end_expr) in
        List.fold_left fold_fun base_acc lbl_to_var
      | TypeList l -> 
        let entry_var = Ident ("~entry" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let list_var = Ident ("~list" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let end_expr = 
          if (Option.is_some p_option)
          then 
            let Predicate p = Option.get p_option in
            Let (dummy_var,  Assume (Appl (p, Var list_var)), Var list_var)
          else Var list_var
        in
        let inner_let = Let (list_var, List [Var entry_var], end_expr) in
        Let (entry_var, generate_assume l, inner_let)
      (* let arg_gen = Ident ("~argGen" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let dummy_arg = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let arg_input = Ident ("~argInput" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let arg_gen_cond = If (Appl (p, (Var arg_input)), Var arg_input, Assert (Bool false)) in
      let arg_gen_body = Let (arg_input, Input, arg_gen_cond) in
      let arg_gen_fun = LetFun (Funsig (arg_gen, [dummy_arg], arg_gen_body), Appl (Var arg_gen, Int 0)) in
      arg_gen_fun *)
    end
  | HigherOrderType (t1, t2) -> 
    let arg_assume = Ident ("~tval" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    (* TODO: The Assert here might needs to change according to how assert works *)
    let inner_expr = If (generate_assert t1 (Var arg_assume), generate_assume t2, Assert (Bool false)) in 
    Function ([arg_assume], inner_expr)

and generate_assert (t : type_decl) (e : expr) : expr = 
  match t with
  | FirstOrderType (TypeDefinition (t', p_option)) -> 
    begin
      if Option.is_some p_option 
      then
        let p = Option.get p_option in
        match t' with
        | TypeInt -> is_int_with_pred e p
        | TypeBool -> is_bool_with_pred e p
        | TypeRecord r -> is_record_with_pred r e p
        | TypeList t -> is_list_with_pred t e p
      else 
        match t' with
        (* TODO: Check how to encode non-exhaustive match? *)
        | TypeInt -> isInt e
        | TypeBool -> isBool e
        (* TODO: Implement more types here *)
        | TypeRecord r -> isRecord r e
        | TypeList t -> isList t e
    end
  | HigherOrderType (t1, t2) -> 
    begin
      let arg_assert = Ident ("~arg" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      Let (arg_assert, generate_assume t1, generate_assert t2 (Appl (e, Var arg_assert)))
    end
  
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
        let test_expr = generate_assert type_decl (Var x) in
        let test_ident = Ident ("~test_expr" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let test_let = Let (test_ident, test_expr, (typed_non_to_on e2)) in
        Let (x, e1, test_let)
      end
    | LetRecFunWithType (sig_lst, e, type_decl_lst) ->
      begin
        let fun_names = List.map (fun (Funsig (id, _, _)) -> Var id) sig_lst in
        let combined_lst = List.combine fun_names type_decl_lst in
        let test_exprs = List.map (fun (f, t) -> generate_assert t f) combined_lst in
        let test_ident = Ident ("~test_expr" ^ string_of_int (counter := !counter + 1 ; !counter)) in
        let test_lets = List.fold_right 
          (fun cur_elm cur_acc -> Let (test_ident, cur_elm, cur_acc)) test_exprs (typed_non_to_on e)
        in
        let sig_lst' = List.map transform_funsig sig_lst in
        LetRecFun (sig_lst', test_lets)
      end
    | LetFunWithType ((Funsig (f, _, _) as fun_sig), e, type_decl) ->
      begin
        let test_expr = generate_assert type_decl (Var f) in
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