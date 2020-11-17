open Batteries;;

open On_ast;;

let counter = ref 0;;

let isInt (e : expr) : expr = 
  Match (e, [(IntPat, Bool true); (AnyPat, Assert (Bool false))])
;;

let isBool (e : expr) : expr = 
  Match (e, [(BoolPat, Bool true); (AnyPat, Assert (Bool false))])
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

and generate_assume (t : type_decl) : expr =
  match t with
  (* TODO: Implement the input type according to the type *)
  | FirstOrderType t' ->
    begin 
    match t' with
    | TypeInt -> Input
    | TypeBool -> 
      let raw_input = Ident ("~rawInput" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      Let (raw_input, Input, Geq (Var raw_input, Int 0))
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
      let fold_fun acc (_, lbl_var, cur_t) = Let (lbl_var, generate_assume cur_t, acc)
      in
      let base_acc = Record res_record
      in
      List.fold_left fold_fun base_acc lbl_to_var
    | TypeList l -> 
      let entry_var = Ident ("~entry" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      Let (entry_var, generate_assume l, List [Var entry_var])
    end
  | HigherOrderType (t1, t2) -> 
    let arg_assume = Ident ("~tval" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    (* TODO: The Assert here might needs to change according to how assert works *)
    let inner_expr = If (generate_assert t1 (Var arg_assume), generate_assume t2, Assert (Bool false)) in 
    Function ([arg_assume], inner_expr)

and generate_assert (t : type_decl) (e : expr) : expr = 
  match t with
  | FirstOrderType t' -> 
    begin
      (* TODO: implement this correctly *)
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
    | Assert e -> typed_non_to_on e

  and transform_funsig (Funsig (fun_name, params, e)) = 
      Funsig (fun_name, params, typed_non_to_on e)