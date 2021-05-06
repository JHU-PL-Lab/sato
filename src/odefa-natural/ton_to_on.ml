open Batteries;;
open Jhupllib;;

open On_ast;;

(* TODO: 
  - 
  -   


node: { left, right, cell_value }
key:  [ list of booleans ]


global state ≡ (global state mapping, next cell ID)
global state mapping ≡ complete binary tree of { left, right, cell_value } nodes
cell ID ≡ list of booleans describing a path in the binary tree


operations:
  new_cell : global state → value → (global state, cell ID)
  get_cell : global state → cell ID → (value, global state)
  set_cell : global state → cell ID → value → global state


global state mapping:
   0 ↦ 5
   1 ↦ true
   2 ↦ []
   3 ↦ 1


             5
            / \
         true  []
          /
         1

   0 ≅ []
   1 ≅ [false]
   2 ≅ [true]
   3 ≅ [false,false]
   4 ≅ [false,true]
   5 ≅ [true,false]
   6 ≅ [true,true]
   7 ≅ [false,false,false]

{ cell_value = 5;
  left =
    { cell_value = true;
      left =
        { cell_value = 1;
          left = {};
          right = {};
        }
      right = {};
    };
  right =
    { cell_value = [];
      left = {};
      right = {};
    };
}


let increment_cell_id (id : bool list) : bool list =
  let rec loop (id : bool list) : bool list * bool =
    match id with
    | [] -> ([], true)
    | h::t ->
      let (t', keep_flipping) = loop t in
      if keep_flipping then
        if h then
          (false::t', true)
        else
          (true::t', false)
      else
        h::t'
  in
  let (id', carry) = loop id in
  if carry then
    false :: id'
  else
    id'
;;



let x : int ref = ref (2+3) in

⇒

let pair = new_cell state_0 (2+3) in
let state_1 = pair.state in
let x = pair.value in
let _ : int = get_cell state_1 x in 


let x : int list = [3,4,x:=5,6] in

let* x : int list =
  let* i1 = pure 3 in
  let* i2 = pure 4 in
  let* i3 = set x 5 in
  let* i4 = pure 6 in
  pure [i1,i2,i3,i4]
in

let* x : int list =
  let pair_578 = pure state_578 3 in
  let state_579 = pair_578.state in
  let i1 = pair_578.value in
  let* i2 = pure 4 in
  let* i3 = set x 5 in
  let* i4 = pure 6 in
  pure ... [i1,i2,i3,i4]
in

let* x =
  let pair_0 = {c_val = 3, gs = state_0} in
  let state_1 = pair_0.gs in
  let i1 = pair_0.c_val in
  let pair_1 = set_cell state_1 [false, false] 5 in
  let state_2 = pair_1.gs in
  let i2 = pair_1.c_val in
  pure ... [i1,i2]
in


*)

let counter = ref 0;;

let pure_fun = Var (Ident "pure");;
let new_cell_fun = Var (Ident "new_cell");;
let get_cell_fun = Var (Ident "get_cell");;
let set_cell_fun = Var (Ident "set_cell");;
let bind_fun = Var (Ident "bind");;

let isInt (e : expr) (antimatch : expr) : expr = 
  Match (e, [(IntPat, Bool true); (AnyPat, antimatch)])
;;

let isBool (e : expr) (antimatch : expr) : expr = 
  Match (e, [(BoolPat, Bool true); (AnyPat, antimatch)])
;;

let rec isRecord (r : type_decl Ident_map.t) (e : expr) (antimatch : expr) : expr = 
  let all_bindings = Ident_map.bindings r in
  let all_keys = Enum.map (fun k -> (k, None)) (Ident_map.keys r) in
  let type_dict = Ident_map.of_enum all_keys in
  let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let fold_fun acc (Ident lbl, t) = Let (dummy_var, generate_assert t (RecordProj (e, Label lbl)) (Assert (Bool false)), acc) in
  let (Ident first_lbl, first_type) = List.hd all_bindings in
  let check_rec_content = List.fold_left fold_fun (generate_assert first_type (RecordProj (e, Label first_lbl)) (Assert (Bool false))) (List.tl all_bindings) in
  let check_rec_type = 
    Match (e, [(RecPat type_dict, check_rec_content); (AnyPat, antimatch)])
  in
  check_rec_type

and isList (t : type_decl) (e : expr) (antimatch : expr) : expr =
  let test_fun_name = Ident ("~testFun" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let test_list = Ident ("~testList" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
  let test_fun = Match (Var test_list, 
                        [(EmptyLstPat, Bool true); 
                         (LstDestructPat (Ident "hd", Ident "tl"), 
                            (Let (dummy_var, 
                                  generate_assert t (Var (Ident "hd")) (Assert (Bool false)), 
                                  Appl (Var test_fun_name, Var (Ident "tl")))
                            )
                         )
                        ]
                       ) in
  let check_fun = Funsig (test_fun_name, [test_list], test_fun) in
  let check_list_content = LetRecFun ([check_fun], Appl (Var test_fun_name, e)) in
  let check_list_type = 
    Match (e, [(EmptyLstPat, Bool true); (LstDestructPat (Ident "hd", Ident "tl"), check_list_content); (AnyPat, antimatch)]) 
  in
  check_list_type

and generate_assume (t : type_decl) : expr =
  match t with
  | TypeInt -> Input
  | TypeBool -> 
    let raw_input = Ident ("~raw_input" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let bool_input = Ident ("~bool_input" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let get_raw = Let (raw_input, Input, Var raw_input) in
    Let (bool_input, Geq (get_raw, Int 0), Var bool_input)
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
    let base_acc = Let (rec_input, Record res_record, Var rec_input) in
    List.fold_left fold_fun base_acc lbl_to_var
  | TypeList l -> 
    let len_var_raw = Ident ("~len_raw" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let len_var = Ident ("~len" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let len_arg = Ident ("~len_arg" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let list_var = Ident ("~list" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let maker_var = Ident ("~list_maker" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let elm_var = Ident ("~elm" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let recur_call = Let (elm_var, generate_assume l, ListCons (Var elm_var, Appl (Var maker_var, Minus (Var len_arg, Int 1)))) in
    let list_maker = If (Equal (Var len_arg, Int 0), List [], recur_call) in
    (* let list_maker = List [] in *)
    let list_maker_fun = Funsig (maker_var, [len_arg], list_maker) in
    let inner_let = Let (list_var, Appl (Var maker_var, Var len_var), Var list_var) in
    let validate_len = Let (len_var_raw, Int 0, If (Geq(Var len_var_raw, Int 0), Var len_var_raw, Assume (Bool false))) in
    let list_len = Let (len_var, validate_len, inner_let) in
    LetRecFun ([list_maker_fun], list_len)
  | TypeUnion (t1, t2) -> 
    let assume_t1 = generate_assume t1 in
    let assume_t2 = generate_assume t2 in
    let select_int = Ident ("~select_int" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let branch = If (Geq (Var select_int, Int 0), assume_t1, assume_t2) in
    Let (select_int, Input, branch)
  | TypeIntersect (t1, t2) -> 
    let assume_t1 = generate_assume t1 in
    let candidate_var = Ident ("~candidate" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let validate = If (generate_assert t2 (Var candidate_var) (Assert (Bool false)), 
                       Var candidate_var, 
                       Assume (Bool false)) in
    Let (candidate_var, assume_t1, validate)
  | TypeArrow (t1, t2) -> 
    let arg_assume = Ident ("~tval" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let inner_expr = If (generate_assert t1 (Var arg_assume) (Assert (Bool false)), generate_assume t2, Assert (Bool false)) in 
    Function ([arg_assume], inner_expr)
  | TypeSet (t, Predicate p) ->
    let assume_t = generate_assume t in
    let candidate = Ident ("~candidate" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let pred_check = If (Appl (p, Var candidate), Var candidate, Assume (Bool false)) in
    Let (candidate, assume_t, pred_check)

and generate_assert (t : type_decl) (e : expr) (antimatch : expr) : expr = 
  match t with
  | TypeInt -> isInt e antimatch
  | TypeBool -> isBool e antimatch
  | TypeRecord r -> isRecord r e antimatch
  | TypeList t -> isList t e antimatch
  | TypeUnion (t1, t2) -> 
    let select_int = Ident ("~select_int" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    let checker1 = generate_assert t1 e (generate_assert t2 e (Assert (Bool false))) in
    let checker2 = generate_assert t2 e (generate_assert t1 e (Assert (Bool false))) in
    let branch = If (Geq (Var select_int, Int 0), checker1, checker2) in
    Let (select_int, Input, branch)
  | TypeIntersect (t1, t2) -> 
    let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    Let (dummy_var, generate_assert t1 e (Assert (Bool false)) , generate_assert t2 e (Assert (Bool false)))
  | TypeArrow (t1, t2) -> 
    let arg_assert = Ident ("~arg" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    Let (arg_assert, 
         generate_assume t1, 
         generate_assert t2 (Appl (e, Var arg_assert)) (Assert (Bool false)))
  | TypeSet (t, Predicate p) ->
    let dummy_var = Ident ("~dummy" ^ string_of_int (counter := !counter + 1 ; !counter)) in
    Let (dummy_var, generate_assert t e (Assert (Bool false)), Assert (Appl (p, e)))

let rec typed_non_to_on (e : expr) : expr = 
  let transform_funsig (Funsig (fun_name, params, e)) = 
    Funsig (fun_name, params, typed_non_to_on e)
  in
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
      (* let _ = print_endline "LetWithType" in *)
      let test_expr = generate_assert type_decl (Var x) (Assert (Bool false)) in
      let test_ident = Ident ("~test_expr" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let test_let = Let (test_ident, test_expr, (typed_non_to_on e2)) in
      Let (x, e1, test_let)
    end
  | LetRecFunWithType (sig_lst, e, type_decl_lst) ->
    begin
      let fun_names = List.map (fun (Funsig (id, _, _)) -> Var id) sig_lst in
      let combined_lst = List.combine fun_names type_decl_lst in
      let test_exprs = List.map (fun (f, t) -> generate_assert t f (Assert (Bool false))) combined_lst in
      let test_ident = Ident ("~test_expr" ^ string_of_int (counter := !counter + 1 ; !counter)) in
      let test_lets = List.fold_right 
        (fun cur_elm cur_acc -> Let (test_ident, cur_elm, cur_acc)) test_exprs (typed_non_to_on e)
      in
      let sig_lst' = List.map transform_funsig sig_lst in
      LetRecFun (sig_lst', test_lets)
    end
  | LetFunWithType ((Funsig (f, _, _) as fun_sig), e, type_decl) ->
    begin
      let _ = print_endline "LetFunWithType" in
      let test_expr = generate_assert type_decl (Var f) (Assert (Bool false)) in
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
  | SetCell _ | GetCell _ | NewCell _ -> raise @@ Utils.Invariant_failure "Should have been desugared by now!"

let rec substitute (old_id : ident) (new_id : ident) (e : expr) : expr = 
  match e with
  | Int _ | Bool _ | Input -> e
  | Var v ->
    if (v = old_id) 
    then Appl (Var new_id, Var new_id)
    else e   
  | Function (id_lst, e) -> 
    if List.mem old_id id_lst then e 
    else 
      Function (id_lst, substitute old_id new_id e) 
  | Appl (e1, e2) -> Appl (substitute old_id new_id e1, substitute old_id new_id e2) 
  | Let (x, e1, e2) ->
    if (x = old_id) then e 
    else
      Let (x, substitute old_id new_id e1, substitute old_id new_id e2)
  | LetRecFun (sig_lst, e) ->
    begin
      let check_bound = fun (Funsig (fun_name, _, _)) -> old_id = fun_name in
      if List.exists check_bound sig_lst then e 
      else
        let subs_one (Funsig (fun_name, id_lst, e) as f) =
          if List.mem old_id id_lst then f
          else Funsig (fun_name, id_lst, substitute old_id new_id e)
        in
        let sig_lst' = List.map subs_one sig_lst in
        LetRecFun (sig_lst', substitute old_id new_id e)
    end
  | LetFun (fun_sig, e) ->
    begin
      let check_bound = fun (Funsig (fun_name, _, _)) -> old_id = fun_name in
      if check_bound fun_sig then e 
      else
        let subs_one (Funsig (fun_name, id_lst, e) as f) =
          if List.mem old_id id_lst then f
          else Funsig (fun_name, id_lst, substitute old_id new_id e)
        in
        let fun_sig' = subs_one fun_sig in
        LetFun (fun_sig', substitute old_id new_id e)
    end
  | LetWithType (x, e1, e2, type_decl) ->
    begin
      if (x = old_id) then e 
      else
        LetWithType (x, substitute old_id new_id e1, substitute old_id new_id e2, type_decl)
    end
  | LetRecFunWithType (sig_lst, e, type_decl_lst) ->
    begin
      let check_bound = fun (Funsig (fun_name, _, _)) -> old_id = fun_name in
      if List.exists check_bound sig_lst then e 
      else
        let subs_one (Funsig (fun_name, id_lst, e) as f) =
          if List.mem old_id id_lst then f
          else Funsig (fun_name, id_lst, substitute old_id new_id e)
        in
        let sig_lst' = List.map subs_one sig_lst in
        LetRecFunWithType (sig_lst', substitute old_id new_id e, type_decl_lst)
    end
  | LetFunWithType (fun_sig, e, type_decl) ->
    begin
      let check_bound = fun (Funsig (fun_name, _, _)) -> old_id = fun_name in
      if check_bound fun_sig then e 
      else
        let subs_one (Funsig (fun_name, id_lst, e) as f) =
          if List.mem old_id id_lst then f
          else Funsig (fun_name, id_lst, substitute old_id new_id e)
        in
        let fun_sig' = subs_one fun_sig in
        LetFunWithType (fun_sig', substitute old_id new_id e, type_decl)
    end
  | Plus (e1, e2) -> Plus (substitute old_id new_id e1, substitute old_id new_id e2)
  | Minus (e1, e2) -> Minus (substitute old_id new_id e1, substitute old_id new_id e2)
  | Times (e1, e2) -> Times (substitute old_id new_id e1, substitute old_id new_id e2)
  | Divide (e1, e2) -> Divide (substitute old_id new_id e1, substitute old_id new_id e2)
  | Modulus (e1, e2) -> Modulus (substitute old_id new_id e1, substitute old_id new_id e2)
  | Equal (e1, e2) -> Equal (substitute old_id new_id e1, substitute old_id new_id e2)
  | Neq (e1, e2) -> Neq (substitute old_id new_id e1, substitute old_id new_id e2)
  | LessThan (e1, e2) -> LessThan (substitute old_id new_id e1, substitute old_id new_id e2)
  | Leq (e1, e2) -> Leq (substitute old_id new_id e1, substitute old_id new_id e2)
  | GreaterThan (e1, e2) -> GreaterThan (substitute old_id new_id e1, substitute old_id new_id e2)
  | Geq (e1, e2) -> Geq (substitute old_id new_id e1, substitute old_id new_id e2)
  | And (e1, e2) -> And (substitute old_id new_id e1, substitute old_id new_id e2)
  | Or (e1, e2) -> Or (substitute old_id new_id e1, substitute old_id new_id e2)
  | Not e -> Not (substitute old_id new_id e)
  | If (e1, e2, e3) -> If (substitute old_id new_id e1, substitute old_id new_id e2, substitute old_id new_id e3)
  | Record m -> Record (Ident_map.map (fun e -> substitute old_id new_id e) m)
  | RecordProj (e, l) -> RecordProj (substitute old_id new_id e, l)
  | Match (e, pattern_expr_lst) ->
    let e' = substitute old_id new_id e in
    let pattern_expr_lst' = List.map (fun (pat, expr) -> (pat, substitute old_id new_id expr)) pattern_expr_lst in
    Match (e', pattern_expr_lst')
  | VariantExpr (lbl, e) -> VariantExpr (lbl, substitute old_id new_id e)
  | List expr_lst -> List (List.map (substitute old_id new_id) expr_lst)
  | ListCons (e1, e2) -> ListCons (substitute old_id new_id e1, substitute old_id new_id e2)
  | Assert e -> Assert (substitute old_id new_id e)
  | Assume e -> Assume (substitute old_id new_id e)
  | SetCell (e1, e2) -> SetCell (substitute old_id new_id e1, substitute old_id new_id e2)
  | GetCell e -> GetCell (substitute old_id new_id e)
  | NewCell e -> NewCell (substitute old_id new_id e) 

let rec desugar_state (e : expr) : expr = 
  let transform_funsig (Funsig (_, params, fun_expr)) = 
    Function (params, fun_expr)
  in
  let transform_rec_funsig (Funsig (fun_name, params, fun_expr)) = 
    let self_ident = Ident ("~self_" ^ string_of_int (counter := !counter + 1; !counter)) in
    (Function (self_ident :: params, substitute fun_name self_ident fun_expr), fun_name)
  in
  match e with
  | Int _ | Bool _ | Input -> 
    Appl (pure_fun, e)
  | Var v -> 
    (* TODO: Maybe remove aliasing for var? Can't think of a reason why this is necessary *)
    let e_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    Let (e_ident, Var v, Appl (pure_fun, Var e_ident))
  | Function (id_lst, e) ->
    let fun_body_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let desugar_body = Let (fun_body_ident, desugar_state e, Var fun_body_ident) in
    Appl (pure_fun, Function (id_lst, desugar_body))
  | Appl (e1, e2) -> 
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Appl (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Let (x, e1, e2) -> 
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_desugar = Let (e2_ident, desugar_state e2, Var e2_ident) in
    let e1_bind_body = Function ([x], e2_desugar) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    Let (e1_ident, desugar_state e1, e1_bind)
  | LetRecFun (sig_lst, e) ->
    begin
      let sig_name_lst = List.map transform_rec_funsig sig_lst in 
      let folder (elm : expr * ident) (acc : expr) : expr =
        let (f_body, fun_name) = elm in
        let rec_ident = Ident ("~rec_" ^ string_of_int (counter := !counter + 1; !counter)) in
        let rec_body = Let (rec_ident, f_body, Appl (Var rec_ident, Var rec_ident)) in
        Let (fun_name, rec_body, acc)
      in
      let let_equiv = List.fold_right folder sig_name_lst e in
      desugar_state let_equiv
    end
  | LetFun (Funsig (fun_name, _, _) as fun_sig, e) ->
    begin
      let func = transform_funsig fun_sig in
      let let_equiv = Let (fun_name, func, e) in
      desugar_state let_equiv
    end
  | LetWithType (x, e1, e2, type_decl) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let dummy_ident = Ident ("~dummy_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_desugar = Let (e2_ident, desugar_state e2, Var e2_ident) in
    let type_check = LetWithType (dummy_ident, Var x, e2_desugar, type_decl) in
    let e1_bind_body = Function ([x], type_check) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    Let (e1_ident, desugar_state e1, e1_bind)
  | LetRecFunWithType (sig_lst, e, type_decl_lst) ->
    begin
      let sig_name_lst = List.map transform_rec_funsig sig_lst in 
      let sig_name_with_type = List.combine sig_name_lst type_decl_lst in
      let folder (elm : (expr * ident) * type_decl) (acc : expr) : expr =
        let ((f_body, fun_name), f_type) = elm in
        let rec_ident = Ident ("~rec_" ^ string_of_int (counter := !counter + 1; !counter)) in
        let rec_body = Let (rec_ident, f_body, Appl (Var rec_ident, Var rec_ident)) in
        LetWithType (fun_name, rec_body, acc, f_type)
      in
      let let_equiv = List.fold_right folder sig_name_with_type e in
      desugar_state let_equiv
    end
  | LetFunWithType (Funsig (fun_name, _, _) as fun_sig, e, type_decl) ->
    begin
      let func = transform_funsig fun_sig in
      let let_equiv = LetWithType (fun_name, func, e, type_decl) in
      desugar_state let_equiv
    end
  | Plus (e1, e2) -> 
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Plus (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Minus (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Minus (pure_fun, Appl (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Times (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Times (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Divide (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Divide (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Modulus (e1, e2) -> 
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Modulus (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Equal (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Equal (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Neq (e1, e2) -> 
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Neq (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | LessThan (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, LessThan (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Leq (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Leq (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | GreaterThan (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, GreaterThan (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Geq (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Geq (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | And (e1, e2) -> 
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, And (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Or (e1, e2) -> 
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, Or (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Not e -> 
    let e_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e_bind_body = Function ([pure_arg1], Appl (pure_fun, Not (Var pure_arg1))) in
    let e_bind = Appl (Appl (bind_fun, Var e_ident), e_bind_body) in
    Let (e_ident, desugar_state e, e_bind)
  | If (e1, e2, e3) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e3_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg3 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e3_bind_body = Function ([pure_arg3], Appl (pure_fun, If (Var pure_arg1, Var pure_arg2, Var pure_arg3))) in
    let e3_bind = Appl (Appl (bind_fun, Var e3_ident), e3_bind_body) in
    let e2_bind_body = Function ([pure_arg2], e3_bind) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e3_desugar = Let (e3_ident, desugar_state e3, e1_bind) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e3_desugar) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Record m -> 
    (* TODO: use the order in which the labels are defined by the user *)
    let all_bindings = Ident_map.bindings m in
    let combined_info = 
      List.map 
      (fun (Ident l, e) -> 
        let normalized_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
        let pure_arg = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
        (pure_arg, normalized_ident, (Ident l, e)))
      all_bindings
    in
    let updated_bindings = 
      List.map 
      (fun (id', _, (id, _)) -> (id, Var id'))
      combined_info
    in
    let updated_map = Ident_map.of_enum (List.enum updated_bindings) in
    let normalized_keys_and_expr = 
      List.map 
      (fun (arg_name, normalized_var, (_, e)) -> (arg_name, normalized_var, e))
      combined_info
    in
    let folder (elm : ident * ident * expr) (acc : expr) : expr = 
      let (cur_arg_name, normalized_var, cur_expr) = elm in
      Let (normalized_var, 
           desugar_state cur_expr, 
           (Appl (Appl (bind_fun, Var normalized_var), Function ([cur_arg_name], acc))))
    in
    let normalized_rec = List.fold_right folder normalized_keys_and_expr (Appl (pure_fun, Record updated_map)) in
    normalized_rec
  | RecordProj (e, l) -> 
    let e_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e_bind_body = Function ([pure_arg1], Appl (pure_fun, RecordProj (Var pure_arg1, l))) in
    let e_bind = Appl (Appl (bind_fun, Var e_ident), e_bind_body) in
    Let (e_ident, desugar_state e, e_bind)
  | Match (e, pattern_expr_lst) ->
    let e_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_e = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let combined_lst = 
      List.map 
      (fun (cur_pat, exp) -> 
        let normalized_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
        let pure_arg = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
        (cur_pat, pure_arg, normalized_ident, exp)
      ) 
      pattern_expr_lst 
    in
    let updated_pat_expr_lst = List.map (fun (cur_pat, pure_arg, _, _) -> (cur_pat, Var pure_arg)) combined_lst in
    let normalized_pat_expr = List.map (fun (_, pure_arg, normalized_ident, exp) -> (pure_arg, normalized_ident, exp)) combined_lst in
    let folder (elm : ident * ident * expr) (acc : expr) : expr = 
      let (cur_arg_name, normalized_var, cur_expr) = elm in
      Let (normalized_var, 
           desugar_state cur_expr, 
           (Appl (Appl (bind_fun, Var normalized_var), Function ([cur_arg_name], acc))))
    in
    let normalize_match = 
        List.fold_right folder normalized_pat_expr 
        (Appl (pure_fun, Match (Var e_ident, updated_pat_expr_lst)))
    in
    let let_body = Appl(Appl (bind_fun, Var e_ident), Function ([pure_e], normalize_match)) in
    Let (e_ident, desugar_state e, let_body)
  | VariantExpr (lbl, e) -> 
    let e_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e_bind_body = Function ([pure_arg1], Appl (pure_fun, VariantExpr (lbl, Var pure_arg1))) in
    let e_bind = Appl (Appl (bind_fun, Var e_ident), e_bind_body) in
    Let (e_ident, desugar_state e, e_bind)
  | List expr_lst -> 
    let combined_lst = 
      List.map 
      (fun exp -> 
        let normalized_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
        let pure_arg = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
        (pure_arg, normalized_ident, exp)
      ) 
      expr_lst
    in
    let updated_lst = List.map (fun (pure_arg, _, _) -> Var pure_arg) combined_lst in
    let folder (elm : ident * ident * expr) (acc : expr) : expr = 
      let (cur_arg_name, normalized_var, cur_expr) = elm in
      Let (normalized_var, 
           desugar_state cur_expr, 
           (Appl (Appl (bind_fun, Var normalized_var), Function ([cur_arg_name], acc))))
    in
    let normalized_lst = List.fold_right folder combined_lst (Appl (pure_fun, List updated_lst)) in
    normalized_lst
  | ListCons (e1, e2) ->
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (pure_fun, ListCons (Var pure_arg1, Var pure_arg2))) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | Assert e -> Assert (typed_non_to_on e)
  | Assume e -> Assume (typed_non_to_on e)
  | SetCell (e1, e2) -> 
    let e1_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg2 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e2_bind_body = Function ([pure_arg2], Appl (Appl (set_cell_fun, Var pure_arg1), Var pure_arg2)) in
    let e2_bind = Appl (Appl (bind_fun, Var e2_ident), e2_bind_body) in
    let e1_bind_body = Function ([pure_arg1], e2_bind) in
    let e1_bind = Appl (Appl (bind_fun, Var e1_ident), e1_bind_body) in
    let e2_desugar = Let (e2_ident, desugar_state e2, e1_bind) in
    Let (e1_ident, desugar_state e1, e2_desugar)
  | GetCell e -> 
    let e_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e_bind_body = Function ([pure_arg1], Appl (get_cell_fun, Var pure_arg1)) in
    let e_bind = Appl (Appl (bind_fun, Var e_ident), e_bind_body) in
    Let (e_ident, desugar_state e, e_bind)
  | NewCell e -> 
    let e_ident = Ident ("~normalized_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let pure_arg1 = Ident ("~pure_arg_" ^ string_of_int (counter := !counter + 1; !counter)) in
    let e_bind_body = Function ([pure_arg1], Appl (new_cell_fun, Var pure_arg1)) in
    let e_bind = Appl (Appl (bind_fun, Var e_ident), e_bind_body) in
    Let (e_ident, desugar_state e, e_bind)

let add_library_code (e : expr) : expr = 
  let library_code = 
    let ch = open_in "library_code.natodefa" in
    let Program (parsed_code, _) = On_parse.parse_program ch in
    close_in ch;
    parsed_code
  in
  let rec traverse_code (c : expr) : expr = 
    match c with
    | Var (Ident v) ->
      if (v = "replaceWithUserExpr") 
      then 
        let init_state_rec = 
          Ident_map.empty
          |> Ident_map.add (Ident "sm") (Var (Ident "empty_b_tree"))
          |> Ident_map.add (Ident "next_cid") (Int 0)
        in 
        Let (Ident "~state_0", Record init_state_rec, e) 
      else c
    | Function (id_lst, e) -> Function (id_lst, traverse_code e)
    | Let (x, e1, e2) -> Let (x, traverse_code e1, traverse_code e2)
    | LetRecFun (sig_lst, e) -> LetRecFun (sig_lst, traverse_code e)
    | LetFun (fun_sig, e) -> LetFun (fun_sig, traverse_code e)
    | _ -> c
    in
    traverse_code library_code

let translate_typed_prog (p : program) : expr = 
  let (Program (e, state_mode)) = p in
  match state_mode with
  | Stateful -> 
    let desugared_code = desugar_state e in
    let stateful_expr_ident = Ident "~stateful_user_expr" in
    let run_expr_with_init_state = Let (stateful_expr_ident, desugared_code, Appl (Var stateful_expr_ident, Var (Ident "init_state"))) in
    let e' = add_library_code run_expr_with_init_state in
    (* let e' = run_expr_with_init_state in *)
    typed_non_to_on e'
  | Stateless -> typed_non_to_on e

(* let translate_typed_prog (p : program) : expr = 
  let (Program (e, _)) = p in e *)


