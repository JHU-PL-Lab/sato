open Batteries;;

open Odefa_ast;;
open Ast;;

open Translator_utils.TranslationMonad;;

let add_abort_expr cond_var =
  let%bind abort_var = fresh_var "ab" in
  let abort_clause = Clause(abort_var, Abort_body [cond_var]) in
  return @@ Expr([abort_clause]);
;;

(** Update any abort clause variables with a new variable. This is called
    when a conditional constraint is formed, since the inner conditional
    may itself have abort clauses encoded with the identifying variable. *)
let rec change_abort_vars
    (old_var : var)
    (new_var : var)
    (clause : clause)
  : clause =
  let Clause(v, body) = clause in
  match body with
  | Value_body value ->
    begin
      match value with
      | Value_function f ->
        let Function_value(arg, Expr(f_body)) = f in
        let f_body' = List.map (change_abort_vars old_var new_var) f_body in
        let value' = Value_function (Function_value (arg, Expr(f_body'))) in
        Clause(v, Value_body value')
      | _ -> clause
    end
  | Conditional_body (pred, e1, e2) ->
    let Expr(cl1) = e1 in
    let Expr(cl2) = e2 in
    let cl1' = List.map (change_abort_vars old_var new_var) cl1 in
    let cl2' = List.map (change_abort_vars old_var new_var) cl2 in
    let body' = Conditional_body (pred, Expr(cl1'), Expr(cl2')) in
    Clause (v, body')
  | Abort_body var_list ->
    let var_list' =
      List.map
        (fun v -> if equal_var v old_var then new_var else v)
         var_list
    in
    Clause (v, Abort_body var_list')
  | _ -> clause
;;

(*
let rec instrument_zero
    (clause : clause)
  : (clause list) m =
  match 
  let Clause(v, body) = clause in
  match body with
  | Value_body value ->
    begin
      match value with
      | Value_function f ->
        let Function_value(arg, Expr(f_body)) = f in
        let f_body' = List.map (instrument_zero clause) f_body in
        let value' = Value_function (Function_value (arg, Expr(f_body'))) in
        return @@ Clause(v, Value_body value')
      | _ -> return @@ clause
    end
  | Conditional_body (pred, e1, e2) ->
    let Expr(cl1) = e1 in
    let Expr(cl2) = e2 in
    let cl1' = List.map instrument_zero cl1 in
    let cl2' = List.map instrument_zero cl2 in
    let body' = Conditional_body (pred, Expr(cl1'), Expr(cl2')) in
    return @@ Clause (v, body')
  | Binary_operation_body (x1, op, x2) ->
    begin
      match op with
      | Binary_operator_divide | Binary_operator_modulus ->
        (* Variables *)
        let%bind b1 = fresh_var "b_zl" in
        let%bind b2 = fresh_var "b_zr" in
        let%bind b = fresh_var "b_z" in
        (* Clauses *)
        let b1_cls = Clause(b1, Binary_operation_body (x1, Binary_operator_less_than, x2)) in
        let b2_cls = Clause(b2, Bianry_operation_body (x2, Binary_operator_less_than, x1)) in
        let b_cls = Clause(b, Binary_operation_body (b1, Binary_operator_and, b2)) in
        (* Conditional *)
        let%bind cz_binop = fresh_var "cz_binop" in
        let%bind () = add_instrument_var_pair cz_binop v in
        let%bind t_path = return @@ Expr([Clause(c_binop, body)]) in
        let%bind f_path = add_abort_expr v in
        let c_cls = Clause(v, Conditional_body(m, t_path, f_path)) in
        let%bind cont = instrument_clauses clauses' in
        return @@ [m1_cls; m2_cls; m_cls; c_cls] @ cont
      | _ ->
        return @@ clause
    end
  | _ ->
    return @@ clause
;;
*)

let rec instrument_clauses
    (c_list : clause list)
  : (clause list) m =
  match c_list with
  | clause :: clauses' ->
    begin
      let Clause(v, body) = clause in
      match body with
      | Value_body value ->
        begin
          match value with
          | Value_function f ->
            let Function_value(arg, Expr(body)) = f in
            let%bind new_body = instrument_clauses body in
            let new_fun_val = Function_value(arg, Expr(new_body)) in
            let new_val_body = Value_body(Value_function(new_fun_val)) in
            let new_clause = Clause(v, new_val_body) in
            let%bind new_clauses' = instrument_clauses clauses' in
            return @@ new_clause :: new_clauses'
          | _ ->
            (* Nothing to constrain *)
            let%bind new_clauses' = instrument_clauses clauses' in
            return @@ clause :: new_clauses'
        end
      | Var_body _
      | Input_body
      | Match_body _
      | Abort_body _ ->
        (* Nothing to constrain *)
        begin
          let%bind new_clauses' = instrument_clauses clauses' in
          return @@ clause :: new_clauses'
        end
      | Binary_operation_body (v1, binop, v2) ->
        begin
          match binop with
          | Binary_operator_plus
          | Binary_operator_minus
          | Binary_operator_times
          | Binary_operator_less_than
          | Binary_operator_less_than_or_equal_to ->
            begin
              (* Variables *)
              let%bind m1 = fresh_var "m_bl" in
              let%bind m2 = fresh_var "m_br" in
              let%bind m = fresh_var "m_b" in
              (* Clauses *)
              let m1_cls = Clause(m1, Match_body(v1, Int_pattern)) in
              let m2_cls = Clause(m2, Match_body(v2, Int_pattern)) in
              let m_bod = Binary_operation_body(m1, Binary_operator_and, m2) in
              let m_cls = Clause(m, m_bod) in
              (* Conditional *)
              let%bind c_binop = fresh_var "c_binop" in
              let%bind () = add_instrument_var_pair c_binop v in
              let%bind t_path = return @@ Expr([Clause(c_binop, body)]) in
              let%bind f_path = add_abort_expr v in
              let c_cls = Clause(v, Conditional_body(m, t_path, f_path)) in
              let%bind cont = instrument_clauses clauses' in
              return @@ [m1_cls; m2_cls; m_cls; c_cls] @ cont
            end
          | Binary_operator_and
          | Binary_operator_or
          | Binary_operator_xor ->
            begin
              (* Variables *)
              let%bind m1 = fresh_var "m_bl" in
              let%bind m2 = fresh_var "m_br" in
              let%bind m = fresh_var "m_b" in
              (* Clauses *)
              let m1_cls = Clause(m1, Match_body(v1, Bool_pattern)) in
              let m2_cls = Clause(m2, Match_body(v2, Bool_pattern)) in
              let m_bod = Binary_operation_body(m1, Binary_operator_and, m2) in
              let m_cls = Clause(m, m_bod) in
              (* Conditional *)
              let%bind c_binop = fresh_var "c_binop" in
              let%bind () = add_instrument_var_pair c_binop v in
              let%bind t_path = return @@ Expr([Clause(c_binop, body)]) in
              let%bind f_path = add_abort_expr v in
              let c_cls = Clause(v, Conditional_body(m, t_path, f_path)) in
              let%bind cont = instrument_clauses clauses' in
              return @@ [m1_cls; m2_cls; m_cls; c_cls] @ cont
            end
          | Binary_operator_divide
          | Binary_operator_modulus ->
            (* TODO: Add inner conditional to constrain divisor to be <> 0 *)
            begin
              (* Variables *)
              let%bind m1 = fresh_var "m_bl" in
              let%bind m2 = fresh_var "m_br" in
              let%bind m = fresh_var "m_b" in
              (* Clauses *)
              let m1_cls = Clause(m1, Match_body(v1, Int_pattern)) in
              let m2_cls = Clause(m2, Match_body(v2, Int_pattern)) in
              let m_bod = Binary_operation_body(m1, Binary_operator_and, m2) in
              let m_cls = Clause(m, m_bod) in
              (* Conditional *)
              let%bind c_binop = fresh_var "c_binop" in
              let%bind () = add_instrument_var_pair c_binop v in
              let%bind t_path = return @@ Expr([Clause(c_binop, body)]) in
              let%bind f_path = add_abort_expr v in
              let c_cls = Clause(v, Conditional_body(m, t_path, f_path)) in
              let%bind cont = instrument_clauses clauses' in
              return @@ [m1_cls; m2_cls; m_cls; c_cls] @ cont
            end
          | Binary_operator_equal_to
          | Binary_operator_not_equal_to ->
            (* TODO: Add or clause to include bools *)
            begin
              (* Variables *)
              let%bind m1 = fresh_var "m_bl" in
              let%bind m2 = fresh_var "m_br" in
              let%bind m = fresh_var "m_b" in
              (* Clauses *)
              let m1_cls = Clause(m1, Match_body(v1, Int_pattern)) in
              let m2_cls = Clause(m2, Match_body(v2, Int_pattern)) in
              let m_bod = Binary_operation_body(m1, Binary_operator_and, m2) in
              let m_cls = Clause(m, m_bod) in
              (* Conditional *)
              let%bind c_binop = fresh_var "c_binop" in
              let%bind () = add_instrument_var_pair c_binop v in
              let%bind t_path = return @@ Expr([Clause(c_binop, body)]) in
              let%bind f_path = add_abort_expr v in
              let c_cls = Clause(v, Conditional_body(m, t_path, f_path)) in
              let%bind cont = instrument_clauses clauses' in
              return @@ [m1_cls; m2_cls; m_cls; c_cls] @ cont
            end
        end
      | Projection_body (r, lbl) ->
        begin
          (*
            proj = r.lbl;
            ==>
            m = r ~ {lbl};
            constrain_proj = m ? (proj = r.l) : (ab = abort);
            ==>
            m = r ~ {lbl};
            proj = m ? ( constrain_proj = r.lbl ) : ( ab = abort );
          *)
          (* Pattern match *)
          let%bind m = fresh_var "m" in
          let rec_pat_set = Ident_set.add lbl Ident_set.empty in
          let rec_pat = Rec_pattern rec_pat_set in
          let m_clause = Clause(m, Match_body(r, rec_pat)) in
          (* Conditional *)
          let%bind c_proj = fresh_var "c_proj" in
          let%bind () = add_instrument_var_pair c_proj v in
          let%bind t_path = return @@ Expr([Clause(c_proj, body)]) in
          let%bind f_path = add_abort_expr v in
          let cond_clause = Clause(v, Conditional_body(m, t_path, f_path)) in
          let%bind cont = instrument_clauses clauses' in
          return @@ [m_clause; cond_clause] @ cont
        end
      | Appl_body (f, _) ->
        begin
          (*
            appl = f x;
            ==>
            m = f ~ fun;
            constrain_appl = m ? (appl = f x) : (ab = abort);
            ==>
            m = f ~ fun;
            appl = m ? ( constrain_appl = f x ) : ( ab = abort );
          *)
          (* Pattern match *)
          let%bind m = fresh_var "m" in
          let m_clause = Clause(m, Match_body(f, Fun_pattern)) in
          (* Conditional *)
          let%bind c_appl = fresh_var "c_appl" in
          let%bind () = add_instrument_var_pair c_appl v in
          let%bind t_path = return @@ Expr([Clause(c_appl, body)]) in
          let%bind f_path = add_abort_expr v in
          let cond_clause = Clause(v, Conditional_body(m, t_path, f_path)) in
          let%bind cont = instrument_clauses clauses' in
          return @@ [m_clause; cond_clause] @ cont
        end
      | Conditional_body (pred, Expr path1, Expr path2) ->
        begin
          (*
            cond = pred ? true_path : false_path;
            ==>
            m = pred ~ bool;
            constrain_cond = m ? (cond = pred ? true_path : false_path)
                               : (ab = abort)
            ==>
            m = pred ~ bool;
            cond = m ? ( constrain_cond = pred ? true_path : false_path )
                     : ( ab = abort );
          *)
          (* Pattern match *)
          let%bind m = fresh_var "m" in
          let m_clause = Clause(m, Match_body(pred, Bool_pattern)) in
          (* Underlying conditional *)
          let%bind path1' = instrument_clauses path1 in
          let%bind path2' = instrument_clauses path2 in
          let body' = Conditional_body(pred, Expr path1', Expr path2') in
          (* Constrain conditional *)
          let%bind c_cond = fresh_var "c_cond" in
          let%bind () = add_instrument_var_pair c_cond v in
          let clause' = Clause (c_cond, body') in
          let clause'' = change_abort_vars v c_cond clause' in
          let%bind t_path = return @@ Expr([clause'']) in
          let%bind f_path = add_abort_expr v in
          let cond_clause = Clause(v, Conditional_body(m, t_path, f_path)) in
          let%bind cont = instrument_clauses clauses' in
          return @@ [m_clause; cond_clause] @ cont
        end
    end
  | [] -> return []
;;

let instrument_odefa (odefa_ast : expr) : (expr * var Var_map.t) =
  let (monad_val : (expr * var Var_map.t) m) =
    (* Transform odefa program *)
    let Expr(odefa_clist) = odefa_ast in
    let%bind trans_clist = instrument_clauses odefa_clist in
    (* Add "~result" to the end of the program *)
    let Clause(last_var, _) = List.last trans_clist in
    let%bind fresh_str = freshness_string in
    let result_var = Ast.Var(Ast.Ident(fresh_str ^ "result"), None) in
    let result_clause = Ast.Clause(result_var, Ast.Var_body(last_var)) in
    let%bind inst_map = instrument_map in
    return (Expr(trans_clist @ [result_clause]), inst_map)
  in
  let context = Translator_utils.new_translation_context () in
  run context monad_val
;;