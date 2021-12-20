let new_rec_fun_with_type fun_sig_and_type let_body =
  let fun_sig_list = List.map fst fun_sig_and_type in 
  let fun_type_list = List.map snd fun_sig_and_type in
  LetRecFunWithType (fun_sig_list, let_body, fun_type_list)
;;

let new_let_fun_with_type fun_sig_and_type let_body =
  let fun_sig, fun_type = fun_sig_and_type in
  LetFunWithType (fun_sig, let_body, fun_type)
;;

let new_fun_with_type 
  (fun_name : ident) 
  (typed_param_list : (ident * expr) list) 
  (return_type : expr)
  (fun_body : expr) = 
  let param_list = List.map fst typed_param_list in
  let (type_list : expr list) = List.map snd typed_param_list in
  let function_type_p = 
    match type_list with
    | [] -> failwith "undefined"
    | _ -> 
      let reversed_list = List.rev type_list in
      let last_type = List.hd reversed_list in
      let accumulator = TypeArrow (last_type, return_type) in
      List.fold_left
          (fun acc -> fun t -> TypeArrow (t, acc)) accumulator (List.tl reversed_list)
  in
  (Funsig (fun_name, param_list, fun_body), function_type_p)
;; 

let new_dependent_fun   
  (fun_name : ident) 
  (typed_param : (ident * expr)) 
  (return_type : expr)
  (fun_body : expr) = 
  let (param, _) = typed_param in
  (Funsig (fun_name, [param], fun_body), TypeArrowD (typed_param, return_type))