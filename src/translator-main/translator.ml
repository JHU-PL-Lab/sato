(**
   A front-end for the parser library.
*)
open Batteries;;

open Odefa_ast;;
open Odefa_natural;;
open Ton_to_on;;

open Ast_tools;;
open Translator_options;;

(** Removes from a variable any special symbols introduced by the translation
    process which are not parseable identifiers. *)
let purge_special_symbols (x : Ast.Var.t) : Ast.Var.t =
  let Ast.Var(Ast.Ident(s), fs) = x in
  let s' =
    s
    |> String.replace_chars
      (fun c ->
         match c with
        | '~' -> "___"
        | _ -> String.of_char c
      )
  in
  Ast.Var(Ast.Ident(s'), fs)
;;

(* A helper function to purge all the tildes in label names *)
let rec purge_special_symbols_in_lbls (e : Ast.expr) : Ast.expr =
  let (Expr cls) = e in
  let transform_clause (c : Ast.clause) : Ast.clause =
      let (Clause (c_var, clause_body)) = c in
      let clause_body' = 
        match clause_body with
        | Value_body v -> 
          begin
          let v' = 
            match v with
              | Value_record (Record_value r) ->
                let entries = Ast.Ident_map.bindings r in
                let mapper (Ast.Ident k, v) = 
                  let k' =
                  k
                  |> String.replace_chars
                    (fun c ->
                      match c with
                      | '~' -> "___"
                      | _ -> String.of_char c
                    )
                  in (Ast.Ident k', v)
                in
                let entries' = List.map mapper entries in
                let r' = Ast.Ident_map.of_enum (List.enum entries') in
                Ast.Value_record (Record_value r')
              | Value_function (Function_value (f_var, f_expr)) -> 
                let f_expr' = purge_special_symbols_in_lbls f_expr in
                Ast.Value_function (Function_value (f_var, f_expr'))
              | Value_int _ | Value_bool _ -> v
          in
            Ast.Value_body v'
          end
        | Projection_body (v, Ast.Ident proj_lbl) -> 
          let proj_lbl' = 
            proj_lbl
            |> String.replace_chars
              (fun c ->
                match c with
                | '~' -> "___"
                | _ -> String.of_char c
              )
          in Projection_body (v, Ast.Ident proj_lbl')
        | Conditional_body (v, e1, e2) ->
          Conditional_body (v, purge_special_symbols_in_lbls e1, purge_special_symbols_in_lbls e2)
        | Var_body _ | Input_body | Appl_body _ | Match_body _
        | Binary_operation_body _ | Abort_body | Assume_body _ -> clause_body
      in
      Clause (c_var, clause_body') 
  in
  let transformed_cls = List.map transform_clause cls in
  Expr transformed_cls
;;

let main () : unit =
  let options = parse_args () in
  match options.ta_mode with
  | Odefa_natural_to_odefa ->
    begin
      let on_expr = On_parse.parse_program IO.stdin in
      (* print_endline (On_ast_pp.show_expr on_expr); *)
      (* print_endline (On_ast_pp.show_expr (typed_non_to_on on_expr)); *)
      let no_type_on_expr = typed_non_to_on on_expr in
      let (odefa_expr, _) = On_to_odefa.translate no_type_on_expr in
      let result_expr =
        if options.ta_parseable then
          map_expr_vars purge_special_symbols odefa_expr
          |> purge_special_symbols_in_lbls
        else
          odefa_expr
      in
      let expr_string = Ast_pp.show_expr result_expr in
      print_endline expr_string;
      print_endline "";
    end
  | Scheme_to_odefa_natural ->
    raise @@ Jhupllib.Utils.Not_yet_implemented "scheme-to-odefa-natural"
;;

main ();;
