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

let main () : unit =
  let options = parse_args () in
  match options.ta_mode with
  | Odefa_natural_to_odefa ->
    begin
      let on_expr = On_parse.parse_program IO.stdin in
      (* print_endline (On_ast_pp.show_expr on_expr); *)
      let no_type_on_expr = typed_non_to_on @@ semantic_type_of on_expr in
      let () = print_endline @@ On_to_odefa.show_expr no_type_on_expr in
      let (odefa_expr, _) = On_to_odefa.translate no_type_on_expr in
      let result_expr =
        if options.ta_parseable then
          map_expr_vars purge_special_symbols odefa_expr
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
