open Batteries;;
open Jhupllib;;

open On_ast;;

(* TODO: Keep replacing " " with "@ " in format strings *)

let pp_label formatter (Label l) =
  Format.pp_print_string formatter l
;;

let pp_ident formatter (Ident s) =
  Format.pp_print_string formatter s
;;

let pp_ident_option formatter id_option =
  match id_option with
  | Some id -> pp_ident formatter id
  | None -> Format.pp_print_string formatter "(none)"
;;

let pp_ident_set formatter set =
  Pp_utils.pp_concat_sep_delim
    "{" "}" ","
    (fun formatter v -> pp_ident formatter v)
    formatter
    (Ident_set.enum set)
;;

let pp_ident_map pp_value formatter map =
  let open Format in
  Pp_utils.pp_concat_sep_delim
    "{" "}" ","
    (fun formatter (k,v) ->
       pp_ident formatter k;
       pp_print_string formatter " = ";
       pp_value formatter v)
    formatter
    (Ident_map.enum map)
;;

let pp_ident_list formatter list =
  Pp_utils.pp_concat_sep
    " "
    (fun formatter x -> pp_ident formatter x)
    formatter
    (List.enum list)
;;

let pp_variant_label formatter (Variant_label label) =
  Format.fprintf formatter "`%s" label
;;

let rec pp_funsig formatter (Funsig (x, ident_list, e)) =
  Format.fprintf formatter "%a@ %a =@ @[%a@]"
    pp_ident x pp_ident_list ident_list pp_expr e

and pp_variant_content formatter (variant_label, ident) =
  Format.fprintf formatter "%a@ (%a)"
    pp_variant_label variant_label
    pp_ident ident

and pp_pattern formatter pattern =
  match pattern with
  | AnyPat -> Format.pp_print_string formatter "any"
  | IntPat -> Format.pp_print_string formatter "int"
  | BoolPat -> Format.pp_print_string formatter "bool"
  | RecPat record ->
    Format.fprintf formatter "%a" (pp_ident_map pp_ident_option) record
  | VariantPat (lbl, var) ->
    Format.fprintf formatter "%a" pp_variant_content (lbl, var)
  | VarPat ident -> Format.fprintf formatter "%a" pp_ident ident
  | FunPat -> Format.pp_print_string formatter "fun"
  | EmptyLstPat -> Format.pp_print_string formatter "[]"
  | LstDestructPat (hd_var, tl_var) ->
    Format.fprintf formatter "%a@ ::@ %a"
      pp_ident hd_var pp_ident tl_var

and pp_expr formatter expr =
  match expr with
  | Int n -> Format.pp_print_int formatter n
  | Bool b -> Format.pp_print_bool formatter b
  | Var x -> pp_ident formatter x
  | Function (x_list, e) ->
    Format.fprintf formatter "fun %a ->@ @[<2>%a@]"
      pp_ident_list x_list pp_expr e
  | Input -> Format.pp_print_string formatter "input"
  | Appl (e1, e2) ->
    Format.fprintf formatter "%a %a"
      pp_expr e1 pp_expr e2
  | Let (ident, e1, e2) -> 
    Format.fprintf formatter "let@ %a =@ %a@ in@ @[%a@]"
      pp_ident ident pp_expr e1 pp_expr e2
  | LetRecFun (funsig_lst, e) ->
    let pp_funsig_list formatter funsig_lst =
      Pp_utils.pp_concat_sep
        " with "
        pp_funsig
        formatter
        (List.enum funsig_lst)
    in
    Format.fprintf formatter "let rec@ %a@ in@ @[%a@]"
      pp_funsig_list funsig_lst pp_expr e
  | LetFun (funsig, e) ->
    Format.fprintf formatter "let@ %a@ in@ @[%a@]"
      pp_funsig funsig pp_expr e
  | Plus (e1, e2) ->
    Format.fprintf formatter "(%a + %a)" pp_expr e1 pp_expr e2
  | Minus (e1, e2) ->
    Format.fprintf formatter "(%a - %a)" pp_expr e1 pp_expr e2
  | Times (e1, e2) ->
    Format.fprintf formatter "(%a * %a)" pp_expr e1 pp_expr e2
  | Divide (e1, e2) ->
    Format.fprintf formatter "(%a / %a)" pp_expr e1 pp_expr e2
  | Modulus (e1, e2) ->
    Format.fprintf formatter "(%a %% %a)" pp_expr e1 pp_expr e2
  | Equal (e1, e2) ->
    Format.fprintf formatter "(%a == %a)" pp_expr e1 pp_expr e2
  | Neq (e1, e2) ->
    Format.fprintf formatter "(%a <> %a)" pp_expr e1 pp_expr e2
  | LessThan (e1, e2) ->
    Format.fprintf formatter "(%a < %a)" pp_expr e1 pp_expr e2
  | Leq (e1, e2) ->
    Format.fprintf formatter "(%a <= %a)" pp_expr e1 pp_expr e2
  | GreaterThan (e1, e2) ->
    Format.fprintf formatter "(%a > %a)" pp_expr e1 pp_expr e2
  | Geq (e1, e2) ->
    Format.fprintf formatter "(%a >= %a)" pp_expr e1 pp_expr e2
  | And (e1, e2) ->
    Format.fprintf formatter "(%a and %a)" pp_expr e1 pp_expr e2
  | Or (e1, e2) ->
    Format.fprintf formatter "(%a or %a)" pp_expr e1 pp_expr e2
  | Not e ->
    Format.fprintf formatter "(not %a)" pp_expr e
  | If (pred, e1, e2) ->
    Format.fprintf formatter "if@ %a@ then@ @[<2>%a@]@ else @[<2>%a@]"
      pp_expr pred pp_expr e1 pp_expr e2
  | Record record ->
    pp_ident_map pp_expr formatter record
  | RecordProj (record_expr, lbl) ->
    Format.fprintf formatter "%a.%a"
      pp_expr record_expr pp_label lbl
  | Match (e, pattern_expr_list) ->
    let pp_pattern_expr formatter (pattern, expr) =
      Format.fprintf formatter "@[| %a ->@ @[<2>%a@]@]"
        pp_pattern pattern pp_expr expr
    in
    let pp_pattern_expr_lst formatter pat_expr_list =
      Pp_utils.pp_concat_sep
        ""
        pp_pattern_expr
        formatter
        (List.enum pat_expr_list)
    in
    Format.fprintf formatter "match@ %a@ with@ @[%a@]@ end"
      pp_expr e pp_pattern_expr_lst pattern_expr_list
  | VariantExpr (variant_lbl, e) ->
    Format.fprintf formatter "%a@ (%a)"
      pp_variant_label variant_lbl pp_expr e
  | List e_list ->
    Pp_utils.pp_concat_sep_delim
      "[" "]" ","
      (fun formatter e -> pp_expr formatter e)
      formatter
      (List.enum e_list)
  | ListCons (e1, e2) ->
    Format.fprintf formatter "%a@ ::@ %a"
      pp_expr e1 pp_expr e2
  | Assert e ->
    Format.fprintf formatter "assert@ %a" pp_expr e
;;

let show_ident = Pp_utils.pp_to_string pp_ident;;
let show_expr = Pp_utils.pp_to_string pp_expr;;
let show_pattern = Pp_utils.pp_to_string pp_pattern;;

let pp_on_type formatter (on_type : On_ast.type_sig) =
  match on_type with
  | TopType -> Format.pp_print_string formatter "Any"
  | IntType -> Format.pp_print_string formatter "Integer"
  | BoolType -> Format.pp_print_string formatter "Boolean"
  | FunType -> Format.pp_print_string formatter "Function"
  | ListType -> Format.pp_print_string formatter "List"
  | RecType lbls -> Format.fprintf formatter "Record %a" pp_ident_set lbls
  | VariantType lbl -> Format.fprintf formatter "Variant %a" pp_variant_label lbl
;;

let show_on_type = Pp_utils.pp_to_string pp_on_type;;