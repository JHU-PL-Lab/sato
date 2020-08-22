open Jhupllib;;

exception Parse_failure of string;;

type t;;

val eq : t -> t -> bool;;

val parse : string -> t;;

val pp : t Pp_utils.pretty_printer;;

val show : t -> string;;
