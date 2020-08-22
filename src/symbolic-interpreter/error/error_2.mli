open Jhupllib;;

exception Parse_failure of string;;

type t;;

(** Equality of two errors. *)
val eq : t -> t -> bool;;

(** Parse an error from a string. *)
val parse : string -> t;;

(** Pretty-prints an error. *)
val pp : t Pp_utils.pretty_printer;;

(** Show an error as a string. *)
val show : t -> string;;