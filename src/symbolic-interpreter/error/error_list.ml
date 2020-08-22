open Batteries;;
open Jhupllib;;

module type Error_2 = sig
  type t;;
  val eq : t -> t -> bool;;
  val parse : string -> t;;
  val pp : t Pp_utils.pretty_printer;;
  val show : t -> string;;
end;;

module type Error_list = sig
  module Err : Error_2;;

  type t;;

  val add_and : t -> t -> t;;

  val add_or : t -> t -> t;;

  val empty : t;;

  val is_empty : t -> bool;;

  val count : t -> int;;

  val pp : t Pp_utils.pretty_printer;;

  val show : t -> string;;

  val mem : Err.t -> t -> bool;;
end;;

module Make(Error : Error_2) : Error_list = struct
  module Err = Error;;

  type t = Err.t list;;

  let add_and elist_1 elist_2 =
    match (elist_1, elist_2) with
    | ([], []) -> []
    | (_, []) -> elist_1
    | ([], _) -> elist_2
    | (_, _) -> elist_1 @ elist_2
  ;;

  let add_or elist_1 elist_2 =
    match (elist_1, elist_2) with
    | ([], []) -> []
    | (_, []) -> []
    | ([], _) -> []
    | (_, _) -> elist_1 @ elist_2
  ;;

  let empty = [];;

  let is_empty = List.is_empty;;

  let count = List.length;;

  let pp formatter error_list =
    Pp_utils.pp_concat_sep
      "\n-------------------\n"
      (fun formatter err -> Err.pp formatter err)
      formatter
      (List.enum error_list)
  ;;

  let show = Pp_utils.pp_to_string pp;;

  let mem error error_list =
    List.exists (Err.eq error) error_list
  ;;
end;;