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

  (** Merge two error trees as if they are part of an AND operation.
      In an AND operation, all values must be true for the op to return true.
      Therefore if one error has a false value, the error tree is false. *)
  val add_and : t -> t -> t;;

  (** Merge two error trees as if they are part of an OR operation.
      In an OR operation, only one value needs to be true for the op to be true
      so only when all errors have a false value can the error tree be false. *)
  val add_or : t -> t -> t;;

  (** Create a new list with no errors. *)
  val empty : t;;

  (** Create a one-element list from a single error. *)
  val singleton : Err.t -> t;;

  (** Returns true if there are no errors in the list, false otherwise. *)
  val is_empty : t -> bool;;

  (** Returns the number of errors in the list. *)
  val count : t -> int;;

  (** Pretty-prints the string list. *)
  val pp : t Pp_utils.pretty_printer;;

  (** Shows the error list as a string. *)
  val show : t -> string;;

  (** Returns true if the error is a member of the error list, else false. *)
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

  let singleton error = [error];;

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