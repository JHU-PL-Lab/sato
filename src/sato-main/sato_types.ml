(** The mode that Sato should operate in.  Currently the available modes are:
    - Type checking: Looking for type errors and other assertion errors
    - Test generation: Looking for input sequences (the same as the origina DDSE)
 *)
type sato_mode =
  | Type_checking | Test_generation
;;

(** The type of output of generation. *)
type output_format =
  | Standard | Compact | JSON
;;