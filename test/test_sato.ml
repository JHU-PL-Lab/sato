open Batteries;;
open OUnit2;;

exception File_test_creation_failure of string;;

let input_root = "test/test-sources";;
let output_root = "test/test-outputs";;

let parse_arguments filename : string list =
  (* let module String_map = Map.Make(String) in *)
  let arg_from_str str =
    let str' = String.trim str in
    if String.starts_with str' "##" then
      str'
      |> (fun s -> String.tail s 2)
      |> String.trim
      |> Option.some
    else None
  in
  filename
  |> File.lines_of
  |> Enum.filter_map arg_from_str
  |> Enum.map (String.split ~by:" ")
  |> Enum.map (fun (s1, s2) -> (String.trim s1, String.trim s2))
  |> Enum.map (fun (name, arg) -> "--" ^ (String.lowercase name) ^ "=" ^ arg)
  |> List.of_enum
;;

let make_test (in_file, out_file) =
  let args = parse_arguments in_file in
  let expected =
    let in_stream = File.open_in out_file in
    let expected_str = BatIO.read_all in_stream in
    BatIO.close_in in_stream;
    expected_str
  in
  let test_thunk ctxt =
    assert_command
      ~foutput:(fun (cstream : char Stream.t) : unit ->
        let chars_ref = ref [] in
        Stream.iter (fun c -> chars_ref := c :: !chars_ref) cstream;
        let actual = String.of_list @@ List.rev !chars_ref in
        assert_equal
          ~msg:(Printf.sprintf "./type_checker %s%s%s"
                (String.join " " args)
                (if List.length args > 0 then " " else "")
                in_file)
          ~printer:(fun s -> "\n" ^ s)
          ~cmp:String.equal
          expected
          actual
      )
    ~ctxt
    "./type_checker"
    (args @ [in_file])
  in
  in_file >:: test_thunk
;;

let make_tests_from_dir dir_name =
  let input_dir = input_root ^ Filename.dir_sep ^ dir_name in
  let output_dir = output_root ^ Filename.dir_sep ^ dir_name in
  if Sys.file_exists input_dir && Sys.file_exists output_dir
    && Sys.is_directory input_dir && Sys.is_directory output_dir then
    input_dir
    |> Sys.files_of
    |> Enum.filter_map
      (fun filename ->
        let in_file = input_dir ^ Filename.dir_sep ^ filename in
        if Sys.is_directory in_file then None
        else if not @@ String.ends_with in_file ".odefa"
              && not @@ String.ends_with in_file ".natodefa" then begin
          None
        end else begin
          let out_file =
            filename
            |> Filename.remove_extension
            |> (fun f -> output_dir ^ Filename.dir_sep ^ f ^ ".out")
          in
          if not @@ Sys.file_exists out_file then
            raise @@ File_test_creation_failure
              (Format.sprintf "No corresponding output file %s" out_file)
          else
            Some (in_file, out_file)
        end
      )
    |> Enum.map make_test
    |> List.of_enum
  else
    raise @@ File_test_creation_failure
      (Format.sprintf "Test file directory %s does not exist" dir_name)
;;

let tests =
  "Test Files" >::: (
    make_tests_from_dir ""
    (* @ make_tests_from_dir "odefa-basic" *)
    @ make_tests_from_dir "odefa-types"
    (* @ make_tests_from_dir "natodefa-basic" *)
    (* @ make_tests_from_dir "natodefa-types" *)
  )
;;