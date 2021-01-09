let major_version = 0;;

let minor_version = 9;;

let patch_version = 0;;

let ascii_art =
  "+---------------------------------------+\n" ^
  "|    _____    ___     _______   ______  |\n" ^
  "|   / ___/   /   |   /__  __/  / __  /  |\n" ^
  "|   \\ \\     / /| |     / /    / / / /   |\n" ^
  "|  __/ /   / __  |    / /    / /_/ /    |\n" ^
  "| /___/   /_/  |_|   /_/    /_____/     |\n" ^
  "|                                       |\n" ^
  "+---------------------------------------+\n"
;;

let version_str =
  ascii_art ^
  (Printf.sprintf "> Version %d.%d.%d\n" major_version minor_version patch_version) ^
  "> Licensed under Apache by the Johns Hopkins Programming Language Lab"
;;