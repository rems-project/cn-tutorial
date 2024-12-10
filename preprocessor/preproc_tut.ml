
let drop_prefix prefix str =
  if String.starts_with ~prefix str
    then
      let n = String.length prefix in
      let l = String.length str in
      Some (String.trim (String.sub str n (l - n)))
    else None

(* Should we start a new mutant block *)
let start_mutant_block line =
  match drop_prefix "#if" line with
  | Some "!MUTATION" -> true 
  | _                -> false

(* Does this line start a mutant *)
let start_mutant = drop_prefix "#elif"

let start_unit_test line =
  match drop_prefix "#if" line with
  | Some txt -> drop_prefix "CN_TEST" txt (* XXX: space or underscore separator? *)
  | _ -> None

(* Ending for mutant blocks and units tests *)
let end_named_block = String.starts_with ~prefix:"#endif"



(* -------------------------------------------------------------------------- *)

type named_lines = {
  start_line: int;        (* starting line number *)
  name:       string;
  lines:      string list;
}

let finish_named_lines (mu: named_lines) =
  { mu with lines = List.rev mu.lines }

(* Some content and its mutants. *)
type mutant_block = {
  start_line: int;               (* starting line number *)
  orig:       string list;
  variants:   named_lines list;
}

type content =
| Mutants  of mutant_block
| UnitTest of named_lines
| Line     of string

type state = 
| TopLevel
| InMutantOrig of int
| InMutant     of int
| InUnitTest   of (int * string)

(* -------------------------------------------------------------------------- *)

type mode =
  | NoTesting                 (* Remove testing related lines *)
  | MutationTesting           (* Translate to Etna notation *)
  | CollectUnitTest           (* Print only names of unit tests *)
  | ExecuteUnitTest of string (* Print only this specific unit test *)

let rec process_input mode start_line state =
  let mb_line = try Some (read_line()) with End_of_file -> None in
  match mb_line with
  | None ->
    begin
    let mk_error no msg = failwith (Printf.sprintf "%d: %s" no msg) in
    match state with
    | TopLevel          -> ()
    | InMutantOrig n    -> mk_error n "Untermianted mutant block"
    | InMutant n        -> mk_error n "Unterminated mutant block"
    | InUnitTest (n,_)  -> mk_error n "Unterminated unit test"
    end
  | Some line ->
    let new_state =
      match state with
  
      (* start a mutation test *)
      | TopLevel when start_mutant_block line ->
        begin match mode with
        | MutationTesting -> print_endline "//! //"
        | _               -> ()
        end;
        InMutantOrig start_line (* next state *)

      | TopLevel ->
        begin match start_unit_test line with

          (* start a unit test *)
          | Some name ->
            begin match mode with
            | CollectUnitTest -> Printf.printf "CN_TEST%s\n" name
            | _               -> ()
            end;
            InUnitTest (start_line, name) (* next state *)

          (* ordinary top level line *)
          | None ->
            begin match mode with
            | CollectUnitTest -> ()
            | _               -> print_endline line
            end;
            TopLevel (* next state *)
        end

      | InMutantOrig ln ->
        begin match start_mutant line with

        (* Start a mutant *)
        | Some name ->
          begin match mode with
          | MutationTesting -> Printf.printf "//!! %s // //!\n" name
          | _               -> ()
          end;
          InMutant ln (* next state *)

        (* Original part of a mutation block *) 
        | None ->
          begin match mode with
          | CollectUnitTest -> ()
          | _               -> print_endline line
          end;
          InMutantOrig ln (* next state *)
        end

      (* End mutant block *)
      | InMutant ln when end_named_block line ->
        begin match mode with
        | MutationTesting -> print_endline "//"
        | _               -> ()
        end;
        TopLevel (* next state *)

      | InMutant ln ->

        begin match start_mutant line with
        (* Next mutatant *)
        | Some name ->
            begin match mode with
            | MutationTesting -> Printf.printf "// //!! %s // //!\n" name
            | _               -> ()
            end;
            InMutant ln (* next state *)

        (* Line in a mutant *)
        | None ->
          begin match mode with
          | MutationTesting -> print_endline line
          | _               -> ()
          end;
          InMutant ln (* next state *)
        end

      (* End unit test *)
      | InUnitTest (ln,name) when end_named_block line ->
        TopLevel (* next state *)

      (* Line in a unit test *)  
      | InUnitTest (ln,name) ->
        begin match mode with
        | ExecuteUnitTest t when String.equal name t -> print_endline line
        | _ -> ()
        end;
        InUnitTest (ln,name) (* next state *)

    in process_input mode (start_line + 1) new_state

let show_usage name =
  Printf.eprintf "USAGE: %s COMMAND\n" name; 
  Printf.eprintf "\
Process lines from `stdin` to `stdout` depending on COMMAND\n\
  Valid comamnds are:\n\
  * no_test       Remove all annotation related to testing.\n\
  * etna          Emit mutation tests in CN Etna notation.\n\
  * list_unit     List names of available unit tests.\n\
  * UNIT_TEST     Emit content relevant for UNIT_TEST.\n\
"



let parse_mode str =
  match str with
  | "no_test"   -> Some NoTesting
  | "etna"      -> Some MutationTesting
  | "list_unit" -> Some CollectUnitTest
  | _ -> match drop_prefix "CN_TEST" str with
         | Some t -> Some (ExecuteUnitTest t)
         | None   -> None

let () =
  if not (Int.equal (Array.length Sys.argv) 2) then show_usage Sys.argv.(0);
  match parse_mode Sys.argv.(1) with
  | Some mode -> process_input mode 1 TopLevel
  | None -> show_usage Sys.argv.(0)