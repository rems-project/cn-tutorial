
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
  | Some txt when String.starts_with ~prefix:"CN_TEST" txt -> Some txt
  | _ -> None

(* Ending for mutant blocks and units tests *)
let end_named_block = String.starts_with ~prefix:"#endif"



(* -------------------------------------------------------------------------- *)


(* How we are processing the file *)
type mode =
  | NoTesting                 (* Remove testing related lines *)
  | MutationTesting           (* Translate to Etna notation *)
  | CollectMutants            (* Print only the names of the mutants *)
  | ExecuteMutant of string   (* Print only this specific mutant *)
  | CollectUnitTest           (* Print only names of unit tests *)
  | ExecuteUnitTest of string (* Print only this specific unit test *)


(* The current state of the processor *)
type state = 
| TopLevel
| InMutantOrig of int            (* start line, for error reprorting *)
| InMutant     of (int * string) (* start line; mutant name *)
| InUnitTest   of (int * string) (* start line; test name *)


let rec process_input mode start_line state =
  let mb_line = try Some (read_line()) with End_of_file -> None in
  match mb_line with
  | None ->
    begin
    let mk_error no msg = failwith (Printf.sprintf "%d: %s" no msg) in
    match state with
    | TopLevel          -> ()
    | InMutantOrig n    -> mk_error n "Untermianted mutant block"
    | InMutant (n,_)    -> mk_error n "Unterminated mutant block"
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
            | CollectUnitTest -> print_endline name
            | _               -> ()
            end;
            InUnitTest (start_line, name) (* next state *)

          (* ordinary top level line *)
          | None ->
            begin match mode with
            | CollectUnitTest
            | CollectMutants  -> ()
            | _               -> print_endline line
            end;
            state (* next state *)
        end

      | InMutantOrig ln ->
        begin match start_mutant line with

        (* Start a mutant *)
        | Some name ->
          begin match mode with
          | MutationTesting -> Printf.printf "//!! %s // //!\n" name
          | CollectMutants  -> print_endline name
          | _               -> ()
          end;
          InMutant (ln,name) (* next state *)

        (* Original part of a mutation block *) 
        | None ->
          begin match mode with
          | CollectUnitTest
          | CollectMutants 
          | ExecuteMutant _ -> ()
          | _               -> print_endline line
          end;
          state (* next state *)
        end

      (* End mutant block *)
      | InMutant _ when end_named_block line ->
        begin match mode with
        | MutationTesting -> print_endline "//"
        | _               -> ()
        end;
        TopLevel (* next state *)

      | InMutant (ln,name) ->

        begin match start_mutant line with
        (* Next mutatant *)
        | Some new_name ->
            begin match mode with
            | MutationTesting -> Printf.printf "// //!! %s // //!\n" new_name
            | CollectMutants  -> print_endline new_name
            | _               -> ()
            end;
            InMutant (ln,new_name) (* next state *)

        (* Line in a mutant *)
        | None ->
          begin match mode with
          | MutationTesting -> print_endline line
          | ExecuteMutant mu when String.equal mu name -> print_endline line
          | _ -> ()
          end;
          state (* next state *)
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



let command = ref (None : mode option)

let set_command cmd () =
  match !command with
  | None -> command := Some cmd
  | Some _ -> raise (Arg.Bad "Conflicting command flags")

let do_command str =
  raise (Arg.Bad (Printf.sprintf "Unexpected argument: %s" str))

let usage = "USAGE:"

let options =
  Arg.align
  [ ("--no-test", Arg.Unit (set_command NoTesting),
    "\tRemove all annotations related to testing");

    ("--etna", Arg.Unit (set_command MutationTesting),
    "\tEmit mutation tests in CN Etna notation");

    ("--list-mutants", Arg.Unit (set_command CollectMutants),
    "\tShow the names of the mutants in the input");

    ("--show-mutant", Arg.String (fun name -> set_command (ExecuteMutant name) ()),
    "NAME\tShow mutant with the given name");

    ("--list-unit", Arg.Unit (set_command CollectUnitTest),
    "\tShow the names of the unit tests in the input");

    ("--show-unit", Arg.String (fun name -> set_command (ExecuteUnitTest name) ()),
    "NAME\tExecute unit test with the given name")
  ]

let () =
  Arg.parse options do_command usage;
  match !command with
  | Some mode -> process_input mode 1 TopLevel
  | None      -> Arg.usage options usage
