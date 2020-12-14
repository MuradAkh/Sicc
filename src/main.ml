open Base

let transform_statement (f: Cabs.statement->Cabs.statement) (stmt: Cabs.statement): Cabs.statement =
  let open Cabs in
  match stmt with
	| NOP -> NOP
	| COMPUTATION(expression) -> COMPUTATION(expression)
	| BLOCK(defs, s) -> BLOCK(defs, s)
	| SEQUENCE(s1, s2) -> SEQUENCE(f s1, f s2)
	| IF(e, s1, s2) -> IF(e, f s1, f s2)
	| WHILE(e, s) -> WHILE(e, f s)
	| DOWHILE(e, s) -> DOWHILE(e, f s)
	| FOR(e1, e2, e3, s) -> FOR(e1, e2, e3,f s)
	| BREAK -> BREAK
	| CONTINUE -> CONTINUE
	| RETURN(e) -> RETURN(e)
	| SWITCH(e, s1) -> SWITCH(e, f s1)
	| CASE(e, s) -> CASE(e, f s)
	| DEFAULT(s) -> DEFAULT(f s)
	| LABEL(st, s) -> LABEL(st, f s)
	| GOTO(st) -> GOTO(st)
	| ASM(st) -> ASM(st)
	| GNU_ASM(st, g1, g2, stl) -> GNU_ASM(st, g1, g2, stl)
	| STAT_LINE(st, s, i) -> STAT_LINE(f st, s, i)


let printFuns (defs: Cabs.definition list) = begin
    let do_fun (def: Cabs.definition) = (
      match def with 
        | Cabs.FUNDEF((_, _, (_, typ, _, _)), (dfs, stmt)) -> (
          (* Cprint.print_defs dfs; *)
          (* Cprint.print_statement bs; *)
          let rec trav_s = (function 
            | Cabs.STAT_LINE(st, s, _) -> (
              Stdio.print_endline s;
              trav_s st)
            | s -> transform_statement trav_s s
          ) in
          trav_s stmt |> ignore;
          
        );
        | _ -> ();
    ) in

    List.iter ~f:do_fun defs;
end

let () = 
  let file = Sys.argv.(1) in
  let result = Frontc.parse_file file Stdio.stdout in 
  begin match result with
    | Frontc.PARSING_OK(stmnts) -> (
      (* Cprint.print_defs stmnts; *)
      (* Cprint.print_def @@ List.hd_exn stmnts; *)
 
      printFuns @@ stmnts;
    )
    | _ -> Stdio.print_endline "sad"
  end;
  (* let rec do_read (_: unit) =
    let message = Caml.read_line () in 
    Stdio.print_endline message;
    do_read ();
  in 
  do_read (); *)
