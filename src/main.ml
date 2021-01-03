open Base

let () = 
  let file = Sys.argv.(1) in
  let result = Frontc.parse_file file Stdio.stdout in 
  begin match result with
    | Frontc.PARSING_OK(stmnts) -> (
      let funs = Rnt.rename_main @@ Rnt.get_funcs stmnts in
      let other = Rnt.get_funcs stmnts ~reverse:true in
      Server.run_server funs other;
      (* printFuns @@ stmnts; *)
    )
    | _ -> Stdio.print_endline "sad"
  end;


 
