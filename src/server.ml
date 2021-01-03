open Rnt
open Base 

let run_server (funs, entry) nonfuns = begin 
   let rnt = generate_rnt @@ entry :: funs in 

   let get_node name = begin 
      match Map.find rnt name with 
        | Some(node) -> print_rnt node 
        | None -> Stdio.print_endline "$NOT_FOUND"
   end in

   let get_parents name = begin 
      match Map.find rnt name with 
      | Some(InnerNode(_, _, _, p)) -> Stdio.print_endline p
      | Some(FunctionNode(_, _, p, _)) -> List.iter ~f:(fun a ->  Stdio.print_endline a) p
      | Some(GhostFunction(p)) -> List.iter ~f:(fun a ->  Stdio.print_endline a) p
      | None -> Stdio.print_endline "$NOT_FOUND"
   end in


   let rec do_read (_: unit) =
    let message = Caml.read_line () in 
    let command = String.split message ~on:' ' in

    begin match command with 
      | ["funs"] -> Cprint.print_defs funs;
      | ["nonfuns"] -> Cprint.print_defs nonfuns;
      | ["main"] -> Cprint.print_def entry;
      | ["print"; node] -> get_node node
      | ["parents"; node] -> get_parents node
      | ["rnt"] -> begin 
        Map.iteri ~f:(fun ~key:_ ~data:d->  print_rnt d) rnt;
      end
      | _ -> Stdio.print_endline "command unknown";
    end;
    Stdio.print_endline "$SICC_SERVER_DONE";
    do_read ();
  in 
  do_read ();
end