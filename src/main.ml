open Base
open Util

let counter = ref 0


let generate_id _ = begin
  let curr = !counter in 
  counter := !counter + 1;
  "RNT_NODE_"^ Int.to_string curr;
end

let get_function_name (sname : Cabs.single_name): string = begin 
  let (_, _, (name, _, _, _)) = sname in name
end

type rnt_node = 
   | GhostFunction
   | InnerNode of Cabs.statement * string (* id of parent *)
   | FunctionNode of Cabs.single_name * Cabs.body 
        * string list (* ids of parents *) 
        * ((string, string sexp_list, String.comparator_witness) Map.t) (* rnt *)

type rntMapT = (string, rnt_node, String.comparator_witness) Map.t

  

let print_rnt = begin function 
  | InnerNode(statement, _) -> Cprint.print_statement statement; 
  | FunctionNode(sn, body, _, _) -> Cprint.print_def @@ Cabs.FUNDEF(sn, body)
  | GhostFunction -> ();
end 

let rec generate_inner_rnt (parent_id: string) index_map tree_map statement = begin 
  let do_add (s: Cabs.statement) = begin 
    let new_id = generate_id () in
    let new_tree = Map.update tree_map parent_id ~f:(function | None -> [new_id] | Some(c) -> new_id :: c) in
    let new_index = Map.set index_map ~key:new_id ~data:(InnerNode(s, parent_id)) in
    generate_inner_rnt new_id new_index new_tree s
  end in 

  let traverse_multiple s1 s2 = begin 
      let s1_rnt, s1_tree = (generate_inner_rnt parent_id index_map tree_map s1) in
      let s2_rnt, s2_tree = (generate_inner_rnt parent_id index_map tree_map s2) in

      (Map.merge_skewed 
            ~combine:(fun ~key:_ v1 _ -> v1)
            s1_rnt
            s2_rnt
      ),
      (Map.merge_skewed 
            ~combine:(fun ~key:_ v1 v2 -> List.concat [v1; v2])
            s1_tree
            s2_tree
      )
  end in

  let open Cabs in
  match statement with
  | WHILE(_, s) -> do_add s
	| DOWHILE(_, s) -> do_add s
	| FOR(_, _, _, s) -> do_add s
	| SEQUENCE(s1, s2) -> traverse_multiple s1 s2
	| IF(_, s1, s2) -> traverse_multiple s1 s2
	| BLOCK(_, s) -> generate_inner_rnt parent_id index_map tree_map s
	| SWITCH(_, s1) -> generate_inner_rnt parent_id index_map tree_map s1
	| CASE(_, s) -> generate_inner_rnt parent_id index_map tree_map s
	| DEFAULT(s) -> generate_inner_rnt parent_id index_map tree_map s
	| LABEL(_, s) -> generate_inner_rnt parent_id index_map tree_map s
	| STAT_LINE(s, _, _) -> generate_inner_rnt parent_id index_map tree_map s
	| BREAK -> index_map, tree_map
	| RETURN(_) -> index_map, tree_map
	| CONTINUE -> index_map, tree_map
  | NOP -> index_map, tree_map
	| GOTO(_) -> index_map, tree_map
	| ASM(_) -> index_map, tree_map
	| COMPUTATION(_) -> index_map, tree_map
	| GNU_ASM(_, _, _, _) -> index_map, tree_map
end


let add_func_node index_map funcnode = begin 
  match funcnode with 
    | Cabs.FUNDEF(sn, (def, s)) -> begin 
       let parents = [] in (*set in update*)
       let stringname = get_function_name sn in 
       let new_index, new_tree = generate_inner_rnt stringname index_map (Map.empty (module String)) s in 
       let new_func = FunctionNode(sn, (def, s), parents, new_tree) in 
       calls_in_stmts  s |> ignore;
       Map.set ~key:stringname ~data:new_func new_index
    end
    | _ -> begin 
      Stdio.print_endline "Bad Input";
      raise Caml.Exit;
    end

end 

let update_func_parents (index_map : rntMapT) funcnode : rntMapT = begin 
  let rec traverse_rnt rnt (map : rntMapT) name s : rntMapT = begin 
      let calls = Util.calls_in_stmts s in 

      let add_calles calles = begin 
        List.fold ~init:map ~f:begin fun acc callee -> 
          Map.update acc name ~f:(function 
            | Some(FunctionNode(sn, b, parents, rnt)) -> FunctionNode(sn, b, callee :: parents, rnt) 
            | _ -> GhostFunction
          ) 
        end 
          @@ Set.to_list 
          @@ Set.of_list (module String) calles
      end in

      Map.find rnt name |> function 
        | None -> begin 
           add_calles calls
           
        end
        | Some(children : string list) -> begin 
            let get_node_child_stmt (m: rntMapT) (c:string) = begin match Map.find_exn m c with 
                | FunctionNode(_, (_, s), _,_) -> s
                | InnerNode(s, _) -> s
                | GhostFunction -> Cabs.NOP;
            end in 

            let new_map = 
              List.fold ~init:map ~f:(fun acc child -> traverse_rnt rnt acc child (get_node_child_stmt acc child) ) children
            in 

            (* TODO - add self, filter and stuff *)

            new_map
        end     
  end in


  match funcnode with 
    | FunctionNode(name, (_, s), _, rnt) -> begin 
       (* Map.update index_map parent_id ~f:(function | None -> [new_id] | Some(c) -> new_id :: c)  *)
       traverse_rnt rnt index_map (get_function_name name) s
    end
    | _ -> begin 
       index_map
    end

end 

let generate_rnt (functions: Cabs.definition list) = begin
  let rnt_index : (string, rnt_node, String.comparator_witness) Map.t = 
    Map.empty (module String) 
  in 

  List.fold ~init:rnt_index ~f:add_func_node functions 
  |> fun a -> List.fold ~init:a ~f:update_func_parents @@ Map.data a

end

let rename_main (defs: Cabs.definition list) = begin
    
    let rename (def: Cabs.definition) : Cabs.definition = (
      match def with 
        | Cabs.FUNDEF((bt, st, (name, bt2, attr, exp)), body) when String.equal name "main" -> 
            Cabs.FUNDEF((bt, st, ("__old_main", bt2, attr, exp)), body)
        | other -> other;
    ) in

    let filter_main (reverse: bool) (def: Cabs.definition)  : bool = (
      match def with 
        | Cabs.FUNDEF((_, _, (name, _, _, _)), _) when String.equal name "main" -> 
            reverse
        | _ -> not reverse;
    ) in

  let others = List.filter ~f:(filter_main false) defs in 
  let only_main = List.filter ~f:(filter_main true) defs in 

  (others, List.hd_exn only_main |> rename)

end 

let get_funcs ?(reverse=false) (defs: Cabs.definition list)  = begin
    let do_fun (def: Cabs.definition) : bool = (
      match def with 
        | Cabs.FUNDEF(_, _) -> not reverse
        | _ -> reverse;
    ) in

  List.filter ~f:do_fun defs;
end 

let run_server (funs, entry) nonfuns = begin 
   let rec do_read (_: unit) =
    let message = Caml.read_line () in 
    begin match message with 
      | "funs" -> Cprint.print_defs funs;
      | "nonfuns" -> Cprint.print_defs nonfuns;
      | "main" -> Cprint.print_def entry;
      | "rnt" -> begin 
        let rnt = generate_rnt @@ entry :: funs in 
        Map.iteri ~f:(fun ~key:k ~data:d-> Stdio.print_endline k; print_rnt d) rnt;
  

      end
      | _ -> Stdio.print_endline "command unknown";
    end;
    Stdio.print_endline "$SICC_SERVER_DONE";
    do_read ();
  in 
  do_read ();
end

let () = 
  let file = Sys.argv.(1) in
  let result = Frontc.parse_file file Stdio.stdout in 
  begin match result with
    | Frontc.PARSING_OK(stmnts) -> (
      let funs = rename_main @@ get_funcs stmnts in
      let other = get_funcs stmnts ~reverse:true in
      run_server funs other;
      (* printFuns @@ stmnts; *)
    )
    | _ -> Stdio.print_endline "sad"
  end;


 
