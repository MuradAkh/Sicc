open Base

let counter = ref 0


let generate_id _ = begin
  let curr = !counter in 
  counter := !counter + 1;
  "RNT_NODE_"^ Int.to_string curr;
end

let get_function_name (sname : Cabs.single_name): string = begin 
  let (_, _, (name, _, _, _)) = sname in name
end

type variable_list = (string * Cabs.base_type) sexp_list
type rnt_node = 
   | GhostFunction
   | InnerNode of string * variable_list * Cabs.statement * string (* id of parent *)
   | FunctionNode of Cabs.single_name * Cabs.body 
        * string list (* ids of parents *) 
        * ((string, string sexp_list, String.comparator_witness) Map.t) (* rnt *)

type rntMapT = (string, rnt_node, String.comparator_witness) Map.t

let get_linear_seq (stmt : Cabs.statement) : (Cabs.statement * Cabs.statement) option = 
  let is_cheap = begin function 
    | Cabs.WHILE(_, _) -> false
    | Cabs.DOWHILE(_, _) -> false
    | Cabs.FOR(_, _, _, _) -> false
    | Cabs.COMPUTATION(expr) when 0 < List.length @@ Util.search_calls expr -> false
    | _ -> true
  end in
  let open Base.List.Monad_infix in
  
  let rec flatten_sequence = begin function 
    | Cabs.SEQUENCE(s1, s2) -> [s1;s2] >>= flatten_sequence 
    | s -> [s]
  end in 

  let rec do_extract (sofar: Cabs.statement list) = begin function
  | (next :: rest) -> 
    if is_cheap next then
      do_extract (next :: sofar) rest
    else 
      sofar, next :: rest
  | [] -> sofar, []
  end in 

  let to_extract, to_leave = do_extract [] (flatten_sequence stmt) in 
  let extracted = List.reduce ~f:(fun a c -> Cabs.SEQUENCE(c, a)) to_extract in
  let left = List.reduce ~f:(fun a c -> Cabs.SEQUENCE(a,c)) to_leave in

  if List.length to_extract < 1 then 
    None 
  else
  
  
  let open Option.Monad_infix in 
    left        >>= fun l ->
    extracted   >>| fun e -> 
    (e, l)

let make_function (s: Cabs.statement) varlist name = begin
  (* let vars = Util.vars_in_stmts s in  *)
  let variables_decs = List.map varlist ~f:(fun (vname, vtype) -> (vtype, Cabs.NO_STORAGE, (vname, vtype, [], Cabs.NOTHING))) in
  let proto = Cabs.PROTO(Cabs.VOID, variables_decs, false) in
  Cabs.FUNDEF((Cabs.VOID, Cabs.NO_STORAGE, (name, proto, [], Cabs.NOTHING)), ([], s))
end

let print_rnt = begin function 
  | InnerNode(name, varlist, statement, _) -> Cprint.print_def @@ make_function statement varlist name 
  | FunctionNode(sn, body, _, _) -> Cprint.print_def @@ Cabs.FUNDEF(sn, body)
  | GhostFunction -> Stdio.print_endline "GHOST";
end 

let rec generate_inner_rnt ntm (parent_id: string) index_map tree_map statement = begin 
  let do_add (s: Cabs.statement) recurse = begin 
    let new_id = generate_id () in
    let new_tree = Map.update tree_map parent_id ~f:(function | None -> [new_id] | Some(c) -> new_id :: c) in
    let variables = Util.vars_in_stmts s in 
    let vars_with_types = List.map variables ~f:(fun v -> (v, match Map.find ntm v with Some(a) -> a | None -> Cabs.VOID )) in
    let new_index = Map.set index_map ~key:new_id ~data:(InnerNode(new_id, vars_with_types, s, parent_id)) in
    if recurse then 
      generate_inner_rnt ntm new_id new_index new_tree s
    else new_index, new_tree
  end in 


  let mergemaps (r1, t1) (r2, t2) = begin 
    (Map.merge_skewed 
            ~combine:(fun ~key:_ v1 _ -> v1)
            r1
            r2
      ),
      (Map.merge_skewed 
            ~combine:(fun ~key:_ v1 v2 -> List.concat [v1; v2])
            t1
            t2
      )
  end in

  let traverse_multiple s1 s2 = begin 
      let m1 = (generate_inner_rnt ntm parent_id index_map tree_map s1) in
      let m2 = (generate_inner_rnt ntm parent_id index_map tree_map s2) in
      mergemaps m1 m2
      
  end in

  let open Cabs in
  match statement with
  | WHILE(_, s) -> do_add s true
	| DOWHILE(_, s) -> do_add s true
	| FOR(_, _, _, s) -> do_add s true
	| SEQUENCE(s1, s2) -> begin 
    let seq = get_linear_seq statement in 
    match seq with 
      | Some((e, rest)) -> mergemaps (do_add e false) (generate_inner_rnt ntm parent_id index_map tree_map rest)
      | _ -> traverse_multiple s1 s2
  end
	| IF(_, s1, s2) -> traverse_multiple s1 s2
	| BLOCK(_, s) -> generate_inner_rnt ntm parent_id index_map tree_map s
	| SWITCH(_, s1) -> generate_inner_rnt ntm parent_id index_map tree_map s1
	| CASE(_, s) -> generate_inner_rnt ntm parent_id index_map tree_map s
	| DEFAULT(s) -> generate_inner_rnt ntm parent_id index_map tree_map s
	| LABEL(_, s) -> generate_inner_rnt ntm parent_id index_map tree_map s
	| STAT_LINE(s, _, _) -> generate_inner_rnt ntm parent_id index_map tree_map s
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
  let create_name_type_map (sn: Cabs.single_name) (defs: Cabs.definition sexp_list) = begin 
    (* local variables *)
    let name_groups = List.fold defs ~init:[] 
      ~f:begin fun acc curr -> 
        match curr with 
        | Cabs.DECDEF(ng) -> ng :: acc
        | Cabs.TYPEDEF(ng, _) -> ng :: acc
        | Cabs.ONLYTYPEDEF(ng) -> ng :: acc
        | _ -> acc
    end in
    
    let vars_of_name_group (group: Cabs.name_group) = begin
      let bt, _, sns = group in 
      List.map sns ~f:(fun (name, _, _, _) ->(name, bt))
    end in

    (* variables from parameters *)
    let _, _, cabs_name = sn in
    let _, bt, _, _ = cabs_name in 
    
    let param_types = match bt with 
      | Cabs.PROTO(_, var_dec, _) -> 
        Option.return @@ List.map var_dec ~f:(fun (bt, _, (vname, _, _, _)) -> (vname, bt))
      | _ -> None
    in

    let open Option.Monad_infix in
    param_types >>| fun types -> 
    Map.of_alist_reduce ~f:(fun a _ -> a) (module String) @@ List.concat [types; (List.bind name_groups ~f:vars_of_name_group)]
  end in


  match funcnode with 
    | Cabs.FUNDEF(sn, (def, s)) -> begin 
       let name_type_map = match create_name_type_map sn def with Some(m) -> m | None -> Map.empty (module String) in
       let parents = [] in (*set in update*)
       let stringname = get_function_name sn in 
       let new_index, new_tree = generate_inner_rnt name_type_map stringname index_map (Map.empty (module String)) s in 
       let new_func = FunctionNode(sn, (def, s), parents, new_tree) in 
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

      let add_calles m calles = begin 
        List.fold ~init:m ~f:begin fun acc callee -> 
          Map.update acc callee ~f:(function 
            | Some(FunctionNode(sn, b, parents, rnt)) -> FunctionNode(sn, b, name :: parents, rnt) 
            (* | Some(a) -> a *)
            | _ -> GhostFunction
          ) 
        end 
          @@ Set.to_list 
          @@ Set.of_list (module String) calles
      end in

      Map.find rnt name |> function 
        | None -> begin 
           add_calles map calls
           
        end
        | Some(children : string list) -> begin 
            let get_node_child_stmt (m: rntMapT) (c:string) = begin match Map.find_exn m c with 
                | FunctionNode(_, (_, s), _,_) -> s
                | InnerNode(_,_, s, _) -> s
                | GhostFunction -> Cabs.NOP;
            end in 

            let new_map = 
              List.fold ~init:map ~f:(fun acc child -> traverse_rnt rnt acc child (get_node_child_stmt acc child) ) children
            in 
            let open List.Monad_infix in 
            let childStatements = List.map ~f:(fun c -> get_node_child_stmt new_map c) children in
            let childCalls = childStatements >>= Util.calls_in_stmts in
            let uniqieCalls = Set.to_list @@ Set.of_list (module String) calls in

            add_calles new_map 
              @@ List.filter
                 ~f:begin fun funcname -> 
                    List.count ~f:(fun a -> String.equal a funcname) childCalls 
                    < List.count ~f:(fun a -> String.equal a funcname) calls
                 end
                 uniqieCalls
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

let get_funcs ?(reverse=false) (defs: Cabs.definition list) = begin
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
        Map.iteri ~f:(fun ~key:_ ~data:d->  print_rnt d) rnt;
  

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


 
