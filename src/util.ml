open Cabs
open Base
open Base.List


let transform_statement (f: Cabs.statement->Cabs.statement) (stmt: Cabs.statement): Cabs.statement = begin
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
end 

let do_generic f g = begin function
	| NOP -> []
	| COMPUTATION(expression) -> f expression
	| BLOCK(_, s) -> g s
	| SEQUENCE(s1, s2) -> [s1; s2] >>= g
	| IF(e, s1, s2) -> concat [f e; g s1; g s2]
	| WHILE(e, s) -> concat [f e; g s]
	| DOWHILE(e, s) -> concat [f e; g s]
	| FOR(e1, e2, e3, s) -> concat [[e1;e2; e3] >>= f; g s]
	| BREAK -> []
	| CONTINUE -> []
	| RETURN(e) -> f e
	| SWITCH(e, s1) -> concat [f e; g s1]
	| CASE(e, s) -> concat [f e; g s]
	| DEFAULT(s) -> g s
	| LABEL(_st, s) -> g s
	| GOTO(_) -> []
	| ASM(_) -> []
	| GNU_ASM(_, _, _, _) -> []
	| STAT_LINE(s, _, _) -> g s
end 

let do_expr f = begin function 
  | NOTHING -> []
	| UNARY(_, e) -> f e
	| BINARY(_, e1, e2) -> [e1; e2] >>= f
	| QUESTION(e1, e2, e3) -> [e1; e2; e3] >>= f
	| CAST(_, e) -> f e
	| CALL(e, el) -> e :: el >>= f
	| COMMA(el) -> el >>= f
	| CONSTANT(_) -> []
	| VARIABLE(_) -> []
	| EXPR_SIZEOF(_) -> []
	| TYPE_SIZEOF(_) -> []
	| INDEX(e1, e2) -> [e1;e2] >>= f
	| MEMBEROF(e, _) -> f e
	| MEMBEROFPTR(e, _) -> f e 
	| GNU_BODY(_) -> []
	| EXPR_LINE(e,_,_) -> f e
end 

let rec search_calls = begin function  
  | CALL(VARIABLE(s), params) ->  s :: (params >>= do_expr search_calls)
  | e -> do_expr search_calls e
end

let rec search_vars = begin function  
  | VARIABLE(s) ->  [s]
	| CALL(_, el) -> el >>= search_calls
  | e -> do_expr search_vars e
end

let calls_in_stmts s = begin 
  let rec searcher st = do_generic search_calls searcher st in 
  searcher s;
end 

let vars_in_stmts s = begin 
  let rec searcher st = do_generic search_vars searcher st in 
  Set.to_list @@ Set.of_list (module String) @@ searcher s;
end 

