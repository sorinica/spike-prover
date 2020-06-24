
(*
   * Project: Spike ver 0.1
   * File: normalize.ml
   * Content: Normalization of terms
*)

open Values
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Order
open Literals
open Clauses
open Dummies
open Coq

let norm_string = ref ""
let broken_symbs = ref []

(* Apply on tr the first rewrite rule from rw_r available and check that its preconditions have equal normal forms *)
let rewrite rw_r (tr:term) c_ref str cxt i =

  (* let ()  = buffered_output ("\n c_ref#number = " ^ (string_of_int c_ref#number)) in *)
  
  (*   let () = buffered_output ("\n Rewrite " ^ tr#string) in *)
  let max_var = c_ref#greatest_varcode + 1 in
  let str_ref = ref str in

  let rec fn2 t_p pos l = 
    
    match l with
      [] -> failwith "fn2"
    | (los, h):: t ->
       
       (* let () = buffered_output ("\n fn2: trying from " ^ los ^ " the clause " ^ h#string ) in *)
       let test1 =  (* the neg lits are not empty ? *) 
	 let negs = h#negative_lits in
	 negs <> [] 
       in
       let test2 = (* the pos literal is t1 <> t2 ?*) 
	 let poss = h#positive_lits in
	 let fst_lit = List.hd poss in
	 fst_lit#is_diff
       in
       if test1 || test2 then fn2 t_p pos t
       else 
         let lhs, rhs = h#both_sides in
	 let fn1 order_tested l r = 
             (* 		let () = buffered_output ("\nHere with l = " ^ l#string ^ " and r = " ^r#string) in *)
	     match t_p#matching (fun s -> s) l with
             | exception (Failure _) -> failwith "fn1"
             | sub ->
		let r_sub = r#substitute sub in
		let l_sub = l#substitute sub in

		let test_ok = 
		  if los = "C1" then 
		    let hsub, _ = h#substitute_and_rename sub max_var in 
		    clause_geq false false c_ref hsub 
		  else if los = "C2" then
		    let hsub, _ = h#substitute_and_rename sub max_var in 
		    let res = clause_greater false false c_ref hsub in
		    res
		  else true
		in
		let tests = 
		  if !dracula_mode then 
		    if los = "C1" || los = "C2" then rpo_greater false l_sub r_sub else true 
		  else test_ok && ((not order_tested) || (order_tested && rpo_greater false l_sub r_sub )) in
		if tests then (sub, r_sub) else failwith "fn1"
	        
	 in
	 let newtr = tr#copy in
	 let reverted = ref false in
	 try 
	   let (sub, r_sub) = match los with
	       "L" -> 
		if h#oriented then
		  (try fn1 false lhs rhs with Failure _ -> failwith "bad")
		else
		  (try fn1 !use_order lhs rhs with Failure _ -> 
		     if not !use_order then failwith "bad"
		     else
		       let () = reverted := true in
		       (try fn1 true rhs lhs with Failure _ -> failwith "bad") 
		  )
	     | "C1" | "C2" ->
		(try fn1 !use_order lhs rhs with Failure _ -> 
		   if not !use_order then failwith "bad"
		   else
		     let () = reverted := true in
		     (try fn1 true rhs lhs with Failure _ -> failwith "bad") 
		)
	     |  "R" -> 
		 (* test if the axiom is broken *)
		 let () = if (not !dracula_mode) && (not (rpo_greater false lhs rhs)) then
		            let head_symb = lhs#head in
		            let str_symb = dico_const_string#find head_symb in
			    broken_symbs := (str_symb, c_ref#number,c_ref#content) :: !broken_symbs 
		 in 
		 (try fn1 false lhs rhs with Failure _ -> failwith "bad")
	     | _ -> failwith "normalize: los"
	   in
	   let res = try newtr#replace_subterm_at_pos pos r_sub with Failure _ -> failwith "bad" in
	   let fn3 h is_rev =
 	     let lhs, rhs = h#both_sides in
	     if is_rev then rhs#string ^ " -> " ^ lhs#string ^ "  (from [ " ^ (string_of_int h#number) ^ " ] of " ^ los ^ ")"
	     else lhs#string ^ " -> " ^ rhs#string ^ "   (from [ " ^ (string_of_int h#number) ^ " ] of " ^ los ^ ")"
	   in
	   let () = str_ref := !str_ref ^ (
		      "\n" ^ (n_spaces i) ^ tr#string ^
		        "\n" ^ (n_spaces (i + 3)) ^ "is simplified by : " ^ (fn3 h !reverted) ^ 
		          "\n" ^ (n_spaces (i + 3)) ^ "with substitution: " ^ (sprint_subst sub) ^ " into" ^ 
		            "\n" ^ (n_spaces i) ^ res#string ^ "\n") in
	   let dummy_c = new clause ([],[(new literal (Lit_equal (tr, tr)))]) [] ("",0,([],[])) in
	   let () = rewriting_clauses := !rewriting_clauses @ [(h, los, dummy_c, sub)] in
           (* 	      let () = buffered_output ( *)
           (* 		"\n" ^ (n_spaces i) ^ tr#string ^ *)
           (* 		"\n" ^ (n_spaces (i + 3)) ^ "is simplified by : " ^ (fn3 h !reverted) ^  *)
           (* 		"\n" ^ (n_spaces (i + 3)) ^ "with substitution: " ^ (sprint_subst sub) ^ " into" ^  *)
           (* 		"\n" ^ (n_spaces i) ^ res#string ^ "\n") in *)
	   let iHs = if (los = "C1") || (los = "C2") then  [(h, sub)] else [] in
	   res, iHs
         with Failure _  -> fn2 t_p pos t
  in 
  
  let k = try tr#head with Failure _ -> failwith "rewrite" in
  let lpat = try if List.mem R rw_r then dico_rules#find k else [] with Not_found -> [](* failwith "rewrite" *) in
  let lpat' = List.map (fun x -> ("R", x)) lpat in  
  let l' = if List.mem R rw_r then try remove_el (=) R rw_r with Failure _ -> failwith "rewrite: remove_el" else rw_r in
  let lres = concrete_system_list l' cxt in
  let lres' = List.filter (fun (_, c) -> c#is_horn && not (c_ref#syntactic_equal c)) lres in
  let rw_r' = (lpat' @ lres') in
  
  let res, iHs = try fn2 tr [] rw_r' with Failure _ -> failwith "rewrite" in
  let res' = if equal_sorts tr#sort res#sort then 
               res#expand_sorts
             else failwith "rewrite"
  in
  !broken_symbs, !str_ref, res', iHs

(* normalize a term: apply rewrite rules until saturation *)
let  normalize rw_r tr c_ref str cxt i =
  (*   let () = buffered_output ("\n Normalize " ^ tr#string) in *)
  
  let found_iHs = ref ([]: (Clauses.peano_context Clauses.clause * (Symbols.var * Terms.term) list) list) in
  let rec fn_norm rw_r tr c_ref str cxt i =
    match tr#content with 
      Var_univ _  | Var_exist _  -> !broken_symbs, str, tr, !found_iHs
      | Term (f, l, s) -> 
	 if !found_iHs <> [] && !dracula_mode then !broken_symbs, str, tr, !found_iHs
	 else
	   let st_list = List.map (fun x -> fn_norm rw_r x c_ref "" cxt (i + 3)) l in
	   let term_list = List.map (fun (_,_,x,_) -> x) st_list in
	   let str_list =  List.map (fun (_, x,_,_) -> x) st_list in
	   let str_list' = list_remove_doubles (fun x y -> x = y) str_list in
	   let str'' = List.fold_right (fun x y -> (x ^ y)) str_list' "" in
	   let tr'' = new term (Term (f, term_list, s)) in	      
	   if !dracula_mode then 
	     let _, str', tr', iHs = 
               if !found_iHs = [] then 
                 try rewrite rw_r tr'' c_ref (str ^ str'') cxt i with (Failure _) ->
		   !broken_symbs, (str ^ str''), tr'', !found_iHs
               else !broken_symbs, str, tr, !found_iHs in
	     if iHs <> [] then let () = found_iHs := iHs in !broken_symbs, str, tr, !found_iHs else fn_norm rw_r tr' c_ref str' cxt i
	   else 
	     let _, str', tr', _ =  try rewrite rw_r tr'' c_ref (str ^ str'') cxt i  with (Failure _) -> !broken_symbs, (str ^ str''), tr'', !found_iHs 
             in  fn_norm rw_r tr' c_ref str' cxt i
  in
  fn_norm rw_r tr c_ref str cxt i

(* Fails if tr = norm tr *)
let normalize_plus rw_r tr c_ref str cxt i =
(*   let str', tr' = rewrite rw_r tr c_ref str cxt i in *)
  let _, str', tr', iHs =  normalize rw_r tr c_ref str cxt i in
  if str = str' then failwith "rewrite" else !broken_symbs, str', tr', iHs
