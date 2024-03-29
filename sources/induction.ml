

(*
   * Project: Spike ver 0.1
   * File: induction.ml
   * Content: Induction rule
*)

(* $Id: induction.ml,v 1.5 2007/06/13 15:55:27 stratula Exp $ *)

open Values
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Terms_parser
open Order
open Literals
open Dummies
open Clauses
open Test_sets
open Normalize

  (* Arguments for induction are:
     - a boolean specifying whether or not we print the result of this rule
     - whether the computation of test subtitutions is automatic or not.
     - a literal position argument
     - two contexts: the first is dummy, the other in the simpl. process
     - a given clause to be treated
     - a strategy for simplification
     - a flag for saying that the CCS is strict or not
     Two modes are therefore proposed:
     - automatic computes test substitutions, and uses default strategies ("1" and "2").
     - non-automatic mode asks for a list of substitutions, and proceeds with those.
  *)




let generate verbose   _ _ (c:Clauses.peano_context Clauses.clause) is_strict =
  let all_hist c = List.map (fun (_,cl) -> cl#number) (c#history) in
    if c#standby then 
      let sb_IHs' = List.filter (fun (cH,_) -> 
				   (* let () = buffered_output ( "\n\n standby: The IH related to " ^ (string_of_int cH#number) ^ " will be checked") in *)
				   let offsprings_cH = List.filter (fun c' -> List.mem cH#number (c'#number :: (all_hist c')))  !real_conjectures_system in 
				     if  offsprings_cH = []  then (* all IHs have been  already proved *)
				       let () = buffered_output ( "\n\n standby: The IH related to " ^ (string_of_int cH#number) ^ " is checked since it is already proved. ") in false
				     else
				       true) c#sb_IHs in
	if sb_IHs' = [] then  let () = buffered_output ("\t    It unblocked the following operation:\n\n" ^ c#sb_string) in c#sb_newconjs
	else let () = c#set_sb_IHs sb_IHs' in [c]
    else
      (*       let offsprings_cH = List.filter (fun c' -> List.mem cH#number (all_hist c'))  !real_conjectures_system in  *)
      (* 	if  offsprings_cH = []  then (\* all IHs have been  already proved *\) *)
      (* 	  let () = buffered_output c#sb_string in *)
      (* 	  let () = List.iter (fun (cH,_) -> buffered_output ( "\n\n standby: The IH related to " ^ (string_of_int cH#number) ^ " is checked since it is already proved"))  c#sb_IHs in c#sb_newconjs *)
      (* 	else *)
      (* 	  if !maximal_output then let () = buffered_output ("\nGenerate cannot be applied on the conjecture [ " ^ (string_of_int c#number) ^ " ] since it is in standby") in [c] else [c] *)
      (* else *)
      let max_var = c#greatest_varcode + 1 in
	(* 0: display *)
      let list_cond = ref [] in
      let ic = !generate_counter in 
      let () = incr generate_counter in
      let () = prerr_endline (!indent_string ^ "[ " ^ (string_of_int conjectures_system#length) ^
				" / " ^ (string_of_int hypotheses_system#length) ^ " ]") in
      let _ = if !maximal_output then  buffered_output ("\nWe will try the rule GENERATE on " ^ (string_of_int c#number)) in   
      let all_pos_c = List.map (fun ((b, n, tp), ls)  -> List.map (fun x -> (b, n, tp @ x)) ls) (all_defined_positions c#content) in
      let pos_subterms = (List.map (fun p -> (p, c#subterm_at_position p)) (List.flatten all_pos_c)) in
      let written_term_list = ref [] in
      let total_inst_var = ref [] in
      let f_ind_arg_vars = ref [] in
	(* buffer for partial outputs  *)
      let text = ref "" in

      let pos_sorted = order_terms pos_subterms true in

      let max_c = c#all_maximal_terms false in 
      let ltested_pos = List.filter 
	(fun (p, _) -> 
	   let (b, n, pos) = p in
	   let term_pos = c#subterm_at_position (b, n, [List.hd pos]) in 
	     if is_strict then list_member (fun x y -> x#syntactic_equal y) term_pos max_c else true
	) 
	pos_sorted
	

      in
      let () = text := !text ^ (List.fold_left (fun x (p, t) -> x ^ (sprint_clausal_position p) ^ " --> " ^ t#string ^ "\n\t" ) ("\n\nfrom the positions:\n\t") ltested_pos) in
      let fn t rule max_v is_gen =
	
	let _ = rule#number in
	  (*     let () = buffered_output ("\nfn: max_v = " ^ (string_of_int max_v)) in *)
	let rule', _ = rule#substitute_and_rename [] max_v in (* rename the variables *)
	let _ = rule'#number in
	let lhs = rule'#lefthand_side in
	  
	let (s1, _) = try unify_terms t lhs is_gen with Failure _ -> failwith "fn" in
	  (*     let () = buffered_output rule'#string in *)
	  (*     let () = print_detailed_clause rule' in *)
	  (*     let () = buffered_output ("\ns1 = " ^ (sprint_subst s1) ^ " s2 = " ^ (sprint_subst s2)) in *)
	let s1' = List.map (fun (i, t') -> (i, t'#expand_sorts)) s1 in
	  (*     let new_rule' = rule'#expand_sorts in *)

	let fn'' (i, t'') =  List.map (fun (t', sigma) -> ((i, t'), sigma)) (expand_nullary [t'']) in
	let expand_s1 = megamix (List.map fn'' s1') in
	let lls1 :((Symbols.var * Terms.term) list * (Symbols.var * Terms.term) list) list  = (List.map (fun l -> let l1, l2 =
													   List.split l in l1, List.flatten l2) expand_s1) (* is a list of pairs (ind subst, subst by expand_nullary) *)
	in 
	let fn' (s1, s2) =  
	  (* applies s2 to each term of the substitution s1 *)
	  (*       let () = buffered_output ("s2 = " ^ (sprint_subst s2) ^ " s2'' = " ^ (sprint_subst s2'')) in *)
	  (*       let sigma = ((List.map (fun (i, t) -> (i, t#substitute s2'')) s2) @ s2'') in *)
	  (*       let sigma' = List.map (fun (i, t') -> (i, t'#expand_sorts)) sigma in *)
	  (*      let () = buffered_output ("\n new_rule' here = " ^ new_rule'#string) in *)
	  (*      let () = buffered_output ("sigma = " ^ (sprint_subst sigma) ) in *)
	  (*       let _ = yy_tmp_param_sorts := [] in *)
	  (*       let r' = new_rule'#substitute sigma in  *)
	  
	  (*      let () = buffered_output ("\n subst = " ^ (sprint_subst sigma) ^ " and \nrule' = " ^ new_rule'#string ^ " and \nr = " ^
		  r#string ) in *)
	  let s1' = List.map (fun (i, t) -> (i, t#substitute s2)) s1 in
	    (s1', rule) 
	in
	let res : ((Symbols.var * Terms.term) list * Clauses.peano_context Clauses.clause) list = List.map fn' lls1 in
	  (*     let () = buffered_output ("\nThe substitutions are: " ^ (List.fold_right (fun (s,_) strg -> strg ^ " " ^ *)
	  (*       (sprint_detailed_subst s) ) res "")) in *)
	  res
      in
      let rec fn1 subterm lrules max_v is_gen = 
	match lrules with 
	    [] -> []
	  | r :: tl -> 
	      try 
		let tmp = fn subterm r max_v is_gen in 
		  tmp :: (fn1 subterm tl max_v is_gen)  
	      with Failure _ -> fn1 subterm tl max_v is_gen
      in
	(* all the instances for a given subterm t *)
      let all_inst t max_v is_gen =
	(*     let () = buffered_output ("\n treating t = " ^ t#string ^ " with is_gen = " ^ (string_of_bool is_gen)) in *)
	let k = try t#head with Failure _ -> failwith ("generate: fail on term " ^ t#string) in
	let rec fn_test1 n t l  =
	  (*       let () = buffered_output ( "\n" ^ (n_spaces n) ^ "fn_test1 t = " ^ t#string ^ " l = " ^ (sprint_list ",  " (fun (symb, p) -> *)
	  (* 	" symb = " ^ (dico_const_string#find symb) ^ " p = " ^ (string_of_int p)) l) ) in *)
	  let res =
	    match l with
		[] -> false
	      | (symb, p) :: tl -> 
		  try 
		    if t#head = symb then 
		      if tl <> [] then 
			let t' = t#subterm_at_position [p] in
			  fn_test1 (n + 2) t'  tl 
		      else false
		    else false
		  with Failure _ -> 
		    (* t is a variable  *)
		    if is_gen then not (is_abstract t#sort) else (not (is_existential_var t)) && not (is_abstract t#sort) 
	  in
	    (*       let () = buffered_output (" return of fn_test1 = " ^ (string_of_bool res)) in *)
	    res
	in
	let rec fn_test2 n t l  =
	  match l with
	      [] -> false
	    | (symb, p) :: tl -> 
		try 
		  if t#head = symb then 
		    if tl <> [] then 
		      let t' = t#subterm_at_position [p] in
			fn_test2 (n + 2) t'  tl 
		    else false
		  else (is_defined t#head)
		with Failure _ -> 
		  (* t is a variable  *)
		  if not is_gen then is_existential_var t else false
	in
	let l1 = try dico_ind_positions_v0#find k with Not_found -> let () =  if !maximal_output then buffered_output ("\n no indpos for " ^ t#string) in [] (* the symbol k is predefined *) in

	(* test for induction variables *)
	let test_indvar = List.exists (fun pos ->  List.exists (fun l -> fn_test1 0 t l) pos) l1  in

	(* no defined symbols in induction positions  *)
	let test_defsymb  = List.exists (fun pos ->  List.exists (fun l -> fn_test2 0 t l) pos) l1 in

	  (*     let () = buffered_output ("\n t = " ^ t#string ^ "\n \t test_indvar = " ^ (string_of_bool test_indvar) ^ " test_defsymb = " ^ (string_of_bool *)
	  (*       test_defsymb)) in *)

	  if (not test_indvar) || test_defsymb then 
	    (*       let ()  = buffered_output ("\n the term is : " ^ t#string) in   *)
	    failwith "all_inst"
	  else 
	    let rules_k = try dico_rules#find k with Not_found -> let () =  buffered_output ("\n no rules for " ^ t#string) in [] in
	      List.flatten (fn1 t rules_k max_v is_gen) 
      in
	
	
      let rec fn2 (p,t) max_v gen_on_term = 
	
	(* 	  let () = buffered_output ("\nTrying t = " ^ t#string) in *)
	try 
	  let ls = try all_inst t max_v false with  Failure _ -> failwith "fn2"  in
	  let all_ts = List.map (fun (s1, _) -> List.map (fun (_, s) -> s) s1) ls in (* the terms for substitution in t *)
	    
	  let test = (List.exists (fun t -> not t#is_term) (List.flatten all_ts)) in
	    if (ls = []) || test then failwith "fn2"
	    else 
	      (p, ls)
	with Failure _ -> 
	  if gen_on_term then 
	    try 
	      (* do again with generalization, this time  *)
	      let ls = try all_inst t max_v true with  Failure _ -> failwith "fn2" in 
	      let () = text := !text ^  "\n\n\t by the generalization of some existential variables to universal ones on term "
		^ t#string in
	      let all_ts = List.map (fun (s1, _) -> List.map (fun (_, s) -> s) s1) ls in (* the terms for substitution in t *)
	      let test = (List.exists (fun t -> not t#is_term) (List.flatten all_ts)) in
		if (ls = []) || test then failwith "fn2"
		else 
		  (p, ls)
	    with Failure _  -> 
	      failwith "fn2"
	  else failwith "fn2"
      in

      let rec fn_tested_pos l = 
	let str = ref "" in
	  match l with
	      [] -> 
		let () = buffered_output ("\n\n **** fail GENERATE *** on " ^ c#string ^ "\n\n") in
		let () = print_detailed_clause c in 
		let () = print_history normalize c false in 
		  (* 	let () = print_history_ic normalize c in  *)
		  raise Refutation
	    | tested_pos :: tl_pos ->	  
		(* compute the substitutions *)
		try 
		  let p, ls = 
		    try 
		      fn2 tested_pos max_var false
		    with Failure _ -> 
		      try 
			(* do again with generalization, this time  *)
			let res = fn2 tested_pos max_var true in
			let () = text := !text ^  "\n\n\t by the generalization of some existential variables to universal ones " in
			  res
		      with Failure _ ->
			failwith "fn_tested_pos"
		  in  
		  let target_term = c#subterm_at_position p in
		  let target_vars = List.map (fun (x,_,_) -> x) target_term#variables in
		    
		  (* expand the other terms whose variables have been instantiated  *)
		  let res_pos = try remove_el (fun (p1, _) (p2, _) -> p1 = p2) (p, c#subterm_at_position p) ltested_pos with Failure _ -> failwith "remove_el: generate" in
		    
		  let rec fn6 i cl (s, r_orig) = 
		    
		    (*     let () = buffered_output ("\n" ^ (n_spaces i) ^ "fn6 called with s = " ^ (sprint_subst s)) in *)
		    let cinst = cl#substitute s in
		    let max_var = cinst#greatest_varcode + 1 in
		      
		    let lpos = List.fold_right 
		      (fun (p, _) l -> 
			 let t' = cinst#subterm_at_position p in 
			 let t'' = cl#subterm_at_position p in 
			   if t'#string <> t''#string then (p, t') :: l else l ) 
		      res_pos [] 
		    in
		      
		      
		    let rec fn l = 
		      match l with 
			  [] -> [(s, r_orig)]
			| (p, trm) :: tl -> 
			    
			    (* new substitutions for the first modified term  *)
			    (* 	    	    let () = buffered_output ("\n" ^ (n_spaces i) ^ "trm = " ^ trm#string) in *)
			    (* try fn2 without the generalization of variables ... to see if should be modified ? *)
			    let _ ,ls =  try fn2 (p,trm) max_var false with Failure _ -> (p, [])  in
			      (* eliminate the duplicates from ls  *)
			    let rec eq_subst (s1,  tr1') (s2,  tr2') = 
			      match s1 with
				  [] -> (match s2 with [] -> true | _ -> false)
				| (i1, trm1) :: t1 -> (match s2 with [] -> false | (i2, trm2) :: t2 -> (i1 = i2) && (trm1#equal_mod_var trm2) && (eq_subst (t1, tr1') (t2, tr2')))
			    in
			      
			    (* 	    let () = buffered_output ("\n" ^ (n_spaces i) ^ "ls_purged = " ^ (sprint_subst (List.flatten (List.map (fun (s, t1,t2) -> s) ls_purged)))) in *)
			      
			    (* build the new set of substitutions  *)
			    let new_ls = 
			      List.fold_right 
				(fun (s', _) l -> 
				   let new_s' = (List.map (fun (i, t) -> (i, t#substitute s')) s) @ s' in
				     (* the variables in new_s' should be in lvar_trm  *)
				   let new_s'' = List.filter (fun (x,_) -> list_member (=) x target_vars) new_s' in
				     
				   let _ = (List.fold_right (fun (_, t) l -> t#variables @ l) s' []) in
				     (new_s'', r_orig) :: l)
				ls [] 
			    in
			      
			    let ls_purged = list_remove_doubles eq_subst new_ls in
			      
			    let res = if new_ls = [] then fn tl  else List.flatten (List.map (fun s -> fn6 (i + 3) cinst s) ls_purged) in
			      (* 	    let () = buffered_output ("\n" ^ (n_spaces i) ^ "Results: ") in *)
			      (* 	    let () = List.iter (fun (s, _, _) ->  buffered_output ("\n" ^ (n_spaces i) ^ (sprint_subst s))) res in *)
			      res
				
		    in
		      fn lpos
			
		  in
		    (* 	        let () = buffered_output ("\n" ^  "ls = " ^ (sprint_subst (List.flatten (List.map (fun (s, _) -> s) ls)))) in *)
		  let ls' = List.flatten (List.map (fn6 0 c) ls) in
		  let written_term = c#subterm_at_position p in
		  let () = written_term_list := written_term :: !written_term_list in
		  let constructor_term_res s = 
		    let sort_res = s in 
		    let lcons = ref [] in  (dico_const_profile#iter (fun i ls -> if (List.length ls) == 1 && List.hd ls == sort_res && is_constructor i then lcons := (dico_const_string#find i) :: !lcons ));
		      if !lcons == [] then 
			(* 	give a new chance to	build a constructor term  *)
			let lcons_i = ref [] in
			let () = dico_const_profile#iter (fun (i:int) ls ->  if  List.hd ls == sort_res  then lcons_i := i :: !lcons_i ) in
			  if !lcons_i == [] then failwith ("coq_induction_schema: No constructors for sort " ^ (dico_sort_string#find sort_res))
			  else 
			    let symb = List.hd (List.filter (fun i -> let arity = dico_const_profile#find i in List.for_all (fun s -> s <> sort_res) (List.tl arity)) !lcons_i)  in
			    let arity = dico_const_profile#find symb in 
			    let fn_constr_arg s = 
			      let lcons_arg = ref [] in
			      let () = (dico_const_profile#iter (fun i ls -> if (List.length ls) == 1 && List.hd ls == s && is_constructor i then lcons_arg := (dico_const_string#find i) :: !lcons_arg )) in
				if !lcons_arg == [] then failwith ("coq_induction_schema: No constant constructor  for sort " ^ (dico_sort_string#find sort_res))
				else List.hd !lcons_arg
			    in 
			      "(" ^ (dico_const_string#find symb) ^ " " ^ (List.fold_right (fun arg s -> let arg_s = fn_constr_arg arg in arg_s ^ " " ^ s) (List.tl arity) "") ^ ")"
		      else List.hd !lcons
		  in
		    (* 	    let () = buffered_output ("\n" ^ "ls' = " ^ (sprint_subst (List.flatten (List.map (fun (s, _) -> s) ls')))) in *)
		  let all_subst = list_remove_doubles (fun s1 s2 -> if List.length s1 == List.length s2 then let s1_s2 = List.combine s1 s2 in List.for_all (fun ((i1, t1), (i2, t2)) -> i1 == i2 && t1#syntactic_equal t2) s1_s2 else false)  (List.map fst ls') in
		  let list_vars' = list_remove_doubles (fun (u,_,_) (v,_,_) -> (u == v)) written_term#variables in
		  let list_inst_var = ref [] in
		  let rec fn_sv s lv = 
		    match lv with
			[] -> " => " ^ (constructor_term_res written_term#sort)
		      | (i, _, _) :: tl -> let s_t = try let t = List.assoc i s in list_inst_var := (i, t) :: !list_inst_var; t#compute_string_coq_with_quantifiers [] with Not_found -> "_" in s_t ^ (if tl = [] then "" else ", ") ^ fn_sv s tl
		  in 
		  let all_inst_vars = List.fold_right (fun (sb, _) l -> (List.map (fun (i, _) -> i) sb) @ l) ls' [] in
		  let struct_str = " {struct u" ^ (string_of_int (List.hd all_inst_vars)) ^ "} " in
		  let f_permut lv = (* returns a permutation of lv where the first variable is instantiated by the first generate case *)
		    let inst_var = List.map fst (List.hd (List.map fst ls')) in
		    let rez = ref [] in
		    let () = List.iter (fun (i, s, b) -> if List.mem i inst_var then rez := !rez @ [(i, s, b)]) lv in
		    let () = List.iter (fun (i, s, b) -> if not (List.mem i inst_var) then rez := !rez @ [(i, s, b)]) lv in
		      !rez
		  in	
		  let list_vars = f_permut list_vars' in 
		  let () = f_ind_arg_vars := list_vars in
		  let () = List.iter (fun subst -> list_inst_var := []; let _ = (fn_sv subst list_vars) in total_inst_var := !total_inst_var @ [!list_inst_var]) (List.map fst ls') in
		  let cases = (List.fold_right (fun subst s ->  let str = "\n| " ^ (fn_sv subst list_vars) ^ s in str) all_subst "") in
		  let f_coq_schema = "\nFunction f_" ^ (string_of_int c#number) ^ " " ^ (sprint_list " " (fun (i, s, _) -> "(u" ^ (string_of_int i) ^ ": " ^ (dico_sort_string#find s) ^ ")") list_vars) ^ struct_str ^ ": " ^ (dico_sort_string#find written_term#sort) ^ " :=\n match " ^ (sprint_list ", " (fun (i, _, _) -> "u" ^ (string_of_int i)) list_vars) ^ " with" ^ cases ^ "\nend.\n" in
		  let () = coq_induction_schemas := !coq_induction_schemas ^ f_coq_schema in 


		    
		  (* start to write the instances  *)
		    
		  let i = ref 0 in
		  let () =
		    if verbose
		    then
		      let () = str := !str ^  ("\n" ^ !indent_string ^ "GENERATE " ^ (string_of_int ic) ^ " on\n" ^ !indent_string ^ "\171 " ^ c#string ^ !text) in
		      let () = str := !str ^ (List.fold_left (fun x (s1,_) -> let () = i := !i + 1 in x ^ "\n " ^ !indent_string ^ (string_of_int
																      !i) ^ ") " ^ (sprint_subst s1)) ("\nat " ^  (sprint_clausal_position p)^ " on \t" ^ written_term#string ^  " \t using the test substitutions:\n") ls') in
			(*       let () = print_history c in *)
			()
		    else ()
		  in
		    
		    
		  let () =
		    if verbose
		    then
		      str := !str ^ ("\n\n" ^ !indent_string ^ "We obtain :\n")
		    else () 
		  in  
		  let () = i := 0 in
		    
		  let fn5 (s, r_orig) = 
		    
		    (* compute the instance of r_orig  *)
		    (* check if there are variables in common  *)
		    
		    let cinst = c#substitute s in
		    let maxvar_c = cinst#greatest_varcode in
		    let new_r, _ = r_orig#substitute_and_rename [] (maxvar_c + 1) in
		    let t1 = cinst#subterm_at_position p in
		    let t2 = new_r#lefthand_side in
		      
		    (*     let () = buffered_output ("t1 = " ^ t1#string) in *)
		    (*     let () = buffered_output ("t2 = " ^ t2#string) in *)
		      
		    let (_, s2) = try unify_terms t1 t2 false with Failure _ -> failwith "\nError in Generate: please report it" in
		    let r = (new_r#substitute s2)#expand_sorts in
		      
		    let cond = r#negative_lits in
		    let rhs = r#righthand_side in
		      (*     let () = write_pos_clause cinst in *)
		      (*     let () = buffered_output ("s1 = " ^ (sprint_subst s1)) in *)
		      (*     let () = buffered_output ("s2 = " ^ (sprint_subst s2)) in *)
		      (*     let () = buffered_output ("r_orig = " ^ r_orig#string) in *)
		      (*     let () = buffered_output ("new_r = " ^ new_r#string) in *)
		      (*     let () = buffered_output ("r = " ^ r#string) in *)
		      (*     let () = buffered_output ("cinst = " ^ cinst#string) in *)
		      (*     let () = buffered_output ("rhs = " ^ rhs#string) in *)
		      
		      

		    let c' = cinst#replace_subterm_at_pos p rhs in
		      
		      
		    (*     let () = buffered_output ("c' = " ^ c'#string) in *)
		    let (b, n, pos) = p in
		      
		    let phead = (b, n, [List.hd pos]) in
		    let term = c'#subterm_at_position phead in
		      
		    let term' = term#update_pos in
		    let cfinal = c'#replace_subterm_at_pos phead term' in
		      
		    let lneg, lpos = cfinal#content in
                    let cond'' = difference (fun x y -> x#syntactic_equal y) cond lneg in
		    let cond' = List.map (fun x -> x#update_pos) cond'' in
		    let () = list_cond :=  !list_cond @ [cond']  in
		    let lpos' = List.map (fun x ->x#copy) lpos in
		    let lneg' = List.map (fun x ->x#copy) (lneg @ cond') in
		    let res = c#build lneg' lpos' in
		    let () = res#add_history (s, c) in
		      

		    let () =
		      let () = i := !i + 1 in
			if verbose
			then
			  str := !str ^ ("\n" ^ !indent_string ^ (string_of_int !i) ^ ") " ^ res#string ^ "\n\n" ^ !indent_string ^ "using the rule " ^ r_orig#string)
			else ()
		    in
 		      
		      (cinst, res)
		  in
		  let () = incr generate_counter_suc in
		  let lcres = List.map fn5 ls' in
		  let () = List.iter (fun (c1, c2) -> coq_less_clauses:= !coq_less_clauses @ [(c2, c1)]) lcres in
		  let add_hyp = List.for_all (fun (cinst, res) -> if !dracula_mode then true else clause_greater false false cinst res) lcres in
		    (* add the treated conjecture as premise  *)
		  let () = 
		    if add_hyp then 
		      hypotheses_system#append [c] (fun c -> ())
		  in
		  let is_case_analysis = List.for_all (fun (cinst, res) -> if !dracula_mode then true else clause_geq false false cinst res) lcres in
		    if is_case_analysis then 
		      let lres = List.map (fun (_,x) -> x) lcres in
		      let () = str := !str ^ "\n" in
			!str, lres
		    else
		      let () = if !maximal_output then str := !str ^  ("fail generate on position" ^ (sprint_clausal_position (fst tested_pos)) ^ "  \n Hint: ordering to be changed || be ready to reinitialize the hypotheses") in
			fn_tested_pos tl_pos
		with Failure _ -> fn_tested_pos tl_pos
      in
      let str_rez, lrez = fn_tested_pos ltested_pos in
      let () = buffered_output str_rez in
      let () = coq_formulas := !coq_formulas @ [c] in
      let () = coq_generate_cond := (c#number, !list_cond) :: !coq_generate_cond  in
      let () = coq_formulas_with_infos := !coq_formulas_with_infos @ [("generate", c#number, !f_ind_arg_vars, (List.combine (List.map (fun x -> x#number) lrez) !total_inst_var), [])]  in
	lrez
      
	      
