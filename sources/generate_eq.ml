

(*
   * Project: Spike ver 0.1
   * File: induction.ml
   * Content: Induction rule
*)

(* $Id: generate_eq.ml,v 1.4 2007/06/25 14:32:56 stratula Exp $ *)

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

Implementing relaxed rewriting from RTA 2008

  *)




let generate_eq verbose   _ _ (c:Clauses.peano_context Clauses.clause) is_strict =

  let max_var = c#greatest_varcode + 1 in
  (* 0: display *)
  let ic = !generate_eq_counter in 
  let () = incr generate_eq_counter in
  let () = prerr_endline (!indent_string ^ "[ " ^ (string_of_int conjectures_system#length) ^
  " / " ^ (string_of_int hypotheses_system#length) ^ " ]") in
  let _ = if !maximal_output then  buffered_output ("\nWe will try the rule GENERATE_EQ on " ^ (string_of_int c#number)) in   
  let all_pos_c = List.map (fun ((b, n, tp), ls)  -> List.map (fun x -> (b, n, tp @ x)) ls) (all_defined_positions c#content) in
  let pos_subterms = (List.map (fun p -> (p, c#subterm_at_position p)) (List.flatten all_pos_c)) in

  (* buffer for partial outputs  *)
  let text = ref "" in

  let pos_sorted = order_terms pos_subterms true in

  let max_c = c#all_maximal_terms false in 
  let tested_pos = List.filter 
    (fun (p, _) -> 
      let (b, n, pos) = p in
      let term_pos = c#subterm_at_position (b, n, [List.hd pos]) in 
      if is_strict then list_member (fun x y -> x#syntactic_equal y) term_pos max_c else true
    ) 
    pos_sorted
    

  in
  let () = text := !text ^ (List.fold_left (fun x (p, t) -> x ^ (sprint_clausal_position p) ^ " --> " ^ t#string ^ "\n\t" ) ("\n\nfrom the positions:\n\t") tested_pos) in
  let fn t rule max_v is_gen =
    
    let _ = rule#number in
    (*     let () = buffered_output ("\nfn: max_v = " ^ (string_of_int max_v)) in *)
    let rule', _ = rule#substitute_and_rename [] max_v in (* rename the variables *)
    let _ = rule'#number in
    let lhs = rule'#lefthand_side in
    
    let (s1, _) = try unify_terms t lhs is_gen with Failure "unify_terms" -> failwith "fn" in
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
	  with Failure "fn" -> fn1 subterm tl max_v is_gen
  in
  (* all the instances for a given subterm t *)
  let all_inst t max_v is_gen =
    (*     let () = buffered_output ("\n treating t = " ^ t#string ^ " with is_gen = " ^ (string_of_bool is_gen)) in *)
    let k = try t#head with Failure "head" -> failwith ("induction: fail on term " ^ t#string) in
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
	      with Failure "head" -> 
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
	    with Failure "head" -> 
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

    if (not test_indvar) or test_defsymb then 
      (*       let ()  = buffered_output ("\n the term is : " ^ t#string) in   *)
      failwith "all_inst"
    else 
      let rules_k = try dico_rules#find k with Not_found -> let () =  buffered_output ("\n no rules for " ^ t#string) in [] in
      List.flatten (fn1 t rules_k max_v is_gen) 
  in
  
  
  let rec fn2 l max_v gen_on_term = 
    match l with 
	[] -> failwith "fn2"
      | (p, t) :: tl -> 
	  (* 	  let () = buffered_output ("\nTrying t = " ^ t#string) in *)
	  try 
	    let ls = all_inst t max_v false in
	    let all_ts = List.map (fun (s1, _) -> List.map (fun (_, s) -> s) s1) ls in (* the terms for substitution in t *)
	    
	    let test = (List.exists (fun t -> not t#is_term) (List.flatten all_ts)) in
	    if (ls = []) or test then fn2 tl max_v gen_on_term
	    else 
	      (p, ls)
	  with Failure "all_inst" -> 
	    if gen_on_term then 
	      try 
		(* do again with generalization, this time  *)
		let ls = all_inst t max_v true in
		let () = text := !text ^  "\n\n\t by the generalization of some existential variables to universal ones on term "
		  ^ t#string in
		let all_ts = List.map (fun (s1, _) -> List.map (fun (_, s) -> s) s1) ls in (* the terms for substitution in t *)
		let test2 = (List.exists (fun t -> not t#is_term) (List.flatten all_ts)) in
		if (ls = []) or test2 then fn2 tl max_v gen_on_term
		else 
		  (p, ls)
	      with Failure "all_inst" -> 
		fn2 tl max_v gen_on_term
	    else fn2 tl max_v gen_on_term
  in
  (* compute the substitutions *)
  let p, ls = 
    try 
      fn2 tested_pos max_var false
    with Failure "fn2" -> 
      try 
	(* do again with generalization, this time  *)
	let res = fn2 tested_pos max_var true in
	let () = text := !text ^  "\n\n\t by the generalization of some existential variables to universal ones " in
	res
      with Failure "fn2" ->
	let () = buffered_output ("\n\n **** fail GENERATE_EQ *** on " ^ c#string ^ "\n\n") in
	let () = print_detailed_clause c in 
	let () = print_history normalize c false in 
(* 	let () = print_history_ic normalize c in  *)
	failwith ("fail induction on " ^ c#string) in
  
  let target_term = c#subterm_at_position p in
  let target_vars = List.map (fun (x,_,_) -> x) target_term#variables in

  (* expand the other terms whose variables have been instantiated  *)
  let res_pos = try remove_el (fun (p1, _) (p2, _) -> p1 = p2) (p, c#subterm_at_position p) tested_pos with Failure "remove_el" -> failwith "remove_el: induction" in

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
	    let _ ,ls =  try fn2 [(p,trm)] max_var false with Failure "fn2" -> (p, [])  in
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
  (*   let () = buffered_output ("\n" ^  "ls = " ^ (sprint_subst (List.flatten (List.map (fun (s, t1,t2) -> s) ls)))) in *)
  let ls' = List.flatten (List.map (fn6 0 c) ls) in
  (*   let () = buffered_output ("\n" ^ "ls' = " ^ (sprint_subst (List.flatten (List.map (fun (s, t1,t2) -> s) ls')))) in *)



  (* start to write the instances  *)
  
  let add_hyp = List.for_all (fun (_, r) -> r#oriented) ls' in
  let i = ref 0 in
  let written_term = c#subterm_at_position p in
  let () =
    if verbose
    then
      let () = buffered_output ("\n" ^ !indent_string ^ "GENERATE_EQ " ^ (string_of_int ic) ^ " on\n" ^ !indent_string ^ "\171 " ^ c#string ^ !text) in
      let () = buffered_output (List.fold_left (fun x (s1,_) -> let () = i := !i + 1 in x ^ "\n " ^ !indent_string ^ (string_of_int
	!i) ^ ") " ^ (sprint_subst s1)) ("\nat " ^  (sprint_clausal_position p)^ " on \t" ^ written_term#string ^  " \t using the test substitutions:\n") ls') in
      (*       let () = print_history c in *)
      ()
    else ()
  in
  
  let () =
    if verbose
    then
      buffered_output ("\n" ^ !indent_string ^ "We obtain :")
    else () 
  in
  (* add the treated conjecture as premise  *)
  let () = if add_hyp then hypotheses_system#append [c] in
  
  let () = i := 0 in
  
  let fn5 (s, r_orig) = 

    (* compute the instance of r_orig  *)
    (* check if there are variables in common  *)

    let cinst = c#substitute s in
    let maxvar_c = cinst#greatest_varcode in
    let new_r,_ = r_orig#substitute_and_rename [] (maxvar_c + 1) in
    let t1 = cinst#subterm_at_position p in
    let t2 = new_r#lefthand_side in

    (*     let () = buffered_output ("t1 = " ^ t1#string) in *)
    (*     let () = buffered_output ("t2 = " ^ t2#string) in *)

    let (_, s2) = try unify_terms t1 t2 false with Failure "unify_terms" -> failwith "\nError in Generate_eq: please report it" in
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
    let cond' = List.map (fun x -> x#update_pos) cond in
    let lpos' = List.map (fun x ->x#copy) lpos in
    let lneg' = List.map (fun x ->x#copy) (lneg @ cond') in
    let res' = c#build lneg' lpos' in

    (* takes as argument the literal lit which is the positive literal of the test instance cinst rewritten.

       1) replaces  the lhs of lit  with an instance of the rhs of the original clause c to obtain a'. 
       2) rewrites the rhs of lit
       3) if the both sides of lit are incomparable, test whether a' is smaller than the rhs of cinst *)

    let fn_eq lit  =
      let fn_term (lhs:Terms.term) rhs is_lhs = 
	let _, str_norm, lhs_norm, _ = normalize [R;L] lhs c "" ([],[]) 0 in  
	let lhs_orig, rhs_orig = 
	  let l, r = (c#head)#both_sides in
	    if is_lhs then l,r else r,l
	in
	let lhs_inst, rhs_inst =
	  let l, r = (cinst#head)#both_sides in
	    if is_lhs then l,r else r, l
	in
	  try
	    let pos, theta = lhs_norm#subterm_matching (fun _ s -> s) lhs_orig in
	      if 
		try 
		  let _ =  (lhs_norm#subterm_at_position pos)#subterm rhs
		  in true 
		with (Failure "subterm") -> false 
	      then str_norm, lhs_norm
	      else
		let lhs_s = lhs_norm#replace_subterm_at_pos pos (rhs_orig#substitute theta) in
		let str_repl = (lhs_norm#subterm_at_position pos)#string ^ "\n   matches the " ^ 
		  (if is_lhs then " left " else " right " ) ^ "side of " ^ c#string ^ "\n   with substitution : "  ^ (sprint_subst theta)
		  ^ "    to give \n" ^ (lhs_s#subterm_at_position pos)#string ^ "\n" in
		  (* 	    let () = buffered_output ("Subterm matching succeeded: I am here !!!\n" ^ str_repl) in *)
		let _, rhs_theta = 
		  let l, r = (c#substitute theta)#both_sides in
		    if is_lhs then l,r else r,l 
		in
		  if ((rpo_greater false lhs_inst rhs_theta) || (rpo_geq false rhs_inst rhs_theta)) && 
		    ((rpo_greater false lhs_inst lhs_norm) || (rpo_greater false rhs_inst lhs_norm))
		  then
		    (str_norm ^ str_repl), lhs_s
		  else
		    str_norm, lhs_norm
	  with (Failure "matching") -> str_norm, lhs_norm
      in
      let lhs, rhs = lit#both_sides in
      let str_lhs, lhs' = fn_term lhs rhs true in
      let str_rhs, rhs' = fn_term rhs lhs' false in
      let lit_rez = (new literal (Lit_equal (lhs', rhs'))) in
(*    if clause_greater false false cinst c_rez && clause_greater false false cinst c_theta then *)
(* 	    str'', l_rez *)
(* 	  else *)
(* 	    failwith "fn_eq" *)
	(str_lhs ^ str_rhs), lit_rez
    in
	
(*       (\*       let () = buffered_output ("\n lit: " ^ lit#string) in *\) *)
(*       let rewritten_side = (fun (_,_,p') -> List.hd p') p in *)
(*       let left_side = 0 in *)
(*       (\*       let () = buffered_output ("\n rewritten side = " ^ (if rewritten_side = left_side then " left_side" else " right_side"))  in *\) *)

(*       let lhs, rhs =  *)
(* 	let l, r = lit#both_sides in *)
(* 	if rewritten_side = left_side then l,r else r,l  *)
(*       in *)
(*       let _, _ =  *)
(* 	let l, r = (cinst#head)#both_sides in *)
(* 	if rewritten_side = left_side  then l,r else r,l  *)
(*       in *)
(*       let lhs_orig, rhs_orig =  *)
(* 	let l, r = (c#head)#both_sides in *)
(* 	if rewritten_side = left_side then l,r else r,l  *)
(*       in *)
(*       (\*       let () = buffered_output ("\n lhs = " ^ lhs#string) in *\) *)
(*       (\*       let () = buffered_output ("\n rhs = " ^ rhs#string) in *\) *)
(*       (\*       let () = buffered_output ("\n lhs_orig = " ^ lhs_orig#string) in *\) *)
(*       (\*       let () = buffered_output ("\n rhs_orig = " ^ rhs_orig#string) in *\) *)
(*       (\*       let () = buffered_output ("\n lhs_inst = " ^ lhs_inst#string) in *\) *)
(*       (\*       let () = buffered_output ("\n rhs_inst = " ^ rhs_inst#string) in *\) *)
      
(*       (\*       let () = buffered_output ("Testing rpo_greater false rhs lhs  yields " ^ (string_of_bool (rpo_greater false rhs lhs))) in *\) *)
(*       try  *)
(* 	let str_norm, lhs_norm = normalize [R;L] lhs c "" ([],[]) 0 in   *)
(* 	(\* 	  let () = buffered_output ("Subterm matching trying: I am here !!!") in  *\) *)
(* 	let pos, theta = lhs_norm#subterm_matching (fun _ s -> s) lhs_orig in *)
(* 	let lhs_s = lhs_norm#replace_subterm_at_pos pos (rhs_orig#substitute theta) in *)
(* 	let str_repl = (lhs_norm#subterm_at_position pos)#string ^ "\n   matches the " ^  *)
(* 	  (if rewritten_side = left_side then " left " else " right " ) ^ "side of " ^ c#string ^ "\n   with substitution : "  ^ (sprint_subst theta) *)
(* 	  ^ "    to give \n" ^ (lhs_s#subterm_at_position pos)#string ^ "\n" in *)
(* 	let lhs_theta, rhs_theta =  *)
(* 	  let l, r = (c#substitute theta)#both_sides in *)
(* 	  if rewritten_side = left_side then l,r else r,l  *)
(* 	in *)
(* 	if (rpo_greater false lhs_orig rhs_orig) || (rpo_geq false lhs_theta rhs_theta) then  *)
(* 	  if rewritten_side = left_side then (str_norm ^ str_repl), (new literal (Lit_equal (lhs_s, rhs))) *)
(* 	  else (str_norm ^ str_repl), (new literal (Lit_equal (rhs, lhs_s))) *)
(* 	else *)
(* 	  let str', lhs' = normalize [R;L] lhs_s c (str_norm ^ str_repl) ([],[]) 0 in *)
(* 	  (\* 	    let () = buffered_output ("str' = " ^ str') in *\) *)
(* 	  (\* 	    let () = buffered_output ("lhs_s = " ^ lhs_s#string) in *\) *)
(* 	  (\* 	    let () = buffered_output ("lhs' = " ^ lhs'#string) in *\) *)
(* 	  (\* 	    let () = buffered_output ("Normalize lhs oK: I am here !!!") in  *\) *)
(* 	  (\* 	    let () = buffered_output ("Testing rpo_greater false lhs_orig rhs_orig yields " ^ (string_of_bool (rpo_greater false *\) *)
(* 	  (\* 	      lhs_orig rhs_orig))) in *\) *)
(* 	  (\* 	    let () = buffered_output ("Testing rpo_equivalent lhs rhs  yields " ^ (string_of_bool (rpo_equivalent lhs rhs))) in *\) *)
(* 	  (\* 	    let () = buffered_output ("Testing rpo_incomparable false rhs_orig lhs_orig  yields " ^ (string_of_bool (rpo_incomparable false rhs_orig lhs_orig))) in *\) *)
(* 	  (\* 	    let () = buffered_output ("Testing rpo_greater false rhs_inst lhs' yields " ^ (string_of_bool (rpo_greater false rhs_inst *\) *)
(* 	  (\* 	      lhs'))) in *\) *)
(* 	  (\* 	    let () = buffered_output ("rhs_inst = " ^ rhs_inst#string) in *\) *)
(* 	  (\* 	    let () = buffered_output (" lhs' = " ^ lhs'#string) in *\) *)

	  
(* 	  let str'', rhs' = normalize [R;L] rhs c str' ([],[]) 0 in *)
(* 	  let l_rez =  *)
(* 	    if rewritten_side = left_side then (new literal (Lit_equal (lhs', rhs'))) *)
(* 	    else (new literal (Lit_equal (rhs', lhs'))) in *)
(* 	  let c_rez = c#build [] [l_rez] in  *)
(* 	  let c_theta = c#substitute theta in *)
(* 	  if clause_greater false false cinst c_rez && clause_greater false false cinst c_theta then *)
(* 	    str'', l_rez *)
(* 	  else *)
(* 	    failwith "fn_eq" *)
(*       with (Failure "matching") -> failwith "fn_eq" *)
(*     in *)
    

    let str, res = if not res'#is_unit then "",res' else
    if (res'#head)#is_diff then "",res' 
    else
      let rec repeat str lit = 
(* 	let () = buffered_output ("lit = " ^ lit#string) in *)
	let str', lit' = fn_eq lit in
(* 	let () = buffered_output ("lit' = " ^ lit'#string) in *)
	  if lit#syntactic_equal lit' then str, lit
	  else
	    repeat (str ^ str') lit' 
      in
      let str', lit = repeat "" res'#head in 
      let _ = lit#update_pos in
	str', (c#build [] [lit])
    in
    let () = res#add_history (s, c) in
      
    let () =
      let () = i := !i + 1 in
	if verbose
	then
	  buffered_output ("\n" ^ !indent_string ^ (string_of_int !i) ^ ")" ^ res#string ^ "\n\n" ^ !indent_string ^ 
			     (if str = "" then "" else cinst#string ^ "\n    is rewritten ") ^ "using the rule " ^ r_orig#string ^ (if str = "" then ""
																    else ( " to get\n" ^ res'#string ^ "\n\nFurther operations on " ^ res'#string ^ "\n\n" ^ str)))
	else ()
    in
      res
  in
  let () = incr generate_eq_counter_suc in
  let res = List.map fn5 ls' in
  let () = buffered_output "\n" in
    res
      
