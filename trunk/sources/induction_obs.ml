
(*
   * Project: Spike ver 0.1
   * File: induction.ml
   * Content: Induction rule
*)

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
open Critical_context_set
open Context
open Induction
  (* Arguments for induction are:
     - a boolean specifying whether or not we print the result of this rule
     - a given clause
     - a literal position argument
     - whether the computation of test subtitutions is automatic or not.
     Two modes are therefore proposed:
     - automatic computes test substitutions, and uses default strategies ("1" and "2").
     - non-automatic mode asks for a list of substitutions, and proceeds with those.
  *)
let generate_obs verbose is_automatic arg_indpos _ (c: peano_context clause) =

  (* 0: display *)
  let ic = !generate_counter in 
  let () = incr generate_counter in
  let () = prerr_endline (!indent_string ^ "[ " ^ (string_of_int conjectures_system#length) ^
                          " / " ^ (string_of_int hypotheses_system#length) ^ " ]") in
  let () = prerr_endline (!indent_string ^ "Applying generate " ^ (string_of_int ic) ^ " on " ^ c#string) in
  let () = buffered_output (!indent_string ^ "Applying generate " ^ (string_of_int ic) ^ " on " ^ c#string) in
  let result = ref [] in

  (* 1: parse a set of (substitutions, strategies) *)
  let get_sigma_and_st (_:strategy) =
    let () = in_a_file := false in
    let () = reset_yy_values () in
    let () = fill_yy_values (c#variables) in
    let () = yy_tmp_vars2 := !yy_tmp_vars
    and () = yy_tmp_sorts2 := !yy_tmp_sorts in
    let () = reset_yy_values () in
    let sigma = !spike_parse_substitution () in
    match sigma with
      [] -> raise Exit
    | _ ->
	let max_var = c#greatest_varcode + 1 in
        buffered_output ("Current instance: " ^ (c#substitute_and_rename sigma max_var)#string) ;
        let (st: strategy) = try dico_st#find name_strat_generate_reduce with Not_found -> failwith "find:generate_obs" (* !spike_parse_strategy def_st () *) in
        st, sigma in

  (* 2: generate test substitutions *)
  let condition_1 lhs (def_st: strategy) los =
    if is_automatic
    then
      let () =
        try
          greatest_var := ((fun (x,_,_) -> x) (last_el c#variables)) + 1
        with (Failure "last_el") -> () in
      let sigma_set = !generate_test_substitutions los lhs in
      let () = buffered_output (!indent_string ^ "Found " ^ (string_of_int (List.length sigma_set)) ^ " test-substitutions") in
      let () = print_tab_list (List.map sprint_subst sigma_set) in let () = buffered_output "\n" in 
      if sigma_set == [] then   
	let () = buffered_output "DEBUG_POINT 10" in 
	[(def_st, [])] 
      else 
	List.map (fun x -> def_st, x) sigma_set 
    else
      let rec fn () =
        try
          let (h: (strategy * (var * term) list)) = get_sigma_and_st def_st in
          h::fn ()
        with Exit ->  [(def_st, [])] in
      fn () in

  (* 2: generate test substitutions *)
  let condition_1_for_clause (def_st:strategy) los =
    if is_automatic
    then
      let () =
        try
          greatest_var := ((fun (x,_,_) -> x) (last_el c#variables)) + 1
        with (Failure "last_el") -> () in
      let sigma_set = !generate_test_substitutions_for_clause los c in
      let () = buffered_output (!indent_string ^ "Found " ^ (string_of_int (List.length sigma_set)) ^ " test-substitutions") in
      let () = print_tab_list (List.map sprint_subst sigma_set) in let () = buffered_output "-" in
      if sigma_set == [] then   let () = buffered_output "DEBUG_POINT 10'" in [(def_st, [])] else  List.map (fun x -> def_st, x) sigma_set 
    else
      let rec fn () =
        try
          let (h: (strategy * (var * term) list)) = get_sigma_and_st def_st in
          h::fn ()
        with Exit ->  [(def_st, [])] in
      fn () in      




     (* List.map (fun x -> def_st, x) sigma_set
    else
      let rec fn () =
        try
          let h = get_sigma_and_st def_st in
          h::fn ()
        with Exit -> [] in
      fn () in *)

  (* 3: this function attempts to reduce subgoals according to the strategy, and stores the results *)
  let new_eq = ref [] in
  let process_instances pos (_, sigma) =
    (*let c' = c#substitute sigma in*)
    let c' = match sigma with
                    [] -> buffered_output "DEBUG_POINT 11 ";c
                    | _ -> c#substitute sigma in


(* ******************************************************************************************************** *)
    let list_of_sorts = List.map (fun lit -> lit#lefthand_side#sort) c'#positive_lits in
    let list_of_list_context = try List.map (fun s -> critical_context_set_by_var#find s) list_of_sorts with _ -> [] in
    let (list_of_clausal_context: context list list) = megamix list_of_list_context in 
    let () = buffered_output "Using Context :" in

    let fn1 a_clausal_context  =  List.iter (fun x -> buffered_output ("\t" ^ x#string)) a_clausal_context  in
    let () = List.iter fn1 list_of_clausal_context  in
    
    let list_of_new_clause = match list_of_clausal_context with
        [] -> [c']
      | _ -> 
	  let fn (clausal_context : context list) = 
	    let pl =  List.map2 
              (fun cont l -> (*let greatest_var := (fst (last_el c'#variables)) + 1 in*)
                
                let greatest_var_of_cont = ((fun (x,_,_) -> x) (last_el cont#variables)) in
                let contren = cont#rename in (*let () = print_string contren#string in*)
                let greatest_var_of_contren = ((fun (x,_,_) -> x) (last_el contren#variables)) in
                let () =
		  try
		    greatest_var := greatest_var_of_contren + 1
		  with (Failure "last_el") -> () in
                new literal (Lit_equal 
                  (contren#substitute [(cont#contextual_var + greatest_var_of_contren  - greatest_var_of_cont, l#lefthand_side)],
                  contren#substitute [(cont#contextual_var + greatest_var_of_contren - greatest_var_of_cont, l#righthand_side)])
                ))
              clausal_context c'#positive_lits 
	    in
            let (res: peano_context clause) = new clause (c'#negative_lits, pl) c#history in
	    res
	  in
	  List.map fn list_of_clausal_context 
    in
    let () = buffered_output (!indent_string ^ "Generation of:") in
    let () = List.iter (fun cl -> buffered_output(!indent_string ^ "» " ^ (cl#string))) list_of_new_clause in
    
(* ******************************************************************************************************** *)
    let all_pos_c cl = List.map (fun ((b, n, tp), ls)  -> List.map (fun x -> (b, n, tp @ x)) ls) (all_defined_positions cl#content) in
    let pos_subterms cl = List.rev (List.map (fun p -> (p, cl#subterm_at_position p)) (List.flatten (all_pos_c cl) )) in
      

    let reduce cl = 
      let lp_t = match pos with 
	  Pos_defined p -> [p, cl#subterm_at_position p] 
	| Pos_litdefined _ | Pos_all | Pos_query | Pos_dumb -> pos_subterms cl 
      in
      let max_var = cl#greatest_varcode + 1 in

      let fn t rule =
(* 	let () = buffered_output ("Unifying the rule is " ^ rule#string ^ " and with the term " ^ t#string ) in *)
(* 	let () = print_detailed_term t in *)
	
	let rule' = rule#substitute_and_rename [] max_var in (* rename the variables *)
	let lhs = rule'#lefthand_side in
	
	let (s1, s2) = try unify_terms t lhs false with Failure "unify_terms" -> failwith "fn" in
(* 	let () = buffered_output ("s1 = " ^ (sprint_subst s1) ^ " s2 = " ^ (sprint_subst s2)) in *)
	let _ = List.map (fun (i, t') -> (i, t'#expand_sorts)) s1 in
	let new_rule' = rule'#expand_sorts in
	
	let r = new_rule'#substitute s2 in 
(* 	let () = buffered_output ("new_rule' = " ^ new_rule'#string) in *)
	if s1 <> [] then failwith "fn" else
	[([], r, rule)] 
      in
      let rec fn1 subterm l = 
	match l with 
	    [] -> []
	  | r :: tl -> 
	      try 
		let tmp = fn subterm r in 
		tmp :: (fn1 subterm tl) 
	      with Failure "fn" -> fn1 subterm tl 
      in
      (* all the instances for a given subterm t *)
      let all_inst t =
 	let () = buffered_output ("\n treating " ^ t#string) in 
 	let k = try t#head with Failure "head" -> failwith ("generate: fail on term " ^ t#string) in 
	let rules_k = try dico_rules#find k with Not_found -> let () =  buffered_output ("\n no rules for " ^ t#string) in [] in
	if rules_k <> [] then
	  List.flatten (fn1 t rules_k) 
	else failwith "all_inst"
      in
      
      let rec fn2 l = 
	match l with 
	    [] -> failwith "fn2"
	  | (p, t) :: tl -> 
	      
	      
	      (* 	  let () = print_string ("\nWe will try to apply at the position " ^ (sprint_clausal_position *)
	      (* 	    p) ^ " (i.e. the term " ^ (c#subterm_at_position p)#string) in *)
	      
	      try 
		let ls = all_inst t in
		
(* 		let test = (List.exists (fun t -> not t#is_term) (List.flatten all_ts))  false in *)
		if (ls = []) (* or test  *)then fn2 tl 
		else 
		  (p, ls)
	      with Failure "all_inst" -> fn2 tl 
      in
      (* compute the substitutions  *)
      let p, ls = try fn2 lp_t with Failure "fn2" -> let () = print_history normalize cl in let () =  buffered_output ("\nWarning: fail generate on " ^ cl#string) in
      failwith "generate_obs" in
      (* start to write the instances  *)

      let i = ref 0 in
(*       let () = *)
(* 	if verbose *)
(* 	then *)
(* 	  let () = buffered_output (List.fold_left (fun x (s1,_,_) -> let () = i := !i + 1 in x ^ "\n " ^ !indent_string ^ (string_of_int *)
(* 	    !i) ^ ") " ^ (sprint_subst s1)) ("\n\nThe rule has been successfully applied at the position " ^ (sprint_clausal_position *)
(* 	    p) ^ " (i.e. the term " ^ (c#subterm_at_position p)#string ^ "), using the test substitutions: ") ls) in *)
(* 	  (*       let () = print_history c in *) *)
(* 	  () *)
(* 	else ()  *)
(*       in *)
      
      let treated_term = cl#subterm_at_position p in
      let () =
	if verbose
	then
	  buffered_output ("\n" ^ !indent_string ^ "We treat the subterm " ^ treated_term#string ^ " of " ^ cl#string)
	else () 
      in
      (* add the treated conjecture as premise  *)
(*       let () = if add_hyp then hypotheses_system#append [c] in *)
      
      let () = i := 0 in
      
      let fn5 (s, r, r_orig) = 
	let cond = r#negative_lits in
	let rhs = r#righthand_side in
	let cinst = cl#substitute s in
	(*     let () = write_pos_clause cinst in *)
(* 	let () = buffered_output ("cinst = " ^ cinst#string) in *)
	let c' = cinst#replace_subterm_at_pos p rhs in
	
	let (b, n, pos) = p in
	
	let phead = (b, n, [List.hd pos]) in
	let term = c'#subterm_at_position phead in
	
	let term' = term#update_pos in
	let cfinal = c'#replace_subterm_at_pos phead term' in
	
	let lneg, lpos = cfinal#content in
	let cond' = List.map (fun x -> x#update_pos) cond in
	let lpos' = List.map (fun x ->x#copy) lpos in
	let lneg' = List.map (fun x ->x#copy) (lneg @ cond') in
	let res = c#build lneg' lpos' in
	let () = res#add_history (s,c) in
	
	let () =
	  let () = i := !i + 1 in
	  if verbose
	  then
	    buffered_output ("\n" ^ !indent_string ^ (string_of_int !i) ^ ")" ^ res#string ^ "\n\n" ^ !indent_string ^ "using the rule
" ^ r_orig#string)
	  else () 
	in
	res
      in
(*       let () = incr generate_counter_suc in *)
      
      List.map fn5 ls
    in
      

      let res = List.flatten (List.map (reduce) list_of_new_clause) in
      let () = new_eq := !new_eq @ (List.map (fun c -> c#update_pos) res)  in
      true

  in

  (* 4: store current system, manage success/system recovery *)
  let e, h = (conjectures_system#content, hypotheses_system#content) in
  let success_or_fail pos l = 
      (*[] ->
        let () = conjectures_system#init e in
        let () = hypotheses_system#init h  in
        false
    | l -> *)
        let () = incr_indent indent_string in
        let () = new_eq := [] in
        if List.for_all (process_instances pos) l
        then (* réussite *)
	  let () = result := !new_eq @ !result in
(*           let () = conjectures_system#init ((list_all_but c_number e) @ !new_eq)  in *)
          let () = hypotheses_system#init (c::h)  in
          let () = decr_indent indent_string in
          let () =
            if verbose
            then
              buffered_output (!indent_string ^ "*** Generate " ^ (string_of_int ic) ^ " succeeded")
            else () in
          true
        else
          let () = decr_indent indent_string in
          let () = conjectures_system#init e in
          let () = hypotheses_system#init h  in
          false in

  (* 5: attempt generate on different sets of symbols *)
  let attempt_on_functions condition (st:strategy) pos =
    let rec fn l = function
        [] -> false (* échec *)
      | h::t ->
          let l' = merge_induction_positions h l in
          let () = buffered_output (!indent_string ^ "Computing test sets on " ^ (sprint_induction_position_specification l')) in
          let ts = condition st l' in
          success_or_fail pos ts
            or
          fn l' t in
    match arg_indpos with
      [] -> fn Ind_pos_void !induction_symbols_priorities
    | _ -> fn Ind_pos_void arg_indpos in

  (* 6: let's do it ! *)
  let res = 
    try 
      if c#is_unit
      then
	let lit = List.hd c#positive_lits in
	let lhs, rhs = lit#both_sides in
	if !rpos_greater false lhs rhs
	then
	  let () = buffered_output ("------> " ^ lhs#string ^ " > " ^ rhs#string) in
	  let () = buffered_output ("limiting position to: " ^ sprint_clausal_position (true, 0, [0])) in
	  attempt_on_functions (condition_1 lhs) (dico_st#find name_strat_generate_reduce) (Pos_defined (true, 0, [0]))
	else if !rpos_greater false  rhs lhs
	then
	  let () = buffered_output ("------> " ^ rhs#string ^ " > " ^ lhs#string) in
	  let () = buffered_output ("limiting position to: " ^ sprint_clausal_position (true, 0, [1])) in
	  attempt_on_functions (condition_1 rhs) (dico_st#find name_strat_generate_reduce) (Pos_defined (true, 0, [1]))
	else if !have_same_induction_variables lhs rhs
	then
	  attempt_on_functions (condition_1 rhs) (dico_st#find name_strat_generate_reduce) Pos_all
	else
	  attempt_on_functions condition_1_for_clause (dico_st#find name_strat_generate_reduce) Pos_all
      else
	attempt_on_functions condition_1_for_clause (dico_st#find name_strat_generate_reduce) Pos_all
    with Not_found -> failwith "raising Not_found in generate_obs"
  in 
  if res then !result else failwith "generate_obs"
    
