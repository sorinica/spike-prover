(*
   * Project: Spike ver 0.1
   * File: contextual_rewriting.ml
   * Content: Contextual rewriting rule
*)
   
open Values
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Order
open Literals
open Dummies
open Clauses
open Normalize
open Shell

(* Arguments for contextual rewriting are:
   - a boolean specifying whether or not we print the result of this rule
   - a strategy for the recursive call
   - a list of systems to be visited
   - a clausal position
   - a context
   - the clause to be treated
*)

let contextual_rewriting verbose st sl c_pos (cxt1,cxt2) c is_strict level =
  
  let res = ref ([] : Clauses.peano_context Clauses.clause list) in
  let max_var = c#greatest_varcode + 1 in

  (* 1: process arguments *)
  let arg_st, arg_sl, arg_pos =
    let arg_st =
      if st#is_query then
        !spike_parse_strategy (try dico_st#find name_strat_query with Not_found -> failwith "raising Not_found in contextual_rewriting") ()
      else st
    and arg_sl =
      match sl with
          LOS_defined l -> l
      	| LOS_query -> !spike_parse_list_of_systems ()
    and arg_pos =
      match c_pos with
          Pos_defined (b, n, p) ->
            begin
              match p with
		  0::_ ->
                    begin
                      try let _ = c#subterm_at_position (b, n, p) in Pos_defined (b, n, p)
                      with (Failure "subterm_at_position") ->
                    	print_string "Invalid position" ;
                    	buffered_output "" ;
                    	!spike_parse_clausal_lhs_position c ()
                    end
            	| _ ->
                    print_string "Invalid position" ;
                    buffered_output "" ;
                    !spike_parse_clausal_lhs_position c ()
            end
      	| Pos_litdefined p ->
            begin
              try let _ = c#lit_at_position p in c_pos
              with (Failure "lit_at_position") ->
              	print_string "Invalid position" ;
              	buffered_output "" ;
              	!spike_parse_clausal_lhs_position c ()
            end
      	| Pos_all -> c_pos
      	| Pos_query -> !spike_parse_clausal_lhs_position c () 
	| Pos_dumb -> failwith "positions in contextual_rewriting"
    in
    arg_st, arg_sl, arg_pos 
  in
  
  (* 2: specify the first condition for success.
     Provided a literal (the positive literal of a horn clause, we return:
     - the clausal position the matching occured at
     - the substitution
     - the boolean concerning preservation of the orientation of the literal *)
  let condition_1 proceed_fun l_2_r =
    match arg_pos with
      Pos_defined (b, n, p) ->
        begin
          let t = c#subterm_at_position (b, n, p)
          and lhs, rhs = l_2_r#both_sides in
          try
            let p', sigma = t#subterm_matching (fun x s -> proceed_fun (b, n, p@x) s true) lhs  in
            (b, n, p@p'), sigma, true
          with Failure ("matching") ->
            if l_2_r#is_oriented
            then failwith ("matching")
            else
              let p', sigma = t#subterm_matching (fun x s -> proceed_fun (b, n, p@x) s false) rhs  in
              (b, n, p@p'), sigma, false
        end
    | Pos_litdefined (b, n) ->
        let lit = c#lit_at_position (b, n) in
        let p, sigma, kept_or = lit#subterm_matching (fun p -> proceed_fun (b, n, p)) l_2_r in
        (b, n, p), sigma, kept_or
    | Pos_all ->
        c#subterm_matching proceed_fun l_2_r
    | Pos_query -> invalid_arg "contextual_rewriting"
    | Pos_dumb -> failwith "positions in contextual_rewriting"

  and condition_2 lhs rhs =
    !rpos_greater false lhs rhs

  (* 6: recursive call *)
  and condition_3 new_soc =
    let new_hyps = recursive_new_hyps c new_soc (cxt1,cxt2) in
      arg_st#apply_to_subgoals !output_verbosity c new_hyps new_soc is_strict (* to complete with the available context for the recursive call *)
  in

  (* 7: Make a conjunction of these conditions for a given rewrite rule. *)
  let all_conditions type_system nr_cxt rw_r =
    let l_2_r = List.hd rw_r#positive_lits
    and _ = rw_r#negative_lits 
    in
    let other_conditions (b, n, p) sigma kept_or =
      let rw_r', _ = rw_r#substitute_and_rename sigma max_var in
      let l_2_r = List.hd rw_r'#positive_lits
      and gamma = rw_r'#negative_lits in
      let lhs, rhs = l_2_r#both_sides_w_or kept_or
      and rw_r_is_oriented = l_2_r#is_oriented in
      let new_cl = c#replace_subterm_at_pos (b, n, p) rhs in
      if (rw_r_is_oriented or condition_2 lhs rhs)
        &&
        (match type_system with C -> (if nr_cxt = 2 then clause_greater false false c rw_r'  else clause_geq false false c rw_r' )
	  | L|R -> true)
	&&
	((is_strict && clause_greater false false c new_cl) || ((not is_strict) && clause_geq false false c new_cl))
        &&
        (let delta = c#build_best_context b n in
         let new_soc = List.map (fun x -> c#build delta [ x ]) gamma in
         let boolval =
           match gamma with
               [] -> true
             | _ ->
		 let () = print_indent_string ("Contextual rewriting producing contexts:") in
                 let () = List.iter (fun x -> print_indent_string ( x#string)) new_soc in
                 let () = print_indent_string  ("will be proved using strategy " ^ st#string)
		 in
		 condition_3 new_soc 
	 in
         let () =
           if boolval (* réussite *)
           then
             let () = res := preprocess_conjecture new_cl in
(*              let () = lemmas_system#append new_soc in *)
             let crc = !contextual_rewriting_counter_suc in
             let () = incr contextual_rewriting_counter_suc in
             if verbose then
               let () = buffered_output (!indent_string ^ "CONTEXTUAL REWRITING " ^ (string_of_int crc) ^ ": simplify clause\n" ^
                                         !indent_string ^ c#string ^ "\n" ^ !indent_string ^ "on " ^
                                         (match b with true -> "positive literal " | false -> "negative literal ") ^
                                         (string_of_int n) ^ " at position " ^ (sprint_position p) ^
                                         "\n" ^ !indent_string ^ "Using clause\n" ^ !indent_string ^ rw_r#string ^ "\n"^ 
	                                 !indent_string ^ "Contexts:") 
	       in
               let () = List.iter (fun x -> buffered_output (!indent_string ^ x#string)) new_soc in
               let () = buffered_output (!indent_string ^ "were proved using strategy " ^ st#string) in
               let () = if !sub_buffer <> ""
               then
                 let () = buffered_output (!indent_string ^ "************************************************************\n") in
                 let () = buffered_output (!sub_buffer ^ !indent_string ^ "************************************************************") in
		 sub_buffer := ""
               else () 
	       in
               buffered_output (!indent_string ^ "\171 " ^ c#string ^ "\n" ^
                                !indent_string ^ "\187 " ^ new_cl#string ^ "\n")
                
            else ()
          else
            let () = print_indent_string ("Failed to prove contexts:") in
            let () = List.iter (fun x -> print_indent_string (x#string)) new_soc in
            print_indent_string ("using strategy " ^ st#string)
	 in
         boolval)
      then sigma
      else failwith "matching" 
    in
    try
      let (_, _, _), _, _ = condition_1 other_conditions l_2_r in
      true
    with (Failure "matching") -> false 
  in
        
  (* 8: same conditions + test that we have a Horn clause
     boolean Horn variants: if used, all possible Horn clauses will be generated out of the (partially) boolean clause cl.
     This slows down the whole rule, although it might allow to find solutions that could be missed otherwise *)

  (* let absolutely_all_conditions is_h_or_e cl = cl#try_on_boolean_horn_variants (all_conditions is_h_or_r)*)
  let absolutely_all_conditions type_system nr_cxt cl = cl#is_horn && all_conditions type_system nr_cxt cl

  and lemmas_all_conditions type_system cl = cl#is_horn && all_conditions type_system 0 cl in

  (* 9: visit all systems in the specified order. *)
  let rec fn = function
      [] ->
        let () = c#set_bit contextual_rewriting_bit in
        false (* échec *)
    | C::t -> 
	 (List.exists (absolutely_all_conditions C 2) cxt2) or (List.exists (absolutely_all_conditions C 1) cxt1) or fn t 
    | R::t ->
        if c#has_bit contextual_rewriting_bit
        then fn t
        else rewrite_system#exists (all_conditions R 0) or fn t
    | L::t -> lemmas_system#exists (lemmas_all_conditions L) or fn t 
  in

  (* 10: let's do it ! *)
  let () = incr contextual_rewriting_counter in
  let _ = if !maximal_output then  buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule CONTEXTUAL REWRITING " ^ " on " ^ (string_of_int c#number)) in
(*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
  if fn arg_sl
  then !res (* réussite principale *)
  else (* échec principal *)
    failwith  "contextual_rewriting"




(* Special case: equational rewriting *)
let equational_rewriting verbose c_pos (cxt1,cxt2) c is_strict level =

  let res = ref ([]: Clauses.peano_context Clauses.clause list) in
  let max_var = c#greatest_varcode + 1 in

  (* 1: process arguments *)
  let arg_pos =
    match c_pos with
      Pos_defined p ->
        begin (* Discards second level PM *)
          try let _ = c#subterm_at_position p in c_pos
          with (Failure "subterm_at_position") ->
            print_string "Invalid position" ;
            buffered_output "" ;
            !spike_parse_literal_position_in_clause c ()
        end
    | Pos_litdefined n ->
        begin (* Discards second level PM *)
          try let _ = c#lit_at_position n in c_pos
          with (Failure "lit_at_position") ->
            print_string "Invalid position" ;
            buffered_output "" ;
            !spike_parse_literal_position_in_clause c ()
        end
    | Pos_all -> c_pos
    | Pos_query -> !spike_parse_literal_position_in_clause c ()
    | Pos_dumb -> failwith "positions in equational_rewriting"  
  in

  (* 2: condition 2 and success *)
  let condition_2 is_less l_2_r p sigma kept_or =
    let c_ref = c#build [] [l_2_r] in
    let c_ref_sigma, _ = c_ref#substitute_and_rename sigma max_var in
    let fst = (List.hd c_ref_sigma#positive_lits) in
    let _, rhs' = fst#both_sides_w_or kept_or in
    let new_cl = c#replace_subterm_at_pos p rhs' in
(*     let () = buffered_output ("the clause " ^ c#string ^ " is replaced by " ^ new_cl#string) in *)
(*     let () = buffered_output ("is_less is " ^ (string_of_bool is_less) ^ " and the comparison is " ^  (string_of_bool (clause_geq false c c_ref_sigma)) ) in *)
    if ((is_less && clause_greater false false c c_ref_sigma ) or ((not is_less) && clause_geq false false c c_ref_sigma))
      && ((is_strict && clause_greater false false c new_cl ) || ((not is_strict) && clause_geq false false c new_cl) )
    then
      let _ = res := preprocess_conjecture new_cl in
      let erc = !equational_rewriting_counter_suc in
      let () = incr equational_rewriting_counter_suc in
      let () =
        if verbose
        then
          let () = buffered_output (!indent_string ^ "EQUATIONAL REWRITING " ^ (string_of_int erc) ^ ": simplify\n" ^
                                    !indent_string ^ "\171 " ^ c#string ^ "\n" ^
                                    !indent_string ^ "\187 " ^ new_cl#string) in
          buffered_output ""
        else ()
      in sigma
    else
      failwith "matching" in

  (* 3: the conditions *)
  let all_conditions eq is_less =
    let l_2_r = List.hd eq#positive_lits in
    match arg_pos with
      Pos_defined (b, n, p) ->
        begin
          let t = c#subterm_at_position (b, n, p)
          and lhs, rhs = l_2_r#both_sides in
          try
            let p', sigma = t#subterm_matching (fun x s -> condition_2 is_less l_2_r  (b, n, p@x) s true) lhs in
            (b, n, p@p'), sigma, true
          with (Failure "matching") ->
            let p', sigma = t#subterm_matching (fun x s -> condition_2 is_less l_2_r (b, n, p@x) s false) rhs in
            (b, n, p@p'), sigma, false
        end
    | Pos_litdefined (b, n) ->
        let lit = c#lit_at_position (b, n) in
        let p, sigma, kept_or = lit#subterm_matching (fun x -> condition_2 is_less l_2_r (b, n, x) ) l_2_r in
        (b, n, p), sigma, kept_or
    | Pos_all ->
	(try
          c#subterm_matching (condition_2 is_less l_2_r ) l_2_r
	with (Failure "matching") ->
	  let inverted_l = l_2_r#swap in
	  c#subterm_matching (condition_2 is_less inverted_l) inverted_l)
    | Pos_query -> invalid_arg "equational rewriting" 
    | Pos_dumb -> failwith "positions in equational_rewriting"  

  in

  (* 4: same conditions + test that we have a unit clause *)
  let absolutely_all_conditions cl is_less =
    if cl#is_unit
    then
      try
        let _ = all_conditions cl is_less in
        true (* réussite *)
      with (Failure "matching") -> false
    else false in

  (* 5: let's do it ! *)
  let () = incr equational_rewriting_counter in
  let _ = if !maximal_output then  buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule EQUATIONAL REWRITING " ^ " on " ^ (string_of_int c#number)) in
(*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
  if (List.exists (fun x -> absolutely_all_conditions x true) cxt2) or  
    (List.exists (fun x -> absolutely_all_conditions x false) cxt1) then (* succes *)
    !res
  else 
    failwith "equational_rewriting"

let all_pos c = 
  let nl, pl = c#content in
  let fn b n lit = 
    let lhs, rhs = lit#both_sides in
    let p_lhs = lhs#pos_rewriting in
    let p_rhs = rhs#pos_rewriting in
    let res1 = if p_lhs = [] then [] else List.map (fun p -> (b, n, [0] @ p)) p_lhs in
    let res2 = if p_rhs = [] then [] else List.map (fun p -> (b, n, [1] @ p)) p_rhs in
    res1 @ res2
  in
  let i = ref (-1) in
  let res = List.fold_left (fun l lit -> i := !i + 1; (fn false !i lit) @ l) [] nl in
  let i = ref (-1) in
  let res' = List.fold_left (fun l lit -> i := !i + 1; (fn true !i lit) @ l) res pl in
  res'
    
let all_terms_pos c = 
  let all_pos_c = (* List.map (fun ((b, n, tp), ls)  -> List.map (fun x -> (b, n, tp @ x)) ls) c#pos_rewriting
		     (all_defined_positions c#content) *) 
    if !normalize_flag then 
      List.filter (fun (b, n, p) -> not (b && n = 0 && (List.hd p) = 0)) (all_pos c)
    else 
      all_pos c in
  let pos_subterms = (List.map (fun p -> (p, c#subterm_at_position p)) all_pos_c) in
  let pos_sorted = order_terms pos_subterms false in
  List.filter (fun (_, t') ->  if t'#is_constructor_term then false else if is_constructor t'#head then false else  true) pos_sorted  

let reduce_clause is_rewrite fn_rewrite arg_sl _ c cxt =
  
  
  let rec fn lpos cl = 
    match lpos with
	[] -> [], "", cl, []
      | ((b, n, p), t) :: tl -> 
	  try
	    (* the subterm at p did not changed after a previous rewriting operation. Start the replacement.  *)
	    (* 	      let () = buffered_output ("Trying at position " ^ (sprint_clausal_position (b, n, p)) ^ " the term " ^ t#string) in *)

	    let broken_infos, str, t', iHs = fn_rewrite arg_sl t c "" cxt 0 in
	    (* let () = buffered_output ("Reduce_clause:  return fn_rewrite with str = " ^ str ) in *)
	      (* if t#syntactic_equal t' then let () = buffered_output ("\nHere: no rewriting ") in broken_infos, str, c, [] *)
	      (* else *)
	    let c' = cl#replace_subterm_at_pos (b, n, p) t' in
	      
	    let phead = (b, n, [List.hd p]) in
	    let term = c'#subterm_at_position phead in
	      
	    let term' = term#update_pos in
	    let cfinal = c'#replace_subterm_at_pos phead term' in
	    let p_c' = all_terms_pos cfinal in
	      (* 	      let () = buffered_output ("\nsimplifications at " ^ (sprint_clausal_position (b, n, p)) ^ " on term\n\t " ^ t#string ^ "" ^ *)
	      (* 	      " \n to get " ^ cfinal#string ) in *)
	      
	    let broken_infos', str', cl', iHs' = 
	      if !dracula_mode then
		if iHs <> [] then  broken_infos, "", cfinal, iHs
		else
		  if is_rewrite then broken_infos, "", cfinal, [] else fn p_c' cfinal
	      else if is_rewrite then broken_infos, "", cfinal, [] else fn p_c' cfinal in
	      broken_infos' @ broken_infos, ("\n- rewriting at the position " ^ (sprint_clausal_position (b, n, p)) ^ ":\n" ^ str ^
					       (* 	      " \n to get " ^ cfinal#string ^ *)
					       str' ), cl', iHs' 
	  with (Failure "rewrite") -> 
	    let phead = (b, n, [List.hd p]) in
	    let term = cl#subterm_at_position phead in

	    let () = term#delpos_rewriting (List.tl p) in
	      fn tl cl 
  in
    
  let all_t = all_terms_pos c in
    fn all_t c
    


   (* Special case: rewriting *)
let rewriting verbose rw_kind sl pos cxt c is_strict level =
  if c#delete_standby then []
  else
    let all_hist c = List.map (fun (_,cl) -> cl#number) (([], c) :: c#history) in
      if c#standby then 
	let sb_IHs' = List.filter (fun (cH,_) -> 
				     (* let () = buffered_output ( "\n\n standby: The IH related to " ^ (string_of_int cH#number) ^ " will be checked") in *)
				     let offsprings_cH = List.filter (fun c' -> List.mem cH#number (c'#number :: (all_hist c')))  !real_conjectures_system in 
				       if  offsprings_cH = []  then (* all IHs have been  already proved *)
					 let () = buffered_output ( "\n\nStandby: The IH related to " ^ (string_of_int cH#number) ^ " is checked since it is already proved. ") in false
				       else
					 true) c#sb_IHs in
	  if sb_IHs' = [] then  let () = buffered_output ("\t    It unblocked the following operation:\n\n" ^ c#sb_string) in c#sb_newconjs
	  else let () = c#set_sb_IHs sb_IHs' in failwith "rewriting"
						  (* if c#standby then *)
						  (* 	let conjectures_historying_c = List.filter (fun c' -> List.mem c#number (all_hist c'))  !real_conjectures_system in  *)
						  (* 	  if  conjectures_historying_c = []  then (\* all IHs have been  already proved *\) *)
						  (* 	    let () = buffered_output c#sb_string in *)
						  (* 	    let () = List.iter (fun (cH,_) -> buffered_output ( "\n\n standby: The IH related to " ^ (string_of_int cH#number) ^ " is checked since it is already proved"))  c#sb_IHs in c#sb_newconjs *)
						  (* 	  else *)
						  (* 	    failwith "rewriting"  *)
						  (* else *)
      else
	let _ = if !maximal_output then  buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule REWRITING "^ " on " ^ (string_of_int c#number) ) in
	let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in

	let _ = rewriting_clauses := [] in
	  (*   let () =  write_pos_clause c in  *)

	let () = incr rewriting_counter in
	let arg_sl =
	  match sl with
	      LOS_defined l -> l
	    | LOS_query -> !spike_parse_list_of_systems ()
	in
	let broken_infos, str_proof, c', liHs = match pos with
	    Pos_defined p ->
	      begin
		try
		  let t = c#subterm_at_position p in
		  let br_symbs, str, t', iHs =
		    if rw_kind
		    then
		      normalize_plus arg_sl t c "" cxt 0
		    else
		      rewrite arg_sl t c "" cxt 0
		  in
		  let res = c#replace_subterm_at_pos p t' in
		    br_symbs, str, res, iHs
		with (Failure "matching")
		  | (Failure "rewrite") | (Failure "replace_subterm_at_pos") -> failwith "rewriting"
	      end
	  | Pos_litdefined _ | Pos_all | Pos_query | Pos_dumb ->
	      
	      match rw_kind with
		  true -> reduce_clause false normalize_plus arg_sl verbose c cxt 
		| false -> reduce_clause true rewrite arg_sl verbose c cxt 
	in
	  if (str_proof <> "") 
	  then
	    let test = if !dracula_mode then (* let () = buffered_output ("str_proof = " ^str_proof) in *) true   else (*  true *) if is_strict then  clause_greater false false c c' else clause_geq false false c c' in
	    let () = if !broken_order && (not test) then
	      let broken_info = try List.hd broken_infos with (Failure "hd") -> failwith "We are expecting a non empty list of broken infos" in 
	      let () = c'#set_broken_info broken_info in
	      let () = buffered_output ("\nWARNING: broken order !!!") in 
		(*       let () = print_history normalize c in *)
		()
	    in 
	      if test || !broken_order then 
		let res = preprocess_conjecture c' in (* réussite *)
		let crc = !rewriting_counter_suc in
		let () = incr rewriting_counter_suc in
		let success_str = ("\n" ^ !indent_string ^ "REWRITING " ^ (string_of_int crc) ^ ": simplify" ^
				     (if rw_kind then " by normalizing " else " by rewriting ") ^ "\n" ^
				     (match pos with 
					  Pos_defined p -> !indent_string ^ "at position " ^ sprint_clausal_position p ^ "\n" 
					| Pos_litdefined _ | Pos_all | Pos_query | Pos_dumb  -> ""
				     ) ^
				     !indent_string ^ "\171 " ^ c#string ^ "\n") 
		in
		  
		  if !dracula_mode && liHs <> [] then 
		    (* let () = buffered_output ("Here: res = " ^ (List.fold_right (fun x s -> x#string ^ s) res "")) in *)
		    let (cH, epsilon) = List.hd liHs in
		      
		    let current_conj_historying_cH = List.filter (fun c' -> List.mem cH#number (c'#number :: (all_hist c')))  !real_conjectures_system in
		      if current_conj_historying_cH = [] then (* cH was already proved *)
			let () = buffered_output success_str in 
			let () = buffered_output ("\n\n The IH (" ^ (string_of_int cH#number) ^ ", epsilon = " ^ (sprint_subst epsilon) ^ ") is checked since already proved") in 
			  res
		      else
			let rec fn_theta l c_rez str_rez cumulate c_ref =
			  match l with
			      [] -> (c_rez, str_rez)
			    | (subst, cl) :: tl ->
				let c' = c_rez#substitute subst in
				let str' = (str_rez ^ "\t(" ^ cl#string ^ " " ^ (sprint_subst subst) ^ ")\n") in
				  if cl#number = c_ref#number then 
				    fn_theta tl c' str' true c_ref 
				  else 
				    if cumulate then 
				      fn_theta tl c' str' true c_ref
				    else
				      fn_theta tl c_rez str_rez false c_ref
			in
			  if List.mem cH#number (List.map (fun (_,cl)-> cl#number) (([], c) :: c#history)) then
			    (* 1-cycle *)
			    let cHtheta, chunk_str = fn_theta c#history cH "" false cH in
 			      if clause_greater false false cHtheta (cH#substitute epsilon) then 
				let () = buffered_output (success_str ^ str_proof ^ (List.fold_left (fun s x-> !indent_string ^ "\n\187 " ^ x#string ^ "\n" ^ s) "\n\n" res)) in
				let () = buffered_output ("The IH (" ^ (cH#string) ^ " " ^ (sprint_subst epsilon) ^ ") is checked by the 1-cycle\n\n" ^ chunk_str) in res
			      else failwith "transitivity problem"
			  else 
			    (* detect 2-cycle. `more than two' cycles are not detected. Moreover, it is assumed that only one IH is attached to the other standby conjs *)
			    let () = buffered_output ("\n The IH (" ^ (cH#string) ^ " " ^ (sprint_subst epsilon) ^ ") will be checked !!! \n") in
			    let current_sb_conjs =  List.filter (fun cl -> cl#standby)  !real_conjectures_system in 
			      let () = if current_sb_conjs <> [] then buffered_output (List.fold_left (fun s c -> s ^ c#string ) "\nThe standby conjectures are: " current_sb_conjs) in
			    let sbconjs_historying_cH = List.filter (fun c' -> List.mem cH#number (all_hist c'))  current_sb_conjs in 
			    let rec fn_conj l = match l with
			      | [] -> failwith "fn_conj"
			      | sbc :: tl ->
				  let iHs_sbc = sbc#sb_IHs in
				    if (List.length iHs_sbc) <> 1 then fn_conj tl
				    else 
				      let (iH_sbc, delta) = List.hd iHs_sbc in
					let () = buffered_output ("\n The IH_sbc (" ^ (iH_sbc#string) ^ " " ^ (sprint_subst delta) ^ ") is found !") in
					if   List.mem iH_sbc#number (List.map (fun (_,cl)-> cl#number) c#history) then				    
					  (* testing 2-cycle *)
					  
					  let cH_theta_1, chunk_str1 = fn_theta sbc#history cH "" false cH in
					  let iH_sbc_theta_2, chunk_str2 = fn_theta c#history iH_sbc  "" false iH_sbc in
					    (* let () = buffered_output ("\nIH_sbc_theta_2 = " ^ iH_sbc_theta_2#string) in *)
					    (* let () = buffered_output ("\nThe history of " ^ c#string ^ " is: \n") in *)
					    let cH_epsilon = cH#substitute epsilon in
					    let iH_sbc_delta = iH_sbc#substitute delta in
					    (* let () = buffered_output ("\ncH_theta_1 = " ^ cH_theta_1#string ^ "should be greater than iH_sbc_delta = " ^ iH_sbc_delta#string) in *)
					    (* let () = buffered_output ("\niH_sbc_theta_2 = " ^ iH_sbc_theta_2#string ^ "should be greater than cH_epsilon = " ^ cH_epsilon#string) in *)
					    if (clause_greater false false cH_theta_1  iH_sbc_delta) && 
					      (clause_greater false false iH_sbc_theta_2 cH_epsilon)
					    then
					      (* success *)
					      let () = buffered_output (success_str ^ str_proof ^ (List.fold_left (fun s x-> !indent_string ^ "\n\187 " ^ x#string ^ "\n" ^ s) "" res)) in
					      let () = buffered_output  ("\n A 2-cycle has been found using the standby conjecture " ^ sbc#string ^ "\n\nThe IHs ([" ^ (string_of_int cH#number) ^ " ], " ^(sprint_subst epsilon) ^ ") and " ^ "([ " ^ (string_of_int iH_sbc#number) ^ " ], (" ^ (sprint_subst delta) ^ ") are checked by the 2-cycle: \n\n" ^ chunk_str1 ^ "\n\n" ^ chunk_str2 ^ "\n\n") in
					      let () = buffered_output ("\n The 2-cycle unblocked the following operation on [ " ^ (string_of_int sbc#number) ^ " ]:\n") in 
					      let () = buffered_output sbc#sb_string in
					      let () = sbc#set_delete_standby true in
						res @ sbc#sb_newconjs
					    else fn_conj tl
					else (* let () = buffered_output "\n... but no 2-cycle has been found !" in  *)fn_conj tl
			    in
			      try fn_conj sbconjs_historying_cH with Failure "fn_conj" -> 
				let () = buffered_output ("\nFailed to find a cycle to check the iH (" ^ cH#string ^ " " ^ (sprint_subst epsilon) ^ "), so the conjecture [ " ^ (string_of_int c#number) ^ " ] is put on standby !\n\n") in
				let () = c#set_standby true in
				let () = c#set_sb_string (success_str ^ str_proof ^ (List.fold_left (fun s x-> !indent_string ^ "\n\187 " ^ x#string ^ "\n" ^ s) "" res)) in
				let () = c#set_sb_newconjs res in 
				let () = c#set_sb_IHs [(cH, epsilon)] in 
				  [c]

		  else
		    let () = 
		      if verbose then
			let () =  buffered_output success_str  in
			let () = buffered_output str_proof in
			  List.iter (fun x -> let () = buffered_output (!indent_string ^ "\n\187 " ^ x#string ^ "\n") in ()) res 
		    in
		    let hyp_rewriting = List.map (fun (c,_,_,s) -> (c, s)) (List.filter (fun (_, los, _, _) -> compare los "C1" == 0 or compare los "C2" == 0)  !rewriting_clauses) in
		      (*       let () = buffered_output ("\nsize of rewriting_clauses is " ^ (string_of_int (List.length !rewriting_clauses))) in *)
		    let () = 
		      if hyp_rewriting == [] then
			let () = List.iter (fun c1 -> coq_less_clauses:= !coq_less_clauses @ [(c1, c)]) res in	
			let () = coq_formulas := !coq_formulas @ [c] in   
			let () = List.iter (fun c1 -> coq_formulas_with_infos := !coq_formulas_with_infos @ [("rewriting", c#number, [], [(c1#number, [])], !rewriting_clauses)]) res in ()
		      else 
			(* 	let () = buffered_output "\nUse ind hypothesis for rewriting !" in *)
			let (h, subst) = List.hd hyp_rewriting in
			let h_subst = h#substitute subst in
			let () = 
			  if c#syntactic_equal h_subst then 
			    coq_replacing_clauses := (c#number, (h, subst, h#number)) :: !coq_replacing_clauses 
			  else
			    let cres = List.hd res in
			    let () = coq_formulas := !coq_formulas @ [c] in   
			    let () = List.iter (fun c1 -> coq_less_clauses:= !coq_less_clauses @ [(c1, c)]) res in	
			    let () = coq_less_clauses:= !coq_less_clauses @ [(h_subst, c)]  in
			    let () = coq_formulas_with_infos := !coq_formulas_with_infos @ [("rewriting", c#number, [(1, Def_sort 1, true)], [(cres#number, [])], (h, "C1", c, subst) :: !rewriting_clauses)] in ()
			in
			  ()
		    in
		    let () = List.iter (fun neq -> neq#add_history ([], c)) res in 
		      res
	      else
		failwith "rewriting" (* echec *)
	  else
	    failwith "rewriting" (* echec *)
