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
		  0::p' ->
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
    and gamma = rw_r#negative_lits 
    in
    let other_conditions (b, n, p) sigma kept_or =
      let rw_r' = rw_r#substitute_and_rename sigma max_var in
      let l_2_r = List.hd rw_r'#positive_lits
      and gamma = rw_r'#negative_lits in
      let lhs, rhs = l_2_r#both_sides_w_or kept_or
      and rw_r_is_oriented = l_2_r#is_oriented in
      let new_cl = c#replace_subterm_at_pos (b, n, p) rhs in
      if (rw_r_is_oriented or condition_2 lhs rhs)
        &&
        (match type_system with C -> (if nr_cxt = 2 then clause_greater false c rw_r'  else clause_geq false c rw_r' )
	  | L|R -> true)
	&&
	((is_strict && clause_greater false c new_cl) || ((not is_strict) && clause_geq false c new_cl))
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
      let (b, n, p), sigma, kept_or = condition_1 other_conditions l_2_r in
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
          try let cs = c#subterm_at_position p in c_pos
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
    let c_ref_sigma = c_ref#substitute_and_rename sigma max_var in
    let fst = (List.hd c_ref_sigma#positive_lits) in
    let lhs', rhs' = fst#both_sides_w_or kept_or in
    let new_cl = c#replace_subterm_at_pos p rhs' in
(*     let () = buffered_output ("the clause " ^ c#string ^ " is replaced by " ^ new_cl#string) in *)
(*     let () = buffered_output ("is_less is " ^ (string_of_bool is_less) ^ " and the comparison is " ^  (string_of_bool (clause_geq false c c_ref_sigma)) ) in *)
    if ((is_less && clause_greater false c c_ref_sigma ) or ((not is_less) && clause_geq false c c_ref_sigma))
      && ((is_strict && clause_greater false c new_cl ) || ((not is_strict) && clause_geq false c new_cl) )
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
    let p_lhs = lhs#pos_conditional_rewriting in
    let p_rhs = rhs#pos_conditional_rewriting in
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
  let all_pos_c = (* List.map (fun ((b, n, tp), ls)  -> List.map (fun x -> (b, n, tp @ x)) ls) c#pos_conditional_rewriting
		     (all_defined_positions c#content) *) 
    if !normalize_flag then 
      List.filter (fun (b, n, p) -> not (b && n = 0 && (List.hd p) = 0)) (all_pos c)
    else 
      all_pos c in
  let pos_subterms = (List.map (fun p -> (p, c#subterm_at_position p)) all_pos_c) in
  let pos_sorted = order_terms pos_subterms false in
  List.filter (fun (p', t') ->  if t'#is_constructor_term then false else if is_constructor t'#head then false else  true) pos_sorted  

let reduce_clause fn_rewrite arg_sl verbose c cxt =
  
  let res_str = ref "" in
  let rec fn lpos cl = 
    match lpos with
	[] -> "", cl
      | ((b, n, p), t) :: tl -> 
	    try
	      (* the subterm at p did not changed after a previous rewriting operation. Start the replacement.  *)
(* 	      let () = buffered_output ("Trying at position " ^ (sprint_clausal_position (b, n, p)) ^ " the term " ^ t#string) in *)

	      let str, t' = fn_rewrite arg_sl t c "" cxt 0 in
	      let c' = cl#replace_subterm_at_pos (b, n, p) t' in
	      
	      let phead = (b, n, [List.hd p]) in
	      let term = c'#subterm_at_position phead in
	      
	      let term' = term#update_pos in
	      let cfinal = c'#replace_subterm_at_pos phead term' in
	      let p_c' = all_terms_pos cfinal in
(* 	      let () = buffered_output ("\nsimplifications at " ^ (sprint_clausal_position (b, n, p)) ^ " on term\n\t " ^ t#string ^ "" ^ *)
(* 	      " \n to get " ^ cfinal#string ) in *)
	      let str', cl' = fn p_c' cfinal in
	      ("\n- rewriting at the position " ^ (sprint_clausal_position (b, n, p)) ^ ":\n" ^ str ^
(* 	      " \n to get " ^ cfinal#string ^ *)
	      str' ), cl' 
	    with (Failure "rewrite") -> 
	      let phead = (b, n, [List.hd p]) in
	      let term = cl#subterm_at_position phead in

	      let () = term#delpos_conditional_rewriting (List.tl p) in
	      fn tl cl 
  in
  
  let all_t = all_terms_pos c in
  fn all_t c
    


   (* Special case: conditional rewriting *)
let conditional_rewriting verbose rw_kind sl pos cxt c is_strict level =
  
  let _ = if !maximal_output then  buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule CONDITIONAL REWRITING "^ " on " ^ (string_of_int c#number) ) in
  let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in

(*   let () =  write_pos_clause c in  *)

  let () = incr conditional_rewriting_counter in
  let arg_sl =
    match sl with
	LOS_defined l -> l
      | LOS_query -> !spike_parse_list_of_systems ()
  in
  let str_proof, c' = match pos with
      Pos_defined p ->
	begin
          try
            let t = c#subterm_at_position p in
            let str, t' =
              if rw_kind
              then
		normalize_plus arg_sl t c "" cxt 0
              else
		rewrite arg_sl t c "" cxt 0
	    in
            let res = c#replace_subterm_at_pos p t' in
	    str, res
          with (Failure "matching")
            | (Failure "rewrite") | (Failure "replace_subterm_at_pos") -> failwith "conditional_rewriting"
	end
    | Pos_litdefined _ | Pos_all | Pos_query | Pos_dumb -> 
	  match rw_kind with
	      true -> reduce_clause normalize_plus arg_sl verbose c cxt 
            | false -> reduce_clause rewrite arg_sl verbose c cxt 
  in
  if (str_proof <> "") 
  then
    let is_greater = true (* clause_greater false c c' *) in
    let is_geq = (* clause_geq false c c'  *) true in
    if not (!broken_order || (is_strict && is_greater) || ((not is_strict) && is_geq)) then 
      failwith "conditional_rewriting" (* échec *)
    else 

      let res = preprocess_conjecture c' in (* réussite *)
      let crc = !conditional_rewriting_counter_suc in
      let () = incr conditional_rewriting_counter_suc in
      let () = 
	if verbose then
	  let () =  buffered_output ("\n" ^ !indent_string ^ "CONDITIONAL REWRITING " ^ (string_of_int crc) ^ ": simplify" ^
          (if rw_kind then " by normalizing " else " by rewriting ") ^ "\n" ^
          (match pos with 
	      Pos_defined p -> !indent_string ^ "at position " ^ sprint_clausal_position p ^ "\n" 
	    | Pos_litdefined _ | Pos_all | Pos_query | Pos_dumb  -> ""
	  ) ^
          !indent_string ^ "\171 " ^ c#string ^ "\n") in
          let () = Coq.contextual_rewriting c#number in
	  let () = buffered_output str_proof in
          List.iter (fun x -> let () = buffered_output (!indent_string ^ "\n\187 " ^ x#string ^ "\n") in ()) res 
      in
      res
  else
    failwith "conditional_rewriting" (* échec *)
