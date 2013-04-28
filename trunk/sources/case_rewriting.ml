
(*
   * Project: Spike ver 0.1
   * File: case_rewriting.ml
   * Content: Case rewriting rule
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
open Test_sets

let axiom_numbers = ref [];;

(* These conditions are shared by both partial and total case rewriting *)

(* condition 1 *)
let case_rw_condition_1 lhs rhs =
  !rpos_greater false lhs rhs


(* TODO: reorient clause instance after orientable test *)

(* compute all ([(rw_r_i, sigma_i)]) couples from the rewrite system,
   given p. (b,n,prefix) is a path *)
let case_rw_condition_2_with_p_given final_update (c: peano_context clause) b n p sl _ _ =
  let t = try c#subterm_at_position (b, n, p) with (Failure "subterm_at_position") -> failwith "case_rw_condition_2_with_p_given" in
(*   let () = buffered_output ("\nTreating t = " ^ t#string) in  *)
  let max_var = c#greatest_varcode + 1 in

  let k = t#head in

	  (* test for induction variables : at least one path should fit t *)
(*   let t_posvar = compute_induction_posvar t in *)
  
  let l1 = try dico_ind_positions_v0#find k with Not_found -> [] (* the symbol k is predefined *) in
  let rec fn_test n t l =
(*     let () = buffered_output ("\n" ^ (n_spaces n) ^ "treating t = " ^ t#string) in *)
    let res =
      match l with
	[] -> false
      | (symb, p) :: tl -> 
	  try 
	    if t#head = symb then 
	      if tl <> [] then 
		let t' = t#subterm_at_position [p] in
		fn_test (n + 2) t' tl
	      else true
	    else false 
	  with Failure "head" -> false
    in 
(*     let () = buffered_output ("\n" ^ (n_spaces n) ^ "Final res = " ^ (string_of_bool res)) in *)
    res
  in 
  let rec fn (l:(string * Clauses.peano_context Clauses.clause) list) = 
    match l with 
      [] -> []
    | (los, h) :: tail ->
(* 	let () =  buffered_output ("\n treating h = " ^ h#string) in *)
        try
	  let lhs' = h#lefthand_side in
(* 	  let () =  buffered_output ("\n\t treating lhs' = " ^ lhs'#string) in *)
            try
              let sub = t#matching
		(fun s ->
		  let hs, _ = h#substitute_and_rename s max_var in
		  if hs#oriented && ( match los with 
		      "L"  -> true
		    | "R"  -> true
		    | "C1" -> if !dracula_mode then failwith "case_rewriting: dracula not yet implemented" else clause_geq false false c hs 
		    | "C2" ->  if !dracula_mode then failwith "case_rewriting: dracula not yet implemented" else clause_greater false false c hs
		    | _ -> failwith "normalize: los") 
		  then 
		    s
		  else failwith "matching"
		)
		lhs'#update_pos
	      in
	      (h, sub, los) :: fn tail
            with 
		(Failure "matching") -> 
		  (   
		    if los <> "R" then (fn tail) else
		      try
	      	      let h' = h#swap_rule in
	      	      let lhs' = h'#lefthand_side in
              	      let sub' = t#matching
			(fun s ->
			  let hs', _ = (h'#substitute_and_rename s max_var) in
			  
			  if hs'#oriented &&
			    match los with 
				"L" -> true
			      | "R" -> false
			      | "C1" -> clause_geq false false c hs' 
			      | "C2" -> clause_greater false false c hs'
			      | _ -> failwith "normalize: los"
			  then 		    
			    s
			  else failwith "matching")
			lhs'#update_pos
		      in
		      (h, sub', los) :: fn tail 
		    with (Failure "matching") 
		      | (Failure "swap_rule") -> (fn tail)
		  )
	    with Not_Horn -> fn tail
  in
  let lpat_L = if List.mem L sl then complete_lemmas_system#content else [] in
  let lpat_L' = List.map (fun x -> ("L", x)) lpat_L in
  let k = try t#head with Failure "head" -> failwith ("case: fail on term " ^ t#string) in
  let rules_k = try dico_rules#find k with Not_found -> [] in
  let lpat_R = if List.mem R sl then rules_k else [] in
  let lpat_R' = List.map (fun x -> ("R", x)) lpat_R in  
  let l = 
    let res_L =  fn lpat_L' in
    if res_L <> [] then res_L else 
      let test = if l1 <> [] then List.exists (fun lpos -> List.for_all (fn_test 0 t) lpos) l1  else true in
      let () = if (not test) then failwith "case_rw_condition_2_with_p_given"  in 
      fn lpat_R' 
  in
  let () = if !maximal_output && l <> [] then buffered_output ("\nThe result is\n" ^ (List.fold_left  (fun y (x, _, _) -> ((y ^ x#string ) ^ "\n ")) "" l)) in 
  try 
    final_update t b n p l
  with (Failure "final_update") -> false
    
let generate_cond_and_eq t c b n p l _ =
  let max_var = c#greatest_varcode + 1 in
  let _, _ = c#content in
  let fn cl s =

    let lhs = cl#lefthand_side in
    let cl'', _ = cl#substitute_and_rename s max_var in
    (* we need to update the parameterized sorts from hsub *)
    let _ = unify_sorts (Actual_sort  t#sort) lhs#sort in
    let cl' = cl''#expand_sorts in
    let p_i = cl'#negative_lits in
    let p_i' = List.map (fun x -> x#update_pos) p_i in
    let r_i = cl'#righthand_side in
    let c' = c#replace_subterm_at_pos (b, n, p) r_i in
    (* update pos of the rewritten term  *)
    
    let phead = (b, n, [List.hd p]) in
    let term = c'#subterm_at_position phead in
    
    let term' = term#update_pos in
    let cfinal = c'#replace_subterm_at_pos phead term' in
    
    
    let negs, poss = cfinal#content in
    let negs' = List.map (fun x ->x#copy) (negs @ p_i') in
    let poss' = List.map (fun x ->x#copy) poss in
    let res = c#build negs' poss' in
    let () = axiom_numbers := !axiom_numbers @ [cl#number, []] in
    let () = rewriting_clauses := !rewriting_clauses @ [(res, "R", cl', s)] in 
    p_i, res 
  in
  let c_i, new_eq = list_2_2_map fn (List.map (fun (x, y, _) -> (x, y)) l) in
  let new_cond =
    if !system_is_strongly_sufficiently_complete && !free_constructors && !system_is_ground_convergent (* TODO: verifier *)
    then []
    else List.map (c#build []) (megamix c_i) in
  new_cond, new_eq
    
(* Arguments for case rewriting are:
   - a boolean specifying whether or not we print the result of this rule
   - a given clause
   - a literal position argument 
   - ...
*)

let partial_case_rewriting verbose sl c_pos cxt c is_strict level =
  
  let res_cxt = ref (true, 0, [], [], [], []: bool * int * position * (Clauses.peano_context Clauses.clause list) *
    (Clauses.peano_context Clauses.clause list) * ('a list))
  in
  (* 1: process arguments *)
  let arg_pos = 
    match c_pos with
        Pos_defined (b, n, p) ->
          begin (* Discards second level PM *)
            try let _ = c#subterm_at_position (b, n, p) in c_pos
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
      | Pos_dumb -> failwith "positions in partial_case_rewriting"

  
  in

  let arg_sl = 
    match sl with
        LOS_defined l ->  l
	 
      | LOS_query -> 
	  !spike_parse_list_of_systems () 
  in

  (* 2: final update *) 
  let final_update t b n p l =
    if l = [] then false else
      let new_cond, new_eq = generate_cond_and_eq t c b n p l true in
      let new_all = new_cond @ new_eq in (* the new conjectures *)
      let () =
(* 	if !broken_order then () *)
(* 	else  *)
	  if ((is_strict && (List.for_all (fun x -> clause_greater false false c x) new_all)) || 
	    ((not is_strict) && (List.for_all (fun x -> clause_geq false false c x) new_all)))
	  then 
	    ()
	  else failwith "final_update"
      in
      let () = res_cxt := (b, n, p, new_cond, new_eq, l) in
      true
  in
  (* 3: all conditions *) 
  let all_pos = 
    let nl, pl = c#content in
    let fn b n lit = 
      let lhs, rhs = lit#both_sides in
      let p_lhs = lhs#pos_partial_case_rewriting in
      let p_rhs = rhs#pos_partial_case_rewriting in
      let res1 = if p_lhs = [] then [] else List.map (fun p -> (b, n, [0] @ p)) p_lhs in
      let res2 = if p_rhs = [] then [] else List.map (fun p -> (b, n, [1] @ p)) p_rhs in
      res1 @ res2
    in
    let i = ref (-1) in
    let res = List.fold_left (fun l lit -> i := !i + 1; (fn false !i lit) @ l) [] nl in
    let i = ref (-1) in
    let res' = List.fold_left (fun l lit -> i := !i + 1; (fn true !i lit) @ l) res pl in
    res'
      
  in
    
  let rec all_conditions lpos =
    match lpos with
	[] -> false 
      | (b, n, p) :: t -> 
	      if case_rw_condition_2_with_p_given final_update c b n p arg_sl cxt is_strict then
		true
	      else 
		let trm = c#subterm_at_position (b, n, [(List.hd p)]) in
		let () = trm#resetpos_partial_case_rewriting in 

		all_conditions t
  in
  (* 4: process conditions on selected arguments ! *) 
  let try_all_conditions  =
    match arg_pos with
	Pos_defined (b, n, p) ->
          case_rw_condition_2_with_p_given final_update c b n p arg_sl cxt is_strict
      | Pos_litdefined (b, n) -> case_rw_condition_2_with_p_given final_update c b n [] arg_sl cxt is_strict
      | Pos_all ->
	  all_conditions all_pos 
      | Pos_query -> invalid_arg "partial case rewriting"
      | Pos_dumb -> failwith "positions in partial_case_rewriting"
  in  
  (* 5: let's do it ! *) 
  let () = incr partial_case_rewriting_counter in
  if c#has_bit partial_case_rewriting_bit
  then failwith "partial_case_rewriting" (* échec principal *)
  else
    let _ = if !maximal_output then  buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule Partial Case Rewriting on " ^ (string_of_int c#number)) in
(*     let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
    if try_all_conditions then 
      let b, n, p, new_cond, new_eq, l = !res_cxt in
      let () = 
	if verbose
	then
	  let pcrc = !partial_case_rewriting_counter_suc in
	  let () = incr partial_case_rewriting_counter_suc in
          let () = buffered_output (!indent_string ^ "Partial case rewriting " ^ (string_of_int pcrc) ^ ": simplify clause\n" ^
          !indent_string ^ c#string ^ "\n" ^
          !indent_string ^ "at position " ^ (sprint_clausal_position (b, n, p))) in
	  let () = 
	    if l <> [] then 
	      buffered_output ( " using the rules\n" ^
            (List.fold_left (^) "" (List.map (fun x -> !indent_string ^ x#string ^ "\n") (List.map (fun (x, _, _) -> x) l))))
	    else () 
	  in
	  let () = buffered_output (!indent_string ^ "\171 " ^ c#string) in
	  let () = if new_cond <> [] 
	  then let () = buffered_output (!indent_string ^ "\187 Conditions") in
	  List.iter (fun x -> buffered_output (!indent_string ^ "\187 " ^ x#string)) new_cond 
	  else ()
	  in
	  let () = buffered_output (!indent_string ^ "\187 Equations") in
	  let () = List.iter (fun x -> buffered_output (!indent_string ^ "\187 " ^ x#string)) new_eq in
	  buffered_output ""
	else ()
      in
      List.flatten (List.map preprocess_conjecture (new_cond @ new_eq)) (* reussite principale *)
    else (* echec principal *)
      let () = c#set_bit partial_case_rewriting_bit in
      failwith "partial_case_rewriting"
	
(* Arguments for case rewriting are:
     - a boolean specifying whether or not we print the result of this rule
     - a given clause
     - a literal position
     - a strategy for the recursive prover
*)

let total_case_rewriting verbose st sl c_pos cxt c is_strict level =
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
	else let () = c#set_sb_IHs sb_IHs' in failwith "total_case_rewriting"
else
  let _ =  if !maximal_output then  buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule TOTAL CASE REWRITING " ^ " on " ^ (string_of_int c#number)) in
    (*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)

  (*   let () = write_pos_clause c in  *)

  let res = ref ([]: Clauses.peano_context Clauses.clause list) in
  let () = rewriting_clauses := [] in
  let () = axiom_numbers := [] in
    (* 1: process arguments *)
  let _ =
    if st#is_query then
      !spike_parse_strategy (try dico_st#find name_strat_query with Not_found -> failwith "raising Not_found in total_case_rewriting") ()
    else st
  and arg_pos =
    match c_pos with
        Pos_defined (b, n, p) ->
          begin (* Discards second level PM *)
            try let _ = c#subterm_at_position (b, n, p) in c_pos
            with (Failure "subterm_at_position") ->
              print_string "Invalid position" ;
              buffered_output "" ;
              !spike_parse_literal_position_in_clause c ()
          end
      | Pos_litdefined (b, n) ->
          begin (* Discards second level PM *)
            try let _ = c#lit_at_position (b, n) in c_pos
            with (Failure "lit_at_position") ->
              print_string "Invalid position" ;
              buffered_output "" ;
              !spike_parse_literal_position_in_clause c ()
          end
      | Pos_all -> c_pos
      | Pos_query -> !spike_parse_literal_position_in_clause c () 
      | Pos_dumb -> failwith "positions in total_case_rewriting"
  in
  let arg_sl = 
    match sl with
        LOS_defined l ->  l
	  
      | LOS_query -> 
	  !spike_parse_list_of_systems () 
  in

  (* 2: final update *)
  let final_update st t b n p l =
    if l = [] then failwith "final_update"
    else
      let _ = (fun (_, _, s) -> s) (List.hd l) in
      let new_cond, new_eq = generate_cond_and_eq t c b n p l false in

      let test = 
	if !dracula_mode then true
	else
	  if !broken_order then true
	  else
	    if not !debug_mode then List.for_all (fun x -> if is_strict then clause_greater false false c x else clause_geq false false c x) new_eq 
	    else
	      (List.for_all (fun x ->
			       let res = if is_strict then clause_greater false false c x else clause_geq false false c x in 
				 (* let () = print_string ("\n Is c = " ^ c#string ^ *)
				 (* 						      " \n greater " ^ (if is_strict then "" else "or equal") ^ " than x = " ^ x#string ^ "\n Result: " ^ (string_of_bool res)) in  *)res) new_eq) 
      in
	if test 
	then
	  let bres = 
	    if !system_is_strongly_sufficiently_complete then true
	    else 
	      let new_hyps = recursive_new_hyps c new_cond cxt in
	      let () = buffered_output ("Warning : You didn't specify that the specification is strongly sufficiently complete. Please change accordingly or the system is going to call itself recursively.(feature not yet supported)") in
		st#apply_to_subgoals !output_verbosity c new_hyps new_cond false  (* to complete with the available context for the recursive call *)
	  in
	  let is_add_hyp = if List.for_all (fun x -> clause_greater false false c x) new_eq then true else false in
	  let tcrc = !total_case_rewriting_counter_suc in
	  let () = incr total_case_rewriting_counter_suc in
	  let () = if verbose
	  then
            let () = buffered_output (!indent_string ^ "TOTAL CASE REWRITING " ^ (string_of_int tcrc) ^ ": simplify clause\n" ^
					!indent_string ^ c#string ^ "\n\n" ^
					!indent_string ^ "at position " ^ (sprint_clausal_position (b, n, p)) ^ " on \t" ^ (c#subterm_at_position (b, n, p))#string) in
	    let () = if is_add_hyp && is_strict then 
	      let () = hypotheses_system#append [c] in buffered_output ("\n\n The current clause is added to H since the new conjectures are smaller : ")  
	    in
	    let () = if new_cond <> [] 
	    then 
	      let () = buffered_output (!indent_string ^ "Preconditions:") in
              let () = List.iter (fun x -> buffered_output (!indent_string ^ "\187 " ^ x#string)) new_cond in
		buffered_output (!indent_string ^ "were proved using strategy " ^ st#string) 
	    else ()
	    in
            let () = if !sub_buffer <> ""
            then
              let () = buffered_output (!indent_string ^ "************************************************************\n") in
		buffered_output (!sub_buffer ^ !indent_string ^ "************************************************************")
            else () 
	    in
            let () = buffered_output ("\n" ^ !indent_string ^ "\171 " ^ c#string ^ "\n\nwith the rules \n") in
	    let i = ref 0 in
	      (* 	  let () = prerr_endline "=====\n" in *)
	      (* 	  let () = List.iter (fun x -> let () = i := !i + 1 in prerr_endline (!indent_string ^ (string_of_int !i) ^ ") " ^
			  x#string)) (List.map fst l) in *)
	    let () = if List.length new_eq = 1 then prerr_endline ("\n total case rewriting : only one case for " ^ t#string) in
	    let () = List.iter (fun x -> let () = i := !i + 1 in  buffered_output (!indent_string ^ (string_of_int !i) ^ ") " ^
										     x#string)) (List.map (fun (x, _, _) -> x) l) in
	    let () = buffered_output ("\nresulting\n") in
	    let i = ref 0 in
            let () = List.iter2 (fun x (l, _, ls) -> let () = i := !i + 1 in buffered_output (!indent_string ^ "\187 " ^ (string_of_int
															    !i) ^ ") " ^ x#string ^ "\n\nusing " ^ !indent_string ^ "[ " ^ (string_of_int l#number) ^ " ] from " ^ ls ^ "\n")) new_eq l in
              buffered_output "" 
	  else () 
	  in
	  let () = res := List.flatten (List.map preprocess_conjecture new_eq) in
	    bres
	      
	else failwith "final_update"
  in
    
  let all_pos = 
    let nl, pl = c#content in
    let fn b n lit = 
      let lhs, rhs = lit#both_sides in
      let p_lhs = lhs#pos_total_case_rewriting in
      let p_rhs = rhs#pos_total_case_rewriting in
      let res1 = if p_lhs = [] then [] else List.map (fun p -> (b, n, [0] @ p)) p_lhs in
      let res2 = if p_rhs = [] then [] else List.map (fun p -> (b, n, [1] @ p)) p_rhs in
      let new_res1 =  
	if !normalize_flag then 
	  if b && n = 0 then [] else res1 
	else res1 
      in 
	new_res1 @ res2 
    in
    let i = ref (-1) in
    let res = List.fold_left (fun l lit -> i := !i + 1; (fn false !i lit) @ l) [] nl in
    let i = ref (-1) in
    let res' = List.fold_left (fun l lit -> i := !i + 1; (fn true !i lit) @ l) res pl in
      res'
	
  in
    
  (* sort the positions according to the order over the symbols  *)
    
  let pos_subterms = (List.map (fun p -> (p, c#subterm_at_position p)) all_pos) in
    
  let pos_subterms' =   List.filter (fun (_, t') ->  if t'#is_constructor_term then false else if is_constructor t'#head then false else true) pos_subterms in
  let pos_sorted = order_terms pos_subterms' false in
    
  (*   let () = buffered_output (List.fold_left (fun x (p, t) -> x ^ (sprint_clausal_position p) ^ "( t = " ^ t#string ^ ")" ^ " " ) ("\nPOS SORTED [" ^ *)
  (*   (string_of_int c#number) ^"] are: ") pos_sorted) in *)


  let rec all_conditions lpos =
    match lpos with
	[] -> false 
      | ((b, n, p), _) :: t -> 
	  (* 	  let () = buffered_output ("\nTreating the term " ^ (c#subterm_at_position (b, n, p))#string ^ " at position " ^ (sprint_clausal_position (b, n, p))) in *)
	  try 
	    if case_rw_condition_2_with_p_given (final_update st) c b n p arg_sl cxt is_strict then
	      true
	    else 
	      let _ = c#subterm_at_position (b, n, [(List.hd p)]) in 
		all_conditions t
	  with Failure "case_rw_condition_2_with_p_given" -> 
	    all_conditions t 
  in
    
  (* 3: process conditions on selected arguments ! *)
  let try_all_conditions =
    match arg_pos with
	Pos_defined (b, n, p) -> case_rw_condition_2_with_p_given (final_update st) c b n p arg_sl cxt is_strict
      | Pos_litdefined (b, n) -> case_rw_condition_2_with_p_given (final_update st) c b n [] arg_sl cxt is_strict
      | Pos_all ->
	  all_conditions pos_sorted
      | Pos_query -> invalid_arg "total case rewriting"
      | Pos_dumb -> failwith "positions in total_case_rewriting"
	  
  in
    (* 5: let's do it ! *) 
  let () = incr total_case_rewriting_counter in
    if all_pos = []  then failwith "total_case_rewriting" (* echec principal *)
    else
      if try_all_conditions
      then 
	let () = List.iter (fun c1 -> coq_less_clauses:= !coq_less_clauses @ [(c1, c)]) !res in
	let () = coq_formulas_with_infos := !coq_formulas_with_infos @ [("total_case_rewriting", c#number, [], !axiom_numbers, !rewriting_clauses)] in
	let () = coq_formulas := !coq_formulas @ [c] in   
	let () = List.iter (fun neq -> neq#add_history ([], c)) !res in 
	  !res (* reussite principale *)
      else (* echec principal *)
	failwith "total_case_rewriting" (* echec principal *)
	
(* TO DO : to add a new rule, CASE ANALYSIS, which performs the case analysis operation  *)
	
