
(*
   * Project: Spike ver 0.1
   * File: delete_set.ml
   * Content: Delete set
*)

open Values
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Literals
open Clauses
open Order
open Dummies
open Polynoms
open Normalize
  
  (* Checks whether clause is a tautology *)
let tautology verbose c level =

  let () = incr tautology_counter in
  (* 0: display *)
  let fn c =
    let n, p = c#content in
    let nd, ne = List.partition (fun x -> x#is_diff) n in
    let pd, pe = List.partition (fun x -> x#is_diff) p in
    let lpos = pe @ nd in
    let lneg = pd @ ne in
    let fn' lhs1 rhs1 l2 = 
      let lhs2, rhs2 = l2#both_sides in
      ((lhs1#syntactic_equal lhs2) && (rhs1#syntactic_equal rhs2)) ||
      ((lhs1#syntactic_equal rhs2) && (rhs1#syntactic_equal lhs2)) 
    in    
    let fn1 lhs rhs = 
      lhs#syntactic_equal rhs(*  or *)
(*       ((is_existential_var lhs) && (not (is_existential_var rhs))) or *)
(*       ((is_existential_var rhs) && (not (is_existential_var lhs)))  *)
    in

    if
      List.exists (fun x -> let lhs, rhs = x#both_sides in  fn1 rhs lhs) lpos
      || List.exists (fun l1 -> let lhs1, rhs1 = l1#both_sides in List.exists (fn' lhs1 rhs1) lpos) lneg
    then
      let () = incr tautology_counter_suc in
      let () = 
        if verbose
        then
          let () = buffered_output (!indent_string ^ "TAUTOLOGY: delete\n" ^
          !indent_string ^ "\171 " ^ c#string) in
          buffered_output ""
        else () 
      in
       []
    else
      let () = c#set_bit tautology_bit in failwith "fn" 
  in
  let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule TAUTOLOGY " ^ " on " ^ (string_of_int c#number)) in
(*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
  if c#has_bit tautology_bit || c#standby
  then
    failwith "tautology"
  else
    let _ = try fn c with (Failure _) -> failwith "tautology" in
    let () =  coq_formulas_with_infos := !coq_formulas_with_infos @ [("tautology", c#number, [], [], [])] in
    let () = coq_formulas := !coq_formulas @ [c] in   

    []

(* Subsumption.
   We use the algorithm of Gottlob & Leitsch (JACM, Vol 32, #2, april 1985, pp 280-295) *)

(* Build the array (literal with its sign, unmatched variables) *)
let subsumption_init_array c =
  let l = (List.map (fun x -> if x#is_diff then (true, x) else (false, x)) c#negative_lits) @ 
          (List.map (fun x -> if x#is_diff then (false, x) else (true, x)) c#positive_lits) in
  Array.of_list l

      (* Retrieve all equivalence classes from d *)
let subsumption_retrieve_equivalence_classes d =
  let l = ref [] in
  let fn _ v = l := v::!l in
  let () = d#iter fn in
  !l

(* Retrieve greatest simple clause *)
let rec subsumption_retrieve_greatest_simple_clause a = function
    [] -> [], []
  | h::t ->
      let simp, rest = subsumption_retrieve_greatest_simple_clause a t in
      match h with
        [] -> invalid_arg "subsumption_retrieve_greatest_simple_clause"
      | [(i, _)] ->
          let lit = a.(i) in
          lit::simp, rest
      | _ ->
          let fn x = List.length (snd x) <= 1 in
          if List.for_all fn h
          then ((List.map (fun x -> a.(fst x)) h) @ simp, rest)
          else (simp, h::rest)

(* Select L_top from a list of literals *)
let subsumption_select_l_top a l =
  match l with
    [] -> invalid_arg "problem"
  | h::t -> a.(fst h), t

(* Literals matching wrt the sign *)
let subsumption_lit_matching_core proceed_fun sigma (b, (lit:literal)) (b', (lit':literal)) =
  if b = b'
  then
(*     let () = buffered_output ("lit = " ^ lit#string ^ " and lit' = " ^ lit'#string) in *)
    lit'#matching_core proceed_fun sigma lit
  else
    failwith "matching"

  (* getting the head symbols of the terms from c  *)
let fn_symb c = 
  let all_t = c#all_terms in
  List.fold_right (fun t l -> try let i = t#head in insert_sorted ( = ) ( < ) i l with Failure _ -> l) all_t [] 

  (* getting the existential vars from c  *)
let fn_vare c = 
  let all_t = c#all_terms in
  List.fold_right (fun t l -> if is_existential_var t  then  insert_sorted ( = ) ( < ) t#var_content l else l) all_t [] 




(* Subsumption test of two clauses: does c' subsume c ? *)
let subsumption_subsumes _ system_string c' c orig_c _ =
  
  (*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ orig_c#string ^ "\n with clause [" ^ *)
  (*   (string_of_int c#number) ^ "]"); flush stdout  in *)
  (*     let lsymb_c' = fn_symb c' in *)
  let lsymb_c = fn_symb c in
  let lvare_c = fn_vare c in
  let _ = fn_vare c' in
  
  let fn_filter t = 
    (* filters only terms which are not related to lvare_c and lsymb_c  *)
    if is_existential_var t then
      not (List.mem t#var_content lvare_c)
    else 
      match t#head with
        | exception (Failure _) -> false
        | i -> not (List.mem i lsymb_c)
  in
  
  let has_c'_uvars = List.exists (fun x -> is_universal_var x) c'#all_terms in
  
  if (has_c'_uvars && c'#cardinal > c#cardinal) || ((not has_c'_uvars) && List.exists fn_filter c'#all_terms)
  then (false, [])
  else 
      let a = subsumption_init_array c' in
      let ln = (List.map (fun x -> if x#is_diff then (true, x) else (false, x)) c#negative_lits) in
      let lp = (List.map (fun x -> if x#is_diff then (false, x) else (true, x)) c#positive_lits) in
      let l_c = ln @ lp in
(*       let () = buffered_output ("\n\nl_c = " ^ (sprint_list " ; " (fun (b,x) -> x#string) l_c) ^ "\n from " ^ c#string) in *)
      let fun_consistency lit_t = 
	let lit = lit_t in
	let cl = c'#build c#negative_lits [lit] in
(* 	let () = buffered_output ("\ncl = " ^ cl#string) in *)
	try 
	  let _ = cl#fill_peano_context in false
	with Inconsistent -> true
      in
      let rec dc sigma l =
	(* 	let () = buffered_output "\nHere_dc" in *)
	let d = new equivalence_dictionary 13 in
	let () = d#init l in
	let () = d#fill (fun (_, l) (_, l') -> match generic_intersection_sorted_lists l l' with [] -> false | _ -> true) l in
	(* 	let () = buffered_output "\ndc: before subsumption_retrieve_equivalence_classes" in *)
	let classes = subsumption_retrieve_equivalence_classes d in
	let simp, rest = subsumption_retrieve_greatest_simple_clause a classes in
(*  	let () = buffered_output ("\nsimp  = " ^ (sprint_list " ; " (fun (b,x) -> x#string) simp) ^ "\n from " ^ c'#string) in  *)
	let sigma' = subsumes (fun s -> s) subsumption_lit_matching_core sigma simp l_c fun_consistency in
	(* 	let () = buffered_output "\ndc: ready to call tc" in *)
	List.fold_left tc sigma' rest
      and tc sigma l =
	(* 	let () = buffered_output "\nHere_tc" in *)
	let l_top, rest = subsumption_select_l_top a l in
	let proceed_fun s  =
          let vars_to_remove = List.map fst s in
          let newrest = List.map (fun (i, v) -> i, generic_remove_sorted_lists vars_to_remove v) rest in
          dc s newrest 
	in
	subsumes proceed_fun subsumption_lit_matching_core sigma [l_top] l_c fun_consistency in
      let n = c'#cardinal in
      let l = list_create n in
      let l' = List.map (fun i -> i, List.map (fun (x,_,_) -> x) ((snd a.(i))#variables)) l 
      in
      try
	let sigma = dc [] l' in
	(* 	let () = buffered_output ("\nsigma = " ^ (sprint_subst sigma) ^ " from " ^ system_string) in *)
	let c_sigma = c'#substitute sigma in
	(* 	let () = print_string ("\nHere, after sigma we have c_sigma = " ^ c_sigma#string) in *)
	let _ = match system_string with (* detect the cases when the procedure fails *)
	    "C2" -> 
	      if not(clause_greater false false orig_c c_sigma) then
		failwith "subsumption_subsumes"
	  | "C1" -> if not(clause_geq false false orig_c c_sigma) 
	    then failwith "subsumption_subsumes" 
	  | _ -> () in
	(* success *)
	(true, sigma)
      with (Failure _ ) ->
	    (false, [])
	      
(* Actual subsumption.  Default order for browsing systems is   [R;L;E;H] *) 

let subsumption verbose c los (cxt1,cxt2) level =

  if c#delete_standby then []
  else
    let all_hist c = List.map (fun (_,cl) -> cl#number) c#history in
    (* if c#standby then  *)
    (* 	let conjectures_historying_c = List.filter (fun c' -> List.mem c#number (all_hist c'))  !real_conjectures_system in  *)
    (* 	  if  conjectures_historying_c == []  then (\* all IHs have been  already proved *\) *)
    (* 	    let () = buffered_output c#sb_string in *)
    (* 	    let () = List.iter (fun (cH,_) -> buffered_output ( "\n\n The IH related to " ^ (string_of_int cH#number) ^ " is checked since it is already proved"))  c#sb_IHs in c#sb_newconjs *)
    (* 	  else *)
    (* 	    failwith "subsumption"  *)
    (* else *)
    let ls =
      match los with
	LOS_defined l -> l
      | LOS_query -> !spike_parse_list_of_systems ()
    in
    let delayed = ref false in  
    let () = incr subsumption_counter in
    let fn c (_,_) = 
      let c' = c#expand in
      let apply ss cH = 
	if c#number = cH#number || c#subsumption_has_failed cH#number then false 
	else
	  let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule SUBSUMPTION on " ^ (string_of_int c#number) ^ " with " ^ (string_of_int cH#number) ^ " from " ^ ss) in
	  let ih_greater = ((compare ss "C1" == 0) || (compare ss "C2" == 0)) && clause_greater false false cH c in (* no IH instance can be used *)
	  if ih_greater then 
	    let () = c#add_failed_subsumption cH#number in
	    false 
	  else
	    let (success, epsilon) = subsumption_subsumes verbose ss cH c' c level  in
	    let cHepsilon = cH#substitute epsilon in
	    let test_hyp = (compare ss "L" == 0) || (compare ss "R" == 0) || (compare ss "C2" == 0 && clause_greater false false c cHepsilon) || (compare ss "C1" == 0 && clause_geq false false c cHepsilon) in
	    if not test_hyp then 
	      let () = c#add_failed_subsumption cH#number in
	      false
	    else
	      if  success then 
		let success_str = (!indent_string ^ "\nSUBSUMPTION: delete\n" ^
				     !indent_string ^ "\171 " ^ c#string ^ "\n\n" ^
				       !indent_string ^ "Subsumed in " ^ ss ^ " by " ^ cH#string ^
				         !indent_string ^ "\n\n\twith epsilon = " ^ (sprint_subst epsilon) ^ "\n")
		in	   
		if !dracula_mode &&  (compare ss "C1" == 0 || compare ss "C2" == 0) then
		  let current_conj_historying_cH = List.filter (fun c' -> List.mem cH#number (c'#number :: (all_hist c')))  !real_conjectures_system in
		  if current_conj_historying_cH = [] then (* cH was already proved *)
		    let () = buffered_output success_str in 
		    let () = buffered_output ("\n\n The IH (" ^ (string_of_int cH#number) ^ ", " ^ (sprint_subst epsilon) ^ ") is checked since already proved") in true
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
		    if List.mem cH#number (List.map (fun (_,cl)-> cl#number) c#history) then
		      (* 1-cycle *)
		      let cHtheta, chunk_str = fn_theta c#history cH "" false cH in
 		      if clause_greater false false cHtheta (cH#substitute epsilon) then 			   
			let () = buffered_output success_str in 
			let () = buffered_output ("The IH (" ^ (cH#string) ^ " " ^ (sprint_subst epsilon) ^ ") is checked by the 1-cycle\n\n" ^ chunk_str) in 
			true
		      else failwith "transitivity problem"
		    else (* detect 2-cycle. `more than one' cycles are not detected. Moreover, it is assumed that only one IH is attached to the other standby conjs *)
		      let current_sb_conjs =  List.filter (fun cl -> cl#standby)  !real_conjectures_system in 
		      let sbconjs_historying_cH = List.filter (fun c' -> List.mem cH#number (all_hist c'))  current_sb_conjs in 
		      let rec fn_conj l = match l with
			| [] -> failwith "fn_conj"
			| sbc :: tl ->
			   let iHs_sbc = sbc#sb_IHs in
			   if (List.length iHs_sbc) <> 1 then fn_conj tl
			   else 
			     let (iH_sbc, delta) = List.hd iHs_sbc in
			     if   List.mem iH_sbc#number (List.map (fun (_,cl)-> cl#number) c#history) then				    
			       (* testing 2-cycle *)
			       let cH_theta_1, chunk_str1 = fn_theta sbc#history cH "" false cH in
			       let iH_sbc_theta_2, chunk_str2 = fn_theta c#history iH_sbc  "" false iH_sbc in
			       (* let () = buffered_output ("\nIH_sbc_theta_1 = " ^ iH_sbc_theta_1#string) in  *)
			       (* let () = buffered_output  ("\n The IHs ([" ^ (string_of_int cH#number) ^ " ], " ^(sprint_subst epsilon) ^ ") and " ^ "([ " ^ (string_of_int iH_sbc#number) ^ " ], (" ^ (sprint_subst delta) ^ ") are checked by the 2-cycle: \n\n chunk_str1 = " ^ chunk_str1 ^ "\n chunk_str2 = " ^ chunk_str2 ^ "\n\n") in *)
			       (* let () = buffered_output ("\nThe history of " ^ c#string ^ " is: \n") in *)
			       (* let () = print_history normalize c false in  *)
			       if (clause_greater false false cH_theta_1 (iH_sbc#substitute delta)) && 
				    (clause_greater false false iH_sbc_theta_2 (cH#substitute epsilon))
			       then
				 (* success *)
				 let () = buffered_output success_str  in
				 let () = buffered_output  ("\n A 2-cycle has been found using the standby conjecture " ^ sbc#string ^ "\n\nThe IHs ([" ^ (string_of_int cH#number) ^ " ], " ^(sprint_subst epsilon) ^ ") and " ^ "([ " ^ (string_of_int iH_sbc#number) ^ " ], (" ^ (sprint_subst delta) ^ ") are checked by the 2-cycle: \n\n" ^ chunk_str1 ^ "\n\n" ^ chunk_str2 ^ "\n\n") in
				 let () = buffered_output ("\n The 2-cycle unblocked the following operation on [ " ^ (string_of_int sbc#number) ^ " ]:\n") in  
				 let () = buffered_output sbc#sb_string in
				 let () = sbc#set_delete_standby true in
				 true
			       else fn_conj tl
			     else fn_conj tl
		      in
		      try fn_conj sbconjs_historying_cH with Failure _ -> 
			let () = buffered_output ("\nFailed to find a cycle to check the iH (" ^ cH#string ^ " " ^ (sprint_subst epsilon) ^ "), so the conjecture [ " ^ (string_of_int c#number) ^ " ] is put on standby !\n\n") in
			let () = c#set_standby true in
			let () = c#set_sb_string success_str in
			let () = c#set_sb_newconjs [] in 
			let () = c#set_sb_IHs [(cH, epsilon)] in 
			failwith "subsumption"
		else
 		  let () = match ss with "C1" -> if !maximal_output then print_history normalize c false | _ -> () in	  
		  if  verbose then 
		    let () = buffered_output success_str in
		    let () = incr subsumption_counter_suc in
		    let () = if compare ss "C1" == 0 || compare ss "C2" == 0 then 
			       let () = coq_replacing_clauses := (c#number, (cH, epsilon, cH#number)) :: !coq_replacing_clauses  in
			       let lc = ref [] in
			       let cHinst = cH#substitute epsilon in 
			       let () =  List.iter (fun (c1, c2) -> if c1#number == c#number then lc := (cHinst, c2) :: !lc) !coq_less_clauses in 
			       coq_less_clauses := !lc @ !coq_less_clauses
		             else
			       let () = coq_formulas := !coq_formulas @ [c] in
			       if compare ss "L" == 0 then
			         coq_formulas_with_infos := !coq_formulas_with_infos @ [("subsumption", c#number, [], [(cH#number,epsilon)], [])]
			       else (* axioms *)
			         coq_formulas_with_infos := !coq_formulas_with_infos @ [("subsumption", c#number, [], [], [])] 
		    in  
		    
		    let member_symb s cl =
		      (* 		let () = print_history normalize cl false in *)
		      let hist = cl#history in
		      let def_symbs = List.fold_right (fun (_, c) l -> c#def_symbols @ l) hist [] in
		      List.mem s def_symbs
		    in
		    
		    let br_symb, br_cl_number, (lnegs,lpos) = c#get_broken_info in
		    (* 	      let () = buffered_output "\nThe current conjectures are: \n========================" in *)
		    (* 	      let () = List.iter (fun x -> print_history normalize x false) !real_conjectures_system in *)
		    (* 	      let () = buffered_output "\n====================" in *)
		    (* 	      let () = buffered_output ("\nThe history of current conjectures having [ " ^ (string_of_int cH#number) ^ " ] as ancestor and broken symbol " ^ br_symb ^ " are: ") in *)
		    let conjectures_historying_cH = List.filter (fun c' -> List.mem cH#number (all_hist c'))  !real_conjectures_system in
		    let () = delayed := (br_symb <> "") && (List.exists (fun y -> not (member_symb br_symb y)) conjectures_historying_cH)  in
		    let () = if !maximal_output then buffered_output ("Delayed = " ^ (string_of_bool !delayed)) in
		    if (not !delayed) && (br_symb <> "") (* !broken_order *) then
		      let fn_greater cf = 
			let () = if !maximal_output then buffered_output ("\n cf = " ^ cf#string) in
			let () = if !maximal_output then print_history normalize cf false in
			let rec fn_gamma l c_rez is_on = match l with
			    [] -> if is_on then c_rez else failwith "fn_gamma in subsumption: doesn't find cH"
			  | (subst, cl') :: tl -> 
			     let () = if !maximal_output then buffered_output ("\nTreating subst" ^ (sprint_subst subst) ^ " when is_on is " ^  (string_of_bool is_on)) in
			     if is_on then 
			       let c' = c_rez#substitute subst in
			       fn_gamma tl c' true
			     else
			       if cl'#number == cH#number then let c' = cl'#substitute subst in fn_gamma tl c' true
			       else fn_gamma tl c_rez false
			in 
			let br_clause = c#build lnegs lpos in
			let () = if !maximal_output then buffered_output ("\n br_clause = " ^ br_clause#string) in
			let rec fn_sigma l c_rez is_on = match l with
			    [] -> if is_on then c_rez else failwith "fn_sigma in subsumption: doesn't find br_clause"
			  | (subst, cl') :: tl ->
			     (* 			  let () = print_string ("\n\n" ^ (sprint_subst subst) ^ " \n \t on " ^ cl#string) in *)
			     if is_on then 
			       let c' = c_rez#substitute subst in
			       fn_sigma tl c' true
			     else
			       if br_cl_number >= cl'#number then fn_sigma tl br_clause true
			       else fn_sigma tl c_rez false
			in
			let br_clause_sigma = fn_sigma c#history br_clause false in
			let () = if !maximal_output then buffered_output ("\n br_clause_sigma = " ^ br_clause_sigma#string) in		      
			let cH_gamma = fn_gamma cf#history cf false in
			let () = if !maximal_output then buffered_output ("\n cH_gamma = " ^ cH_gamma#string) in
			let cH_epsilon = cH#substitute epsilon in 
			let () = if !maximal_output then buffered_output ("\nepsilon = " ^ (sprint_subst epsilon)) in
			let () = if !maximal_output then buffered_output ("\ncH = " ^ cH#string ^ "\n cH_epsilon = " ^ cH_epsilon#string) in
			try
			  let (rho1, rho2) = List.fold_right2 (fun t1 t2 (s1,s2) -> 
                                                 let (s1',s2') = try unify_terms (t1#substitute s1) (t2#substitute s2) false  with Failure _ -> failwith "subsumption" in (s1@s1', s2@s2')) cH_gamma#all_terms cH_epsilon#all_terms ([],[]) in
			  let () = if !maximal_output then buffered_output ("\nrho1 = " ^ (sprint_subst rho1) ^ " \nrho2 =  " ^ (sprint_subst rho2)) in
			  let () = if !maximal_output then buffered_output ("\nComparing br_clause_sigma substituted by rho2 " ^ (br_clause_sigma#substitute rho2)#string ^ "\nwith cf substituted by rho1 " ^ (cf#substitute rho1)#string) in
			  clause_greater false false (br_clause_sigma#substitute rho2) (cf#substitute rho1)
			with Failure _ -> 
			  let () = if !maximal_output then buffered_output "\nFail to unify cH_gamma and cH_epsilon" in 
			  true
		      in
		      let () = if !maximal_output then buffered_output ("\nTesting the conjectures historying [" ^ (string_of_int cH#number) ^ "]") in

		      let cH_is_a_premise = (match ss with "C1" -> true|_ -> false) && not (List.mem cH#number (List.map (fun c -> c#number) !real_conjectures_system)) in
		      if cH_is_a_premise then
			let br_symb_cH, _, _ = cH#get_broken_info in
			if  (br_symb_cH == "") then true 
			else
			  let res = List.for_all (fun c -> fn_greater c) conjectures_historying_cH in
			  if res then let () = buffered_output "\n Broken rewritten conjecture was deleted" in true
			  else
			    let () = c#add_failed_subsumption c'#number in
			    false
		      else (* cH is a conjecture *)
			let cH_is_a_conjecture = List.mem cH#number (List.map (fun c -> c#number) !real_conjectures_system) in
			if cH_is_a_conjecture then 
			  let () = c#add_failed_subsumption c'#number in
			  false 
			else true
		    else true
		  else
		    true
	      else 
		let () = c#add_failed_subsumption c'#number in
		false
		
      in
      let rec test l = 
	match l with 
	  [] -> false
	| h :: tl -> 
	   (match h with 
	      R -> List.exists (apply "R") rewrite_system#content 
	    | L -> List.exists (apply "L") lemmas_system#content 
	    | C  -> 
	       let c_hist = List.map snd c#history in
	       List.exists (apply "C1") cxt1 || List.exists (apply "C2") cxt2 || List.exists (apply "C1") c_hist
	   )
	   || test tl
      in	
      if (not (c#has_bit subsumption_bit)) && (test ls) then if !delayed then let () =  buffered_output "\n Delayed !" in failwith "fn" (* stuttering *) else [] 
      else
	let () = c#set_bit subsumption_bit in
	failwith "fn" 
    in
    try 
      fn c (cxt1,cxt2) 
    with (Failure _) -> 
      failwith "subsumption" (* échec *)
    
(* Applied on all negative literals *)
let negative_clash verbose c level =

  let fn c =
    let rec fn2 is_negative = function
        [] -> let () = c#set_bit negative_clash_bit in false
      | h::t ->
         let lhs, rhs = h#both_sides in
	 let fn_occur var t = 
	   let rec fn_constructor p = 
	     match p with
	       [] -> true
	     | (s, _) :: t -> is_constructor s && fn_constructor t
	   in
	   let all_vars_with_pos = t#variable_paths in 
	   List.exists (fun ((v, _, _), path) -> v == var && fn_constructor path) all_vars_with_pos
	 in
	 let test_occur_check = 
	   ((not lhs#is_term) && rhs#is_term && is_constructor rhs#head && (fn_occur lhs#var_content rhs)) || 
	     ((not rhs#is_term) && rhs#is_term && is_constructor lhs#head && (fn_occur rhs#var_content lhs)) 
	 in
	 if test_occur_check && ((is_negative && not h#is_diff) || (not is_negative && h#is_diff)) then
	   let () = 
             if verbose
             then
               let () = buffered_output ("\n" ^ !indent_string ^ "NEGATIVE CLASH by occur check: delete\n" ^
                                           !indent_string ^ "\171 " ^ c#string) in
               buffered_output ""
             else () in
           true
	 else 
           match lhs#head with
           | exception (Failure _) -> fn2 is_negative t 
           | f -> match rhs#head with
                  | exception (Failure _) -> fn2 is_negative t 
                  | f' ->
		     let test1 = 
		       f <> f' && is_free_constructor f &&
		         is_free_constructor f' && 
		           (((not h#is_diff) && is_negative) || 
		              (h#is_diff && (not is_negative)))
		     in
		     if test1 then
                       let () = 
                         if verbose
                         then
			   let () = buffered_output ("\n" ^ !indent_string ^ "NEGATIVE CLASH: delete\n" ^
                                                       !indent_string ^ "\171 " ^ c#string) in
			   buffered_output ""
                         else () in
                       true
		     else
                       fn2 is_negative t
    in
    let n, p = c#content in
    if (fn2 true n) || (fn2 false p) then 
      let () =  coq_formulas_with_infos := !coq_formulas_with_infos @ [("negative_clash", c#number, [], [], [])] in
      let () = coq_formulas := !coq_formulas @ [c] in   
      true
    else failwith "fn"
  in
  let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule NEGATIVE CLASH " ^ " on " ^ (string_of_int c#number) ) in
  (*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)

  (*   let () =  write_pos_clause c in  *)

  if c#has_bit negative_clash_bit || c#standby
  then failwith "negative_clash"
  else
    let _ = try  fn c with (Failure _) -> failwith "negative_clash" in 
    [] 

(* Augmentation (c_eq, c) - adds to c the conclusion of a conditional equation if the conditions are subsumed by c
   Default order for browsing systems is [L] *)
let augmentation verbose c los (cxt1,cxt2) level =


  let ls =
    match los with
        LOS_defined l -> l
      | LOS_query -> !spike_parse_list_of_systems ()
  in
  
  let () = incr augmentation_counter in
  let success_lc = ref [] in 
  let fn c (_,_) = 
    let max_var = c#greatest_varcode + 1 in
    let lneg', lpos' = c#content in 
    let c_exp = c#expand in
    let lneg'', _ = c_exp#content in
    let apply ss x1 = 
      let () = if !dracula_mode && ss <> "L" then failwith "augmentation" in
(*       let () = buffered_output ("\n augmentation : treating x = " ^ x#string) in  *)
      let x, subst = x1#substitute_and_rename [] max_var in
      if not (c#augmentation_has_failed x1#number) then 
	  (* take x and extract its negative part  *)
	let lneg, lpos = x#content in
	let x_lneg = new clause (lneg, []) [] ("",0,([],[])) in
	let x_lpos = new clause ([], lpos) [] ("",0,([],[])) in
	if (* x#is_horn &&  *) clause_greater false false x_lneg x_lpos && lneg <> [] then 
	  let rec fn1 ln = 
(* 	    let () = buffered_output ("\n ln = " ^ (sprint_list "\t" (fun x -> x#string) ln)) in *)
	    let new_c = c#build ln lpos' in 
	    let c' = new_c#expand in
	    let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule AUGMENTATION " ^ " on " ^ (string_of_int c#number) ^ " with " ^ (string_of_int x1#number) ^ " from " ^ ss) in
	    let success, sigma  = subsumption_subsumes verbose ss x_lneg c' new_c level  in
	    if  success then 
		let x_sigma = x#substitute sigma in
		let added_lits = 
		  let fn lit = 
(* 		    let () = buffered_output ("\n Treating lit = " ^ lit#string) in *)
		    let is_bad = 
		      let lhs, rhs = lit#both_sides in
		      (lhs#syntactic_equal rhs) ||
		      (list_member (fun x y -> x#syntactic_equal y) lit c#negative_lits) ||
		      (let vars_xsigma = x_sigma#variables in
		      (difference (fun (i1, s1, b1) (i2, s2, b2) -> i1 = i2 && s1 = s2 && b1 = b2) vars_xsigma c#variables) <> [])
		    in
		    let already_added = list_member (fun x y -> x#syntactic_equal y) lit c#augmentation_literals in
		    if not (is_bad || already_added) then
		      let final_subst = List.map (fun (i, t) -> (i, t#substitute sigma)) subst   in
		      let () = success_lc := list_insert (fun (x, _,_) (y, _, _) -> x#syntactic_equal y) (x1, ss, final_subst) !success_lc in
		      let () = c#add_augmentation lit in
		      [lit, x_sigma#negative_lits] 
		    else let () = c#add_failed_augmentation x1#number in []
		  in
		  (* || between the results  *)
		 List.flatten (List.map fn x_sigma#positive_lits)

		in
(* 		let () = buffered_output ("\n added lits : ") in *)
(* 		let () = print_list " || " (fun x -> print_string x#string) added_lits in *)
		(* eliminate the conditions common to new_c and  x_sigma and try again new augmentation possibilities *)
		let new_ln = difference (fun x y -> x#syntactic_equal y) c'#negative_lits x_sigma#negative_lits in
		if difference (fun x y -> x#syntactic_equal y) ln new_ln <> [] then
		  let added_llits = fn1 new_ln in
		  (* 		let () = buffered_output ("\n ADDED LLITS : ") in *)
		  (* 		let () =   print_list "\n\tAND" (fun l -> let () = buffered_output "\nstart\t" in print_list " || " (fun x -> print_string x#string) l) added_llits in *)
		  let res = 
		  if added_llits = [] then [added_lits] 
		  else 
		    (* || between lists of AND *)
		    added_lits :: added_llits in
		  (* 		let () = buffered_output ("\n ---> res : ") in *)
		  (* 		let () = print_list "\n\tAND" (fun l -> let () = buffered_output "start\t" in print_list " || " (fun x -> print_string x#string) l) res in *)
		  res
		else
		  let () = c#add_failed_augmentation x1#number in []
	    else let () = c#add_failed_augmentation x1#number in []
	  in
	  fn1 lneg''
	else let () = c#add_failed_augmentation x1#number in []
      else []
    in
    let rec test l = 
      match l with 
	  [] -> []
	| h :: tl -> 
	    (match h with 
		R -> List.flatten (List.map (apply "R") rewrite_system#content)
	      | L -> let res = List.flatten (List.map (fun lit -> (apply "L" lit)) lemmas_system#content) in
(* 		let () = buffered_output ("\n ---> RES : ") in *)
(* 		let () = print_list "\n\tAND"  (fun l -> let () = buffered_output "start\t" in print_list " || " (fun x -> print_string x#string) l) res in *)
		res
	      | C  -> 
		  let c_hist = List.map snd c#history in
		  let lconj = List.flatten ((List.map (apply "C1") cxt1) @ (List.map (apply "C2")  (difference (fun x y ->
		    x#syntactic_equal y) cxt2 [c])) @ (List.map (apply "C1")  c_hist))  in
		  lconj
	    @ test tl)
    in	
    let llits = megamix (List.filter (fun x -> x <> []) (test ls)) in 
(*     let () = buffered_output ("\n ---> LLITS : ") in *)
(*     let () = print_list "\n\tOR" (fun l -> let () = buffered_output "start\t" in print_list " AND " (fun x -> print_string x#string) l) llits in *)
    let fn lits =
      let lits_to_add = List.map fst lits in
      let lits_to_elim = List.map snd lits in
      let lneg'_elim = difference (fun x y -> x#syntactic_equal y) lneg' (List.flatten lits_to_elim) in
      let updated_lits = List.map (fun l -> l#update_pos) lits_to_add in
      let new_c = c#build (lneg'_elim @ updated_lits) lpos' in 
      new_c
    in
    let lres = List.map fn  llits in
      if (not (c#has_bit augmentation_bit)) && (lres <> [] ) then 
	(* ready to create the new clause  *)
	let () = if !coqc_mode then 
	  let () = List.iter (fun c1 -> coq_less_clauses:= !coq_less_clauses @ [(c1, c)]) lres in
	  let () = coq_formulas_with_infos := !coq_formulas_with_infos @ [("augmentation", c#number, [], List.map (fun (x, ss, s) -> if compare ss "L" == 0 then (x#number, s) else failwith ("augmentation with infos from " ^ ss ^ " not yet treated !")) !success_lc, [])] in
	  let () = coq_formulas := !coq_formulas @ [c] in 
	    ()
	in
	  let () = if  verbose then 
            let () = buffered_output (!indent_string ^ "\nAUGMENTATION: simplify\n" ^
					!indent_string ^ "\171 " ^ c#string ^ "\n") in
	    let () = List.iter (fun (x, ss, _) -> buffered_output ("\t Success with " ^ x#string ^ " from " ^ ss) ) !success_lc in
            let () = List.iter (fun x -> buffered_output (!indent_string ^ "\n\187 " ^ x#string)) lres in
	      ()
	  in
	  let () = incr augmentation_counter_suc in
	  let () = List.iter (fun neq -> neq#add_history ([], c)) lres in 
	    lres
      else
	let () = c#set_bit augmentation_bit in
	  failwith "fn" 
  in
  try 
    fn c (cxt1,cxt2) 
  with (Failure _) -> 
    failwith "augmentation" (* échec *)
