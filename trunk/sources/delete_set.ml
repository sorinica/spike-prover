
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
      ((lhs1#syntactic_equal lhs2) && (rhs1#syntactic_equal rhs2)) or
      ((lhs1#syntactic_equal rhs2) && (rhs1#syntactic_equal lhs2)) 
    in    
    let fn1 lhs rhs = 
      lhs#syntactic_equal rhs(*  or *)
(*       ((is_existential_var lhs) && (not (is_existential_var rhs))) or *)
(*       ((is_existential_var rhs) && (not (is_existential_var lhs)))  *)
    in

    if
      List.exists (fun x -> let lhs, rhs = x#both_sides in  fn1 rhs lhs) lpos
      or List.exists (fun l1 -> let lhs1, rhs1 = l1#both_sides in List.exists (fn' lhs1 rhs1) lpos) lneg
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
      let () =
        if !coq_mode
        then Coq.delete_set c#number
        else () 
      in
      []
    else
      let () = c#set_bit tautology_bit in failwith "fn" 
  in
  let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule TAUTOLOGY " ^ " on " ^ (string_of_int c#number)) in
(*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
  if c#has_bit tautology_bit
  then
    failwith "tautology"
  else
    let _ = try fn c with (Failure "fn") -> failwith "tautology" in
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
  List.fold_right (fun t l -> try let i = t#head in insert_sorted ( = ) ( < ) i l with Failure "head" -> l) all_t [] 

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
      try 
	let i = t#head in
	not (List.mem i lsymb_c)
      with Failure "head" -> false
  in
  
  let has_c'_uvars = List.exists (fun x -> is_universal_var x) c'#all_terms in
  
  if (has_c'_uvars && c'#cardinal > c#cardinal) or ((not has_c'_uvars) && List.exists fn_filter c'#all_terms)
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
		failwith "subsumption_subsumes: comparison"
	  | "C1" -> if not(clause_geq true false orig_c c_sigma) 
	    then failwith "subsumption_subsumes: comparison" 
	  | _ -> () in
	(* success *)
	(true, sigma)
      with (Failure "matching") 
	| (Failure "subsumption_subsumes: comparison") ->
	    (false, [])
	      
(* Actual subsumption.
   Default order for browsing systems is [R;L;E;H] *)
let subsumption verbose c los (cxt1,cxt2) level =

  let ls =
    match los with
        LOS_defined l -> l
      | LOS_query -> !spike_parse_list_of_systems ()
  in
  let delayed = ref false in  
  let () = incr subsumption_counter in
  let fn c (_,_) = 
    let c' = c#expand in
    let apply ss x = 
      if c#number = x#number or c#subsumption_has_failed x#number then false 
      else
	let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule SUBSUMPTION on " ^ (string_of_int c#number) ^ " with " ^ (string_of_int x#number) ^ " from " ^ ss) in
	let (success, epsilon) = subsumption_subsumes verbose ss x c' c level  in
	if  success then 
          let () = 
            if !coq_mode then
              match ss with
              | "L" -> 
                  let () = Coq.todo ("rewrite sp_lemma_" ^ (string_of_int x#number) ^ "\t (*delete_set*)") in
                  Coq.todo "trivial"                    
              | "C1" | "C2" ->
                  let () = Coq.rewrite_last_induction () in
                  Coq.todo "trivial"
              | _ -> ()
            else ()
          in
	  let () = match ss with "C1" -> if !maximal_output then print_history normalize c false | _ -> () in	  
	    if  verbose then 
              let () = buffered_output (!indent_string ^ "\nSUBSUMPTION: delete\n" ^
					  !indent_string ^ "\171 " ^ c#string ^ "\n\n" ^
					  !indent_string ^ "Subsumed in " ^ ss ^ " by " ^ x#string ^
					  !indent_string ^ "\n\n\twith epsilon = " ^ (sprint_subst epsilon) ^ "\n") in
	      let () = incr subsumption_counter_suc in
	      let member_symb s cl =
(* 		let () = print_history normalize cl false in *)
		let hist = cl#history in
		let def_symbs = List.fold_right (fun (_, c) l -> c#def_symbols @ l) hist [] in
		  List.mem s def_symbs
	      in
	      let all_hist c =
		List.map (fun (_,cl) -> cl#number) c#history
	      in
	      let br_symb, br_cl_number, (lnegs,lpos) = c#get_broken_info in
(* 	      let () = buffered_output "\nThe current conjectures are: \n========================" in *)
(* 	      let () = List.iter (fun x -> print_history normalize x false) !real_conjectures_system in *)
(* 	      let () = buffered_output "\n====================" in *)
(* 	      let () = buffered_output ("\nThe history of current conjectures having [ " ^ (string_of_int x#number) ^ " ] as ancestor and broken symbol " ^ br_symb ^ " are: ") in *)
	      let conjectures_historying_x = List.filter (fun c' -> List.mem x#number (all_hist c'))  !real_conjectures_system in
	      let () = delayed := (br_symb <> "") && (List.exists (fun y -> not (member_symb br_symb y)) conjectures_historying_x)  in
	      let () = if !maximal_output then buffered_output ("Delayed = " ^ (string_of_bool !delayed)) in
		if not !delayed then
		  let fn_greater cf = 
		    let () = if !maximal_output then buffered_output ("\n cf = " ^ cf#string) in
		    let () = if !maximal_output then print_history normalize cf false in
		    let rec fn_gamma l c_rez is_on = match l with
			[] -> if is_on then c_rez else failwith "fn_gamma in subsumption: doesn't find x"
		      | (subst, cl') :: tl -> 
			  let () = if !maximal_output then buffered_output ("\nTreating subst" ^ (sprint_subst subst) ^ " when is_on is " ^  (string_of_bool is_on)) in
			  if is_on then 
			    let c' = c_rez#substitute subst in
			      fn_gamma tl c' true
			  else
			    if cl'#number == x#number then let c' = cl'#substitute subst in fn_gamma tl c' true
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
		    let x_gamma = fn_gamma cf#history cf false in
		    let () = if !maximal_output then buffered_output ("\n x_gamma = " ^ x_gamma#string) in
		    let x_epsilon = x#substitute epsilon in 
		    let () = if !maximal_output then buffered_output ("\nepsilon = " ^ (sprint_subst epsilon)) in
		    let () = if !maximal_output then buffered_output ("\nx = " ^ x#string ^ "\n x_epsilon = " ^ x_epsilon#string) in
		      try
			let (rho1, rho2) = List.fold_right2 (fun t1 t2 (s1,s2) -> let (s1',s2') = unify_terms (t1#substitute s1) (t2#substitute s2) false in (s1@s1', s2@s2')) x_gamma#all_terms x_epsilon#all_terms ([],[])  in
			let () = if !maximal_output then buffered_output ("\nrho1 = " ^ (sprint_subst rho1) ^ " \nrho2 =  " ^ (sprint_subst rho2)) in
			let () = if !maximal_output then buffered_output ("\nComparing br_clause_sigma substituted by rho2 " ^ (br_clause_sigma#substitute rho2)#string ^ "\nwith cf substituted by rho1 " ^ (cf#substitute rho1)#string) in
			  clause_greater false false (br_clause_sigma#substitute rho2) (cf#substitute rho1)
		      with Failure "unify_terms" -> 
			let () = if !maximal_output then buffered_output "\nFail to unify x_gamma and x_epsilon" in 
			  true
		  in
		  let () = if !maximal_output then buffered_output ("\nTesting the conjectures historying [" ^ (string_of_int x#number) ^ "]") in
		  let res = List.for_all (fun c -> fn_greater c) conjectures_historying_x in
		  let br_symb_x,_,_ = x#get_broken_info in
		  let x_is_a_premise = (match ss with "C1" -> true|_ -> false) && not (List.mem x#number (List.map (fun c -> c#number) !real_conjectures_system)) in
		    if x_is_a_premise then
		      if  (br_symb_x == "") then true 
		      else
			if res then let () = buffered_output "\n Broken rewritten conjecture was deleted" in true
			else
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
		  List.exists (apply "C1") cxt1 or List.exists (apply "C2") cxt2 or List.exists (apply "C1") c_hist
	    )
	    or test tl
    in	
    if (not (c#has_bit subsumption_bit)) && (test ls) then if !delayed then let () = if !maximal_output then buffered_output "\n Delayed !" in failwith "fn" (* stuttering *) else [] 
    else
      let () = c#set_bit subsumption_bit in
      failwith "fn" 
  in
  try 
    fn c (cxt1,cxt2) 
  with (Failure "fn") -> 
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
	      if test_occur_check && ((is_negative && not h#is_diff) or (not is_negative && h#is_diff)) then
		let () = 
                  if verbose
                  then
                    let () = buffered_output ("\n" ^ !indent_string ^ "NEGATIVE CLASH by occur check: delete\n" ^
                    !indent_string ^ "\171 " ^ c#string) in
                    buffered_output ""
                  else () in
                true
	      else 
		try
		  let f = lhs#head
		  and f' = rhs#head in
		  let test1 = 
		    f <> f' && is_free_constructor f &&
		    is_free_constructor f' && 
		    (((not h#is_diff) && is_negative) or 
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
		with (Failure "head") ->
		  fn2 is_negative t in
      let n, p = c#content in
      if (fn2 true n) or (fn2 false p) then true
      else failwith "fn"
  in
  let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule NEGATIVE CLASH " ^ " on " ^ (string_of_int c#number) ) in
(*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)

(*   let () =  write_pos_clause c in  *)

  if c#has_bit negative_clash_bit
  then failwith "negative_clash"
  else
    let _ = try  fn c with (Failure "fn") -> failwith "negative_clash" in 
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
(*       let () = buffered_output ("\n augmentation : treating x = " ^ x#string) in  *)
      let x = x1#substitute_and_rename [] max_var in
      if not (c#augmentation_has_failed x#number) then 
	let lneg, _ = x#content in
	if (* x#is_horn &&  *) lneg <> [] then 
	  (* take x and extract its negative part  *)
	  let x' = new clause (lneg, []) [] ("",0,([],[])) in

	  let rec fn1 ln = 
(* 	    let () = buffered_output ("\n ln = " ^ (sprint_list "\t" (fun x -> x#string) ln)) in *)
	    let new_c = c#build ln lpos' in 
	    let c' = new_c#expand in
	    let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule AUGMENTATION " ^ " on " ^ (string_of_int c#number) ^ " with " ^ (string_of_int x1#number) ^ " from " ^ ss) in
	    let success, sigma  = subsumption_subsumes verbose ss x' c' new_c level  in
	    if  success then 
		let x_sigma = x#substitute sigma in
		let added_lits = 
		  let fn lit = 
(* 		    let () = buffered_output ("\n Treating lit = " ^ lit#string) in *)
		    let is_bad = 
		      let lhs, rhs = lit#both_sides in
		      (lhs#syntactic_equal rhs) or
		      (list_member (fun x y -> x#syntactic_equal y) lit c#negative_lits) or
		      (let vars_xsigma = x_sigma#variables in
		      (difference (fun (i1, s1, b1) (i2, s2, b2) -> i1 = i2 && s1 = s2 && b1 = b2) vars_xsigma c#variables) <> [])
		    in
		    let already_added = list_member (fun x y -> x#syntactic_equal y) lit c#augmentation_literals in
		    if not (is_bad or already_added) then
		      let () = success_lc := list_insert (fun (x, _) (y, _) -> x#syntactic_equal y) (x1, ss) !success_lc in
		      let () = c#add_augmentation lit in
		      [lit] 
		    else let () = c#add_failed_augmentation x1#number in []
		  in
		  (* OR between the results  *)
		 List.flatten (List.map fn x_sigma#positive_lits)

		in
(* 		let () = buffered_output ("\n added lits : ") in *)
(* 		let () = print_list " OR " (fun x -> print_string x#string) added_lits in *)
		(* eliminate the conditions common to new_c and  x_sigma and try again new augmentation possibilities *)
		let new_ln = difference (fun x y -> x#syntactic_equal y) c'#negative_lits x_sigma#negative_lits in
		if difference (fun x y -> x#syntactic_equal y) ln new_ln <> [] then
		  let added_llits = fn1 new_ln in
		  (* 		let () = buffered_output ("\n ADDED LLITS : ") in *)
		  (* 		let () =   print_list "\n\tAND" (fun l -> let () = buffered_output "\nstart\t" in print_list " OR " (fun x -> print_string x#string) l) added_llits in *)
		  let res = 
		  if added_llits = [] then [added_lits] 
		  else 
		    (* OR between lists of AND *)
		    added_lits :: added_llits in
		  (* 		let () = buffered_output ("\n ---> res : ") in *)
		  (* 		let () = print_list "\n\tAND" (fun l -> let () = buffered_output "start\t" in print_list " OR " (fun x -> print_string x#string) l) res in *)
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
(* 		let () = print_list "\n\tAND"  (fun l -> let () = buffered_output "start\t" in print_list " OR " (fun x -> print_string x#string) l) res in *)
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
    let fn (lits : Literals.literal  list) = 
      let updated_lits = List.map (fun l -> l#update_pos) lits in
      let new_c = c#build (lneg' @ updated_lits) lpos' in 
      new_c
    in
    let lres = List.map fn llits in
    if (not (c#has_bit augmentation_bit)) && (lres <> [] ) then 
      (* ready to create the new clause  *)
      let () = if  verbose then 
        let () = buffered_output (!indent_string ^ "\nAUGMENTATION: simplify\n" ^
        !indent_string ^ "\171 " ^ c#string ^ "\n") in
	let () = List.iter (fun (x, ss) -> buffered_output ("\t Success with " ^ x#string ^ " from " ^ ss) ) !success_lc in
        let () = List.iter (fun x -> buffered_output (!indent_string ^ "\n\187 " ^ x#string)) lres in
	()
      in
      let () = incr augmentation_counter_suc in
      lres
    else
      let () = c#set_bit augmentation_bit in
      failwith "fn" 
  in
  try 
    fn c (cxt1,cxt2) 
  with (Failure "fn") -> 
    failwith "augmentation" (* échec *)
