
(*
   * Project: Spike ver 0.1
   * File: decomposition_set.ml
   * Content: Decomposition set
*)

open Values
open Diverse
open Io
open Symbols
open Terms
open Literals
open Clauses
open Dummies
open Order
open Normalize

  (* DECOMPOSITION  *)


(* If both term head are free constructors, build new literals with their sons *)
let decompose counter lit =
  let counter_tmp = !counter in 
  let fn1 lhs rhs  = 
    if equal_sorts lhs#sort rhs#sort then 
      match lit#content with
	  Lit_equal _ -> new literal (Lit_equal (lhs, rhs))
	| Lit_rule _ -> new literal (Lit_rule (lhs, rhs))
	| Lit_diff _ -> new literal (Lit_diff (lhs, rhs))
    else 
      failwith "fn1"
  in
  let rec fn lhs rhs =
    try
      let f, l = try lhs#head_n_sons with  Failure _ -> failwith "fn"
      and f', l' = try rhs#head_n_sons with  Failure _ -> failwith "fn" in
      if f = f' && is_free_constructor f
      then
        let () = incr counter in
        List.fold_left (@) [] (List.map2 fn l l')
      else
        [fn1 lhs rhs]
    with (Failure _) ->
        [fn1 lhs rhs]
  in
  let lhs = lit#lefthand_side in
  let rhs = lit#righthand_side in
  try fn lhs rhs with Failure _ -> let () = counter := counter_tmp in [lit]


let main_function verbose c level is_pos = 

  let _ =  if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule DECOMPOSITION" ^ " on " ^ (string_of_int c#number)) in
(*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)

(*   let () = if !maximal_output then  write_pos_clause c in  *)
  (* do it !  *)
  let n, p = c#content in


  let i = ref (-1) in
  let nl = List.map (fun x -> let () = i := !i + 1 in  (x, !i, false)) n in
  let i = ref (-1) in
  let pl = List.map (fun x -> let () = i := !i + 1 in  (x, !i, true)) p in

  let _ = rewriting_clauses := [] in
  (* compute the new literals  *)
  let main c =
    let appl_counter = ref 0 in
    let rec fn1 l = 
      match l with
	  [] -> failwith "fn1" 
	| (lit, n, b) :: tl ->
      let cnt = !appl_counter in
      let () = yy_tmp_param_sorts := [] in
      let new_lits = if b && n = 0 && !normalize_flag then [lit] else decompose appl_counter lit  in
      if cnt = !appl_counter then
	fn1 tl
      else (* the rule was applied *)
(* 	let new_lits' = List.map fn2 new_lits in *)
	let is_positive = 
	  match lit#content with 
	      Lit_equal _ | Lit_rule _ -> b
	    | Lit_diff _ -> not b
	in 
	(is_positive, b, n, new_lits)
    in
    
    let is_positive, b, pos, new_lits = try fn1 (nl @ pl) with Failure _ -> failwith "main" in

    let full_res = 
      if is_positive then List.map (fun x -> if not b then c#build (list_replace_element pos x n)  p else  c#build n (list_replace_element pos x p)) new_lits
      else [if not b then c#build (list_replace_element_w_list pos new_lits n) p else c#build n (list_replace_element_w_list pos new_lits p)]
    in
    is_positive, full_res

  in
  if (is_pos && c#has_bit positive_decomposition_bit) || ((not is_pos) && c#has_bit negative_decomposition_bit) then 
    if is_pos then failwith "positive_decomposition" else failwith "negative_decomposition"
  else 
 (* print the result *)   
    let is_positive, lres = 
      try 
	main c
      with (Failure _) -> 
	let () = c#set_bit positive_decomposition_bit in 
	let () = c#set_bit negative_decomposition_bit in 
	if is_pos then failwith "positive_decomposition" else failwith "negative_decomposition"
    in
    let () =
      if verbose
      then
        let () = buffered_output (!indent_string ^ (if is_positive then "POSITIVE" else "NEGATIVE")  ^ " DECOMPOSITION : simplify\n" ^
        !indent_string ^ "\171 " ^ c#string ^ "\n") in

	let () = List.iter (fun x -> buffered_output (!indent_string ^ "\187 " ^ x#string)) lres in
        buffered_output "" 
    in
    let lres' = List.map (fun x -> x#expand_sorts) lres in
    (* let dummy_term = List.hd (c#all_terms) in *)
    let dummy_clause = c in 
    let () = List.iter (fun c1 -> rewriting_clauses := !rewriting_clauses @ [(c1, "", dummy_clause, [] )]) lres' in 
    let () = List.iter (fun c1 -> coq_less_clauses:= !coq_less_clauses @ [(c1, c)] ) lres' in
    let () = coq_formulas_with_infos := !coq_formulas_with_infos @ [((if is_positive then "positive_decomposition" else "negative_decomposition"), c#number, [], (List.map (fun x -> (x#number, [])) lres'), !rewriting_clauses)] in
    let () = coq_formulas := !coq_formulas @ [c] in
	let () = List.iter (fun neq -> neq#add_history ([], c)) lres' in 
      (List.rev lres')
      
(* Recursively applied until saturation on all positive literals *)
let positive_decomposition verbose c level = main_function verbose c level true

(* Recursively applied until saturation on all negative literals *)
let negative_decomposition verbose c level  = main_function verbose c level false




  (* POSITIVE CLASH  *)

(* Applied on all positive literals *)
let positive_clash verbose c level  =

  (* 0: display *)
  let fn c =
    let pos_clash_counter = ref 0 in

  (* take the positions of c  *)
    let rec fn2 is_positive  = function
        [] -> []
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
	    let test_occur_check = ((not lhs#is_term) && rhs#is_term && is_constructor rhs#head && (fn_occur lhs#var_content rhs)) || 
		                     ((not rhs#is_term) && rhs#is_term && is_constructor lhs#head && (fn_occur rhs#var_content lhs)) in
	    if test_occur_check && ((is_positive && not h#is_diff) || (not is_positive && h#is_diff))
	    then
	      fn2 is_positive t
	    else
	      try
		let f = try lhs#head with  Failure _ -> failwith "fn2" 
		and f' = try rhs#head with  Failure _ -> failwith "fn2" in 
		if (f <> f' && is_free_constructor f &&
		is_free_constructor f' && 
		(((not h#is_diff) && is_positive) || 
		(h#is_diff && (not is_positive))))
		then
		  let () = incr pos_clash_counter in
		  fn2 is_positive t 
		else
		  h :: fn2 is_positive t 
              with (Failure _) ->
		h :: fn2 is_positive t 
    in
    let n, p = c#content in
    let p' = fn2 true p 
    and n' = fn2 false n in 
    match n', p' with
        [], [] -> let () = buffered_output "Positive clash produced a refutation" in 
	let () = if level = 1 then print_history normalize c true in 
	raise Refutation
      | _ ->
          if !pos_clash_counter > 0
          then
            let c' = c#build n' p' in
            let () = c'#set_bit positive_clash_bit in
            let () =
              if verbose
              then
                let () = buffered_output (!indent_string ^ "POSITIVE CLASH: simplify\n" ^
                !indent_string ^ "\171 " ^ c#string ^ "\n\n" ^
                !indent_string ^ "\187 " ^ c'#string) in
                buffered_output ""
              else () 
	    in c'
          else
            let () = c#set_bit positive_clash_bit in
            failwith "fn" 
  in
  if c#has_bit positive_clash_bit
  then failwith "positive_clash"
  else
    let _ = if !maximal_output then  buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule POSITIVE CLASH " ^ " on " ^ (string_of_int c#number)) in
    (*     let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
    let res = try fn c with (Failure _) -> failwith "positive_clash" in
    [res]


      
let insert_eq (lhs, rhs) l_eqcl =
(*   let () = buffered_output ("\ninsert_eq : " ^ lhs#string ^ " and " ^ rhs#string ^ " with l_eqcl =") in *)
(*   let () = print_list "\n\t " (fun l -> print_list ", " (fun x -> print_string x#string) l) l_eqcl in *)

  let fn_eq = (fun x y -> x#string = y#string) in
  let fn_inf = (fun x y -> x#string < y#string) in
  let rec get_eqcl t = function
    [] -> [t]
    | l :: tl -> if list_member fn_eq t l then l else get_eqcl t tl
  in

  (* build equivalence classes  *)
  let eqcl_lhs = get_eqcl lhs l_eqcl in
(*   let () = buffered_output ("\ninsert_eq : return list of lhs =" ) in *)
(*   let () = print_list ", " (fun x -> print_string x#string) eqcl_lhs in *)
  let eqcl_rhs = get_eqcl rhs l_eqcl in
(*   let () = buffered_output ("\ninsert_eq : return list of rhs =" ) in *)
(*   let () = print_list ", " (fun x -> print_string x#string) eqcl_rhs in *)

  (* merge equivalence classes  *)
  let lres = merge_sorted_lists fn_inf eqcl_lhs eqcl_rhs in
(*   let () = buffered_output ("\ninsert_eq : return res =" ) in *)
(*   let () = print_list ", " (fun x -> print_string x#string) lres in *)

  (* simplify equivalence classes  *)
  let rec fn = function
      [] -> []
    | l :: tl -> if is_included fn_eq fn_inf l lres then fn tl else l :: (fn tl)
  in
  let l_eqcl' = fn l_eqcl in
(*   let () = buffered_output ("\ninsert_eq : return res =") in *)
(*   let () = print_list "\n\t " (fun l -> print_list ", " (fun x -> print_string x#string) l) res in *)
  lres :: l_eqcl'
  

let build_equalities lst =
  let rec fn l = function
      [] -> l
    | (lhs, rhs) :: tl -> 
	let res = fn l tl in
	insert_eq (lhs, rhs) res
  in 
  let l_eqcl = fn [] lst in
(*   let () = buffered_output ("\nbuild_equalities l_eqcl =") in *)
(*   let () = print_list "\n\t " (fun l -> print_list ", " (fun x -> print_string x#string) l) l_eqcl in *)

  let rec fn_eq l l' = 
    match l,l' with
	[], [] -> true
      | [], _ -> false
      | _, [] -> false
      | h :: tl, h'::tl' -> if h#string = h'#string then fn_eq tl tl' else false
  in
  let l_eqcl' = list_remove_doubles fn_eq l_eqcl in
(*   let () = buffered_output ("\nbuild_equalities l_eqcl' =") in *)
(*   let () = print_list "\n\t " (fun l -> print_list ", " (fun x -> print_string x#string) l) l_eqcl' in *)
  let rec all_comb = function 
      [] -> []
    | l :: tl ->
	let all_eq = all_combinations_from_list l in
	let rs = all_comb tl in
	all_eq @ rs
  in
  all_comb l_eqcl'


let congruence_closure _ c level = 

  if c#has_bit congruence_closure_bit then failwith "congruence_closure" 
  else 
    let n', p' = c#content in
    let n = List.map (fun x ->(x#copy)#update_pos) n' in
    let p = List.map (fun x ->(x#copy)#update_pos) p' in
    
    let _ = n @ p in
    let _, ne = List.partition (fun x -> x#is_diff) n in
    let pd, _ = List.partition (fun x -> x#is_diff) p in
(*     let lpos =  List.map (fun x -> x#both_sides) (pe @ nd) in *)
    let lneg = List.map (fun x -> x#both_sides) (pd @ ne) in
    
    let _ =  if !maximal_output then  buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule CONGRUENCE CLOSURE on " ^ (string_of_int c#number)) in
    (*     let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
(*     let new_r = fn lneg  in  *)

    let fn_equal (x, y) (x', y') = (x#syntactic_equal x' && y#syntactic_equal y') || (x#syntactic_equal y' && y#syntactic_equal x') in
(*     let new_r' = List.filter (fun lit -> not (list_member fn_equal lit (List.map (fun l -> l#both_sides) ne))) new_r in *)
(*     let () = print_string ("\nRules =") in *)
(*     let () = print_list "\t" (fun (s, t) -> let () = print_string ("\n\t" ^ s#string) in let () = print_string (" = " ^ t#string) in () ) new_r'  in *)
    let () = c#set_bit congruence_closure_bit in
    let new_lits = build_equalities lneg in
    let res = new_lits @ lneg in
    let res'' = list_remove_doubles fn_equal res in
    let res' = List.filter (fun (x, y) -> x#is_constructor_term && y#is_constructor_term) res'' in
    
    let add_l = ref [] in
    let all_cterms = c#all_terms in
    let () = List.iter 
      (fun (s, t) ->
	(* tests if s, t are new w.r.t. ne and pd *)
	  let cond1 = ((not (list_member fn_equal (s, t) (List.map (fun x -> x#both_sides) ne))) && (not (list_member fn_equal (s, t) (List.map (fun x -> x#both_sides) pd)))) in
	  let cond2 = 
	    (list_member (fun z y -> z#syntactic_equal y) s all_cterms) &&
	    (list_member (fun z y -> z#syntactic_equal y) t all_cterms)
	  in
	  if cond1 && cond2 then let () = add_l := (s, t) :: !add_l  in ()
	) 
	res'
      in
    let rec fn3 l = 
      match l with
	  [] -> []
	| (s, t) :: tl -> 
	    let () = yy_tmp_param_sorts := [] in
	    if equal_sorts s#sort t#sort then
	      if ((s#is_term && (is_constructor s#head)) ) && 
		 ((t#is_term && (is_constructor t#head)) ) then 
		let counter = ref 0 in
		let l = decompose counter (new literal (Lit_equal (s, t))) in
(* 		let l' = List.filter (fun lit -> not (list_member (fun x y -> x#syntactic_equal y) lit ne)) l in *)
		l @ fn3 tl 
	      else if  (is_existential_var s) && (is_existential_var t) then (new literal (Lit_equal(s, t))) :: (fn3 tl) else fn3 tl
	    else
	      
	      let () = 
		if !maximal_output then
		  let () = print_string "\n unify_sorts in: " in
		  let () = print_detailed_clause c in
		  let () = print_string "\ns = " in
		  let () = print_detailed_term s in
		  let () = print_string "\nt = " in
		  let () = print_detailed_term t in
		    ()
		else 
		  ()
	      in
	      fn3 tl
    in 
    
    let new_lits = fn3 !add_l in
    let new_lits' = List.filter (fun lit -> not (list_member (fun x y -> x#syntactic_equal y) lit ne)) new_lits in
    if new_lits' = [] then failwith "congruence_closure" 
    else
      let () = buffered_output ("\n" ^ !indent_string ^ "CONGRUENCE CLOSURE: simplify\n" ^ !indent_string ^ "\171 " ^ c#string ^ "\n") in
      
      (*       let () = print_detailed_clause c in *)
      let () = print_list "" (fun lit -> print_string ("\tAdding " ^ lit#string ^ "\n")) new_lits' in
      let new_c = c#build (n' @ new_lits') p'  in
      
      let () = List.iter (fun x -> let () = buffered_output (!indent_string ^ "\n\n\187 " ^ x#string) in () (* print_detailed_clause x *)) [new_c] in
      
      [new_c] 
