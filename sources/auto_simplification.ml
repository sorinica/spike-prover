
(*
   * Project: Spike ver 0.1
   * File: auto_simplification.ml
   * Content: Auto simplification
*)

open Values
open Diverse
open Io
open Symbols
open Terms
open Clauses
open Order
open Literals
open Dummies
open Terms


let auto_simplification verbose c _ level =
  
  
  (* 0: displa
y *)
  
  let n1, p1 = c#content in
  let size_n1 = List.length n1 in
  let _ = List.length p1 in

  (* store of rewriting rules  *)
  
  let lrules = ref ([]: (Terms.ground_term * Terms.ground_term) list) in
  let lrules_tmp = ref ([]: (Terms.ground_term * Terms.ground_term) list) in

  let fn_eq  (s, t) (s', t')  = (s#string = s'#string) && (t#string = t'#string) in

  let rec fn2 lit_eq l =
    let is_equality lit = 
      match  lit#content with
	  Lit_equal _ -> true
	| Lit_rule _ -> true
	| Lit_diff _ -> false
    in
    

    if not (is_equality lit_eq) then l
    else
      (* go !  *)
      let lhs1, rhs1 = lit_eq#both_sides in
      let rec fn3 s t lp  = 
	match lp with
	    [] -> []
	  | lit :: tl -> 
	      (* before the replacement test *)
(* 	      let () = buffered_output ("Treating lit " ^ lit#string) in *)
	      let fn trm' = 
		let trm = trm'#copy in
		try 
(* 		  let () = buffered_output ("\ntrm' = " ^ trm#string ^ " with s = " ^ s#string) in *)
		  let p = s#subterm trm in
(* 		  let _ = unify_sorts (Actual_sort s#sort) t#sort in *)
(* 		  if p = [] then trm' else *)
(* 		  let () = buffered_output ("\nPosition p " ^ (sprint_position p) ) in *)
		    let res = trm#replace_subterm_at_pos p (t#copy) in
(* 		    let s' = s#expand_sorts in *)
(* 		    let t' = t#expand_sorts in *)
		  (* 			  let () = buffered_output ("\n\n The term " ^ trm#string ^  " can be rewritten by using the negative oriented literal " *)
		  (* 			  ^ s#string ^ " -> " ^ t#string ^ " to give " ^ res#string) in *)
		    let () = lrules_tmp := (s,t) :: !lrules_tmp in
		  
		    res#update_pos 
		    (* 			else trm *)
		with Failure "subterm" | Failure "unify_sorts" -> trm'
	      in
	      let lhs, rhs = lit#both_sides in
	      let lhs' = fn lhs in
	      let rhs' = fn rhs in
(* 	      let () = buffered_output ("\nmaking a literal from " ^ lhs'#string ^ " and " ^ rhs'#string) in  *)
	      let lit' = 
		match lit#content with
		    Lit_equal (_, _) -> new literal (Lit_equal (lhs', rhs'))
		  | Lit_rule (_, _) ->  new literal (Lit_rule (lhs', rhs'))
		  | Lit_diff (_, _) ->   new literal (Lit_diff (lhs', rhs'))
	      in
	      (* after the replacement test *)
	      lit' :: fn3 s t tl
      in
      
      let fn_greater t t' = 
	match t#content, t'#content with
	    Term (_, _, _), Term (_, _, _)  -> (!rpos_greater false t t') (* or ((not t#is_constructor_term) && t'#is_constructor_term) *)
	  | Var_exist _ , Term _ | Var_univ _ , Term _  | Var_exist _, Var_univ _ -> true
	  | Var_exist(i, _), Var_exist(i', _) | Var_univ(i, _), Var_univ(i', _) -> i > i'
	  | Var_univ _, Var_exist _| Term _, Var_univ _| Term _, Var_exist _ -> false
      in
      
      if fn_greater lhs1 rhs1 && ((rhs1#is_term && is_constructor rhs1#head) || (is_existential_var lhs1 && not (rhs1#occur
	lhs1#var_content))) || (is_universal_var lhs1 && is_universal_var rhs1)
      then
(* 	let () = print_string ("\nCall :lhs1 = " ^ lhs1#string ^ " rhs1 = " ^ rhs1#string) in *)
        fn3 lhs1 rhs1 l
      else if fn_greater rhs1 lhs1 && ((lhs1#is_term && is_constructor lhs1#head) || (is_existential_var rhs1) && not (lhs1#occur
	rhs1#var_content)) || (is_universal_var lhs1 && is_universal_var rhs1) (* the same test for h#swap *)
      then
(* 	let () = print_string ("\nCall reverse :lhs1 = " ^ lhs1#string ^ " rhs1 = " ^ rhs1#string) in *)
	fn3 rhs1 lhs1 l
      else 
	l
  in
  let rec fn c min_i =
    let ln, lp = c#content in
    let ln1, ln2 = list_split_at_n (min_i - 1) ln in

    let () = lrules_tmp := [] in
    (* scanning ln2  *)
    let size_ln2 = size_n1 - min_i + 1 in
    let rec fn' j l = 
(*       let () = buffered_output ("j = " ^ (string_of_int j) ^ " size_ln2 = "  ^ (string_of_int size_ln2)) in *)
      match l with
	  [] -> c 
	| lit :: tl -> 
	    (* the other negative literals  *)
	    let ln3 = list_all_but (j - 1) ln2 in
	    (* go !  *)
	    
	    let lres = fn2 lit (ln3 @ lp) in
	    (* undo the new ln and lp  *)
	    let ln', new_lp = list_split_at_n  (size_ln2 - 1) lres in
	    let new_ln = ln1 @ (first_n  ln' (j - 1)) @ [lit] @ (last_n  ln' (size_ln2 - j )) in
	    
(* 	    let () = buffered_output ("new_ln = " ^ (sprint_list ", " (fun x -> x#string) new_ln )) in *)
	    let c' = c#build new_ln new_lp in
(* 	    let () = buffered_output ("c' = " ^ c'#string) in *)
	    (* test if c' is good  *)
	    
	    if (not (c#syntactic_equal c'))(*  &&  (!broken_order or ((is_strict && clause_greater false c c') || ((not is_strict) && clause_geq false c c'))) *) then
(* 	      let () = buffered_output "\nCall recursively fn" in *)
	      let () = lrules := List.fold_right (fun x l -> if list_member fn_eq x l then l else x :: l) !lrules_tmp !lrules in
	      fn c' 1 (* if OK auto_rewrite c' *)
	    else 
(* 	      let () = buffered_output "\nCall next element with fn'" in *)
	      fn' (j + 1) tl (* otherwise try to rewrite with the next negative literal *)
    in
    fn' 1 ln2
  in      
  let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule AUTO SIMPLIFICATION "
    ^ " on " ^ (string_of_int c#number)) in
(*   let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)

(*   let () = if !maximal_output then  write_pos_clause c in  *)

  if c#has_bit auto_simplification_bit then  failwith "auto_simplification"
  else 
(*     let () = buffered_output ("c = " ^ c#string) in *)

  (* let's start  *)

  (* initialization of yy_tmp_param_sorts since the rule creates new literals  *)
    let () = yy_tmp_param_sorts := [] in

    let new_c = fn c 1 in
    if (not (c#syntactic_equal new_c))(* réussite *)
    then
      let () = c#set_bit auto_simplification_bit in
      let () =
	if verbose
	then
          buffered_output (!indent_string ^ "\n\nAUTO SIMPLIFICATION: simplify \n" ^
          !indent_string ^ "\171 " ^ c#string ^ "\n\n" ^ "using the negative literal(s):\n\n\t" ^
	  (sprint_list "\n\t" (fun (s, t) -> (s#string ^ " -> " ^ t#string)) (List.rev !lrules)) ^ "\n\n" ^
          !indent_string ^ "\187 " ^ new_c#string ^ "\n\n") 
	else () 
      in
      [new_c]
    else (* échec *)
      let () = c#set_bit auto_simplification_bit in
      failwith "auto_simplification" 



