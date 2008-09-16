
(*
   * Project: Spike ver 0.1
   * File: normalize.ml
   * Content: Normalization of terms
*)

open Values
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Order
open Literals
open Clauses
open Dummies
open Coq

let norm_string = ref ""

(* Apply on tr the first rewrite rule from rw_r available and check that its preconditions have equal normal forms *)
let rec rewrite rw_r (tr:term) c_ref str cxt i =
  
(*   let () = buffered_output ("\n Rewrite " ^ tr#string) in *)
  let max_var = c_ref#greatest_varcode + 1 in
  let str_ref = ref str in

  let rec fn2 t_p pos l = 
	  
    match l with
	[] -> failwith "fn2"
      | (los, h):: t ->
	  
(* 	  let () = buffered_output ("\n fn2: trying from " ^ los ^ " the clause " ^ h#string ) in *)
          let test1 =  (* the neg lits are not empty ? *) 
	    let negs = h#negative_lits in
	    negs <> [] 
	  in
	  let test2 = (* the pos literal is t1 <> t2 ?*) 
	    let poss = h#positive_lits in
	    let fst_lit = List.hd poss in
	    fst_lit#is_diff
	  in
	  if test1 or test2 then fn2 t_p pos t
	  else 
            let lhs, rhs = h#both_sides in
	    let fn1 order_tested l r = 
	      try 
(* 		let () = buffered_output ("\nHere with l = " ^ l#string ^ " and r = " ^r#string) in *)
		let sub = t_p#matching (fun s -> s) l in
		let r_sub = r#substitute sub in
		let l_sub = l#substitute sub in
		let test_ok = 
		  if los = "C1" then 
		    let hsub = h#substitute_and_rename sub max_var in 
		    clause_geq false c_ref hsub 
		  else if los = "C2" then
		    let hsub = h#substitute_and_rename sub max_var in 
		    let res = clause_greater false c_ref hsub in
		    res
		  else true
		in
		if test_ok && ((not order_tested) || (order_tested && rpo_greater false l_sub r_sub )) then (sub, r_sub) else failwith "fn1"
	      with Failure "matching" -> failwith "fn1"
	    in
	    let newtr = tr#copy in
	    let reverted = ref false in
	    try 
	      let (sub, r_sub) = match los with
		  "L" -> 
		    if h#oriented then
		      (try fn1 false lhs rhs with Failure "fn1" -> failwith "bad")
		    else
		      (try fn1 !use_order lhs rhs with Failure "fn1" -> 
			if not !use_order then failwith "bad"
			else
			  let () = reverted := true in
			  (try fn1 true rhs lhs with Failure "fn1" -> failwith "bad") 
		      )
		| "C1" | "C2" ->
		    (try fn1 !use_order lhs rhs with Failure "fn1" -> 
		      if not !use_order then failwith "bad"
		      else
			let () = reverted := true in
			(try fn1 true rhs lhs with Failure "fn1" -> failwith "bad") 
		    )
		|  "R" -> 
		     (try fn1 false lhs rhs with Failure "fn1" -> failwith "bad")
		| _ -> failwith "normalize: los"
	      in
	      let res = newtr#replace_subterm_at_pos pos r_sub in
	      let fn3 h is_rev =
                let () = 
                  if !coq_mode then match los with
                  | "R" -> prepare_rewrite ("sp_axiom_" ^ (string_of_int h#number))
                  | "L" -> prepare_rewrite ("sp_lemma_" ^ (string_of_int h#number))
                  | _ -> prepare_rewrite_last_induction ()
                  else ()
                in
		let lhs, rhs = h#both_sides in
		if is_rev then rhs#string ^ " -> " ^ lhs#string ^ "  (from [" ^ (string_of_int h#number) ^ "] of " ^ los ^ ")"
		else lhs#string ^ " -> " ^ rhs#string ^ "   (from [" ^ (string_of_int h#number) ^ "] of " ^ los ^ ")"
	      in
	      let () = str_ref := !str_ref ^ (
		"\n" ^ (n_spaces i) ^ tr#string ^
		"\n" ^ (n_spaces (i + 3)) ^ "is simplified by : " ^ (fn3 h !reverted) ^ 
		"\n" ^ (n_spaces (i + 3)) ^ "with substitution: " ^ (sprint_subst sub) ^ " into" ^ 
		"\n" ^ (n_spaces i) ^ res#string ^ "\n") in
(* 	      let () = buffered_output ( *)
(* 		"\n" ^ (n_spaces i) ^ tr#string ^ *)
(* 		"\n" ^ (n_spaces (i + 3)) ^ "is simplified by : " ^ (fn3 h !reverted) ^  *)
(* 		"\n" ^ (n_spaces (i + 3)) ^ "with substitution: " ^ (sprint_subst sub) ^ " into" ^  *)
(* 		"\n" ^ (n_spaces i) ^ res#string ^ "\n") in *)
	      res
            with (Failure "bad" | Failure "replace_subterm_at_pos") -> fn2 t_p pos t
  in 
  
  let k = try tr#head with Failure "head" -> failwith "rewrite" in
  let lpat = try if List.mem R rw_r then dico_rules#find k else [] with Not_found -> [](* failwith "rewrite" *) in
  let lpat' = List.map (fun x -> ("R", x)) lpat in  
  let l' = if List.mem R rw_r then try remove_el (=) R rw_r with Failure "remove_el" -> failwith "rewrite: remove_el" else rw_r in
  let lres = concrete_system_list l' cxt in
  let lres' = List.filter (fun (_, c) -> c#is_horn) lres in
  let rw_r' = (lpat' @ lres') in
  
  let res = try fn2 tr [] rw_r' with Failure "fn2" -> failwith "rewrite" in
  let res' = if equal_sorts tr#sort res#sort then 
    res#expand_sorts
  else failwith "rewrite"
  in
  !str_ref, res'

(* normalize a term: apply rewrite rules until saturation *)
and normalize rw_r tr c_ref str cxt i =
(*   let () = buffered_output ("\n Normalize " ^ tr#string) in *)
   match tr#content with 
     Var_univ _  | Var_exist _  -> str, tr
   | Term (f, l, s) ->
       let st_list = List.map (fun x -> normalize rw_r x c_ref "" cxt (i + 3)) l in
       let term_list = List.map (fun (_,x) -> x) st_list in
       let str_list =  List.map (fun (x,_) -> x) st_list in
       let str_list' = list_remove_doubles (fun x y -> x = y) str_list in
       let str'' = List.fold_right (fun x y -> (x ^ y)) str_list' "" in
       let tr'' = new term (Term (f, term_list, s)) in
       try
	 let str', tr' = rewrite rw_r tr'' c_ref (str ^ str'') cxt i in
	 normalize rw_r tr' c_ref str' cxt i
       with (Failure "rewrite") ->
	 (str ^ str''), tr''

(* Fails if tr = norm tr *)
let normalize_plus rw_r tr c_ref str cxt i =
(*   let str', tr' = rewrite rw_r tr c_ref str cxt i in *)
  let str', tr' =  normalize rw_r tr c_ref str cxt i in
  if str = str' then failwith "rewrite" else str', tr'
