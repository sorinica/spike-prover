
(*
   * Project: Spike ver 0.1
   * File: augment.ml
   * Content: The augmentation operation over LA and CC
*)

open Polynoms
open Clauses
open Dummies
open Diverse
open Strategies
open Order
open Values 
open Io
open Symbols
open Auto_simplification
open Contextual_rewriting

let true_by_context counter n1 reference cr g l =
  let fn lit = 
    try 
      let new_counter = counter + 1 in 
      let cx = new peano_context [] [lit]  cr g l in
      let () = cx#check_inconsistencies new_counter reference in 
      false
    with Inconsistent -> true
  in
  if counter >= !max_counter_augmentation then false 
  else List.for_all (fun x -> fn x) n1 
    
  (* defined by not yet used  *)

let true_by_strategy n1 c_sigma c_ref cxt = 
  let st = !augmentation_strat in 
  let new_soc = List.map (fun x -> c_sigma#build [] [ x ]) n1 in
  let new_hyps = recursive_new_hyps c_ref new_soc cxt in
  (*    save the current state ? *)
  st#apply_to_subgoals !output_verbosity c_sigma new_hyps new_soc  (* to complete with the available context for the recursive call *)
    

  (* is_conservative tests if multiplicands are included in p, lp, cr, 
   g, l or are smaller than the maximal multiplicand of the polynomial*)
let is_conservative max_poly multiplicands _ _ l = 
  let p, ie = l in
  let fn_poly multiplicand poly = (rpo_greater false max_poly multiplicand) or
    (list_member (fun x y -> x#syntactic_equal y) multiplicand poly#multiplicands)
  in
  let fn_eq multiplicand eq = 
    let s, t = eq#both_sides in
    (s#syntactic_equal multiplicand) or (t#syntactic_equal multiplicand)
  in
 List.for_all (fun x -> ((List.exists (fun y -> fn_poly x y) (List.hd p)) or
(*                       (List.exists (fun y -> fn_eq x y) cr) or  *)
(*                       (List.exists (fun y -> fn_eq x y) g) or  *)
                      (List.exists (fun y -> fn_eq x y) ie))) 
              multiplicands
               
(* augmenting a polynom with the information derived from a set of clauses  *)  
  (*                    Arguments:                         *)
  (* p         = the polynom used in the augmentation      *)
  (* lp        = the other polynoms from the database      *)
  (* reference = the original clause                       *)
  (* cr, g, l  = the current state of the context          *)
  

(* to be completed: to add the context  *)

let augment_polynom counter p lp reference cr g l = 
  let c_reference = new clause reference [] in (* rebuild a copy of the reference *)
  let () = print_indent_string (" augment_l has been called on the polynom " ^ p#string ^ " \n with the reference clause " ^ c_reference#string)
  in
  try 
    let coef, max = p#maximal_monomial  in
    if max#is_term then 
      let fn c system = (* computes a peano literal that may process p *)
      	let _, pos = c#content in
      	if List.length pos = 1 then
	  (* c has only one positive literal. A further improvement is to use #pi to put to the left side the
	     maximum literals from the right side *)
      	  let lit = List.hd pos in
      	  let peano_lit = convert_literal lit in
	  if peano_lit#is_pi then 
	    let poly_lit = linearize peano_lit in
      	    let redundant_information = List.for_all (fun x -> is_subset (fun z -> z#syntactic_equal) x lp) poly_lit in
      	    if List.length poly_lit > 1 or redundant_information
	      (* we do not treat s <> t if the information is redundant *)
      	    then [] 
      	    else
      	      let rec fn1 = function (* computes the matching substitution *)
	      	  [] -> failwith "fn1"
	      	| poly :: t -> 
	      	    try 
	      	      let coef_poly, max_poly = poly#maximal_monomial in 
	      	      if (coef_poly * coef < 0)  then 
	      	      	let sigma = max#matching (fun x -> x) max_poly in 
	      	      	let () = print_indent_string (" the successful substitution is " ^ (sprint_subst sigma))
		      	in
		      	sigma
	      	      else fn1 t
 	      	    with Failure "matching" 
		      | Failure "maximal_monomial" -> fn1 t
     	      in 
      	      try 
	      	let sigma = fn1 (List.flatten poly_lit) in
		let lit_sigma = lit#substitute sigma in
	      	let new_lit = (convert_literal lit_sigma) in
		let poly_lit_sigma = List.hd (List.hd (linearize new_lit)) in
	      	(* tests if c\sigma is appropriate for augmentation *)
	      	let c_sigma = c#substitute sigma in 
	      	if (system = "R" or system = "L" or 
(* 		  (system = "C1" && clause_geq false c_reference c_sigma) or  *)
		  (system = "C2" && clause_greater false c_reference c_sigma))  
		  && (is_conservative max poly_lit_sigma#multiplicands cr g l) then 
	      	  let () = print_indent_string  ( "\nAUGMENTATION will use the clause " ^ c_sigma#string ^ " from " ^ system )
	      	  in
	      	  let n1, p1 = c_sigma#content in 
		  
		  let n1', _ = c_reference#content in
		  let c_sigma' = c_reference#build (n1 @ n1') p1 in

	      	  let () = print_indent_string ("\n c_sigma' = " ^ c_sigma'#string) in
		  let c_sigma1 = List.hd (try auto_simplification false c_sigma' true 1 with Failure "auto_simplification" -> [c_sigma']) in
	      	  let () = print_indent_string ("\n c_sigma1 = " ^ c_sigma1#string) in
		  let c_sigma2 = List.hd (try conditional_rewriting false true (LOS_defined [R]) Pos_all ([],[]) c_sigma1 true 1 with Failure "conditional_rewriting" -> [c_sigma1]) in
	      	  let () = print_indent_string ("\n c_sigma2 = " ^ c_sigma2#string) in
		  let _, new_p1 = c_sigma2#content in
	      	  if n1 = [] 
	      	    or (true_by_context counter n1 reference cr g l) 
		    (* 	      or (true_by_strategy n1 c_sigma ) *)
	      	  then (* success proof of the conditions *)
		    let lit' = List.hd new_p1 in
		    let new_lit' = convert_literal lit' in
	      	    let () = print_indent_string ( "Augmentation: new added Peano literal\n" ^ new_lit'#string)
	      	    in
	      	    [new_lit']
	      	  else []
	      	else []
      	      with Failure "fn1" -> []
      	  else []
	else []
      in
      let all_context = 
      	(List.map (fun x -> x, "C1") conjectures_system#content) @  
      	(List.map (fun x -> x, "L") lemmas_system#content) @
      	(List.map (fun x -> x, "C2") hypotheses_system#content) @
      	(List.map (fun x -> x, "R") rewrite_system#content) in
      let rec fn2 = function 
      	  [] -> []
      	| (cl, s) :: t -> 
	    let p =  fn cl s in 
(* 	    let () = print_indent_string ( "\nThe potential added literal is" ^ p#string) *)
(* 	    in *)
      	    p @ (fn2 t)
      in 
      fn2 all_context
    else [] (* max is a variable *)
  with 
      Failure "maximal_monomial" -> []

let () = oracle_a := augment_polynom
