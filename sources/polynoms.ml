
(*
   * Project: Spike ver 0.1
   * File: polynoms.ml
   * Content: polynoms definitions
*)

open Diverse 

open Io
open Dicos
open Symbols
open Terms
open Order

exception Inconsistent

  (* the arguments of any ac function are sorted in decreasing order  *)
let preprocess_ac t = 
  let rec fn t = match t#content with
      Var_exist _  
    | Var_univ _  -> t
    | Term (f, l, s) -> 
	let l' = List.map fn l in
	if symbol_is_ac f then 
	  let l'_sorted = List.sort (fun x y -> if heavier y x then -1 else if x == y then 0 else 1) l' in
	  new term (Term (f, l'_sorted, s))
      	else new term (Term (f, l', s))

  in
  fn t

let rec well_founded (_:int) list = 
  let peano_sort = if !nat_specif_defined then id_sort_nat else
    id_sort_int in
  match list with
      [] -> true
    | (coef,monom)::t -> 
	if monom#sort = peano_sort then 
	  well_founded coef t
	else 
(* 	  let () = buffered_output ("\nThe sort of the monom " ^ monom#string ^ " is " ^ (sprint_sort monom#sort)) in *)
	  false
;;

  (* for s(..s(x)) returns the number of s and the term x  *)
let rec count_s term = match term#content with  
     Term (symb, l, _) -> 
      if symb = id_symbol_s then begin
	assert (List.length l = 1);
      	let count_l, term_l = count_s (List.hd l) in 
      	count_l+1, term_l
      end
      else 0, term
  | Var_exist _ | Var_univ _ -> 0, term
;;


  (* for p(..p(x)) returns the number of p and the term x  *)
let rec count_p term = match term#content with  
    Term (symb, l, _)  -> 
      if !int_specif_defined && symb = id_symbol_p then begin
	assert (List.length l = 1);
      	let count_l, term_l = count_p (List.hd l) in 
      	count_l+1, term_l
      end
      else 0, term
  | Var_exist _ | Var_univ _ -> 0, term
;;


  (* orders two elements according to f_greater  *)
let order_two f_greater t1 t2  = 
  if f_greater t1 t2 then t1,t2 else t2,t1
;;

let rec elim_null_monoms p = 
  match p with
      [] -> []
    | (0,_) :: t -> elim_null_monoms t
    | h :: t  -> h :: elim_null_monoms t
;;

let multiply_term t p =
  let peano_sort = if !nat_specif_defined then id_sort_nat else
    id_sort_int in
  List.map 
    (fun (c',t') -> 
      c',  
      new term (Term (id_symbol_times, 
      (let t1,t2 = order_two (heavier) t t'  in
      [t1;t2]), peano_sort)))
    p
  ;;

let multiply_const (c,m) = 
  List.map (fun (c', t') -> (c * c', t')) m
;;

let multiply_monoms (c1,m1) (c2,m2) = 
  let const = c1 * c2 in
  let c1_m2 = multiply_const (c1, m2) in
  let c2_m1 = multiply_const (c2, m1) in
  let m1_m2 = List.flatten (List.map (fun (c', t') -> multiply_const (c',
      (multiply_term t' m1))) m2) in
  const, (c1_m2@c2_m1@m1_m2)
;;


  (* normalize a list of monoms. It also flattens "+" and "-" terms, eliminates 
     the "zero" terms and transforms terms representing naturals into constants  *)
let rec normalize_monom_list l = 
  let treat_monoms = function 
      [] -> 0,[]
    | (0, _) :: t -> normalize_monom_list t
    | (c, m) :: t  -> 
	let const_m, processed_m = process_monom (c,m) in 
	let const_t, poly_t = (normalize_monom_list t) in 
	(const_m + const_t, multiset_merge_sorted_lists  (fun m1 m2  ->
      	  m1#syntactic_equal m2) (fun m1 m2 -> heavier m1 m2)
      	  processed_m poly_t) 
  in
  let const, treated_monoms = treat_monoms l in
  let no_null = elim_null_monoms treated_monoms in 
  let sorted_monoms = List.sort (fun (_, t1) (_, t2) -> if heavier 
    t1 t2 then -1 else if t1#syntactic_equal t2 then 0 else 1) no_null in 
  const, sorted_monoms
and process_monom (c,m) =  
  match m#content with
      Term (symb,l,_)-> 	
	(if symb = id_symbol_plus then
	let l_sorted = List.sort (fun x y -> if heavier y x then -1 else if x == y then 0 else 1) l in 
	let lc = List.map (fun x -> (c, x)) l_sorted in 
	normalize_monom_list lc 
      else if symb = (id_symbol_zero) then 0,[]
      else if symb = (id_symbol_minus) then 
	(assert (List.length l = 2);
	let minuhend = List.hd l in
	let subtrahend = last_el l in
	let (c1,t1),(c2,t2) = order_two (fun (_,t') (_,t'') -> heavier t' t'')  (c,minuhend) (-c,subtrahend)  in 
	normalize_monom_list [c1, t1; c2, t2])
      else if symb = (id_symbol_s) then
	(assert (List.length l = 1);
	let s_of_l, term_l = count_s (List.hd l) in
 	let s_of_t = s_of_l + 1 in 
	let const,poly = normalize_monom_list [1,term_l] in
	let c_times_poly = (multiply_const (c, poly)) in
	c * (s_of_t + const), c_times_poly)
      else if !int_specif_defined && symb = (id_symbol_p) then
	(assert (List.length l = 1);
	let p_of_l, term_l = count_p (List.hd l) in
 	let p_of_t = - (p_of_l + 1) in 
	let const,poly = normalize_monom_list [1,term_l] in
	let c_times_poly = (multiply_const (c, poly)) in
	c * (p_of_t + const), c_times_poly) 
      else if symb = (id_symbol_times) then
	(let test_zero t = t#syntactic_equal (term_nat 0) in
	if List.exists test_zero l then 0, [0, m]
	else 
	  let fn t p =
	    let si, ti = count_s t in
	    let ci, pi = normalize_monom_list [1, ti] in
	    multiply_monoms p ((ci + si), pi)
	  in 
	  let l_sorted = List.sort (fun x y -> if heavier y x then -1 else if x == y then 0 else 1) l in
	  let const_pi, mult_pi = List.fold_right fn l_sorted (normalize_monom_list [1, (term_nat 1)]) in
	  let true_pi = (elim_null_monoms mult_pi) in 
	  if List.length true_pi = 1 then (c * const_pi, (multiply_const (c,true_pi)))
	  else 
	    let c_norm, normalized_pi = normalize_monom_list true_pi in
	    let returned_const = c * (const_pi + c_norm) in
	    let returned_poly = multiply_const (c, normalized_pi) in
	    returned_const, returned_poly)
      else 0,[(c,m)])
    | Var_exist _ | Var_univ _ -> 0,[(c,m)]
;;

(* a polynom is a wrapper around
   - a constant
   - a sorted (w.r.t. Order.heavier) list of int * term
   - a history showing the polynoms implicated in its creation *)
class polynom (i: int) (p': (int * ground_term) list) (h: 'a list) =
  let _ = if not (well_founded i p') then failwith "inconsistent polynom" in
  let p = List.map (fun (c, t) -> (c, preprocess_ac t)) p' in 
  let c_p, p_normalized =  normalize_monom_list  p in
  let new_c = c_p + i in 
  let gcd_all_coef = abs (if new_c <> 0 
  then List.fold_left (fun x y -> gcd (abs x) (abs y))
    new_c (List.map (fun (c,_) -> c) p_normalized)
  else if p_normalized <> [] then List.fold_left (fun x y -> gcd (abs x) (abs y))
    (fst (List.hd p_normalized)) (List.map (fun (c,_) -> c) p_normalized)
  else 1) in
object (self: 'a)

    inherit generic
    inherit printable_object

    val content = List.map (fun (c,m) -> (c / gcd_all_coef, m)) p_normalized
    val constant = new_c / gcd_all_coef
    val length = List.length p_normalized
    val history = h

    method content = content
    method constant = constant
    method length = length
    method history = history


  (* pretty print function *)
    method pprint f = Format.fprintf f "@[@ Polynom: %s@]" self#string

    method compute_string =
      let string_nonempty_constant (c,t) =  
	  if c <> 0 then (string_of_int c) ^ " * ("
	^ t#string ^ ")" 
	  else "" 
      in
      let sprint_list sep dispfun l =
  	let rec fn =
	  function
	      [] -> ""
	    | [h] -> dispfun h
	    | h :: t -> let str_before_sep = dispfun h in 
			let str_after_sep = fn t in 
	      if str_before_sep = "" then str_after_sep
	      else if str_after_sep = "" then str_before_sep 
	      else str_before_sep ^ sep ^ str_after_sep
  	in
  	fn l
      in
      let polynom_string = 
      	match p with
	    [] -> (string_of_int constant)
	  |  _ -> let monoms_string = (sprint_list " + "
	       string_nonempty_constant content) in 
	     match constant with 
		 0 -> if monoms_string = "" then "0" else monoms_string
	       | _ -> 
		   if monoms_string = "" then (string_of_int constant) else
		     (string_of_int constant) ^ " + " ^ monoms_string
      in polynom_string ^ " <= 0"

    method equal p =
      constant = p#constant
        &&
      length = p#length
        &&
      List.for_all2 (fun (i, x) (j, y) -> i = j  &&  x#syntactic_equal y) content p#content

    method syntactic_equal (p: 'a) =
      constant = p#constant
        &&
      length = p#length
        &&
      List.for_all2 (fun (i, x) (j, y) -> i = j  && x#syntactic_equal y) content p#content

    method vacuous = constant  <= 0 && (List.for_all (fun (i, _) -> i <= 0) content)
    method impossible = 
      constant > 0 && (content = [])

    method add (p: 'a) =
      let l = multiset_merge_sorted_lists (fun (x:ground_term) (y:ground_term) ->
	x#syntactic_equal y) (heavier) content p#content in
      let l' = elim_null_monoms l in 
      {< content = l' ;
         constant = constant + p#constant ;
         length = List.length l'; 
	 history = self :: p :: p#history @ history;
         string = Undefined >}

    method maximal_monomial =
      try List.hd content
      with (Failure "hd") -> failwith "maximal_monomial"

    method maximal_multiplicand = snd self#maximal_monomial

    method cross_multiply_add (p: 'a) coefs=
      let sign x = x/abs(x) in
      let k, k' = coefs 
      and c = constant
      and c' = p#constant
      and fn x = List.map (fun (i, t) -> i * x, t) in
      let gcd_k_k' = gcd (abs k) (abs k') in 
      let multiply_self = abs (k' / gcd_k_k') in 
      let multiply_p = abs (k / gcd_k_k') in 
      let new_c = multiply_p * c' + multiply_self * c
      and new_p = multiset_merge_sorted_lists syntactic_equal (heavier)
	(fn multiply_self content) (fn multiply_p p#content) in
      let new_p' = elim_null_monoms new_p in 
      let new_c' = 
	if List.length new_p' = 0 then
 	  if new_c = 0 then 0 
	  else sign new_c
      	else new_c 
      in
      	  {< content = new_p' ;
        constant = new_c' ;
        length = List.length new_p'; 
	history = self :: p :: (p#history @ history);
        string = Undefined >}


    method combination (p: 'a) =
      try 
	  let k, t = self#maximal_monomial 
	  and k', t' = p#maximal_monomial in
      	  if t#syntactic_equal t' && k * k' < 0 then (k, k')
	  else failwith "combination"
      with 
	  Failure "maximal_monomial" -> failwith "combination"
	  
    method independent = true

    method multiplicands = List.map snd content

    method coefficients = List.map fst content
	
  end

let new_polynom c p h = new polynom c p h

(* the special polynom "0 <= 0" *)
let poly_0_leq_0 =
  new polynom 0 [] []

  (* returns polynoms of the form -m <= 0, for all m \in monoms(lp)   *)
let add_nat_variables  lp = 
  let rec fn  = (* returns the different monomials *)
    function
    	[] -> []
      | p :: tail -> 
	  let monoms_p = List.map (fun (_,x) -> x) p#content in
	  list_union (fun x y -> x#syntactic_equal y) monoms_p (fn tail)
  in
  let distinct_monoms_lp = fn lp in
  List.map (fun x -> new_polynom 0 [(-1),x] []) distinct_monoms_lp
  
