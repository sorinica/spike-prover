
(*
   * Project: Spike ver 0.1
   * File: clauses.ml
   * Content: clauses definitions
*)

open Values
open Io
open Symbols
open Terms
open Order
open Literals
open Pi
open Polynoms
open Max
open Min
open Zmaxmin
open Npolynoms
open Natlist
open Diverse


exception Not_Horn

(* Ad hoc function for computation of capital d's (i.e. the global depth) of a rewrite system.
   We have sorted lists of (sort * depth). All sorts featured in the first list are also in the second.
   First argument must be depths, second strict_depths to enforce this condition.
*)
let rec fn_for_capital_d l l' =
  match l, l' with
    [], [] -> []
  | [], _ -> failwith "fn_for_capital_d"
  | _, [] -> List.map (fun (s, d) -> s, d - 1) l
  | (s, d) as h::t, (s', d')::t' ->
      if s > s'
      then failwith "fn_for_capital_d"
      else if s = s'
      then
        if d > d' then (s, d - 1)::fn_for_capital_d t t'
        else h::fn_for_capital_d t t'
      else (assert ( s < s' );
        h::fn_for_capital_d t l')

let rec print_redundant lc c  =
  match lc with
      [] -> ()
    | c' :: t -> 
   	if c#syntactic_equal c' then 
	  buffered_output ("\n  The clause " ^ (string_of_int c#number) ^ " is eliminated since redundant with " ^ (string_of_int c'#number) ^ "\n")
   	else print_redundant t c
	  

exception Proof
exception Refutation
exception MyExit of string

  (* system of clauses  *)
class ['a] system (ini_l: 'a list) =

object (self)

  val mutable content = ini_l

  method content = content

  method copy = {< >}

  method length = List.length content

  method sprint_numbers =
    let l = List.map (fun x -> x#number) content in
    List.fold_left (fun x y -> x ^ " " ^ y) "" (List.map string_of_int l)

  (* Checks whether one element satisfies predicate p *)
  method exists p =
    List.exists p content

  method iter f =
    List.iter f content

  method current_el =
    match content with
        [] -> raise Proof
      | h::_ -> h

  method all_but i =
    list_all_but i content

  method append els =
    
    let els', els_equal = List.partition (fun x -> not
      (generic_list_object_member x content)) els in
    let () = List.iter (print_redundant content) els_equal in
    let els'', content' = if !resolution_mode then resolution els' content else els', content in
    self#replace_w_list (List.length content') els'' 

  method init (c: 'a list) =
    content <- [];
    self#replace_w_list 0 c

  method is_empty =
    match content with
        [] -> true
      | _ -> false

  method print ind_s =
    List.iter (fun x -> buffered_output (ind_s ^ x#string)) content

  method ith i = try List.nth content i with (Failure "nth") -> failwith "ith"

  (* Replace nth element. Put all previous elements at the tail of the list *)
  method replace n el =
    self#replace_w_list n [el]
      
  method replace_w_list n (els: 'a list) =
    let els', els_equal = List.partition (fun x -> not
      (generic_list_object_member x content)) els in
    let () = if els_equal <> [] then 
	print_string (List.fold_left (fun str c -> str ^ (" \n The clause " ^ c#string ^ "\n is eliminated from the current set of conjectures since redundant\n\n" ) ) "\n " els_equal) in
    let els'', content' = if !resolution_mode then resolution els' content else els', content in
    (* dealing with the decision procedures *)
    let els_res = 
      if els'' == [] then []
      else
	let els_Rnatlist = 
	  if !specif_Rnatlist_defined 
	  then 
	    list_special_map (fun c -> 
	      if c#negative_lits == [] && List.length c#positive_lits == 1 then
		try 
		  let () = if !maximal_output then buffered_output ("\nTrying the Rnatlist module on " ^ c#string) in 
		  let (lhs, rhs) = c#both_sides in 
		  let lhs_norm = natlist_norm lhs 0 in 
		  let rhs_norm = natlist_norm rhs 0 in 
		  let () = buffered_output ("\nNormalized lhs = " ^ lhs_norm#string ^ "\nNormalized rhs = " ^ rhs_norm#string) in
		  if  lhs_norm#syntactic_equal rhs_norm 
		  then let _ = buffered_output ("\nThe Rnatlist module validated the conjecture " ^ c#string) in 
		       raise Inconsistent 
		  else let _ = buffered_output ("\nThe Rnatlist module refuted the conjecture " ^ c#string) in  
		       raise Refutation 
		with Failure "natlist_norm" -> c
	      else c) Inconsistent els'' 
	  else els''
	in
	let els_Rzmm = 
	  if els_Rnatlist == [] then []
	  else if !specif_Rzmm_defined 
	  then 
	    list_special_map (fun c -> 
	      if c#negative_lits == [] && List.length c#positive_lits == 1 then
		try 
		  let () = if !maximal_output then buffered_output ("\nTrying the Rzmm module on " ^ c#string) in 
		  let (lhs, rhs) = c#both_sides in 
		  let lhs_norm = zmm_norm lhs 0 in 
		  let rhs_norm = zmm_norm rhs 0 in 
		  let () = buffered_output ("\nNormalized lhs = " ^ lhs_norm#string ^ "\nNormalized rhs = " ^ rhs_norm#string) in
		  if  lhs_norm#syntactic_equal rhs_norm 
		  then let _ = buffered_output ("\nThe Rzmm module validated the conjecture " ^ c#string) in 
		       raise Inconsistent 
		  else let _ = buffered_output ("\nThe Rzmm module refuted the conjecture " ^ c#string) in  
		       raise Refutation 
		with Failure "zmm_norm" -> c
	      else c) Inconsistent els_Rnatlist 
	  else els_Rnatlist
	in
	let els_Rmins0 = 
	  if els_Rzmm == [] then [] 
	  else if !specif_Rmins0_defined 
	  then 
	    list_special_map (fun c -> 
	      if c#negative_lits == [] && List.length c#positive_lits == 1 then
		try 
		  let () = if !maximal_output then buffered_output ("\nTrying the Rmins0 module on " ^ c#string) in 
		  let (lhs, rhs) = c#both_sides in 
		  let lhs_norm = min_norm lhs 0 in 
		  (* let () = buffered_output "\nDealing with rhs_norm !\n\n\n" in *)
		  let rhs_norm = min_norm rhs 0 in 
		  let () = buffered_output ("\nNormalized lhs = " ^ lhs_norm#string ^ "\nNormalized rhs = " ^ rhs_norm#string) in
		  if  lhs_norm#syntactic_equal rhs_norm 
		  then let _ = buffered_output ("\nThe Rmins0 module validated the conjecture " ^ c#string) in 
		       raise Inconsistent 
		  else let _ = buffered_output ("\nThe Rmins0 module refuted the conjecture " ^ c#string) in  
		       raise Refutation 
		with Failure "min_norm" -> c
	      else c) Inconsistent els_Rzmm
	  else els_Rzmm
	in
	let els_Rmaxs0 = 
	  if els_Rmins0 == [] then []
	  else if !specif_Rmaxs0_defined 
	  then 
	    list_special_map (fun c -> 
	      if c#negative_lits == [] && List.length c#positive_lits == 1 then
		try 
		  let () = if !maximal_output then buffered_output ("\nTrying the Rmaxs0 module on " ^ c#string) in 
		  let (lhs, rhs) = c#both_sides in 
		  let lhs_norm = max_norm lhs 0 in 
		  let rhs_norm = max_norm rhs 0 in 
		  let () = buffered_output ("\nNormalized lhs = " ^ lhs_norm#string ^ "\nNormalized rhs = " ^ rhs_norm#string) in
		  if  lhs_norm#syntactic_equal rhs_norm 
		  then let _ = buffered_output ("\nThe Rmaxs0 module validated the conjecture " ^ c#string) in 
		       raise Inconsistent 
		  else let _ = buffered_output ("\nThe Rmaxs0 module refuted the conjecture " ^ c#string) in  
		       raise Refutation 
		with Failure "max_norm" -> c
	      else c) Inconsistent els_Rmins0
	  else els_Rmins0
	in
	let els_Rmps0 = 
	  if els_Rmaxs0 == [] then []
	  else if !specif_Rmps0_defined 
	  then 
	    list_special_map (fun c -> 
	      if c#negative_lits == [] && List.length c#positive_lits == 1 then
		try 
		  let () = if !maximal_output then buffered_output ("\nTrying the Rmps0 module on " ^ c#string) in 
		  let (lhs, rhs) = c#both_sides in 
		  let lhs_norm = np_norm lhs 0 in 
		  let rhs_norm = np_norm rhs 0 in 
		  let () = buffered_output ("\nNormalized lhs = " ^ lhs_norm#string ^ "\nNormalized rhs = " ^ rhs_norm#string) in
		  if  lhs_norm#syntactic_equal rhs_norm 
		  then let _ = buffered_output ("\nThe Rmps0 module validated the conjecture " ^ c#string) in 
		       raise Inconsistent 
		  else let _ = buffered_output ("\nThe Rmps0 module refuted the conjecture " ^ c#string) in  
		       raise Refutation 
		with Failure "np_norm" -> c
	      else c) Inconsistent els_Rmaxs0 
	  else els_Rmaxs0
	in
	let els_LA =
	  if els_Rmps0 == [] then [] 
	  else if !specif_LA_defined
	  then 
	    let () = if !maximal_output then buffered_output "\nTrying LA + CC !\n" in 
	    list_special_map (fun c -> let () = c#fill_peano_context in c) Inconsistent els_Rmps0
      	  else els_Rmps0
	in
	els_LA
    in
    (*       let new_l = List.flatten (List.map preprocess_conjecture newels) in *)
    let new_n = if (difference (fun z y -> z#syntactic_equal y) content content') = [] then n else (n-1) in
    let new_n' = if List.length content' < new_n then List.length content' else new_n in
    let new_n'' = if new_n' < 0 then 0 else new_n' in
    let v, tv = try list_split_at_n new_n'' content' with Failure "list_split_at_n" -> failwith "replace_w_list" in
    let tv' = if tv = [] then [] else List.tl tv in
    content <- tv'@v@els_res

  method clear =
    content <- []

end

  (* used for lemmas system *)
class ['a] l_system (ini_l : 'a list) =

  object (_)

    inherit ['a] system ini_l

    method append els =
      let els1 = generic_list_object_remove_doubles els in
      let els' = List.map (fun x -> x#try_to_orient) els1 in
      let els'' = List.filter (fun x -> not (generic_list_object_member x content)) els' in
      content <- content @ els''

    method init (c : 'a list) =
      let c' = generic_list_object_remove_doubles c in
      let c'' = List.map (fun x -> x#try_to_orient) c' in
      content <- List.map (fun x -> x#rename_from_zero) c'' ;

  end

class ['a] rw_system (ini_l: 'a list) =

  object (self)

    val mutable content = ini_l

    method content = content

    method init c =
      content <- c ;

    (* Checks whether one element satisfies predicate p *)
    method exists p =
      List.exists p content

    method iter f =
      List.iter f content

    (* All elements except ith *)
    method minus i =
      let l = list_all_but i content in
      new rw_system l

    method ith i = try List.nth content i with (Failure "nth") -> failwith "ith"

    (* Lefthand sides of the rules (i.e. the Horn clauses only) *)
    method lefthand_sides =
      let fn x = x#lefthand_side in
      (List.map fn content : term list)

    (* Left linearity *)
    method is_left_linear =
      let fn x = x#is_left_linear in
      if List.for_all fn content
      then
        let () = buffered_output "R is left linear" in
        true
      else
        let () = buffered_output "R is not left linear" in
        false

    (* Maximum depth of all rules *)
    method depth =
      let d t = t#depth in
      generic_list_max (List.map d self#lefthand_sides)

    (* Maximum strict depth of all rules *)
    method strict_depth =
      let d t = t#strict_depth in
      generic_list_max (List.map d self#lefthand_sides)

    (* D (r) *)
    method capital_d =
      let d = self#depth
      and s = self#strict_depth in
      if s < d && self#is_left_linear
      then d - 1
      else d

    (* Maximum depth of all rules per sort *)
    method depth_per_sort =
      let d t = t#depth_per_sort in
      list_max max_assoc_merge (List.map d self#lefthand_sides)

    (* Maximum depth of all rules per sort *)
    method strict_depth_per_sort =
      let d t = t#strict_depth_per_sort in
      list_max max_assoc_merge (List.map d self#lefthand_sides)

    (* D (r) per sort *)
    method capital_d_per_sort =
      let l = self#depth_per_sort
      and l' = self#strict_depth_per_sort in
      let res =
        if self#is_left_linear
        then fn_for_capital_d l l'
        else l in
      let () = 
	try 
	  buffered_output ("D [s] = " ^ (sprint_list "; " (fun (x, y) -> "(" ^ (dico_sort_string#find x) ^ ", " ^ (string_of_int y) ^ ")") res))
	with Not_found -> failwith "raising Not_found in capital_d_per_sort"
      in
      res

    (* Compute induction positions of a rewrite system r. Puts them in the dictionary *)
    method compute_induction_positions_v0 =
      let () = if !debug_mode then buffered_output "\nComputing the induction positions ..." in
      let fn2 x = generic_remove_el [] x#strict_positions  in
      let fn c = 
        let lhs = c#lefthand_side in
	  
	  (* 	let () = buffered_output ("\n lhs = " ^ lhs#string) in *)
	  let rec fn' t (lp:position) = 
	    match lp with 
		[] -> [(t#head), 0]
	      | h :: tl -> 
		  let k, l = t#head_n_sons in
		  let h_el = List.nth l h in
		  (k, h) :: (fn' h_el tl)
	  in
          let fn3 t =
	    let nl =  t#non_linear_positions in
	    if nl <> [] then failwith ("Rules with non_linear lhs are not yet supported. Please use the conditional variant for " ^  c#string) 
	    else
	      let lpos = fn2 t in
(* 	      let () = buffered_output (sprint_list "\t" sprint_position lpos) in *)
	      let l = List.map (fn' t) lpos in
              let f = t#head in
	      let old_l  = try dico_ind_positions_v0#find f with Not_found -> [] in
	      let new_l = if l <> [] then list_insert (=) l old_l else old_l in
              dico_ind_positions_v0#merge f (new_l) 
	  in
          fn3 lhs 
      in
      self#iter fn
	
    (* Compute induction positions of a rewrite system r. Puts them in the dictionary *)
    method compute_induction_positions_v1 =
      let max_depth ((d, _) as v) ((d', _) as v') = if d > d' then v else v' in
      let fn (p, ds) = dico_ind_positions_v1#apply_f max_depth p ds in
      let fn2 c =
        let lhs = c#lefthand_side in
        let l = lhs#ind_positions_v1 in
        List.iter fn l in
      self#iter fn2

    method string =
      sprint_list "\n" (fun x -> x#string) content

  end


type concrete_peano_literal =
    Peano_equal of ground_term * ground_term
  | Peano_diff of ground_term * ground_term
  | Peano_less of ground_term * ground_term
  | Peano_leq of ground_term * ground_term

let peano_members = function
    Peano_equal (t, t') -> t, t'
  | Peano_diff (t, t') -> t, t'
  | Peano_less (t, t') -> t, t'
  | Peano_leq (t, t') -> t, t'

let is_peano_equal = function
    Peano_equal _ -> true
  | Peano_diff _ | Peano_less _ | Peano_leq _ -> false

let is_peano_diff = function
    Peano_diff _ -> true
  | Peano_equal _ | Peano_less _ | Peano_leq _  -> false

let is_peano_less = function
    Peano_less _ -> true
  | Peano_diff _ | Peano_equal _ | Peano_leq _ -> false

let is_peano_leq = function
    Peano_leq _ -> true
  | Peano_diff _ | Peano_less _ | Peano_equal _ -> false

class peano_literal c_p_l' =
  let c_p_l = match c_p_l' with
      Peano_equal (t, t') -> Peano_equal ((preprocess_ac t), (preprocess_ac t'))
    | Peano_diff (t, t') -> Peano_diff ((preprocess_ac t), (preprocess_ac t'))
    | Peano_less (t, t') -> Peano_less ((preprocess_ac t), (preprocess_ac t'))
    | Peano_leq (t, t') -> Peano_leq ((preprocess_ac t), (preprocess_ac t'))
  in
  object (self: 'a)

    inherit printable_object
    inherit pi_object

    val content = c_p_l

    val variables =
      let lhs, rhs = peano_members c_p_l in
      generic_merge_sorted_lists lhs#variables rhs#variables

    method content = content

    method members = peano_members content

  (* pretty print function *)
    method pprint f = Format.fprintf f "@[@ Peano literal: %s@]" self#string

    method compute_pi =
      let peano_sort = if !nat_specif_defined then id_sort_nat else id_sort_int in
      let list_bool_operators = [id_symbol_leq; id_symbol_less; id_symbol_geq; id_symbol_greater] in 
      let list_bool_values = [id_symbol_true; id_symbol_false] in 
      let fn t t'= 
	if t#sort = peano_sort then true
      	else if t#sort = id_sort_bool 
	then 
	  t#is_term && t'#is_term && (list_member ( = ) t'#head (list_bool_values @ list_bool_operators)) &&
	 (list_member ( = ) t#head (list_bool_values @ list_bool_operators)) &&
         (not ((list_member ( = ) t'#head list_bool_values) && (list_member ( = ) t'#head list_bool_values))) 
	else false 
      in 
      match content with
        Peano_equal (t, t') -> fn t t'
      | Peano_diff (t, t') -> fn t t' (* false *)
      | Peano_less _ | Peano_leq _ -> true

    method compute_string =
      match content with
    	Peano_equal (t, t') -> t#string ^ " = " ^ t'#string
      | Peano_diff (t, t') -> t#string ^ " <> " ^ t'#string
      | Peano_less (t, t') -> t#string ^ " < " ^ t'#string
      | Peano_leq (t, t') -> t#string ^ " <= " ^ t'#string

    method both_sides = peano_members content

    method syntactic_equal (l : peano_literal) =
	match self#content, l#content with 
	    Peano_less (lhs, rhs), Peano_less (lhs', rhs') ->  
	      lhs#syntactic_equal lhs' && rhs#syntactic_equal rhs'
	  | Peano_diff (lhs, rhs), Peano_diff (lhs', rhs') ->  
	      lhs#syntactic_equal lhs' && rhs#syntactic_equal rhs'
	  | Peano_leq (lhs, rhs), Peano_leq (lhs', rhs') ->  
	      lhs#syntactic_equal lhs' && rhs#syntactic_equal rhs'
	  | Peano_equal (lhs, rhs), Peano_equal (lhs', rhs') ->  
	      lhs#syntactic_equal lhs' && rhs#syntactic_equal rhs'
	  | Peano_less _, Peano_diff _| Peano_diff _, Peano_less _| Peano_less _, Peano_leq _| Peano_leq _, Peano_less _| Peano_less _, Peano_equal _| Peano_equal _, Peano_less _| Peano_diff _, Peano_leq _| Peano_leq _, Peano_diff _| Peano_diff _, Peano_equal _| Peano_equal _, Peano_diff _| Peano_leq _, Peano_equal _| Peano_equal _,	Peano_leq _ -> false

    method is_subterm (t : term) =
      let lhs, rhs = self#both_sides in
      try
	let _ = t#subterm lhs in true
      with (Failure "subterm") ->
	try
	  let _ = t#subterm rhs in true
      	with (Failure "subterm") ->
	  false
  end

(* negativize a literal. Normal form contains no greater symbols *)
let rec invert_literal (lit: literal) =
  match lit#content with
      Lit_diff (x,y) -> convert_literal (new literal (Lit_equal (x,y)))
    | Lit_equal _ | Lit_rule _ ->
  	let lhs, rhs = lit#both_sides
  	and bool_content b t =
	  try
	    match t#head_n_sons with
        	f, [ t1 ; t2 ] ->
		  if f = id_symbol_less then
		    if b then
		      Peano_leq (t2, t1)
		    else
		      Peano_less (t1, t2)
		  else if f = id_symbol_leq then
		    if b then
		      Peano_less (t2, t1)
		    else
		      Peano_leq (t1, t2)
		  else if f = id_symbol_greater then
		    if b then
		      Peano_leq (t1, t2)
		    else
		      Peano_less (t2, t1)
		  else if f = id_symbol_geq then
		    if b then
		      Peano_less (t1, t2)
		    else
		      Peano_leq (t2, t1)
		  else failwith "bool_content"
	      | _ -> failwith "bool_content"
	  with (Failure "head_n_sons") -> failwith "bool_content" in
  	new peano_literal
	  (
	    if term_is_true lhs
	    then try bool_content true rhs with (Failure "bool_content") -> Peano_equal (rhs, term_false)
	    else if term_is_false lhs
	    then try bool_content false rhs with (Failure "bool_content") -> Peano_equal (rhs, term_true)
	    else if term_is_true rhs
	    then try bool_content true lhs with (Failure "bool_content") -> Peano_equal (lhs, term_false)
	    else if term_is_false rhs
	    then try bool_content false lhs with (Failure "bool_content") -> Peano_equal (lhs, term_true)
	    else Peano_diff (lhs, rhs)
	  )
	  
(* convert a literal into a Peano literal. Normal form contains no greater symbols *)
and convert_literal (lit: literal) =
  match lit#content with
      Lit_diff (x,y) -> invert_literal (new literal (Lit_equal (x,y)))
    | Lit_equal _ | Lit_rule _ ->
  	let lhs, rhs = lit#both_sides
  	and bool_content b t =
	  try
	    match t#head_n_sons with
        	f, [ t1 ; t2 ] ->
		  if f = id_symbol_less then
		    if b then
		      Peano_less (t1, t2)
		    else
		      Peano_leq (t2, t1)
		  else if f = id_symbol_leq then
		    if b then
		      Peano_leq (t1, t2)
		    else
		      Peano_less (t2, t1)
		  else if f = id_symbol_greater then
		    if b then
		      Peano_less (t2, t1)
		    else
		      Peano_leq (t1, t2)
		  else if f = id_symbol_geq then
		    if b then
		      Peano_leq (t2, t1)
		    else
		      Peano_less (t1, t2)
		  else failwith "bool_content"
	      | _ -> failwith "bool_content"
	  with (Failure "head_n_sons") -> failwith "bool_content" in
  	new peano_literal
	  (if term_is_true lhs
	  then try bool_content true rhs with (Failure "bool_content") -> Peano_equal (rhs, term_true)
	  else if term_is_false lhs
	  then try bool_content false rhs with (Failure "bool_content") -> Peano_equal (rhs, term_false)
	  else if term_is_true rhs
	  then try bool_content true lhs with (Failure "bool_content") -> Peano_equal (lhs, term_true)
	  else if term_is_false rhs
	  then try bool_content false lhs with (Failure "bool_content") -> Peano_equal (lhs, term_false)
	  else Peano_equal (lhs, rhs))


    (* produces a list of polynoms from a peano_literal *)
let linearize (l: peano_literal) =
  let () = if !maximal_output then print_indent_string  (" the literal to linearize is  " ^ l#string )
  in
  let () = assert l#is_pi in 
  let peano_sort = if !nat_specif_defined then id_sort_nat else id_sort_int in
  let fn = function
      Peano_less (t, t') ->  new_polynom 1 [ (1, t) ; (-1, t') ] []
    | Peano_leq (t, t') -> let () = if !maximal_output then print_indent_string (" the term t is " ^ t#compute_string ^ " and the term t' is " ^ t'#compute_string)
      in
	let np = new_polynom 0 [ (1, t) ; (-1, t') ] [] in 
  	let () = if !maximal_output then print_indent_string (" the resulted polynomial is  " ^ np#string )
	in
	np
    | Peano_equal _ | Peano_diff _ -> failwith "linearize" in
  match l#content with
      Peano_equal (t, t') -> if t#sort = peano_sort then 
	(* t = t' is equivalent to t <= t' && t >= t' *)
	[[( fn (Peano_leq (t, t')) ) ; ( fn (Peano_leq (t', t)))]]
  	else 
	(* t = t' is equivalent to t \equiv t' *)
	let () = assert (t#sort = id_sort_bool) in 
	[
	  [ fn (convert_literal (new literal (Lit_equal (t, term_true))))#content; 
	  fn (convert_literal (new literal (Lit_equal (t', term_true))))#content];
	  [ fn (convert_literal (new literal (Lit_equal (t, term_false))))#content; 
	  fn (convert_literal (new literal (Lit_equal (t', term_false))))#content]
	]
    | Peano_diff (t, t') -> if t#sort = peano_sort then 
	(* t <> t' is equivalent to t < t' or t > t' *)
        [[ fn (Peano_less (t, t')) ] ; [ fn (Peano_less (t', t))]]
      else 
	(* t <> t' is equivalent to t \xor t' *)
	let () = assert (t#sort = id_sort_bool) in 
	[
	  [ fn (convert_literal (new literal (Lit_equal (t, term_true))))#content; 
	  fn (convert_literal (new literal (Lit_equal (t', term_false))))#content];
	  [ fn (convert_literal (new literal (Lit_equal (t, term_false))))#content; 
	  fn (convert_literal (new literal (Lit_equal (t', term_true))))#content]
	]
	
    | Peano_less _ 
    | Peano_leq _  -> [[ fn l#content ]]

(* not used for the moment *)	
let literalize (p: polynom) =
  let peano_sort = if !nat_specif_defined then id_sort_nat else
    id_sort_int in
  let l = p#content
  and c = p#constant
  and fn (i, t) = new term (Term (id_symbol_times, [ term_nat i ; t ], peano_sort)) in
  let l' = List.map fn l
  and c' = term_nat c in
  let t' = new term (Term(id_symbol_plus, c'::l', peano_sort)) in
  let term_zero = new ground_term (Term(id_symbol_zero, [],peano_sort)) in 
  new peano_literal (Peano_equal (new term (Term (id_symbol_leq,[t' ; term_zero ], peano_sort)) , term_true))
    
let peano_literal_tautology = new peano_literal (Peano_equal (term_true, term_true))

let oracle_a = ref (fun (_: int)
  (_: Polynoms.polynom) (_: Polynoms.polynom list) _ _ _ _ ->
    ([]:peano_literal list))

  (* computes the normal form of trm by using a list of rewrite rules r *)
let normal_form (r : peano_literal list) (trm:ground_term) =
  let rec parcours_positions tr lhs rhs = function
      [] -> tr
    | p :: t -> try 
	let tr_at_p = tr#subterm_at_position p in 
	if tr_at_p#syntactic_equal lhs then
	  let repl = tr#replace_subterm_at_pos p rhs in
	  rewrite repl r 
	else
	  parcours_positions tr lhs rhs t
      with Failure "subterm_at_position" ->
	parcours_positions tr lhs rhs t
	  
  and  rewrite tr = function
      [] -> tr
    | h::t ->
        match h#content with
          Peano_equal (lhs, rhs) ->
            begin
(* 	      assert (ground_greater lhs rhs); *)
              let all_p = tr#all_positions in 
	      let new_tr = parcours_positions tr lhs rhs all_p in
              rewrite new_tr t
            end
          | Peano_less _ | Peano_leq _ | Peano_diff _ -> failwith "normal_form"
  in 
  rewrite trm r 

let critical_pairs (a : peano_literal list) (l: ground_term) (r: ground_term) =
  let rec fn = function
      [] -> []
    | h::t ->
        let lhs, rhs = h#both_sides in
        try
          let p = lhs#subterm l in
          (r, l#replace_subterm_at_pos p rhs)::fn t
        with (Failure "subterm") ->
          try
            let p = l#subterm lhs in
            (rhs, lhs#replace_subterm_at_pos p r)::fn t
          with (Failure "subterm") -> fn t
  in 
  let crit_pair = fn a in
  if crit_pair = [] then [l, r]
  else crit_pair
       
	  
  (* used only by apply_cc  *)
let inconsistent (d : peano_literal list) (r : peano_literal list) =
  let fn plit =
    let s, t = plit#both_sides in
    let s' = normal_form r s
    and t' = normal_form r t in
    s'#syntactic_equal t'
  in List.exists fn d


  (* tests if t' is a subterm of t  *)
let reduces (t: ground_term) (t':ground_term) =
  try
    let _ = t'#subterm t in
    true
  with (Failure "subterm") -> false

let apply_cc cr l =
  let e, d = List.partition (function x -> match x#content with Peano_equal _ -> true | Peano_diff _ -> false | Peano_leq _ | Peano_less _ -> failwith "apply_cc") l in
  let rec fn r = function
      [] -> r @ d
    | hd :: tl -> begin
        match hd#content with
            Peano_equal (s, t) ->
              let s' = normal_form (r @ cr) s
              and t' = normal_form (r @ cr) t in
              if s'#syntactic_equal t'
              then fn r tl
              else
              	let lhs, rhs = 
		  try orient  s' t' with 
		      Failure "orient" -> 
			print_string (" Fail to orient  " ^ 
			s'#string ^ " = " ^ t'#string); failwith "apply_cc" 
		in
		let oriented_lit = new peano_literal (Peano_equal
		  (lhs, rhs)) in
              	if inconsistent d (oriented_lit :: (r @ cr))
              	then raise Inconsistent
              	else
                  let r', e' = fn2 lhs rhs r
                  in fn (oriented_lit :: r') (e' @ tl)
          |  Peano_diff (s, t) ->
	       let () = if !maximal_output then print_indent_string ("Peano_diff: s" ^ s#string) in
	       let () = if !maximal_output then print_indent_string ("Peano_diff: t" ^ t#string) in
              let s' = normal_form (r @ cr) s
              and t' = normal_form (r @ cr) t in
	      if s'#syntactic_equal t' then raise Inconsistent
	      else failwith "apply_cc"
	  | Peano_less _ | Peano_leq _ -> failwith "apply_cc"
      end
  and fn2 lhs rhs = function
      [] -> [], []
    | hd::tl -> begin
        match hd#content with
          Peano_equal (s, t) ->
	    assert (ground_greater s t );
            let r, e = fn2 lhs rhs tl in
            if reduces s lhs
            then
              r, hd::e
            else if reduces t lhs
            then
              let t' = normal_form r t in
              ((new peano_literal (Peano_equal (s, t')))::r, e)
            else
              let cp = List.map (fun (x, y) -> new peano_literal (Peano_equal (x, y))) (critical_pairs (hd::r) lhs rhs) in
              hd::r, cp @ e
          | Peano_diff _| Peano_less _| Peano_leq _ -> failwith "apply_cc" 
      end 
  in
  fn [] e

let implicit_equations l = 
  let peano_sort = if !nat_specif_defined then id_sort_nat else
    id_sort_int in
  let equationable p = 
    match p#content with
	[(1, t)] -> if p#constant <= 0 then (* t = - p#constant *)
	  new peano_literal (Peano_equal (t, term_nat (- p#constant)))
	else (* t = (0 - p#constant) *)
	  new peano_literal (Peano_equal (t, 
	  new term (Term (id_symbol_minus, [new term (Term (id_symbol_zero, [], peano_sort)); term_nat p#constant], peano_sort))))
      | [(1, t1);(-1,t2)] -> if p#constant = 0 then new peano_literal (Peano_equal (t1,t2))
	else failwith "equationable"
      | [(-1, t1);(1,t2)] -> if p#constant = 0 then new peano_literal (Peano_equal (t1,t2))
	else failwith "equationable"
      | _ -> failwith "equationable"
  in
  let rec fn1  = function (* transforms a list of polynoms into equations *)
      [] -> []
    | p :: tl -> 
	try let eq = (equationable p) in eq :: (fn1 tl)
	with   Failure "equationable" -> fn1 tl
  in
  let fn p = 
    if p#syntactic_equal poly_0_leq_0 then (* p#history contains only elements equal to 0  *)
      fn1 p#history
    else []
  in 
  let all_eq = List.flatten (List.map fn l) in 
  list_remove_doubles (fun x y -> x#syntactic_equal y) all_eq
       
let apply_la l = 
  let l' = if !nat_specif_defined then l @ (add_nat_variables l) else l in
  let is_inconsistent lp =    (* tests if the set of polynoms lp is inconsistent *)
    if List.exists (fun x ->  x#impossible) lp then 
      let () = if !maximal_output then buffered_output  ("\nThe inconsistent polynom is one of: \n" ^ (sprint_list
      	"\n" (fun x -> ("   " ^ x#string)) (list_remove_doubles (fun x
	  -> x#syntactic_equal) lp )))  in 
      true
    else false
  in
  let nl = list_remove_doubles (fun x -> x#syntactic_equal) l' in
  let max_length = List.fold_right (fun x y -> max x y) (List.map (fun x
    -> List.length x#content) nl) 0 in
  let max_iterations = max max_length (List.length nl) in
  let rec apply_la_core l nr_iter =
    let rec calcul_coef = function 
	[] -> []
      | (p1,p2) :: tl ->
	  let lpc' = calcul_coef tl in
	  try
	    let (k1, k2) = p1#combination p2 in 
	    ((p1,p2), (k1, k2)) :: lpc'
	  with Failure "combination" -> 
	    lpc'
    in
    let c_l =  all_combinations_from_list l in
    let () = if !maximal_output then print_indent_string ("\n    apply_la: the size of c_l and l are:" 
                ^ (string_of_int (List.length c_l)) ^ " and " ^ (string_of_int (List.length l)) ^ "\n" ) in
    let lpc = calcul_coef c_l  (* lpc contains the combinable polys + the appropriate coefficients *)
    in
    let added_poly =  List.map (fun ((p1,p2),(k1,k2)) -> (p1#cross_multiply_add p2 (k1,k2))) lpc in 
    let new_l = l @ added_poly in 
    let np = list_remove_doubles (fun y -> y#syntactic_equal) new_l in
    let () = if !maximal_output then print_indent_string ("\n\tthe polynoms list l is \n"
    ^ (List.fold_right (fun x y -> "\n" ^ x#string ^ y) l "")) in 
    let () = if !maximal_output then print_indent_string  ("\n\tthe polynoms list nc is \n"
    ^ (List.fold_right (fun x y -> "\n" ^ x#string ^ y) np ""))  in 
    if is_inconsistent np then raise Inconsistent 
    else 
      if nr_iter > max_iterations  (* the fixpoint has been reached *)
           then np
           else apply_la_core np (nr_iter + 1)
  in   
  if not (is_inconsistent l) then 
    let new_l = (apply_la_core nl 0) in 
    let i_e = implicit_equations new_l in 
    new_l, i_e 
  else raise Inconsistent
  ;;

let normalize_cx_l (poly_ie : Polynoms.polynom list list * 'a) rules = 
  let l_polys, ie = poly_ie in
  let fn_poly p = 
    let hist = p#history 
    and const = p#constant in
    let new_content = List.map (fun (c, t) -> (c, normal_form rules t)) p#content in
    new polynom const new_content hist
  in
  let fn_polys polys = List.map fn_poly polys in
  (List.map fn_polys l_polys), ie

  (* normalize_lit normalizes the Peano literal "lit" with the rewriting 
     rules "rules" *)
let normalize_lit rules lit = match lit#content with
    Peano_equal (t1,t2) -> new peano_literal (Peano_equal
      ((normal_form rules t1), (normal_form rules t2)))
  | Peano_diff (t1,t2) -> new peano_literal (Peano_diff
      ((normal_form rules t1), (normal_form rules t2)))
  | Peano_leq (t1,t2) -> new peano_literal (Peano_leq
      ((normal_form rules t1), (normal_form rules t2)))
  | Peano_less (t1,t2) -> new peano_literal (Peano_less
      ((normal_form rules t1), (normal_form rules t2)))


  (* the type for the rules acting to build the context  *)
type rule = Augment_L | Augment_G | A2L | A2G | L2G | G2CR

class peano_context  (negs: literal list) (poss: literal list) cr g l =
  let a = List.map convert_literal negs @ List.map
    invert_literal poss in 
  let initialize_a = List.map (fun x -> normalize_lit cr x) a in
  let () = if !maximal_output then print_indent_string ( " the original clause is " ^ (List.fold_right (fun x y -> x#string ^ ", " ^ y) negs "") ^ " => "^ (List.fold_right (fun x y -> x#string ^ ", " ^ y) poss "") )       
  in

  object (self)

    inherit printable_object

    val mutable cx_cr = cr
    val mutable cx_a = initialize_a
    val mutable cx_g = g
    val mutable cx_l = l

    method cx_cr = cx_cr
    method cx_a = cx_a
    method cx_g = cx_g
    method cx_l = cx_l
    method cx_p = fst cx_l
    method cx_ie = snd cx_l
  (* pretty print function *)
    method pprint f = Format.fprintf f "@[@ Peano context: %s@]" self#string

    method compute_string =
      let cx_p, cx_ie = cx_l in
      let cr_string = match cx_cr with [] -> "" | _ -> !indent_string ^ "\t\tCR: " ^ (sprint_list ", " (fun x -> x#string) cx_cr)
      and a_string = match cx_a with [] -> "" | _ -> !indent_string ^ "\t\tA: " ^ (sprint_list ", " (fun x -> x#string) cx_a)
      and g_string = match cx_g with [] -> "" | _ -> !indent_string ^ "\t\tG: " ^ (sprint_list ", " (fun x -> x#string) cx_g)
      and p_string = match cx_p with [] -> "" | _ -> !indent_string ^ "\t\tL.P: " ^ (sprint_list ("\n" ^ !indent_string ^ "       ") (sprint_list ", " (fun x -> x#string)) cx_p)
      and ie_string = match cx_ie with [] -> "" | _ -> !indent_string ^ "\t\tL.IE: " ^ (sprint_list ", " (fun x -> x#string) cx_ie) in
     cr_string ^ a_string ^ g_string ^ p_string ^ ie_string 
(*       cat_nonempty_strings [ cr_string ; a_string ; g_string ; p_string ; ie_string ] *)

    (* The following methods implement the REPEATED application of the
       context transformation rules described in the documentation ???? *)
    method g_2_cr =
      let () = if !maximal_output then print_indent_string ( "G2CR: the status before applying the rule is " ^ self#compute_string) in      
      let e = apply_cc (* cx_cr *) [] cx_g
      in let rec fn = function
          [] -> [], []
        | h::t ->
	    match h#content with
		Peano_equal (lhs, rhs) -> 
		  let l, l' = fn t in
		  if rpo_greater false lhs rhs
		  then
		    let c = new peano_literal (Peano_equal (lhs, rhs)) in
		    c::l, l'
		  else if rpo_greater false rhs lhs
		  then
		    let c = new peano_literal (Peano_equal (rhs, lhs)) in
		    c::l, l'
		  else (l, h::l') 
	      | Peano_diff _ | Peano_leq _| Peano_less _ -> let l, l' = fn t in
		(l, h::l')
      in
      let rules, notrules = fn e in
      let _ = cx_g <- notrules in
      match rules with
	[] -> []
      |	_ ->
	  let diff = difference (fun x y ->x#syntactic_equal y) rules cx_cr in
	  match diff with
	      [] ->  []
	    | _  -> 
		let fn1 e = 
		  let s',t' = e#both_sides in 
		  if s'#sort = id_sort_bool && ((s'#syntactic_equal term_true && t'#syntactic_equal term_false) || 
                                             (t'#syntactic_equal term_true && s'#syntactic_equal term_false)) then true 
		  else false 
		in
	  	let () = if List.exists fn1 diff then raise Inconsistent else cx_cr <- cx_cr @ diff in
		cx_l <- normalize_cx_l cx_l cx_cr;
	  	[Augment_G; Augment_L]

    method a_2_g =
       let l, l' = List.partition (fun x -> x#is_pi) cx_a in
       let () = cx_a <- l in (* update cx_a *)
       let diff = difference (fun x y ->x#syntactic_equal y ) l' cx_g in
       let a2g = 
	 if diff = [] 
	 then [] 
	 else let () = cx_g <- cx_g @ diff in
	 [G2CR]
       in a2g

    method l_2_g =
      let p, ie = cx_l in
      let diff =  difference (fun x y ->x#syntactic_equal y ) ie cx_g in
      if ie = [] || diff = []
      then []
      else
        let () = cx_g <- diff @ cx_g in
        let () = cx_l <- p, [] in
	[G2CR]

  (* to be modified. We still don't treat the sets of polynoms *)
    method a_2_l =
      let l, l' = List.partition (fun x -> x#is_pi) cx_a
      and p, _ = cx_l in
      let () = cx_a <- l' in (* update cx_a *)
      let () = if !maximal_output then print_indent_string ( " the status is " ^ self#compute_string)       
      in
      let a2g = match l' with [] -> [] | _ -> [A2G] in
      match  l with
	  []  -> a2g
      	| _ -> 
	    let fn l p = List.for_all (fun x -> list_member (fun y z -> y#syntactic_equal z) x p) l in 
	    if (List.length p) > 1 then a2g @ [Augment_L]
	    else if (List.length p) = 1 && List.for_all (fun x -> fn (List.flatten (linearize x)) (List.hd p)) l then []
	    else
	      let distrib llp p = 
		if p = [] then llp
		else 
	      	  match llp with
		      [lp] -> List.map (fun x -> x @ lp) p
		    | [lp1;lp2] -> (List.map (fun x -> x @ lp1) p) @
		      	(List.map (fun x -> x @ lp2) p)
		    | _ -> failwith "a_2_l"
	      in
	      let () = if !maximal_output then print_indent_string (" the peano literals before linearization are " 
	      ^ (List.fold_right (fun x y -> x#string ^ ", " ^ y)
		l "") )   
	      in 
	      let new_p = List.fold_right (fun x -> distrib (linearize x)) l p in
	      let () = if !maximal_output then print_indent_string (" the peano_literals after linearization are " 
	      ^ (List.fold_right (fun x y -> x#string ^ ", " ^ y)
		(List.hd new_p) "") )   
	      in
	      match new_p with
		  [] -> failwith "a_2_l"
		| [lp] ->
		    let p', ie' = apply_la lp in 
		    let p'_nonredundant = list_remove_doubles (fun x -> x#syntactic_equal) p' in
		    let () = cx_l <- [p'_nonredundant], ie' in
		    if ie' = [] then a2g @ [Augment_L] else [L2G] @ a2g @ [Augment_L]
		| _ -> 
		    let test lp = 
		      try let rez = apply_la lp in (false, rez)
		      with Inconsistent -> (true, ([],[]))
		    in
		    let _, consistent_lp = List.partition (fun (x,_) -> x) (List.map test new_p) in
		    match List.length  consistent_lp with
			0 ->  raise Inconsistent
		      | 1 ->  let _, (p', ie') =  (List.hd consistent_lp) in
			      let p'_nonredundant = list_remove_doubles (fun x -> x#equal) p' in
			      let () = cx_l <- [p'_nonredundant], ie' in
			      a2g @ [Augment_L]
		      | _ -> failwith "a_2_l"
			    
    method apply_la (l:Polynoms.polynom list)  =
      let p, (ie: peano_literal list) = apply_la l
      in p, ie

    method check_inconsistencies augment_counter (c: Literals.literal list * Literals.literal list)  =
      let initial_op =  [A2G;A2L] in
      let () = if !maximal_output then print_indent_string ( " the status before checking the inconsistencies is " ^ self#compute_string)       
      in
      let str p = match p with 
	  A2L -> "A2L" | A2G -> "A2G" | G2CR -> "G2CR" | L2G -> "L2G" | Augment_L -> "Augment_L" | Augment_G -> "Augment_G" 
      in
      let fn p = if !maximal_output then print_indent_string (  (str p)^ " is applying\n") 
      in
      let fn1 p = if !maximal_output then print_indent_string (  (str p) ^ " WAS applied\n") 
      in
      let rec cycle = function 
	  [] -> ()
	| A2L :: t -> 
	    (try
	      let () = fn A2L in
	      let op = self#a_2_l in 
	      let () = fn1 A2L in
	      cycle (list_remove_doubles (=) (op @ t))
	    with (Failure "a_2_l") -> cycle t   
	      )
	| A2G :: t ->  
	    let () = fn A2G in 
	    let op = self#a_2_g in 
	    let () = fn1 A2G in 
	    cycle (list_remove_doubles (=) (op @ t))
	| G2CR :: t ->  
	    let () = fn G2CR in 
	    let op = self#g_2_cr in 
	    let () = fn1 G2CR in 
	    cycle (list_remove_doubles (=) (op @ t))
	| L2G :: t ->  
	    let () = fn L2G in 
	    let op = self#l_2_g in 
	    let () = fn1 L2G in 
	    cycle (list_remove_doubles (=) (op @ t))
	| Augment_L :: t -> 
	    (try
	      let () = fn Augment_L in 
	      let op = if !augmentation_mode then self#augment_l augment_counter c else [] in  
	      let () = fn1 Augment_L in 
	      cycle (list_remove_doubles (=) (op @ t))
	    with (Failure "a_2_l") -> cycle t
	    )
	| Augment_G :: t -> let () = fn Augment_G in 
			    let op = if !augmentation_mode then self#augment_g else [] in (* nothing for the moment *)
			    let () = fn1 Augment_G in 
			    cycle (list_remove_doubles (=) (op @ t))
      in
      cycle initial_op

      

    method augment_l counter (reference: Literals.literal list *
    Literals.literal list) = 
      let nr, pr = reference in 
      let () = if !maximal_output then print_indent_string (" #augment_l has been called on the status " ^ self#compute_string) in
      let () = if !maximal_output then print_indent_string (" the original clause is " ^ (List.fold_right (fun x y -> x#string ^ ", " ^ y) nr "") ^ " => "
	^ (List.fold_right (fun x y -> x#string ^ ", " ^ y) pr "")) 
      in
      match cx_l with
          p, [] -> (* we treat only one polynomial database *)
	    if p = [] then [] 
	    else
	      let new_lits = List.flatten (List.map (fun x ->
	      	!oracle_a counter x (List.hd p) reference cx_cr cx_g (p,[]) ) (List.hd p))
	      in
	      if new_lits = [] then let () = if !maximal_output then print_indent_string ("\n    There are no added  literals ") in [] else
		let () = if !maximal_output then print_indent_string ("\n    The new added  literals are:") in 
		let () = List.iter (fun x -> print_indent_string
		    (x#string)) new_lits in 
		let normalized_new_lits = List.map (fun x -> normalize_lit cx_cr x) new_lits in
	      	let () = cx_a <- (cx_a @ normalized_new_lits) in
		let () = if !maximal_output then print_indent_string ("\n    The new added (normalized) literals are:") in 
		let () = List.iter (fun x -> if !maximal_output then print_indent_string
		    (x#string)) normalized_new_lits in 
        	let () = if !maximal_output then print_indent_string (" #augment_l has been called on the status " ^ self#compute_string)
		in
		[A2G;A2L]
	| _ -> [L2G]
		  
    method augment_g = []

  end

class ['peano] clause c_v hist br_info =

  object (self: 'a)

    inherit generic
    inherit printable_object

    val content = c_v
    val variables =
      let n, p = c_v in
      let v = generic_merge_set_of_lists (List.map (fun x -> x#variables) n)
      and v' = generic_merge_set_of_lists (List.map (fun x -> x#variables) p) in
      generic_merge_sorted_lists v v'
    val number = new_clause_number ()
    val mutable subsumption_failure = ([]: int list)
    val mutable augmentation_failure = ([]: int list)
    val mutable augmentation_literals = ([]: literal list)
    val mutable inference_bitstream = 0
    val neg_card = List.length (fst c_v)
    val pos_card = List.length (snd c_v)
    val card = List.length (fst c_v) + List.length (snd c_v)
    val mutable history = (hist: ((var * term) list * 'a) list)
    val mutable standby = false
    val mutable delete_standby = false
    val mutable sb_string = ""
    val mutable sb_IHs = ([]: ('a *  (Symbols.var * Terms.term) list) list)
    val mutable sb_newconjs = ([]: 'a list)
    val mutable broken_info = (br_info:string * int * (Literals.literal list * Literals.literal list ))
    val is_horn =
      match snd c_v with
        [l] -> (match l#content with 
	    Lit_rule _ | Lit_equal _ -> true
	  | Lit_diff _ -> false
	    )
      | _ -> false
    val mutable peano_context = (Undefined: 'peano pointer)
    val mutable oriented = (Undefined: bool pointer)
    val mutable maximal_terms = (Undefined: Terms.term list pointer)

      
    method set_broken_info info = broken_info <- info
    method get_broken_info = broken_info

    method augmentation_literals = augmentation_literals

    method add_augmentation lit = augmentation_literals <- 
      if list_member (fun x y ->x#syntactic_equal y) lit augmentation_literals 
      then augmentation_literals 
      else lit :: augmentation_literals

  (* pretty print function *)
    method pprint f = Format.fprintf f "@[@ Clause: %s@]" self#string

    method oriented =
      match oriented with
	Undefined ->
	  let b = try self#orientable with Not_Horn -> false in
	  let () = oriented <- Defined b in
	  b
      |	Defined b -> b

    method compute_peano_context :peano_context =
      let n, p = content in
      let cx = new peano_context n p [] [] ([],[]) in
      let () = cx#check_inconsistencies 0 content in
      cx

    method peano_context =
      match peano_context with
        Undefined ->
          let s = self#compute_peano_context in
          let () = peano_context <- Defined s in
          s
      | Defined s ->
	  s

    method fill_peano_context =
      match peano_context with
        Undefined ->
          let s = self#compute_peano_context in
          peano_context <- Defined s
      | Defined _ -> ()

    method cachedstring = string_of_bool (match string with Undefined -> false | Defined _ -> true) (* TODO *)

    method content = content

    method variables = variables

    method number = number

    method is_horn = is_horn

    (* Returns lefthand side of the positive literal *)
    method lefthand_side =
      if is_horn
      then (List.hd self#positive_lits)#lefthand_side
      else raise Not_Horn

    (* Returns the head of a Horn rule *)
    method head =
      if is_horn
      then List.hd self#positive_lits
      else raise Not_Horn

    (* Righthand side *)
    method righthand_side =
      if is_horn
      then (List.hd self#positive_lits)#righthand_side
      else raise Not_Horn

    (* Both *)
    method both_sides =
      if is_horn
      then (List.hd self#positive_lits)#both_sides
      else raise Not_Horn

    method conditions =
      if is_horn
      then fst content
      else raise Not_Horn

    method l_2_r =
      if is_horn
      then List.hd (snd content)
      else raise Not_Horn

  (* swaps lhs and rhs of the positive literal of a horn clause if not 
   oriented *)
    method swap_rule =
      if is_horn
      then
	let () = if oriented = Defined true then failwith "swap_rule" else () in
	let lhs, rhs = self#l_2_r#both_sides in
	let n = self#conditions in
 	{< oriented = Undefined ; content = (n, [ new literal (Lit_equal (rhs, lhs)) ]) >}
      else raise Not_Horn

    method force_orientation = 
      let n, p = self#content in
      if List.length p <> 1 then failwith "force_orientation" else
	let lit = List.hd p in
	let lit' = match lit#content with 
	    Lit_equal (t1, t2) -> new literal (Lit_rule (t1, t2))
	  | Lit_diff _ | Lit_rule _ -> lit 
	in
	{< oriented = Defined false ; content = (n, [lit']) >}

    (* Tries to orient the Horn clause into a rule. Fails otherwise. *)
    method orient =
      if oriented = Defined true then self
      else if oriented = Defined false || (self#head)#is_diff then failwith "orient"
      else
      	let lhs, rhs = self#both_sides
      	and negs = self#negative_lits in
      	let neg_terms = self#all_neg_terms in
	let order_on_terms = !rpos in
      	if multiset_greater (order_on_terms false)  [ lhs ] (rhs::neg_terms)     	
            &&
          (let lhs_vars = lhs#variables in
          let subset_lhs_vars x = generic_is_subset x#variables lhs_vars in
          subset_lhs_vars rhs
            &&
          List.for_all subset_lhs_vars neg_terms)
      	then
          let new_positive_literal = new literal (Lit_rule (lhs, rhs)) in
          {< content = (negs, [new_positive_literal]) ;
            string = Undefined ;
	    oriented = Defined true >}


     	else
          failwith "orient"

    method update_pos = 
      let negs, pos = content in
      let negs' = List.map (fun x -> x#update_pos) negs in
      let pos' = List.map (fun x -> x#update_pos) pos in
      {< content = (negs',pos') ; >}

    method try_to_orient =
      try self#orient with Not_Horn | (Failure "orient") -> {< oriented = Defined false >}

  (* again, the clause should be Horn  *)
    method orientable =
      if is_horn
      then
      	match (List.hd self#positive_lits)#content with
          Lit_rule _ -> true
	| Lit_diff _ -> false
      	| Lit_equal _ ->
            try
              let _ = self#orient in
              true
            with (Failure "orient") -> false
      else raise Not_Horn

    (* Left linearity *)
    method is_left_linear = (self#lefthand_side)#is_linear

    (* Set bit corresponding to a rule *)
    method set_bit b =
      inference_bitstream <- inference_bitstream lor b

    (* Do we have the right bit ? *)
    method has_bit b =
      inference_bitstream = inference_bitstream lor b

    method negative_cardinal = neg_card

    method positive_cardinal = pos_card

    method cardinal = card

    method is_non_empty =
      match c_v with
        [], [] -> false
      | _ -> true

    method is_empty =
      match c_v with
        [], [] -> true
      | _ -> false

    method greatest_varcode = 
      let fn variables = 
      try 
	let i = (fun (x,_,_) -> x) (last_el variables) in
	let j = (fun (x,_,_) -> x) (List.hd variables) in
	max (abs i) (abs j)
      with 
	  (Failure "last_el") -> 0
      in
      let lc_history = List.map (fun (s, c) -> let lv = c#variables in let vs = List.flatten (List.map (fun (_, t) -> t#variables)
      s) in lv @ vs) history in
      List.fold_right (fun lv_c max_l -> let n = fn lv_c in max (abs n) (abs max_l)) (variables ::  lc_history) 0

    method compute_string =
      let init_str =  "[ " ^ (string_of_int number) ^ " ] " in
      let final_str = " ;" in
      init_str ^
      (let l, r = content
      and f x = x#string in
      match l, r with
        [], [] -> "[]"
      | [], _ -> sprint_list " \\/ " f r
      | _, [] -> (sprint_list " /\\ " f l) ^ " => "
      | _ -> (sprint_list " /\\ " f l) ^ " => " ^ (sprint_list " \\/ " f r)) ^ final_str
(*       ^ (if !specif_LA_defined then "\n" ^ self#peano_context#string else "") *)


    method compute_string_coq_with_quantifiers print_quantifiers =
      let init_str = if variables = [] || (not print_quantifiers) then "" else "forall " ^ (sprint_list " " (fun (x, _, _) -> "u" ^ (string_of_int x)) variables) ^ ", " in
      init_str ^
      (
	let l, r = content
	and f x = x#compute_string_coq_with_quantifiers in
	  match l, r with
              [], [] -> "[]"
	    | [], _ -> (sprint_list " \\/ " f r) 
	    | _, [] -> (sprint_list " -> " f l) ^ " -> False"
	    | _ ->       let is_disj = List.length r > 1 in
		(sprint_list " -> " f l) ^ " -> " ^ (if is_disj then " (" else "") ^ (sprint_list " or " f r)^ (if is_disj then " )" else "")
      ) 

    method compute_string_coq_for_order with_model =
      let l, r = content and f x = x#compute_string_coq with_model in
	(sprint_list "::" f l) ^ (if l == [] || r == [] then "" else "::") ^ (sprint_list "::" f r) ^ "::nil"

    method def_symbols = 
      let l, r = content in
      let def_symb_l = List.map (fun x -> x#def_symbols) l in
      let def_symb_r = List.map (fun x -> x#def_symbols) r in
	(List.flatten def_symb_l) @ (List.flatten def_symb_r)

    (* Bijective renaming modulo AC properties of logical operators *)
    method bijective_renaming ren (c: 'a) =
      let lit_match r (l: literal) l' = l#bijective_renaming r l'
      and n, p = content
      and n', p' = c#content in
      let ren' = ac_eq lit_match (Failure "bijective_renaming") ren  n n' in
      ac_eq lit_match (Failure "bijective_renaming") ren' p p'

    (* Equality modulo bijective renaming and AC properties *)
    method equal (c: 'a) =
      try
        let _ = self#bijective_renaming [] c in
        true
      with (Failure "bijective_renaming") | (Failure "ac_eq") ->
        false

    method negative_lits = fst content

    method positive_lits = snd content

    method is_unit = match content with ([], [_]) -> true | _ -> false

    method lit_at_position (b, n) =
      try
        if b
        then List.nth self#positive_lits n
        else List.nth self#negative_lits n
      with Failure("nth") -> failwith ("lit_at_position : cl = " ^ self#string ^ " n = " ^ (string_of_int n) ^ " b = " ^ (string_of_bool b))

    method subterm_at_position (b, n, p) =
      try
        if b
        then (List.nth self#positive_lits n)#subterm_at_position p
        else (List.nth self#negative_lits n)#subterm_at_position p
      with Failure("nth") -> failwith "subterm_at_position"

    (* Returns all terms featured in the clause *)
    method all_neg_terms =
      let members l = l#both_sides in
      uncouple_list (List.map members self#negative_lits)

    method all_pos_terms =
      let members l = l#both_sides in
      uncouple_list (List.map members self#positive_lits)

    method all_terms =
      let members l = l#both_sides in
      uncouple_list (List.map members self#negative_lits) @ uncouple_list (List.map members self#positive_lits)

    method all_maximal_terms is_total =
      match maximal_terms with 
	  Undefined -> let l = self#all_terms in
		       let greater_f_on_terms = !rpos_greater is_total  in
		       let max_l, _ = list_select_maximal_elements greater_f_on_terms l in
		       let () = maximal_terms <- Defined max_l in
		       max_l
	| Defined l -> l

    method copy = {< >}

    (* Apply function on literals *)
    method apply_to_clause f =
      let n, p = content in
      let n' = List.map f n
      and p' = List.map f p in
      self#build n' p' 

  (* history of a clause : TODO replace a clause with the its number. The clause to be retrieved from a dictionary  *)
    method history = history
    method standby = standby
    method delete_standby = delete_standby
    method sb_string = sb_string
    method sb_newconjs = sb_newconjs
    method sb_IHs = sb_IHs 
    method add_history (el: ((var * term) list * 'a)) = history <- history @ [el]

    method set_history hist = history <-hist

    method set_standby sb = standby <- sb
    method set_delete_standby ds = delete_standby <- ds
    method set_sb_string sbs = sb_string <- sbs
    method set_sb_newconjs sbc = sb_newconjs <- sbc
    method set_sb_IHs ihs = sb_IHs <- ihs

    (* Substitution *)
    method substitute sigma' =
      let sigma = List.map (fun (v, t) -> (v, t#expand_sorts)) sigma' in 
      let subst_s s (l: literal) = l#substitute s in
      self#apply_to_clause (subst_s sigma)

    (* Apply a substitution and rename all variables unconcerned by this substitution *)
    method substitute_and_rename sigma i =
      let () = greatest_var := i in
      let v = List.map fst sigma in
      let () = yy_tmp_param_sorts := [] in

      let myfailwith s =
	let () = buffered_output ("sigma     = " ^ sprint_int_list v) in
	let () = buffered_output ("variables = " ^ sprint_int_list (List.map (fun (x,_,_) -> x) variables)) in
	failwith s in

      let rec fn l l' =
        match l, l' with
          _, [] -> l
        | [], _ -> myfailwith "substitute_and_rename1"
        | (h, s, b)::t, h'::t' ->
            if h < h'
            then (h, s, b)::fn t l'
            else if h = h'
            then fn t t'
            else myfailwith "substitute_and_rename2" in
      let v' = fn variables v in
      let sigma' = generic_merge_sorted_lists sigma (List.map (fun (x, s, is_univ) -> if is_univ then x, new term (Var_univ
	(newvar (), s)) else x, new term (Var_exist (newvar (), s)) ) v') in
      (self#substitute sigma', sigma')

    method replace_subterm_at_pos (b, n, p) st =
      let negs, poss = content
      and replace x = x#replace_subterm_at_pos p st in
      if b
      then
        try
	  let poss' = apply_f_to_element_n replace n poss in
	  self#build negs poss' 
	with (Failure "apply_f_to_element_n") -> failwith "replace_subterm_at_pos"
      else
	try
          let negs' = apply_f_to_element_n replace n negs in
	  self#build negs' poss 
	with (Failure "apply_f_to_element_n") -> failwith "replace_subterm_at_pos"

	  
  (* useless  *)
    method flatten =
      let n, p = content in
      let n' = List.map (fun x -> x#flatten) n
      and p' = List.map (fun x -> x#flatten) p in
      let _ = generic_merge_set_of_lists (List.map (fun x -> x#variables) n')
      and _ = generic_merge_set_of_lists (List.map (fun x -> x#variables) p') in
      {< content = (n', p') ;
        string = Undefined >}

    (* proceed_fun: position -> substitution -> bool -> bool *)
    method subterm_matching proceed_fun (lit: literal) =
      let rec fn b i = function
          [] -> failwith "matching"
        | hd::tl ->
            try
              let new_proceed_fun p s kept_or = proceed_fun (b, i, p) s kept_or in
              let p, s, kept_or = hd#subterm_matching new_proceed_fun lit in
              (b, i, p), s, kept_or
            with (Failure "matching") -> fn b (i + 1) tl in
      let n, p = content in
      try fn false 0 n
      with (Failure "matching") -> fn true 0 p

    method expand_sorts = 
      let ln, lp = content in
      {< content = expand_sorts_list ln, expand_sorts_list lp; string = Undefined>}
	  

    (* proceed_fun: substitution -> bool -> bool *)
    method subterm_matching_at_pos proceed_fun (b, n, p) (lit: literal) =
      let s = self#subterm_at_position (b, n, p) in
      let fn t t' =
        begin
          try
            let new_proceed_fun s = proceed_fun s true in
            let sigma = s#matching new_proceed_fun t in
            sigma, true
          with (Failure "matching") ->
            let new_proceed_fun s = proceed_fun s false in
            let sigma = s#matching new_proceed_fun t' in
            sigma, false
        end
      in
      match lit#content with
          Lit_equal (t, t') -> fn t t'
	| Lit_diff (t, t') -> fn t t'
      	| Lit_rule (t, _) ->
            let new_proceed_fun s = proceed_fun s true in
            let sigma = s#matching new_proceed_fun t in
            sigma, true
	      
    method syntactic_equal (c: 'a) =
      let n, p = content
      and n', p' = c#content in
      try
        List.for_all2 (fun x y -> x#syntactic_equal y) n n'
          &&
        List.for_all2 (fun x y -> x#syntactic_equal y) p p'
      with (Invalid_argument "List.for_all2") -> false

    method add_failed_subsumption i =
      subsumption_failure <- generic_insert_sorted i subsumption_failure

    method subsumption_has_failed i =
      generic_list_sorted_mem i subsumption_failure

    method add_failed_augmentation i =
      augmentation_failure <- generic_insert_sorted i augmentation_failure

    method augmentation_has_failed i =
      generic_list_sorted_mem i augmentation_failure

    method is_boolean =
      let n, p = content in
      List.for_all (fun x -> x#is_boolean) n && List.for_all (fun x -> x#is_boolean) p

    method rename =
      let v' = List.map (fun (x, _, b) -> x, newvar (), b) variables
      and ls = List.map (fun (_, s, _) -> s) variables
      and n, p = content in
      let v = List.map (fun (x, x', _) -> x, x') v' in
      let n' = List.map (fun x -> x#rename_core v) n
      and p' = List.map (fun x -> x#rename_core v) p in
      {< content = (n', p') ;
        variables = List.map2 (fun (_, x', b) s -> (x', s, b)) v' ls;
        string = Undefined ;
        maximal_terms = Undefined >}

    method rename_from_zero :'a =
      let () = greatest_var := 1 in
      self#rename

    method depth =
      let n, p = content in
      let d = List.fold_left max 0 (List.map (fun x -> x#depth) n)
      and d' = List.fold_left max 0 (List.map (fun x -> x#depth) p) in
      max d d'

    (* function proceed is attempted on each horn clause that can be built with one of the positive literals *)
    method try_on_boolean_horn_variants proceed =
      let n, p = content in
      let n1, n2 = List.partition (fun x -> x#is_boolean) n
      and p1, p2 = List.partition (fun x -> x#is_boolean) p in
      let _ = List.map (fun x -> x#revert_boolean) n1
      and p'1 = List.map (fun x -> x#revert_boolean) p1
      in
      match p2 with
        [] ->
          let rec fn i = function
              [] -> false
            | h::t ->
                proceed {< content = (n @ (list_all_but i p'1), [h]) ; maximal_terms = Undefined;
                          string = Undefined >} || fn (i + 1) t
          and fn2 i = function
              [] -> false
            | h::t ->
                proceed {< content = (n2 @ (list_all_but i n1) @ p'1, [h]) ; maximal_terms = Undefined;
                          string = Undefined >} || fn2 (i + 1) t in
          fn 0 p1 || fn2 0 n1
      | [h] -> proceed {< content = (n @ p'1, [h]) ; maximal_terms = Undefined;
			 string = Undefined >}
      | _ -> false

    (* Expand duplicates all negative boolean literals into the positives and vice-versa.
       To be used for the subsumption.
       Beware, a true copy of the clause is not performed. *)
    method expand =
      let n, p = content in
      let n1, _ = List.partition (fun x -> x#is_boolean) n
      and p1, _ = List.partition (fun x -> x#is_boolean) p in
      let n'1 = List.map (fun x -> x#revert_boolean) n1
      and p'1 = List.map (fun x -> x#revert_boolean) p1 in
      {< content = (n @ p'1, p @ n'1)(*  ; string = Defined self#string *) >}

    (* In the contextual rewriting, we try to put as many boolean literals in the contexts preconditions *)
    method build_best_context b n =
      let neg, pos = content in
      let neg', pos' =
        if b
        then (neg, list_all_but n pos)
        else (list_all_but n neg, pos) in
      let p1 = List.filter (fun x -> x#is_boolean) pos' in
      let p'1 = List.map (fun x -> x#revert_boolean) p1 in
      neg' @ p'1

    method is_subterm t =
      let rec fn b i = function
	  [] -> failwith "subterm"
	| hd::tl ->
	    try
	      let p = hd#is_subterm t
	      in (b, i, p)
	    with (Failure "subterm") -> fn b (i + 1) tl in
      let n, p = content in
      try fn false 0 n
      with (Failure "subterm") -> fn true 0 p

    method build (n:Literals.literal list) (p:Literals.literal list) :'a = 
      let v = List.fold_left (fun l l' ->  merge_sorted_lists ( < ) l l') [] (List.map (fun x -> x#variables) n) in
      let v' = List.fold_left (fun l l' ->  merge_sorted_lists ( < ) l l') [] (List.map (fun x -> x#variables) p) in

      let ln = List.length n in
      let lp = List.length p in
      let vars = merge_sorted_lists ( < ) v v' in

      let ih = match p with [_] -> true | _ -> false in
      {< content = (n, p) ;
	peano_context = Undefined ; 
        variables = vars ;
        number = new_clause_number () ;
        subsumption_failure = [] ;
        augmentation_failure = [] ;
        inference_bitstream = 0 ;
        neg_card = ln ;
        pos_card = lp ;
        card = ln + lp ;
        is_horn = ih ;
        string = Undefined ; 
	maximal_terms = Undefined;
	oriented = Undefined;
      >}

  end

(* let build n p = new  clause (n, p) *)

let all_nonvariable_symbols c = 
  let rec fn t = 
    match t#content with
	Var_exist _ | Var_univ _ -> []
      | Term (f, l, _) -> 
	  let ldef_symb = List.fold_left (fun x y -> merge_sorted_lists ( < ) x (fn y)) [] l  in 
	  if List.mem f ldef_symb then ldef_symb else insert_sorted ( = ) ( < ) f  ldef_symb
  in
  let fn1 lit = 
    match lit#content with
	Lit_rule (t1, t2) -> merge_sorted_lists ( < ) (fn t1) (fn t2)
      | Lit_equal (t1, t2) -> merge_sorted_lists ( < ) (fn t1) (fn t2)
      | Lit_diff (t1, t2) -> merge_sorted_lists ( < ) (fn t1) (fn t2)
  in
  let ln, lp = c#content in
  List.fold_right (fun x y -> merge_sorted_lists ( < ) (fn1 x)  y) (ln @ lp) []


(* Takes a clause. Checks whether it is a Horn clause, and tries to orient it *)
let orient_clause c =
  try c#orient with
      Failure "orient" -> failwith "orient"
(*   let negs, poss = c#content in *)
(*   match poss with *)
(*     [h] -> (new clause (negs, poss))#orient *)
(*   | _ -> failwith "orient" *)

let try_to_orient_clause c = try orient_clause c with (Failure "orient") -> c

let print_clause_list l = buffered_output (sprint_list "\n" (fun x -> "\t" ^ x#string) l)

(* Type describing systems to be visited in some inference rules *)
type which_system = C | R | L

let sprint_which_system_list = sprint_list "|" (function C -> "C" | R -> "R" | L -> "L")
let sprint_which_rw_system_list = sprint_list "&" (function C -> "C" | R -> "R" | L -> "L")

(* Sufficient completeness for a horn clauses system *)
let check_sufficient_completeness s =
  let b = ref true in
  let fn c =
    let lhs = c#lefthand_side in
    b := !b && lhs#has_constructor_arguments in
  s#iter fn

(* List of systems (los) *)
type list_of_systems_argument =
    LOS_defined of which_system list
  | LOS_query

let sprint_which_system_list_arg = function
    LOS_defined los -> sprint_which_system_list los
  | LOS_query -> "?"

let sprint_which_rw_system_list_arg = function
    LOS_defined los -> sprint_which_rw_system_list los
  | LOS_query -> "?"


(* The four main sets of clauses *)
let hypotheses_system = new system []
let conjectures_system = new system []
let rewrite_system = new rw_system []
let lemmas_system = new l_system []
let real_conjectures_system = ref [] ;;

let complete_lemmas_system = new l_system []
let all_conjectures_system = new system []

let coq_formulas = ref [] ;;

let coq_all_lemmas = ref [] ;;

let coq_formulas_with_infos = ref [];;

let coq_less_clauses  = ref [];;

let coq_spec_lemmas  = ref [];;

let coq_main_lemma = ref "";;

let main_lemma_proof = ref "";;

let coq_induction_schemas = ref "";;

let coq_generate_cond = ref [];;

let rewriting_clauses = ref [] ;;

let coq_replacing_clauses = ref [] ;;
 
let sprint_lemmas () =
  sprint_list "\n" (fun x -> x#string) lemmas_system#content

let sprint_axioms () =
  sprint_list "\n" (fun x -> x#string) rewrite_system#content

let sprint_goals () =
  sprint_list "\n" (fun x -> x#string) conjectures_system#content

let sprint_hypotheses () =
  sprint_list "\n" (fun x -> x#string) hypotheses_system#content

let proof_found () = conjectures_system#is_empty

(* Update the dictionary of free constructors.
   We all set them to true, then visit the system. *)
let update_dico_free_constructors () =
  let fn f _ =
    if is_constructor f
    then
      dico_free_constructors#add f true
    else
      ()
  and fn2 c =
    let lhs = c#lefthand_side in
    try
      let f = lhs#head in
      if is_constructor f
      then
        let () = dico_free_constructors#add f false in
        free_constructors := false
      else ()
    with (Failure "head") -> () in
  let () = dico_const_string#iter fn in
  List.iter fn2 rewrite_system#content

let is_free_constructor (f: const) = (f >= 0)

(* sufficient_completeness_test *)
let sufficient_completeness_test () =
  buffered_output "Sufficient completeness test not yet implemented"

(* strongly_sufficient_completeness_test *)
let strongly_sufficient_completeness_test () =
  buffered_output "Strongly sufficient completeness test not yet implemented"

(* ground_convergence_test *)
let ground_convergence_test () =
  buffered_output "Ground convergence test not yet implemented"


let preprocess_conjecture c = 
  let peano_sort = if !nat_specif_defined then id_sort_nat else
    id_sort_int in
  let rec fn c = (* replaces c with conjectures without 'minus_nat'
		    symbols *)
    let fn1 t = (difference (=) t#all_positions t#variable_positions) in
    let all_subterms_c = List.flatten (List.map (fun x -> List.map (fun y ->
      x#subterm_at_position y) (fn1 x)) c#all_terms) in
    let terms_minus, _ = List.partition (fun x -> match x#content with 
	Var_univ _ | Var_exist _ -> false | Term (id, _, _) -> id = id_symbol_minus_nat) all_subterms_c in
    if terms_minus = [] then [c]
    else (* build the two new conjectures *)
      let trm = List.hd terms_minus in
      let pos = c#is_subterm trm in
      let l,r = match trm#content with Term(_,[l';r'],_) -> l',r' 
	| Term(_, [], _)| Term(_, [_],_)|Term(_,_::_::_::_,_)|Var_univ _| Var_exist _ ->  failwith "preprocess_conjectures"
      in 
      let l_geq_r = new literal (Lit_equal ((new term (Term (id_symbol_geq, [l;r], id_sort_bool))), term_true)) in
      let l_less_r = new literal (Lit_equal ((new term (Term (id_symbol_less, [l;r], id_sort_bool))), term_true)) in
      let trm_minus = new term (Term (id_symbol_minus, [l;r], peano_sort)) in
      let trm_zero = new term (Term (id_symbol_zero, [], peano_sort)) in
      let ln,lp = c#content in 
      let c1 = (c#build (ln @ [l_geq_r]) lp)#replace_subterm_at_pos pos trm_minus in
      let c2 = (c#build (ln @ [l_less_r]) lp)#replace_subterm_at_pos pos trm_zero in
      List.flatten [(fn c1);(fn c2)]
  in
  if !nat_specif_defined then (* for naturals *)
    let new_l = fn c in
    let () = if List.length new_l <> 1 || (List.length new_l > 1 && not(c#syntactic_equal (List.hd new_l))) then 
      begin
	buffered_output ("\nThe conjecture \n" ^ "      " ^ c#string ^ "\n    has been preprocessed to:\n"); 
    	List.iter (fun x -> buffered_output x#string)
	  new_l;
	flush stdout
      end
    else ()
    in 
    new_l
  else (* for integers *)
    [c]

let recursive_new_hyps c_ref r_conj (cxt1, cxt2) = 
  if List.for_all (fun x -> clause_greater false false c_ref x) r_conj
  then cxt1
  else if  List.for_all (fun x -> clause_geq false false c_ref x) r_conj
  then cxt1 @ cxt2
  else []
 


  (* variables to be instantiated for debugging purposes  *)

(* let cl1 = ref (new clause ([],[]) [] ("",c)) *)
(* let cl2 = ref (new clause ([],[]) [] ("",c)) *)

let print_detailed_clause c = 
  let () = print_string ("\nDetailing clause " ^ (string_of_int c#number)) in

  let () = buffered_output ("\t where the list yy_tmp_param_sorts is : " ^
  (List.fold_right (fun (x, s) y -> (x ^ " has associated the sort " ^ (sprint_sort s) ^ ", " ^ y)) !yy_tmp_param_sorts ""))  in


  let ln, lp = c#content in
  let tmp = !maximal_output in
  let () = maximal_output := true in (* to print the detailed terms *)
  let () = 
    for i = 0 to (List.length ln) - 1 do
      let t0 = c#subterm_at_position (false, i, [0]) in
      let t1 = c#subterm_at_position (false, i, [1]) in
      let () = print_string ("\n\n The term " ^ t0#string ^ " is detailed as follows: \n\n") in
      let () = print_detailed_term t0 in
      let () = print_string ("\n\n The term " ^ t1#string ^ " is detailed as follows: \n\n") in
      let () = print_detailed_term t1 in
      () 
    done 
  in 
  let () = 
    for i = 0 to (List.length lp) - 1 do
      let t0 = c#subterm_at_position (true, i, [0]) in
      let t1 = c#subterm_at_position (true, i, [1]) in
      let () = print_string ("\n\n The term " ^ t0#string ^ " is detailed as follows: \n\n") in
      let () = print_detailed_term t0 in
      let () = print_string ("\n\n The term " ^ t1#string ^ " is detailed as follows: \n\n") in
      let () = print_detailed_term t1 in
      () 
    done 
  in
  let () = maximal_output := tmp in (* restore the flag *)
  ()

let print_detailed_position_clause c = 
  let () = buffered_output ("\nDetailing the positions of clause " ^ (string_of_int c#number)) in

  let ln, lp = c#content in
  let tmp = !maximal_output in
  let () = maximal_output := true in (* to print the detailed terms *)
  (* the string to be tested  *)
  let () = 
    for i = 0 to (List.length ln) - 1 do
      let t0 = c#subterm_at_position (false, i, [0]) in
      let t1 = c#subterm_at_position (false, i, [1]) in
      let () = buffered_output ("\n\n" ^ t0#string ^ " has the following positions: \n\n") in
      let () = print_detailed_position_term t0 in
      let () = buffered_output ("\n\n" ^  t1#string ^ " has the following positions: \n\n") in
      let () = print_detailed_position_term t1 in
      () 
    done 
  in 
  let () = 
    for i = 0 to (List.length lp) - 1 do
      let t0 = c#subterm_at_position (true, i, [0]) in
      let t1 = c#subterm_at_position (true, i, [1]) in
      let () = buffered_output ("\n\n" ^ t0#string ^ " has the following positions: \n\n") in
      let () = print_detailed_position_term t0 in
      let () =  buffered_output ("\n\n" ^  t1#string ^ " has the following positions: \n\n") in
      let () =  print_detailed_position_term t1 in
      () 
    done 
  in
  let () = maximal_output := tmp in (* restore the flag *)
  ()

let all_defined_positions c_v = 
  let nlits, plits = c_v in 
  let i = ref (-1) in
  let f lit b n = 
    match lit#content with
	Lit_rule  (t1, t2) -> [((b, n, [0]), t1#defined_positions); ((b, n, [1]), t2#defined_positions)]
      | Lit_equal (t1, t2) -> [((b, n, [0]), t1#defined_positions); ((b, n, [1]), t2#defined_positions)]
      | Lit_diff  (t1, t2) -> [((b, n, [0]), t1#defined_positions); ((b, n, [1]), t2#defined_positions)]
  in
  let neg_pos = (List.map (fun l -> i := !i + 1; f l false !i) nlits) in
  let () = i := -1 in
  let poz_pos = (List.map (fun l -> i := !i + 1; f l true !i) plits) in
  List.filter (fun (_, l) -> l <> []) (List.flatten (neg_pos @ poz_pos))
    

let sprint_clausal_position (b, n, p) = (string_of_bool b) ^ "/" ^ (string_of_int (n + 1)) ^ "/[" ^ (sprint_position p) ^ "]"

let initial_conjectures = ref ([]: (peano_context clause) list);;

let write_pos_clause  c  = 
  let fn b i (lhs, rhs) = 
    [(b, i, [1]), (rhs#pos_rewriting, rhs#pos_partial_case_rewriting, rhs#pos_total_case_rewriting)] @
    [(b, i, [0]), (lhs#pos_rewriting, lhs#pos_partial_case_rewriting, lhs#pos_total_case_rewriting)] 
  in

  let n, p = c#content in
  let i = ref (-1) in
  let pos = List.fold_left (fun l lit -> i := !i + 1; (fn false !i lit#both_sides) @ l) [] n in
  let i = ref (-1) in
  let pos' = List.fold_left (fun l lit -> i := !i + 1; (fn true !i lit#both_sides) @ l) pos p in

  let fn' ((b, n, t), lp) = List.fold_left (fun str p -> str ^ " " ^ (sprint_clausal_position (b, n, (t @ p)))) " " lp  in
  let () = buffered_output ("\n\nThe positions of " ^ c#string ) in
(*   let () =  print_string ((List.fold_left (fun str x -> str ^  "  " ^ (fn' x )) "\n Contextual Rewriting\n" *)
(*     c#pos_contextual_rewriting) ^ " \n\n") in  *)
  let () = buffered_output ((List.fold_right (fun  (p, (pos, _, _)) str -> str ^  "  " ^ (fn' (p, pos) )) pos' "\n\nConditional Rewriting\n" ) ^ " \n") in 
  let () = buffered_output ((List.fold_right (fun  (p, (_, pos, _)) str -> str ^  "  " ^ (fn' (p, pos) )) pos' "\n\nPartial Case Rewriting\n" ) ^ " \n") in 
  let () = buffered_output ((List.fold_right (fun  (p, (_, _, pos)) str -> str ^  "  " ^ (fn' (p, pos) )) pos' "\n\nTotal Case Rewriting\n") ^ " \n") in
(*   let () = print_string ((List.fold_left (fun str x -> str ^  "  " ^ (fn' x )) "\n Equational Rewriting\n" *)
(*     c#pos_equational_rewriting) ^ " \n\n") in *)
  ()

let write_pos_term_clause  c  = 

  let fn b i (lhs, rhs) = 
    [(b, i, [1]), (rhs#pos_rewriting, rhs#pos_partial_case_rewriting, rhs#pos_total_case_rewriting)] @
    [(b, i, [0]), (lhs#pos_rewriting, lhs#pos_partial_case_rewriting, lhs#pos_total_case_rewriting)] 
  in

  let n, p = c#content in
  let i = ref (-1) in
  let pos = List.fold_left (fun l lit -> i := !i + 1; (fn false !i lit#both_sides) @ l) [] n in
  let i = ref (-1) in
  let pos' = List.fold_left (fun l lit -> i := !i + 1; (fn true !i lit#both_sides) @ l) pos p in

  let fn' ((b, n, t), lp) = List.fold_left (fun str p -> str ^ "\n\t The term at " ^ (sprint_clausal_position (b, n, (t @ p))) ^ " is " ^ (c#subterm_at_position (b, n, (t @ p)))#string) " " lp  in
   let () = if !maximal_output then buffered_output ((List.fold_right (fun  (p, (_, _, pos)) str -> str ^  "  " ^ (fn' (p, pos) ))
     pos' ("\n\nThe terms and positions for "^ c#string))  ^ " \n") in
  ()

(* Existence test, with a predicate using the number of the element *)
let list_exists_w_number p =
  let rec fn i =
    function
      [] -> false
    | h :: t -> 		      
(* 	let _ = if !maximal_output then buffered_output ("\n TREATING the clause " ^ h#string); flush stdout  in *)
(* 	let () = write_pos_clause h in  *)
	let test = p i h in
	test || fn (i + 1) t
  in
  fn 0
;;

let rec expand_nullary lt  = 
  (* fn expands the variables with sorts having only one constructor (since they are not recursive)  *)
  let fn i s = 
    let res = ref [] in
    let () = dico_const_profile#iter 
      (fun x profile -> 
	let s' = List.hd profile in 
	if is_constructor x then 
	  let () = yy_tmp_param_sorts := [] in
	  if equal_sorts s s' then
	    if List.length !res <> 0 then failwith "fn"
	    else res := (x, List.map (fun x -> expand_sorts x) profile) :: !res 
	  else ()
	else ()
      )
    in
    if !res = [] then failwith ("expand_nullary: failure finding constructors for sort " ^ (sprint_sort s)) (* it should be at least one constructor *)
    else 
      let id_x, profile_x = List.hd !res in
      let _ = List.hd profile_x in
      let lvar = List.map (fun s -> new term (Var_univ (newvar (), s))) (List.tl profile_x) in
      let trm = new term (Term (id_x, lvar, s)) in
      trm, [(i, trm)]
  in
  match lt with
      [] -> []
    | t :: tl -> 
	(
	  match t#content with
	      Var_exist (_, _) -> failwith "expand_nullary" 
	    | Var_univ  (i, s) -> 

		if is_nullary_sort s then 
		  let l = try List.filter is_constructor (dico_const_profile#find_keys [s]) with Not_found -> [] in
		  (List.map (fun x -> let trm = new term (Term (x, [], s)) in (trm, [i, trm])) l) @ (expand_nullary tl )
		else 
		let exp_tl = expand_nullary tl  in
		(try (fn i s) :: exp_tl  with Failure "fn" -> (t, []) :: exp_tl)
	    |  Term (i, l, s) -> 

		 let expanded_args =  megamix ((List.map (fun x -> expand_nullary [x] ) l)) in 
		 let expanded_t = 
		   if expanded_args <> [] then 
		     let fn l' = 
		       let l'' = List.map fst l' in 
		       let sigma = List.flatten (List.map snd l') in
		       (new term (Term (i, l'', s))), sigma
		     in
		     List.map fn expanded_args
		   else [(t, [])] 
		 in
		 expanded_t @ (expand_nullary tl )
	)		 

let counterexample fn_norm c =
  let lvar_c = List.fold_right (fun (i,s,b) l -> if b = true then (new term (Var_univ (i, s))) :: l else l) c#variables [] in
  
  (* expand the nullary variables from c *)
  let lvar_expand = if !exclude_nullary_mode then List.map (fun v -> (v, [])) lvar_c else expand_nullary lvar_c in
  let lvar' = List.flatten (List.map snd lvar_expand) in
  let c' = c#substitute lvar' in
  let lvar_c' = List.filter (fun (_,_,b) -> b = true) c'#variables in
  (* computes the ground constructors of sort s *)
  let rec fn (i,s) accept_recursivity iter = 
(*     let () = buffered_output ("BEFORE recursivity = " ^ (string_of_bool accept_recursivity) ^ " in iteration " ^ (string_of_int *)
(*       iter) ^ ": The variable u" ^ (if is_abstract s then "a" else "") ^ (string_of_int i) ^ " of sort " ^ (sprint_sort s) ^ " is instantiated by:\n\n") in *)
    let res = ref [] in
    let () = 
      dico_const_profile#iter 
	(fun x profile ->
	  let s' = List.hd profile in 
	  if is_constructor x && (equal_sorts s s') then
	    (* should be a constant of sort s  *)
	    if ((List.length profile) = 1) then 
	      let () = yy_tmp_param_sorts := [] in
	      res := (new term (Term(x, [], s))):: !res 
	      else if accept_recursivity then
		let largs = megamix (List.map (fun sort -> fn (i,sort) false (iter + 1)) (List.tl profile)) in
		let l_terms = List.map (fun args -> let () = yy_tmp_param_sorts := [] in new term (Term (x, args, s))) largs in
		res := l_terms @ !res
	      else ()
	  else ()
	)
    in
(*     let () = List.iter (fun t -> buffered_output ("iteration = " ^ (string_of_int iter) ^ "    term = " ^ t#string ^ "\n")) !res in *)
    if !res = [] then
      let () = buffered_output ("\nPlease provide a ground instance of the variable u" ^ (if is_abstract s then "a" else "") ^
      (string_of_int i) ^ " of sort " ^ (sprint_sort s) ^ " !!!" ) in
      let () = yy_tmp_param_sorts := [] in
      [new term (Var_univ(i, s))] 
    else
      !res
  in
  let lground_s = megamix (
    List.map (fun (i,s,_) -> 
		let ltconstr = fn (i, s) true 0 in 
(* 		let () = buffered_output ("AFTER: The variable u" ^ (if is_abstract s then "a" else "") ^ (string_of_int i) ^ " is instantiated by:\n\n") in *)
(* 		let () = List.iter (fun t -> buffered_output ("    term = " ^ t#string ^ "\n")) ltconstr in *)
		  List.map (fun tc -> (i, tc)) ltconstr) lvar_c'
  ) 
  in 


  (* reduces by normalization the literal and tests it with the boolean value  *)
  let fn_litred lit value = 
    match lit#content with
	Lit_equal (x,y) | Lit_rule (x,y) -> 
	  let _, _, x_norm, _ = fn_norm [R;L] x c "" ([],[]) 0 in
	  let _, _, y_norm, _ = fn_norm [R;L] y c "" ([],[]) 0 in
	  let res = x_norm#equal y_norm in 
	  res = value
      | Lit_diff (x,y) -> 
	  let _, _, x_norm, _ = fn_norm [R;L] x c "" ([],[]) 0 in
	  let _, _, y_norm, _ = fn_norm [R;L] y c "" ([],[]) 0 in
	  let res = x_norm#equal y_norm in 
	  res <> value
  in
  
  (* tests if a ground clause is false  *)
  let fn_false cl = 
    let ln, lp = cl#content in
    (List.for_all (fun lit -> fn_litred lit true) ln) &&
    (List.for_all (fun lit -> fn_litred lit false) lp)
  in
  let res = ref [] in
  let nr_tests = 10 in
  let nr_subst = List.length lground_s in
  let str_total = "Checking for counterexample " ^ (string_of_int nr_subst) ^ " substitutions :\n" in
  let str_partial =  "Checking for counterexample only " ^ (string_of_int nr_tests) ^ " out of " ^ (string_of_int nr_subst) ^ " substitutions :\n" in
  let () = buffered_output (if nr_tests > nr_subst then str_total else str_partial) in
  let rec fn_test iter l =
    match l with  
	[] -> ()
      | s :: tl -> 
	  let () = buffered_output ("\n substitution : " ^ (sprint_subst s)) in
	  let cs = c#substitute s in 
	  let () = if fn_false cs then res := cs :: !res in
            if iter < nr_tests then fn_test (iter + 1) tl 
  in  
  let () = fn_test 1 lground_s in
    if !res = [] then failwith "counterexample" 
    else List.hd !res
      
let clause_ground_instance c =
  let lvar_c = List.fold_right (fun (i,s,b) l -> if b = true then (new term (Var_univ (i, s))) :: l else l) c#variables [] in

  (* expand the nullary variables from c *)
  let lvar_expand = if !exclude_nullary_mode then List.map (fun v -> (v, [])) lvar_c else expand_nullary lvar_c in
  let lvar' = List.flatten (List.map snd lvar_expand) in
  let c' = c#substitute lvar' in

  let lvar_c' = List.filter (fun (_,_,b) -> b = true) c'#variables in
  (* fn computes the ground nullary constructor of sort s *)
  let fn (i,s) = 
    let res = ref [] in
    try
      let () = 
	dico_const_profile#iter 
	  (fun x profile -> 
	    let s' = List.hd profile in 
	    if is_constructor x && ((List.length profile) = 1) then 
	      let () = yy_tmp_param_sorts := [] in
	      if equal_sorts s s' then
		let () = res := [new term (Term(x, [], s))] in
		failwith "found"
	      else ()
	    else ()
	  )
      in
      let () = buffered_output ("\nPlease provide a ground instance of the variable u" ^ (if is_abstract s then "a" else "") ^
      (string_of_int i) ^ " of sort " ^ (sprint_sort s) ^ " !!!" ) in
      let () = res := [new term (Var_univ(i, s))] in
      failwith "found"
    with Failure "found" ->  List.hd !res
  in
  let ground_s = List.map (fun (i,s,_) -> let constr = fn (i, s) in (i, constr)) lvar_c' in 

  let res = c'#substitute ground_s in
  res


let print_history fn_norm c show_ctx= 
  let rec fn l c_rez= match l with
      [] -> c_rez
    | (subst, cl) :: tl -> 
	let () = print_string ("\n\n" ^ (sprint_subst subst) ^ " \n \t on " ^ cl#string) in
	let c' = c_rez#substitute subst in
	fn tl c'
  in 
  let br_symb, cl_number, _ = c#get_broken_info in 
  let () = if br_symb <> "" then buffered_output ("\nThe broken functional symbol for [" ^ (string_of_int c#number) ^ "] is " ^ br_symb ^ " and the number of the clause where the break happened is [ " ^ (string_of_int cl_number) ^ " ] \n") in
  let () = print_string ("\n The history of " ^ c#string) in
  try 
    let (_, c_orig) = List.hd c#history in
    (* computing an instance  *)
    let c_inst = fn c#history c_orig in
    let () = buffered_output ("\n\n The corresponding instance is \n\t" ^ c_inst#string) in
    (* computing a ground instance  *)
      if show_ctx then 
	let c_ginst = 
	  (try 
	     let cxp = counterexample fn_norm c_inst in 
	     let () = buffered_output ("\n\n One of its counterexamples is  \n\t" ^ cxp#string) in
	       cxp
	   with Failure "counterexample" -> 
	     let () = buffered_output "\n\n Preparing a ground instance ...\n" in
	     let cinst = clause_ground_instance c_inst in
	     let () = buffered_output ("\n\n One of such instance is \n\t" ^ cinst#string) in
	       cinst) 
	in
	let () = print_detailed_clause c_ginst in
	  () 
  with Failure "hd" -> ()

let print_history_instance c = 
  let rec fn l c_rez= match l with
      [] -> c_rez
    | (subst, cl) :: tl -> 
	let () = print_string ("\n\n" ^ (sprint_subst subst) ^ " \n \t on " ^ cl#string) in
	let c' = c_rez#substitute subst in
	fn tl c'
  in 
  let () = print_string ("\n The history of " ^ c#string) in
  try 
    let (_, c_orig) = List.hd c#history in
  (* computing an instance  *)
    let c_inst = fn c#history c_orig in
    let () = buffered_output ("\n\n The corresponding instance is \n\t" ^ c_inst#string) in
    () 
  with Failure "hd" -> ()


let compute_string_clause_caml c = 
      (let l, r = c#content
      and f x = compute_string_literal_caml x in
      match l, r with
        [], [] -> "[]"
      | [], _ -> sprint_list " \\/ " f r
      | _, [] -> (sprint_list " /\\ " f l) ^ " => "
      | _ -> (sprint_list " /\\ " f l) ^ " => " ^ (sprint_list " \\/ " f r))
      ^ " ;"

let oracle_g = ref (fun (_: peano_context clause) (_: peano_literal list) -> peano_literal_tautology)

(* Convert a symbolic system list to its concrete representation as a horn clause list *)
 let concrete_system_list l (cxt1, cxt2) = 
   let fn = function 
       L -> List.map (fun x -> ("L", x)) lemmas_system#content 
     | R -> List.map (fun x -> ("R", x)) rewrite_system#content 
     | C -> (List.map (fun x -> ("C2", x)) cxt2 ) @ (List.map (fun x -> ("C1", x)) cxt1 ) 
   in 
  List.fold_left (@) [] (List.map fn l) 

