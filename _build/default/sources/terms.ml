(*
  * Project: Spike ver 0.1
 * File: terms.ml
 * Content: terms definitions
 *)
  
open Values
open Diverse
open Io
open Dicos
open Symbols
  
(* Concrete representation of a term *)
type 'a concrete_term =
    Var_exist of var * sort
  | Var_univ of var * sort
  | Term of const * 'a list * sort

let compute_depth = function
    [] -> 1
  | l ->
      let l'  = List.map (fun x -> x#depth) l in
      1 + generic_list_max l'

let get_sort t = match t with
    Var_exist (_, s) | Var_univ (_, s) | Term (_, _, s) -> s

let is_existential_var v = 
  match v#content with
      Var_exist (_, _) -> true
    | Var_univ _ | Term _ -> false   

let is_universal_var v = 
  match v#content with
      Var_univ (_, _) -> true
    | Var_exist _ | Term _ -> false   

let all_defined_positions c_t = 
  let rec fn2 i = function
      [] -> []
    | h::t -> (List.map (fun l -> i::l) h#defined_positions) @ (fn2 (i + 1) t) in
  match c_t with
      Var_exist _ | Var_univ _ -> []
    | Term (f, l, _) -> if is_defined f then [] :: (fn2 0 l) else (fn2 0 l)
				


class term c_t' =
  (* flattening is compulsory *)
  let c_t = match c_t' with
      Var_exist _ | Var_univ _ -> c_t'
    | Term (f, l, s) ->
	let  get_ac_f_args f t =  
	  match t#content with
	      Var_exist _ | Var_univ _ -> [t]
	    | Term (f', l', _)  -> 
		if const_equal f f' then (List.flatten (List.map (fun x -> x#get_ac_f_args f) l'))
		else [t]
	in
	if symbol_is_ac f
	then
          let l' = List.flatten (List.map (get_ac_f_args f) l) in
          let lflatten = List.map (fun x -> x#flatten) l' in
          Term (f, lflatten, s)
	else
          let l' = List.map (fun x -> x#flatten) l in
          Term (f, l', s)
  in
  object (self: 'a)
      
    inherit generic
    inherit printable_object

    (* Contents *)
    val content = c_t
	
    val variables =
      match c_t with
          Var_exist (x, s) -> [(x, s, false)] | Var_univ (x, s) -> [(x, s, true)]
	| Term (_, l, _) -> generic_merge_set_of_lists (List.map (fun x -> x#variables) l)
	    
    val depth =
      match c_t with
          Var_univ _ | Var_exist _ -> 1
	| Term (_, l, _) -> compute_depth l
          
    val mutable pos_rewriting  = []
    val mutable pos_contextual_rewriting   = []
    val mutable pos_partial_case_rewriting = []
    val mutable pos_total_case_rewriting   = []
    val mutable pos_equational_rewriting   =(*  [] *)(all_defined_positions c_t) (* just for testing *)

    (* Accessors *)
    method content = content
	
    method variables = variables
	
    method copy = {< >}

    method pos_rewriting  = pos_rewriting
    method pos_contextual_rewriting   = pos_contextual_rewriting
    method pos_partial_case_rewriting = pos_partial_case_rewriting
    method pos_total_case_rewriting   = pos_total_case_rewriting
    method pos_equational_rewriting   = pos_equational_rewriting
    method resetpos_rewriting  = 
      let () = buffered_output ("\nReset pos_rewriting in " ^ self#string) in
      let () = 
	match content with 
	    Term (_, l, _) -> List.iter (fun x -> x#resetpos_rewriting) l
	  | Var_exist _ | Var_univ _ -> ()
      in
      pos_rewriting <- []

    method resetpos_contextual_rewriting = 
      let () = 
	match content with 
	    Term (_, l, _) -> List.iter (fun x -> x#resetpos_contextual_rewriting) l
	  | Var_exist _ | Var_univ _ -> ()
      in
      pos_contextual_rewriting <- []

    method resetpos_partial_case_rewriting  = 
      let () = 
	match content with 
	    Term (_, l, _) -> List.iter (fun x -> x#resetpos_partial_case_rewriting) l
	  | Var_exist _ | Var_univ _ -> ()
      in
      pos_partial_case_rewriting <- []

    method resetpos_total_case_rewriting  = 
      let () = 
	match content with 
	    Term (_, l, _) -> List.iter (fun x -> x#resetpos_total_case_rewriting) l
	  | Var_exist _ | Var_univ _ -> ()
      in
       pos_total_case_rewriting <- []

    method resetpos_equational_rewriting  = 
      let () = 
	match content with 
	    Term (_, l, _) -> List.iter (fun x -> x#resetpos_equational_rewriting) l
	  | Var_exist _ | Var_univ _ -> ()
      in
      pos_equational_rewriting <- []


    method delpos_rewriting pos  =
      let lpos = self#pos_rewriting in
(*       let () = buffered_output ("\n cond_rew: Eliminating " ^ (sprint_position pos) ^ " from " ^ self#string ^ " having positions : ") in *)
(*       let () = List.iter (fun x -> buffered_output (" " ^ (sprint_position x))) lpos in *)
      let lpos' = 
	try 
	  remove_el (=) pos lpos 
	with Failure "remove_el" -> 
	  let () = if !maximal_output then  buffered_output ("WARNING: " ^ ("delpos_rewriting on " ^ self#string ^ " at position " ^ (sprint_position pos))) in
	  try 
	    remove_el (=) pos self#all_positions 
	  with Failure "remove_el" -> failwith ("delpos_rewriting on " ^ self#string ^ " at position " ^ (sprint_position pos))  in
      let () = pos_rewriting <- lpos' in

      (* eliminating the positions from subterms   *)
      if pos <> [] then 
	(match content with
	    Term (_, l, _) -> 
	      let n = List.hd pos in
	      let pos' = List.tl pos in
	      let t = List.nth l n in
	      let () = t#delpos_rewriting pos' in
	      ()
	  | Var_exist _ | Var_univ _ -> failwith "delpos_rewriting"
	)

    method delpos_partial_case_rewriting pos  =
      let lpos = self#pos_partial_case_rewriting in
(*       let () = buffered_output ("\n part_case : Eliminating " ^ (sprint_position pos) ^ " from " ^ self#string ^ " having positions : ") in *)
(*       let () = List.iter (fun x -> buffered_output (" " ^ (sprint_position x))) lpos in *)
      let lpos' = try remove_el (=) pos lpos with Failure "remove_el" -> failwith "delpos_partial_case_rewriting" in
      let () = pos_partial_case_rewriting <- lpos' in

      (* eliminating the positions from subterms   *)
      if pos <> [] then 
	(match content with
	    Term (_, l, _) -> 
	      let n = List.hd pos in
	      let pos' = List.tl pos in
	      let t = List.nth l n in
	      let () = t#delpos_partial_case_rewriting pos' in
	      ()
	  | Var_exist _ | Var_univ _ -> failwith "delpos_partial_case_rewriting"
	)

    method delpos_contextual_rewriting pos  =
      let lpos = self#pos_contextual_rewriting in
(*       let () = buffered_output ("\n context_rewr:  Eliminating " ^ (sprint_position pos) ^ " from " ^ self#string ^ " having positions : ") in *)
(*       let () = List.iter (fun x -> buffered_output (" " ^ (sprint_position x))) lpos in *)
      let lpos' = try remove_el (=) pos lpos with Failure "remove_el" -> failwith "delpos_contextual_rewriting" in
      let () = pos_contextual_rewriting <- lpos' in

      (* eliminating the positions from subterms   *)
      if pos <> [] then 
	(match content with
	    Term (_, l, _) -> 
	      let n = List.hd pos in
	      let pos' = List.tl pos in
	      let t = List.nth l n in
	      let () = t#delpos_contextual_rewriting pos' in
	      ()
	  | Var_exist _ | Var_univ _ -> failwith "delpos_contextual_rewriting"
	)

    method delpos_total_case_rewriting pos  =
      let lpos = self#pos_total_case_rewriting in
(*       let () = buffered_output ("\n total case : Eliminating " ^ (sprint_position pos) ^ " from " ^ self#string ^ " having positions : ") in *)
(*       let () = List.iter (fun x -> buffered_output (" " ^ (sprint_position x))) lpos in *)
      let lpos' = try remove_el (=) pos lpos with Failure "remove_el" -> failwith "delpos_total_case_rewriting" in
      let () = pos_total_case_rewriting <- lpos' in

      (* eliminating the positions from subterms   *)
      if pos <> [] then 
	(match content with
	    Term (_, l, _) -> 
	      let n = List.hd pos in
	      let pos' = List.tl pos in
	      let t = List.nth l n in
	      let () = t#delpos_total_case_rewriting pos' in
	      ()
	  | Var_exist _ | Var_univ _ -> failwith "delpos_total_case_rewriting"
	)

    method delpos_equational_rewriting pos  =
      let lpos = self#pos_equational_rewriting in
(*       let () = buffered_output ("\n equational rew: Eliminating " ^ (sprint_position pos) ^ " from " ^ self#string ^ " having positions : ") in *)
(*       let () = List.iter (fun x -> buffered_output (" " ^ (sprint_position x))) lpos in *)
      let lpos' = try remove_el (=) pos lpos with Failure "remove_el" -> failwith "delpos_equational_rewriting" in
      let () = pos_equational_rewriting <- lpos' in

      (* eliminating the positions from subterms   *)
      if pos <> [] then 
	(match content with
	    Term (_, l, _) -> 
	      let n = List.hd pos in
	      let pos' = List.tl pos in
	      let t = List.nth l n in
	      let () = t#delpos_equational_rewriting pos' in
	      ()
	  | Var_exist _ | Var_univ _ -> failwith "delpos_equational_rewriting"
	)

    (* Depth of tree *)
    method depth = depth
	

    method expand_sorts = 
      match content with
	  Var_exist (x, s) -> let s' = expand_sorts s in {< content = Var_exist (x, s'); variables = [(x, s', false)]; string =
	    Undefined  >}
	| Var_univ (x, s) -> let s' = expand_sorts s in {< content = Var_univ (x, s'); variables = [(x, s', true)]; string =
	    Undefined >}
	| Term (i, l, s) -> let l' = List.map (fun x -> x#expand_sorts) l in
			    let v = generic_merge_set_of_lists (List.map (fun x -> x#variables) l') in
			    {< content = Term (i, l', expand_sorts s); variables = v; string = Undefined>}

			    
  (* if full then the positions to be tested will be  all the defined positions  *)
    method update_pos = 
      match content with
	  Term (k, l, s) -> 
	    let allpos =  all_defined_positions content in
	    let l' = List.map (fun x -> x#update_pos) l in 
	    let () = pos_rewriting <-  allpos  in
	    let () = pos_contextual_rewriting <-  allpos in
	    let () = pos_partial_case_rewriting <- allpos in
	    let () = pos_total_case_rewriting <-  allpos in
	    let () = pos_equational_rewriting <- allpos in
	    {< content = Term (k, l', s)>}
	| Var_exist _ | Var_univ _ -> self
	    

    (* Replace all subterms v of self by v'. We count replacements *)
    method replace_subterms counter v v' =
      if self#syntactic_equal v
      then
        let () = incr counter in
        v'
      else
        match content with
          Var_exist _ | Var_univ _ -> {< >}
        | Term (f, l, s) ->
            let l' = List.map (fun x -> x#replace_subterms counter v v') l in
            let v = generic_merge_set_of_lists (List.map (fun x -> x#variables) l') in
	      let fn t t' n = 
		if t#string <> t'#string then 
		  (* reset the positions starting with n  *)
		  let fn' p = 
		    if p <> [] then 
		      if List.hd p = n then false
		      else true
		    else false
		  in
		  let () = pos_rewriting <- (List.filter  fn' pos_rewriting) in
		  let () = pos_contextual_rewriting <- (List.filter  fn' pos_contextual_rewriting) in
		  let () = pos_partial_case_rewriting <- (List.filter  fn' pos_partial_case_rewriting) in
		  let () = pos_total_case_rewriting <- (List.filter  fn' pos_total_case_rewriting) in
		  let () = pos_equational_rewriting <- (List.filter  fn' pos_equational_rewriting) in
		  let lpos_t = (List.map (fun p -> n :: p) t'#pos_equational_rewriting) in
		  try if (((not t'#is_term) or (is_constructor t'#head)) && is_defined f) then generic_merge_sorted_lists [[]] lpos_t else lpos_t with Failure "head" -> lpos_t
		else
		  []
	      in
	      let i = ref (-1) in	  
	      let new_pos = List.flatten (List.map2 (fun t t' -> let () = i := !i + 1 in fn t t' !i) l l')
	      in

              {< content = Term (f, l', s) ;
              variables = v ;
              depth = compute_depth l' ;
	      pos_rewriting  = generic_merge_sorted_lists pos_rewriting new_pos ;
	      pos_contextual_rewriting   = generic_merge_sorted_lists pos_contextual_rewriting new_pos ;
	      pos_partial_case_rewriting = generic_merge_sorted_lists pos_partial_case_rewriting new_pos ;
	      pos_total_case_rewriting   = generic_merge_sorted_lists pos_total_case_rewriting new_pos ;
	      pos_equational_rewriting   = generic_merge_sorted_lists pos_equational_rewriting new_pos ;
	      string = Undefined>}
	      
    (* Replacement of the subterm at position p with term t *)
    method replace_subterm_at_pos p (t: 'a) =
      match p, content with
        ([], _) ->  t
      | (hd :: tl, Term (f, l, s)) ->
          begin
            try
              let l' = apply_f_to_element_n (fun x -> x#replace_subterm_at_pos tl t) hd l in
              let v = generic_merge_set_of_lists (List.map (fun x -> x#variables) l') in

	      let fn t t' n = 
		if t#string <> t'#string then 
		  (* reset the positions starting with n  *)
		  let fn' p = 
		    if p <> [] then 
		      if List.hd p = n then false
		      else true
		    else false
		  in
		  let () = pos_rewriting <- (List.filter  fn' pos_rewriting) in
		  let () = pos_contextual_rewriting <- (List.filter  fn' pos_contextual_rewriting) in
		  let () = pos_partial_case_rewriting <- (List.filter  fn' pos_partial_case_rewriting) in
		  let () = pos_total_case_rewriting <- (List.filter  fn' pos_total_case_rewriting) in
		  let () = pos_equational_rewriting <- (List.filter  fn' pos_equational_rewriting) in
		  let lpos_t = (List.map (fun p -> n :: p) t'#pos_equational_rewriting) in
(* 		  let () = buffered_output ("\nt' = " ^ t'#string) in *)
		  try 
		    if (((not t'#is_term) or (is_constructor t'#head)) && is_defined f)  
		    then generic_merge_sorted_lists [[]] lpos_t 
		    else lpos_t 
		  with Failure "head" -> lpos_t
		else
		  []
	      in
	      let i = ref (-1) in	  
	      let new_pos = List.flatten (List.map2 (fun t t' -> let () = i := !i + 1 in fn t t' !i) l l')
	      in
              {< content = Term (f, l', s) ;
                 variables = v ;
                 depth = compute_depth l' ;
		 pos_rewriting  = generic_merge_sorted_lists pos_rewriting new_pos ;
		 pos_contextual_rewriting   = generic_merge_sorted_lists pos_contextual_rewriting new_pos ;
		 pos_partial_case_rewriting = generic_merge_sorted_lists pos_partial_case_rewriting new_pos ;
		 pos_total_case_rewriting   = all_defined_positions (Term (f, l', s));(* generic_merge_sorted_lists pos_total_case_rewriting new_pos ; *)
		 pos_equational_rewriting   = generic_merge_sorted_lists pos_equational_rewriting new_pos ;
                 string = Undefined >}
            with
              (Failure "apply_f_to_element_n")
            | (Invalid_argument "apply_f_to_element_n") -> failwith "replace_subterm_at_pos"
          end
      | (_ :: _, Var_exist _) | (_ :: _, Var_univ _) -> failwith "replace_subterm_at_pos"
	    
    (* AC term normalization: get all nodes strictly under f-headed trees *)
    method get_ac_f_args f =
      match content with
        Var_exist _ | Var_univ _ -> [ {< >} ]
      | Term (f', l, _) ->
          if const_equal f f'
          then List.flatten (List.map (fun x -> x#get_ac_f_args f) l)
          else [ {< >} ]
	      
    (* Returns functional positions *)
    method strict_positions =
      let rec fn2 i = function
          [] -> []
        | h::t -> (List.map (fun l -> i::l) h#strict_positions) @ (fn2 (i + 1) t) in
      match content with
        Var_exist _ | Var_univ _ -> []
      | Term (_, l, _) -> []:: (fn2 0 l)
				
    (* Returns defined functional positions *)
    method defined_positions = all_defined_positions content

    (* Returns all valid positions in a term (i.e. an int list list).
       The list is sorted *)
    method all_positions_w_sort =
      let rec fn2 i = function
          [] -> []
        | h::t -> (List.map (fun (l, s) -> (i::l, s)) h#all_positions_w_sort) @ (fn2 (i + 1) t) in
      match content with
        Var_exist (_, s) | Var_univ (_, s) -> [([], s)]
      | Term (_, l, s) -> ([], s)::(fn2 0 l)
				     
    (* Returns all variable positions in a term (i.e. an int list list) *)
    method variable_positions_w_sort =
      let rec fn2 i = function
          [] -> []
        | h::t -> (List.map (fun (l, s) -> (i::l, s)) h#variable_positions_w_sort) @ (fn2 (i + 1) t) in
      match content with
        Var_exist (_, s) | Var_univ (_, s) -> [([], s)]
      | Term (_, l, _) -> fn2 0 l
	    
    (* Returns functional positions *)
    method strict_positions_w_sort =
      let rec fn2 i = function
          [] -> []
        | h::t -> (List.map (fun (l, s) -> (i::l, s)) h#strict_positions_w_sort) @ (fn2 (i + 1) t) in
      match content with
        Var_exist _ | Var_univ _ -> []
      | Term (_, l, s) -> ([], s)::(fn2 0 l)
				     
    method sort =
      match content with
        Var_exist (_, s) | Var_univ (_, s) -> s
      | Term (_, _, s) -> s
	    
    (* Returns all variable positions in a term (i.e. an int list list) *)
    method variable_positions =
      let rec fn2 i = function
          [] -> []
        | h::t -> (List.map (fun l -> i::l) h#variable_positions) @ (fn2 (i + 1) t) in
      match content with
        Var_exist _ | Var_univ _ -> [[]]
      | Term (_, l, _) -> fn2 0 l
	    
    (* Returns list of couples: (var_#, occurrences_positions) *)
    method vars_n_pos =
      let fn1  inf_f l1 l2 =
	let rec fn =
	  function
	      l, [] -> l
	    | [], l -> l
	    | ((h, n) :: t as l), ((h', n') :: t' as l') ->
		if inf_f h h' then (h, n) :: fn (t, l')
		else if inf_f h' h then (h', n') :: fn (l, t')
		else (h, n @ n') :: fn (t, t')
	in
	fn (l1, l2)
      in
      let f i (x, l) = (x, List.map (fun l' -> i::l') l) in
      let rec fn2 i = function
          [] -> []
        | h::t -> fn1 var_inf (List.map (f i) h#vars_n_pos) (fn2 (i + 1) t) in
      match content with
        Var_exist (x, s) -> [((x, s, false), [[]])] | Var_univ (x, s) -> [((x, s, true), [[]])]
      | Term (_, l, _) -> fn2 0 l

    (* Flatten a term where AC symbols take place. *)
    method flatten =
      match content with
        Var_exist _ | Var_univ _ -> {< >}
      | Term (f, l, s) ->
          if symbol_is_ac f
          then
            let l' = self#get_ac_f_args f in
            let lflatten = List.map (fun x -> x#flatten) l' in
            {< content = Term (f, lflatten, s) ;
               depth = compute_depth l' ;
               string = Undefined >}
          else
            let l' = List.map (fun x -> x#flatten) l in
            {< content = Term (f, l', s) ;
               depth = compute_depth l' ;
               string = Undefined >}

    (* Depth per sort *)
    method depth_per_sort =
      match content with
        Var_exist (_, s) | Var_univ (_, s) -> [ (s, 1) ]
      | Term (_, [], s) -> [ (s, 1) ]
      | Term (_, l, s) ->
          let l' = List.map (fun x -> x#depth_per_sort) l in
          let l'' = List.map (fun x -> List.map (fun (h, n) -> h, n + 1) x) l' in
          List.fold_left max_assoc_merge [ (s, 1) ] l''
	    
    (* Maximum non-variable position depth *)
    method strict_depth_core =
      match content with
	Var_exist _ | Var_univ _ -> Undefined
      | Term (_, [], _) -> Defined 1
      | Term (_, l, _) ->
          let l' = List.map (fun x -> x#strict_depth_core) l in
          pointer_incr (list_max pointer_max l')
	    
    (* Max non variable depth *)
    method strict_depth =
      match self#strict_depth_core with
	Defined (n: int) -> n
      | Undefined -> failwith "strict_depth"
	    
    (* Maximum non-variable position depth per sort. Produces a sorted list w.r.t. the sort. *)
    method strict_depth_per_sort =
      match content with
	Var_exist _ | Var_univ _ -> []
      | Term (_, [], s) -> [ (s, 1) ]
      | Term (_, l, s) ->
          let l' = List.map (fun x -> x#strict_depth_per_sort) l in
          let l'' = List.map (fun x -> List.map (fun (h, n) -> h, n + 1) x) l' in
          List.fold_left max_assoc_merge [ (s, 1) ] l''

    (* Check property on all subterms *)
    method check_property f =
      match content with
        Var_exist _ | Var_univ _ -> f self
      | Term (_, l, _) -> f self && List.for_all (fun x -> x#check_property f) l

    (* Returns all valid positions in a term (i.e. an int list list).
       The list is sorted *)
    method all_positions =
      let rec fn2 i = function
          [] -> []
        | h::t -> (List.map (fun l -> i::l) h#all_positions) @ (fn2 (i + 1) t) in
      match content with
        Var_exist _ | Var_univ _ -> [[]]
      | Term (_, l, _) -> []:: (fn2 0 l)


    (* Occurrence check *)
    method occur x =
      match content with
        Var_exist (x', _) | Var_univ (x', _) -> var_equal x x'
      | Term (_, l, _) -> List.exists (fun v -> v#occur x) l

    (* Checks if a term contains only constructors *)
    method is_constructor_term =
      match content with
        Var_exist _ | Var_univ _ -> true
      | Term (f, l, _) -> is_constructor f && List.for_all (fun x -> x#is_constructor_term) l

    (* Substitution *)
    method substitute sigma' =
      let sigma = if !specif_parameterized then List.map (fun (id_v, t) -> id_v, t#expand_sorts) sigma' else sigma' in
(*       let () = if !maximal_output then buffered_output (sprint_subst sigma) in *)
      match content with
        Var_exist (x, _) | Var_univ (x, _) ->
          begin (* Dicards PM on exceptions *)
            try List.assoc x sigma
            with Not_found -> self
          end
      | Term (f, l, s) ->
          let l' = List.map (fun x -> x#substitute sigma) l in

	  let fn t t' n = 
	    if t#string <> t'#string then 
	      let lpos_t = (List.map (fun p -> n :: p) t'#pos_rewriting) in
	      try if (is_constructor t'#head  or (not t'#is_term)) && is_defined f then generic_merge_sorted_lists [[]] lpos_t else lpos_t with Failure "head" -> lpos_t
	    else
	      []
	  in
	  let i = ref (-1) in	  
	  let new_pos = List.flatten (List.map2 (fun t t' -> let () = i := !i + 1 in fn t t' !i) l l')
	  in
          {< content = Term (f, l', s) ;
             variables = generic_merge_set_of_lists (List.map (fun x -> x#variables) l') ;
             depth = compute_depth l' ;
	     pos_rewriting  = generic_merge_sorted_lists pos_rewriting new_pos ;
	     pos_contextual_rewriting   = generic_merge_sorted_lists pos_contextual_rewriting new_pos ;
	     pos_partial_case_rewriting = generic_merge_sorted_lists pos_partial_case_rewriting new_pos ;
	     pos_total_case_rewriting   = generic_merge_sorted_lists pos_total_case_rewriting new_pos ;
	     pos_equational_rewriting   = generic_merge_sorted_lists pos_equational_rewriting new_pos ;
             string = Undefined >}

    (* Sufficient completeness test *)
    method has_constructor_arguments =
      match content with
        Var_exist _ | Var_univ _ -> false
      | Term (f, l, _) -> is_defined f && List.for_all (fun x -> x#is_constructor_term) l

    (* Number of symbols in the term *)
    method treesize =
      match content with
        Var_exist _ | Var_univ _ -> 1
      | Term (_, l, _) ->
          1 + List.fold_left (+) 0 (List.map (fun x -> x#treesize) l)

(* Computes all the defined symbols in a term *)
    method def_symbols = 
      match content with
	  Var_exist _ | Var_univ _ -> []
	| Term (f, l, _) -> let v = try dico_const_string#find f with Not_found -> failwith "raising Not_found in def_symbs of terms" in
	  let lv = List.flatten (List.map (fun x -> x#def_symbols) l) in
	    v :: lv


    (* Syntactic equality *)
    method syntactic_equal (v: 'a) =
	match content, v#content with
            Var_exist (x, s), Var_exist (x', s') 
          | Var_univ (x, s), Var_univ (x', s') -> 	
	      if equal_sorts s s' then var_equal x x' else false
	  | Term (_, _, s), Term (_, _, s') ->	
	      if equal_sorts s s' then self#string = v#string else false
		(* TO MODIFY IF DEALING WITH AC OPERATORS	       *)
		(* 		const_equal f f' && *)
		(* 		(List.length l = List.length l') && *)
		(* 		if symbol_is_ac f *)
		(* 		then check_on_permutations syntactic_equal l l' *)
		(* 		else List.for_all2 syntactic_equal l l' when *)
		(* 	      ) *)
	  | Var_exist _, Var_univ _ | Var_univ _, Var_exist _ | Var_exist _, Term _ | Term _, Var_exist _ | Var_univ _, Term _| Term _, Var_univ _-> false
	      
	    
    (* Equality modulo renaming. It it under construction. Not to be used *)
    method equal (v: 'a) =
      try
        let _ = self#bijective_renaming [] v in
        true
      with (Failure "bijective_renaming") ->
        false
          
    (* Bijective renaming. The first argument is list of previous renamings *)
    method bijective_renaming ren (v: 'a) =
      if depth <> v#depth
      then failwith "bijective_renaming"
      else self#bijective_renaming_core ren v


  (* If ren = [] then it returns the matching substitution between
     self and v  *)
    method bijective_renaming_core ren v =
      let fn x x' s s' = 
	if equal_sorts s s' then
	  begin
	    try
	      let x'' = List.assoc x ren in
	      if var_equal x' x''
	      then ren
	      else failwith "bijective_renaming"
	    with Not_found ->
	      try
                let x'' = 
		  try list_assoc_2 x' ren with 
		      (Failure "list_assoc_2") -> failwith "bijective_renaming" 
		in
                if var_equal x x''
                then ren
                else failwith "bijective_renaming"
	      with Not_found ->
                generic_insert_sorted (x, x') ren
	  end
	else failwith "bijective_renaming"
      in
      match content, v#content with
          Var_exist (x, s), Var_exist (x', s') 
	| Var_univ (x, s), Var_exist (x', s') 
        | Var_exist (x, s), Var_univ (x', s') 
        | Var_univ (x, s), Var_univ (x', s') -> fn x x' s s'
	| Term (f, l, _), Term (f', l', _) ->
            if const_equal f f'
            then
              if symbol_is_ac f
              then
		ac_eq (fun x y z -> y#bijective_renaming_core x z) (Failure "bijective_renaming") ren l l'
              else
		List.fold_left2 (fun x y z -> y#bijective_renaming_core x z) ren l l'
            else failwith "bijective_renaming"
	| Term _, Var_exist _| Var_exist _, Term _| Var_univ _, Term _| Term _, Var_univ _ -> failwith "bijective_renaming"
	    
    (* Checks if toplevel symbol is a constant and returns its value *)
    method head =
      match content with
        Term (f, _, _) -> f
      | Var_exist _ | Var_univ _ -> failwith "head"

    method sons =
      match content with
        Term (_, l, _) -> l
      | Var_exist _ | Var_univ _ -> failwith "sons"

    method head_n_sons =
      match content with
        Term (f, l, _) -> f, l
      | Var_exist _ | Var_univ _ -> failwith "head_n_sons"

    method is_term =
      match content with
        Term _ -> true
      | Var_exist _ | Var_univ _ -> false

    method var_content =
      match content with
          Var_exist (x, _) | Var_univ (x, _) -> x
	| Term _ -> failwith "var_content"
	    
    (* Do we have a natural encoded *)
    method is_a_natural =
      match content with
        Term (f, l, _) ->
          (try
	    let id_symbol_s =
	      try
		dico_const_string#find_key "s"
	      with Failure "find_key" -> 
		try
		  dico_const_string#find_key  "S"
		with Failure "find_key" -> failwith "id_symbol_s"
	    in
	    let id_symbol_zero =
	      try
		dico_const_string#find_key "0"
	      with Failure "find_key" -> failwith "id_symbol_zero"
	    in
	    if f = id_symbol_s
            then List.for_all (fun x -> x#is_a_natural) l
            else if f = id_symbol_zero
            then true
            else false
	  with Failure "id_symbol_s"| Failure "id_symbol_zero" -> false
	  )
      | Var_exist _ | Var_univ _ -> false

    (* Status-induced congruence on terms *)
    method term_congruence v =
      match content, v#content with
        Term (f, l, _), Term (f', l', _) ->
          begin (* Discards PM on status *)
            equivalent f f' &&
            (List.length l = List.length l') &&
            match get_status f with
              Left | Right -> List.for_all2 (fun x y -> x#term_congruence y) l l'
            | Multiset -> check_on_permutations (fun x y -> x#term_congruence y) l l'
          end
      | Var_exist (x, _), Var_exist (x', _) 
      | Var_univ (x, _), Var_univ (x', _) -> var_equal x x'
      | Var_exist _, Var_univ _ | Var_univ _, Var_exist _ | Var_exist _, Term _ | Term _, Var_exist _ | Var_univ _, Term _| Term _, Var_univ _ -> false

    (* Linear variables with their positions *)
    method linear_variables = List.filter (function (_, l) -> match l with [_] -> true | _ -> false) self#vars_n_pos

    (* Only the positions (for test test computations) *)
    method linear_positions = List.flatten (List.map  (fun (_, y) -> y) self#linear_variables)

    (* Only the values *)
    method linear_values = List.map (fun (x, _) -> x) self#linear_variables

    (* Linear variables with their positions *)
    method non_linear_variables = List.filter (function (_, l) -> match l with [_] -> false | _ -> true) self#vars_n_pos

    (* Only the positions (for test test computations) *)
    method non_linear_positions = List.flatten (List.map (fun (_, y) -> y) self#non_linear_variables)

    (* Only the values *)
    method non_linear_values = List.map (fun (x, _) -> x) self#non_linear_variables

    (* Tests whether a term is linear *)
    method is_linear = List.for_all (fun (_, l) -> match l with [_] -> true | _ -> false) self#vars_n_pos

    method private compute_basic_string =
      match content with
          Var_exist (x, s) -> sprint_var x s false | Var_univ (x, s) -> sprint_var x s true 
	| Term (f, [], _) -> let v = try dico_const_string#find f with Not_found -> failwith "raising Not_found in compute_basic_string" in v
	| Term (f, l, _) ->
            let v = try dico_const_string#find f with Not_found -> failwith "raising Not_found in compute_basic_string" in
            let a = sprint_list ", " (fun x -> x#string) l in
            v ^ " (" ^ a ^ ")"
	      

    (* Pretty printer. Takes care of integers and ac symbols. *)
    method compute_string =

      let rec fn2 v l_ar r_ar l =
        let rec fn3 l =
          let l_args, r_args = try list_split_at_n l_ar l with Failure "list_split_at_n" -> failwith "compute_string" in
          let s = match l_args with
            [] -> ""
          | [h] -> if h#depth = 1 then h#string ^ " " else "(" ^ h#string ^ ") "
          | _ -> "(" ^ (sprint_list ", " (fun x -> x#string) l_args) ^ ") "
          and s' =
            if List.length r_args = r_ar
            then
              match r_args with
                [] -> []
              | [h] -> if h#depth = 1 && l_ar = 1 then [h#string] else ["(" ^ h#string ^ ")"]
              | _ -> ["(" ^ (sprint_list ", " (fun x -> x#string) r_args) ^ ")"]
            else
              fn3 r_args in
          s::s' in
        sprint_string_list (v ^ " ") (fn3 l) in

      match content with
        Var_exist (x, s) -> sprint_var x s false | Var_univ (x, s) -> sprint_var x s true
      | Term (f, [], _) -> let v = try dico_const_string#find f with Not_found -> failwith ((string_of_int f) ^ ":  this symbol raised Not_found in compute_string (1)")  in v
      | Term (f, l, _) ->
          if self#is_a_natural
          then string_of_int (self#depth - 1)
          else
            let l_ar, r_ar = try dico_arities#find f  with Not_found -> failwith "raising Not_found in compute_string (2)" 
            and v = try dico_const_string#find f  with Not_found -> failwith "raising Not_found in compute_string (3)" in
            if symbol_is_ac f
            then
              if l_ar = 0 && r_ar = 2
              then
                let l' = self#get_ac_f_args f in
                let ls = List.map (fun x -> x#string) l' in
                (try dico_const_string#find f with Not_found -> failwith "raising Not_found in compute_string (4)")  ^ " (" ^ (sprint_string_list ", " ls) ^ ")"
              else if l_ar = 1 && r_ar = 1
              then
                let l' = self#get_ac_f_args f in
                let ls = List.map (fun x -> x#string) l' in
                sprint_string_list (" " ^ v ^ " ") ls
              else invalid_arg "string"
            else
              let _, _ = try list_split_at_n l_ar l with Failure "list_split_at_n" -> failwith "compute_string" in
              fn2 v l_ar r_ar l

  (* pretty print function *)
    method pprint f = Format.fprintf f "@[{@[Term: %s@]@ @[ with sort \"%s\"@]}@]" self#string (sprint_sort self#sort)

    method compute_string_coq with_model =   
      match content with
          Var_exist (_, _) -> failwith "compute_string_coq: existential variables not yet treated" 
	| Var_univ (x, s) -> (match s with 
				  Def_sort _ -> let s_name = dico_sort_string#find s in if with_model then "(model_" ^ s_name ^ " u" ^ (string_of_int x) ^ ")" else "(Var " ^ (string_of_int x) ^ ")"
				| Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _ -> failwith "compute_string_coq: parameterized specifications not yet treated"
			     )
	| Term (f, l, _) ->
            let v = try (let s = dico_const_string#find f in if String.compare s "+" == 0 then "plus" else s) with Not_found -> failwith "raising Not_found in compute_basic_string" in
            let a = sprint_list ":: " (fun x -> x#compute_string_coq with_model) l in
              "(Term id_" ^ v ^ (if l == [] then " nil)" else " (" ^ a ^ "::nil))")

    method compute_string_coq_with_quantifiers lv =   
      match content with
          Var_exist (_, _) -> failwith "compute_string_coq: existential variables not yet treated" 
	| Var_univ (x, s) -> (match s with 
				  Def_sort _ ->  (if List.mem x lv then "_u" else "u") ^ (string_of_int x)
				| Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _ -> failwith "compute_string_coq: parameterized specifications not yet treated"
			     )
	| Term (f, l, _) ->
            let v = try (let s = dico_const_string#find f in if String.compare s "+" == 0 then "plus" else s) with Not_found -> failwith "raising Not_found in compute_basic_string" in
            let a = sprint_list " " (fun x -> x#compute_string_coq_with_quantifiers lv) l in
              (if l == [] then "" else "(") ^ v ^ (if l == [] then "" else " ") ^ a ^ (if l == [] then "" else ")")
	      

    (* Returns: (position, path (mixed), max depth of subterm, sort)
       for each strict position, and non linear position. *)
    method core_ind_positions_v1 l_v =
      let fn2 f _ =
        let rec fn3 i = function
            [] -> []
          | h::t -> (List.map (fun (l, (d, s')) -> (f, i)::l, (d, s')) (h#core_ind_positions_v1 l_v)) @ (fn3 (i + 1) t) in
        fn3 0 in
      match content with
        Var_univ (x, s) -> if List.mem (x, s, true) l_v then [ ([], (1, s)) ] else [] 
	| Var_exist (x, s) -> if List.mem (x, s, false) l_v then [ ([], (1, s)) ] else []
      | Term (f, l, s) -> ([], (self#depth, s))::(fn2 f s l)

    method ind_positions_v1 =
      List.filter (function ([], _) -> false | _ -> true) (self#core_ind_positions_v1 self#non_linear_values)

    (* Returns a sorted (path * subterm) list *)
    method core_ind_positions_v2 l_v =
      let fn f =
        let rec fn2 i = function
            [] -> []
          | h::t -> (List.map (fun (l, tr) -> (f, i)::l, tr) (h#core_ind_positions_v2 l_v)) @ (fn2 (i + 1) t) in
        fn2 0 in
      match content with
          Var_exist (x, s) -> if List.mem (x, s, false) l_v then [ ([], {< >}) ] else []
	| Var_univ (x, s) -> if List.mem (x, s, true) l_v then [ ([], {< >}) ] else []
      | Term (f, l, _) -> ([], {< >})::(fn f l)

    method ind_positions_v2 =

      let () = buffered_output ("analysing " ^ self#string) in
      let ind_pos = self#core_ind_positions_v2 self#non_linear_values in
      if ind_pos = [] then failwith "ind_position_v2" else
	let l = List.tl ind_pos in
	let () = buffered_output ("Found paths: " ^ (sprint_list " ; " (fun (p, t) -> sprint_path p ^ " ---> " ^ t#string) l)) in
	l

    (* Paths to variables in the term (to get induction variables in v2) *)
    method variable_paths =
      let rec fn2 f i = function
          [] -> []
        | h::t -> (List.map (fun (x, l) -> x, (f, i)::l) h#variable_paths) @ (fn2 f (i + 1) t) in
      match content with
          Var_exist (x, s) -> [((x, s, false), [])]
	| Var_univ (x, s) -> [((x, s, true), [])]
	| Term (f, l, _) -> fn2 f 0 l

    method replace_sort new_s = 
      match content with 
	  Var_exist (x, _) ->  {< content = Var_exist (x, new_s) >}
	| Var_univ (x, _) -> {< content = Var_univ (x, new_s) >}
	| Term (f, l, _) -> {< content = Term (f, l, new_s) >}
	    
    (* Matching: checks whethers exists sigma: t'.sigma = self
       proceed_fun : substitution -> substitution is applied on the substitution after the matching *)

    method matching_core (proceed_fun: (var * 'a) list -> (var * 'a) list) (sigma: (var * 'a) list) l =
(*       let () = print_string "\nInitialize1 yy_tmp_param_sorts" in *)
      yy_tmp_param_sorts := [];
      let rec fn sigma lt = 
	match lt with
          [] ->
(* 	    let () = if !maximal_output then buffered_output ("\nInside the matching core procedure ") in *)
(* 	    let () = if !maximal_output then buffered_output (sprint_subst sigma) in *)
            let res = proceed_fun sigma in
(* 	    let () = if !maximal_output then buffered_output ("\nOUTSIDE the matching core procedure ") in *)
	    res
        | (v, v')::t ->
            begin
              match v#content, v'#content with
                  Var_exist(x, _) , Var_exist (x', _) -> if x = x' then fn sigma t else failwith "matching"
		| Term _, Var_univ (x', s') | Var_exist _ ,  Var_univ (x', s') | Var_univ _, Var_univ (x', s') ->
					     let s = v#sort in
					     (
					       try 
						 begin
						   let new_v = 
						     if !specif_parameterized then 
						       let new_s = unify_sorts (Actual_sort s) s' in 
						       v#replace_sort new_s else v
						   in
						   try
						     let v_assoc = List.assoc x' sigma in
						     if new_v#syntactic_equal v_assoc
						     then fn sigma t
						     else failwith "matching"
						   with Not_found ->
						     let fn_eq = (fun (x, _) (x', _) -> x = x') in
						     let fn_inf = (fun (x, _) (x', _) -> x < x') in
						     fn (insert_sorted fn_eq fn_inf  (x', new_v) sigma) t
						 end
					       with Failure "unify_sorts" -> failwith "matching"
					     )
		| Term (f, l, s), Term (f', l', _) ->
                  if const_equal f f'
                  then
                    if symbol_is_ac f
                    then
                      let new_proceed_fun s = fn s t
                      and m = l
                      and m' = l' in
                      if List.length m' > List.length m
                      then failwith "matching"
                      else matching_core_ac new_proceed_fun sigma f s m m'
                    else fn sigma ((List.combine l l') @ t) (* Put t in front for width-first search *)
                  else failwith "matching"
              | Term _, Var_exist _| Var_exist _, Term _| Var_univ _, Term _| Var_univ _, Var_exist _ -> failwith "matching"
            end

      and matching_core_ac proceed_fun sigma f s l l' =

        let rec process_sigma_vars = function
            [] -> [], []
          | h::t ->
              try
                let tr = List.assoc h#var_content sigma
                and l, l' = process_sigma_vars t
                in tr::l, l'
              with Not_found ->
                let l, l' = process_sigma_vars t
                in l, h::l'

        and term_multiplicity = function
            [] -> []
          | h::t ->
              let l, l' = List.partition h#syntactic_equal t in
              (1 + List.length l, h)::term_multiplicity l' in

        (* Remove vars of sigma *)
        let lt, lw = List.partition (fun x -> x#is_term) l' in
        let lsigma, lw' = process_sigma_vars lw in
        let luniques = term_multiplicity lw' in

        (* Remove terms of sigma *)
        let lsigma' = List.flatten (List.map (fun x -> x#get_ac_f_args f) lsigma) in
        let lt' = try unsorted_setminus syntactic_equal lt lsigma' with Failure "unsorted_setminus" -> failwith "matching" in
        let ls, lv = List.partition (fun x -> x#is_term) l in

        (* Make a substitution out of a variable and a list of terms *)
        let rec build_ac_subst v l =
          match List.length l with
            0 -> invalid_arg "build_ac_subst"
          | 1 -> v, List.hd l
          | _ ->
              let v' = generic_merge_set_of_lists (List.map (fun x -> x#variables) l) in
              v, {< content = Term (f, l, s) ;
                    variables = v' ;
                    depth = compute_depth l ;
                    string = Undefined >}

        and process_couples proceed_fun sigma rest = function
            [] -> try_on_partitions proceed_fun sigma rest
          | (a, a')::t -> process_same_head proceed_fun sigma rest t a a'

        and process_same_head proceed_fun sigma rest tail a = function
            [] -> process_couples proceed_fun sigma (rest @ a) tail
          | h::t ->
              let rec fn acc = function
                  [] -> failwith "matching"
                | hd::tl ->
                    try
                      let new_proceed_fun s = process_same_head proceed_fun s rest tail (acc @ tl) t in
                      self#matching_core new_proceed_fun sigma [ (hd, h) ]
                    with (Failure "matching") -> fn (hd::acc) tl in
              fn [] a

        (* n' parties de n éléments, avec multiplicités *)
        and get_partitions proceed_fun sigma l l' =

          let rec fn s l l' =
            match l, l' with
              [], [] -> proceed_fun (subst_compose s sigma)
            | _::_, [] -> failwith "matching"
            | _, h::t ->
                fn2 h s [] [] t l
                  
          and fn2 (i, v) s l l' tl = function
              [] ->
                (match l with [] -> failwith "matching" | _ -> fn (generic_insert_sorted (build_ac_subst v#var_content l) s) l' tl)
            | (j, h)::t ->
                if j >= i
                then
                  try fn2 (i, v) s (h::l) l' tl (match i - j with 0 -> t | _ -> (j - i, h)::t)
                  with (Failure "matching") -> fn2 (i, v) s l ((j, h)::l') tl t
                else
                  fn2 (i, v) s l ((j, h)::l') tl t
                    
          in fn [] l l'

        and try_on_partitions proceed_fun sigma rest =
          let l = (term_multiplicity rest) @ (term_multiplicity lv)
          in get_partitions proceed_fun sigma l luniques

        (* Group terms from two lists into sublists. None of the terms of the list has 'f' as head symbol (normal forms)
           We return:
         * a list of couples of terms having identical head symbols
         * the rest of terms of the first list
         *)
        and group_for_ac_matching l l' =
          match l, l' with
            _, [] -> [], l
          | [], _ -> failwith "matching"
          | _::_, h'::_ ->
              let f' = h'#head in
              let l1, l2 = List.partition (fun x -> x#head = f') l
              and l'1, l'2 = List.partition (fun x -> x#head = f') l' in
              if List.length l1 < List.length l'1
              then failwith "matching"
              else
                let r, r' = group_for_ac_matching l2 l'2 in
                (l1, l'1)::r, r' in

        let couples, rest = group_for_ac_matching ls lt' in

        process_couples proceed_fun sigma rest couples in

      fn sigma l

    (* Basic order *)
    method leq (v: 'a) =
      match content, v#content with
          Var_exist (x, _), Var_exist (y, _) 
	| Var_univ (x, _), Var_exist (y, _) 
        | Var_exist (x, _), Var_univ (y, _) 
        | Var_univ (x, _), Var_univ (y, _) -> x <= y
	| Term (f, _, _), Term (f', _, _) -> f <= f'
	| Term _, Var_exist _ -> true
	| Term _, Var_univ _ -> true
	| Var_univ _, Term _ -> false
	| Var_exist _, Term _ -> false

    (* Matching: returns a substitution sigma such that t*sigma = self 
     *)
    method matching proceed_fun (t: 'a) =
      self#matching_core proceed_fun [] [(self, t)]

    (* Returns the position (and substitution) of a subterm s of self such that t.sigma = s
       proceed_fun: position -> substitution -> bool *)
    method subterm_matching proceed_fun (t: 'a) =
      let rec fn p s =
        match s#content with
          Var_exist (_, _) | Var_univ (_, _)-> p, s#matching (proceed_fun p) t
        | Term (_, l, _) ->
            try
              fn2 p l
(*            (p, s#matching (proceed_fun p) t)*)
            with (Failure "matching") ->
              (p, s#matching (proceed_fun p) t)
(*            fn2 p l*)
      and fn2 p =
        let rec fn3 i = function
            [] -> failwith "matching"
          | h::t ->
              try
                fn (p @ [i]) h
              with (Failure "matching") ->
                fn3 (i + 1) t in
        fn3 0 in
      fn [] self

  (* tests if t1 = t2 modulo renaming variables  *)
    method equal_mod_var t = 
      try 
	let s = self#subterm_matching_at_pos (fun x -> x) [] t in
	(List.for_all (fun (_, t) -> (not t#is_term)) s)
      with Failure "subterm_matching_at_pos" -> false 

    (* Checks if the subterm of self at position p matches t (i.e. exists sigma, t.sigma = s[p])
       proceed_fun: substitution -> bool *)
    method subterm_matching_at_pos proceed_fun p t =
      try
        let s = self#subterm_at_position p in
        s#matching proceed_fun t
      with (Failure "subterm_at_position")| Failure "matching" -> failwith "subterm_matching_at_pos"

    (*
     * Returns the subterm at a given position. A position is a list of integers.
     * Raises Failure "subterm_at_position" is the position is not valid in the term
     *)
    method subterm_at_position l =
      match l, content with
        [], _ -> self
      | _, Var_univ _ | _, Var_exist _ -> failwith "subterm_at_position"
      | h::t, Term (_, l', _) ->
          try (List.nth l' h)#subterm_at_position t
          with (Failure "nth") -> failwith "subterm_at_position"

    (* Is self a subterm of t. Returns the position *)
    method subterm t =

      let eq = self#syntactic_equal in
      let rec fn t =
	if eq t
	then []
	else
	  match t#content with
            Var_exist _ | Var_univ _ -> failwith "subterm"
	  | Term (_, l, _) ->
	      fn2 0 l

      and fn2 i = function
	  [] -> failwith "subterm"
	| h::t ->
	    try
	      let p = fn h
	      in i::p
	    with (Failure "subterm") -> fn2 (i + 1) t

      in fn t

(* Rename variables of a term with fresh ones *)
    method rename_core lv =
      match content with
        Var_exist (x, s) ->
          begin (* Dicards PM on exceptions *)
            try
              let v = List.assoc x lv in
              {< content = Var_exist (v, s) ; variables = [ (v, s, false) ] ;
                 string = Undefined >}
            with Not_found -> self
          end
        | Var_univ (x, s) ->
          begin (* Dicards PM on exceptions *)
            try
              let v = List.assoc x lv in
              {< content = Var_univ (v, s) ; variables = [ (v, s, true) ] ;
                 string = Undefined >}
            with Not_found -> self
          end
      | Term (f, l, s) ->
          let l' = List.map (fun x -> x#rename_core lv) l in
          {< content = Term (f, l', s) ;
             variables = generic_merge_set_of_lists (List.map (fun x -> x#variables) l') ;
             string = Undefined >}

    method rename =
      let v = List.map (fun (x, _, _) -> x, newvar ()) variables in
      self#rename_core v

    (* unsafe: this method should NOT be called unless add_nat_specif (therefore id_sort_nat set) has been called.
       It is not checked at run-time *)
    method is_nat = if !nat_specif_defined then (self#sort =
						 id_sort_nat) else failwith "is_nat: naturals are used but not loaded !"

    (* unsafe: this method should NOT be called unless add_int_specif (therefore id_sort_int set) has been called.
       It is not checked at run-time *)
    method is_int = if !int_specif_defined then (self#sort =
						 id_sort_int) else failwith "is_int: integers are used but not loaded !"

    method contextual_var = 5
    method has_no_obs_strict_subcontext = true
    method subterms = List.map (self#subterm_at_position ) self#all_positions
    method is_not_ground_reducible = true 
    method vars_but_context_var = [(5, Def_sort 5, true)]
    method sort_var_cont = Def_sort 5

  end


  (* ground_term is not yet used. All reference to it is in fact a
     reference to the class term  *)
and ground_term c_t =

  object (self : 'a)

    inherit term c_t as super
	
    (* the initial substitution / renaming is neutralized *)
    method matching _ (trm:'a) =
      if self#syntactic_equal trm 
      then []
      else failwith "matching"

  end

(* Two constants *)
let term_true = new term (Term (id_symbol_true, [], id_sort_bool))
and term_false = new term (Term (id_symbol_false, [], id_sort_bool))


let rec term_nat x =
  let peano_sort = if !nat_specif_defined then id_sort_nat else
    id_sort_int in
  match x with 
      0 -> new term (Term (id_symbol_zero, [], peano_sort))
    | n -> new term (Term (id_symbol_s, [ term_nat (n - 1) ], peano_sort))
(* Is a substitution primitive, i.e. contains only constructor terms ? *)
let subst_is_primitive s =
  List.for_all (fun (_, t) -> t#is_constructor_term) s

(* The inference rules bitstream. These values set bits to true once a rule has failed on a certain clause.
   Next time the same rule is to be applied, failure will occur at once or special cases will be triggered *)

let contextual_rewriting_bit        = get_bitstream [1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]
let equational_rewriting_bit        = get_bitstream [0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]
let rewriting_bit       = get_bitstream [0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]
let partial_case_rewriting_bit      = get_bitstream [0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]
let total_case_rewriting_bit        = get_bitstream [0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0]
let induction_bit                   = get_bitstream [0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0;0]
let positive_decomposition_bit      = get_bitstream [0;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0;0]
let negative_decomposition_bit      = get_bitstream [0;0;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0;0]
let positive_clash_bit              = get_bitstream [0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0;0]
let tautology_bit                   = get_bitstream [0;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0;0]
let subsumption_bit                 = get_bitstream [0;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0;0;0]
let negative_clash_bit              = get_bitstream [0;0;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0;0]
let eliminate_redundant_literal_bit = get_bitstream [0;0;0;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0;0]
let eliminate_trivial_literal_bit   = get_bitstream [0;0;0;0;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0;0]
let auto_simplification_bit         = get_bitstream [0;0;0;0;0;0;0;0;0;0;0;0;0;0;1;0;0;0;0;0]
let complement_bit                  = get_bitstream [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1;0;0;0;0]
let congruence_closure_bit          = get_bitstream [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1;0;0;0]
let augmentation_bit                = get_bitstream [0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1;0;0]
let smt_bit                          = get_bitstream [1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1;0]
let la_bit                           = get_bitstream [1;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;0;1]

(* Dictionay for the list of individuals of nullary sorts *)
let dico_nullary_individuals = (new dictionary 11: (sort, (int * term list)) dictionary)

let print_dico_nullary_individuals () =
  let rec f s (_, l) = buffered_output ((try dico_sort_string#find s with Not_found -> failwith "raising Not_found in print_dico_nullary_individuals") ^ "\n" ^
                                        (sprint_list "\n" (fun x -> "\t" ^ x#string) l)) in
  let () = buffered_output "dico_nullary_individuals =" in
  dico_nullary_individuals#iter f

  (* defined but not used  *)
let deepest_depth l =
  let fn v =
    let rec fn2 = function
        [] -> v
      | h::t ->
          let h' = fn2 t in
          max h#depth h' in
    fn2 in
  match l with
    [] -> failwith "list_max"
  | h::t -> fn h t

(* Build these individuals. Defined but not used  *)
let rec nullary_individuals l_profiles s =
  match s with
      Def_sort _ -> (
	try
	  snd (dico_nullary_individuals#find s)
	with Not_found ->
	  let l_symbols = List.assoc s l_profiles in
	  let rec fn = function
              [] -> []
	    | (f, [])::t -> (new term (Term (f, [], s)))::fn t
	    | (f, l)::t ->
		let l' = List.map (nullary_individuals l_profiles) l in
		let new_args = megamix l' in
		(List.map (fun a -> new term (Term (f, a, s))) new_args) @ fn t in
	  let inds = fn l_symbols in
	  let () = dico_nullary_individuals#add s (0, inds) in
	  inds
      )
    | Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _ -> []
	  

(* Update the dictionary above browsing the profile dico *)
let update_dico_nullary_individuals () =
  let l = ref [] in
  let fn x v =
    if is_constructor x
    then
      let s = try dico_const_sort#find x with Not_found -> failwith "update_dico_nullary_individuals" in
      match s with 
	  Def_sort _ -> 
	    if is_nullary_sort s
	    then
	      if v = [] then failwith "update_dico_nullary_individuals" 
	      else
		l := generic_assoc_insert_sorted (s, (x, List.tl v)) !l
	    else ()
	|  Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _ -> ()
    else () 
  in
  let () = dico_const_profile#iter fn in
  let _ = List.map (fun (s, _) -> nullary_individuals !l s) !l in
  ()

(* Instanciate all nullary variables in a term by their
   individuals. If it is not solution it returns the term alone in the 
   list*)
let produce_nullary_instances t =
  let v = t#variables in
  let v' = List.filter (fun (_, s, _) -> is_nullary_sort s) v in
  let l = List.map (fun (x, s, _) -> List.map (fun tr -> (x, tr)) (snd (try dico_nullary_individuals#find s with Not_found -> failwith "produce_nullary_instances"))) v' in
  let sigmas = megamix l in
  match sigmas with
    [] -> [t]
  | _ -> List.map t#substitute sigmas

(* Complete a substitution: given sigma and a list of variables, all v
   not in dom (sigma) are renamed. Defined but not used *)
let complete_substitution sigma lv =
  let rec fn l l' =
    match l, l' with
      _, [] -> l
    | [], _ -> failwith "complete_substitution"
    | (h, s)::t, h'::t' ->
        if h < h'
        then (h, s)::fn t l'
        else if h = h'
        then fn t t'
        else failwith "setminus" in
  let v = List.map fst sigma in
  let v' = fn lv v
  and () = try greatest_var := 1 + ((fun (x, _) -> x) (last_el lv)) with
      (Failure "last_el") -> ()
  in
  generic_merge_sorted_lists sigma (List.map (fun (x, s) -> (x, new term (Var_univ (newvar (), s)))) v')

(* Given u, f, l, s, build u (u (... (u (f (l))))) *)
let make_unary_term h f l s =
  let rec fn = function
      0 -> new term (Term (h, l, s))
    | i ->
        let t = fn (i - 1) in
        new term (Term (f, [t], s)) in
  fn

let term_is_true = term_true#syntactic_equal
and term_is_false = term_false#syntactic_equal

		  
let expand_sorts_list l = 
  List.map (fun x -> x#expand_sorts) l

let print_detailed_term t  = 
  let rec fn spaces t = 
    let () = print_string ("\n" ^ (n_spaces spaces) ^ "the term " ^ t#string ^ " has the type " ^ (sprint_sort
      t#sort)) in 
    match t#content with
	Var_exist _ | Var_univ _ -> ()
      | Term (_, l, _) -> List.iter (fun x -> fn (spaces + 3) x) l
  in fn 0 t
       
let sprint_detailed_term t  = 
  let rec fn spaces t =  
    match t#content with
	Var_exist _ | Var_univ _ -> ""
      | Term (_, l, _) -> List.fold_right (fun x _ -> "\n" ^ (n_spaces (spaces + 3)) ^ "the term " ^ x#string ^ " has the type " ^ (sprint_sort
      x#sort)) l ""
  in fn 0 t
       
let print_detailed_position_term t = 
  let rec fn spaces t = 
    let spos = List.fold_left (fun x y -> x ^ "  " ^ (sprint_position y)) "" t#pos_rewriting in
    let () = buffered_output ("\n" ^ (n_spaces spaces) ^ "the term " ^ t#string ^ " has the positions " ^ spos) in
    match t#content with
	Var_exist _ | Var_univ _ -> ()
      | Term (_, l, _) -> List.iter (fun x -> fn (spaces + 3) x) l
  in fn 0 t
       
let rec expand_terms (i, t)  (j, t') = 
  let rec fn (i, t) t' =
      match t'#content with
	  Var_exist (_, _) ->  t'
	| Var_univ (x, _) -> 
	    if i = x then t else t' 
	| Term (k, l, s) -> 
	    let l' = List.map (fn (i, t)) l in
	    new term (Term(k, l', s))
  in 
  let res = (fn (i, t) t') in
  (j, res)

  (* unification algorithm of two terms that do not share variables and are well typed. The tc term does not instantiate the
     existential/parameterized sort variables. It is assumed that the tr's variables are universally quantified.*)
let unify_terms tc tr is_gen = 
  (*  lc and lt are two lists with binding variables in tc and tr respectively   *)
  let () = yy_tmp_param_sorts := [] in
  let lc = ref ([]: (var * term) list) in
  let lr = ref ([]: (var * term) list) in
  let is_var t = not t#is_term in

  let rec fn tc lc tr lr = 
(*     let () = buffered_output ("\nTry to unify the terms tc = " ^ tc#string ^ " with tr = " ^ tr#string) in *)
(*     let () = buffered_output ("\nThe substitution lc = " ^ (sprint_subst !lc) ^ " and lr = " ^ (sprint_subst !lr) ^ "\n\n") in *)
(*     let () = buffered_output ("\nThe detailed tc is ") in let () = (print_detailed_term tc) in *)
(*     let () = buffered_output ("\nThe detailed tr is ") in let () =  (print_detailed_term tr)  in *)

    let fn1 ((i, s), t) l = 

      if equal_sorts s t#sort then 
	let univ_vars t = List.filter (fun (_, _, b) -> b = true) t#variables in
	let fn3 t =  List.map (fun (j, _, _) -> j) (univ_vars t) in
	if List.mem i (fn3 t) && t#is_term then failwith "fn"
	else 
	  try 
	    let cnt_t = t#var_content in
	    if i = cnt_t then l else (i, t) :: (List.map (expand_terms (i, t)) l) 
	  with Failure "var_content" -> (try (i, t) :: (List.map (expand_terms (i, t)) l) with Failure "expand_terms" -> failwith "unify_terms") 
	    | Failure "expand_terms" -> failwith "unify_terms"
      else failwith "unify_terms"
    in
    match (is_var tc), (is_var tr) with
	true, true -> 
	  let t1 = try List.assoc tc#var_content !lc with Not_found -> tc in
	  let t2 = try List.assoc tr#var_content !lr with Not_found -> tr in
	  let tc_is_free = (t1#syntactic_equal tc) in
	  let tr_is_free = (t2#syntactic_equal tr) in
	  (match tc_is_free, tr_is_free with
	      true, true -> (* both variables are free *)
		(match (is_existential_var tr), (is_existential_var tc) with
		    true, true ->   
		      if is_gen then 
			 lr := fn1 ((tc#var_content, tc#sort), tr) !lr 
		      else
			failwith "unify_terms"
		  | true, false ->  lr := fn1 ((tc#var_content, tc#sort), tr) !lr 
		  | false, true ->  lr := fn1 ((tr#var_content, tr#sort), tc) !lr 
		  | false, false -> lr := fn1 ((tr#var_content, tr#sort), tc) !lr 
		)
	    | true, false -> (* tc free, tr bound *)
	      if is_existential_var tc then failwith "fn"
	      else lc := fn1 ((tc#var_content, tc#sort), t2) !lc
	    | false, true -> (* tr free, tc bound *)
		if is_existential_var tr && not is_gen  then failwith "fn" else
		  lr := fn1 ((tr#var_content, tr#sort), t1) !lr
	    | false, false -> (* both variables are bound *)
		  fn t1 lc t2 lr
	  )
      | true, false ->  (* tc is var, tr is term *)
	  let t1 = try List.assoc tc#var_content !lc with Not_found -> tc in
	  let tc_is_free = (t1#syntactic_equal tc) in
	  if tc_is_free then 
	    if is_existential_var tc && not is_gen then failwith "fn" 
	    else lc := fn1 ((tc#var_content, tc#sort), tr) !lc
	  else fn t1 lc tr lr
	    
      | false, true -> 	  (* tc is term, tr is var *)
	  let t2 = try List.assoc tr#var_content !lr with Not_found -> tr in
	  let tr_is_free = (t2#syntactic_equal tr) in
	  if tr_is_free then 
	    if is_existential_var tr  then failwith "fn"
	    else  lr := fn1 ((tr#var_content, tr#sort), tc) !lr
	  else fn tc lc t2 lr

      | false, false ->  (* both tc and tr are not variables *)
	  let hd1, l1 = tc#head_n_sons in
	  let hd2, l2 = tr#head_n_sons in
	  if hd1 <> hd2 then failwith "fn"
	  else List.iter2 (fun x y -> let x' = x#substitute !lc in let y' = y#substitute !lr in  fn x' lc y' lr) l1 l2 
  in 
  try 
    let () = fn tc lc tr lr in  (* get lc and lr *)
(*     let () = buffered_output ("\nThe FINAL substitution lc = " ^ (sprint_subst !lc) ^ " and lr = " ^ (sprint_subst !lr) ^ "\n\n") in *)
    let s1 = List.map (fun (i, t) -> (i, t#expand_sorts)) !lc in
    let s2 = List.map (fun (i, t) -> (i, t#expand_sorts)) !lr in
    (s1, s2) 
  with Failure "fn" -> (*  let () = buffered_output "Failure on unification" in *) failwith "unify_terms";;


let sprint_detailed_subst l =
  let f (x, t) =  sprint_var x (Def_sort 0) true ^ ", " ^ t#string  ^ (if !maximal_output then (" of sort " ^ (sprint_sort t#sort)) else 
    "") in
  "< " ^ sprint_list " ; " f l ^ " >"
;;

let write_pos_term t = 
  let fn lp = 
     List.fold_left (fun str p -> str ^ " " ^ (sprint_position p)) " " lp 
  in
  if !maximal_output then 
    buffered_output ("\nThe positions of t = " ^ t#string ^ " are: " ^ "\n\nConditional Rewriting : " ^ (fn
      t#pos_rewriting)^ "\n\nPartial Case Rewriting : " ^ (fn
      t#pos_partial_case_rewriting)^ "\n\nTotal Case Rewriting : " ^ (fn
      t#pos_total_case_rewriting)  )

(* let rec copy_term t = *)
(*   match t#content with *)
(*      Term (f, l, s) ->  *)
(* 	  let l' = List.map (fun x -> copy_term x) l  in *)
(* 	  new term (Term(f, l', s)) *)
(*     | Var_exist (x, s) -> new term (Var_exist(x, s))  *)
(*     | Var_univ (x, s) -> new term (Var_univ(x, s))  *)

let dico_rpo_greater = (new dictionary 101: ((string * string), order) dictionary)

let order_terms lp is_generate = 

  (* treating first the terms from the positive literals  *)
  let neg_terms, pos_terms = List.partition (fun ((b, _, _), _) -> b ) lp in
  let pos_subterms' = neg_terms @ pos_terms in
  
  let to_sort_terms, lt = 
    if !dico_infs_flag && is_generate
    then List.partition (fun (_, t) -> try List.mem t#head !list_ind_priorities with Failure "head" -> let () = buffered_output ("\n t = "
    ^ t#string) in  false) pos_subterms' 
    else pos_subterms', []

  in
  let fn_sort x l  = 

(*     let () =  buffered_output (List.fold_left (fun x (p, t) -> x ^ (sprint_clausal_position p) ^ "( t = " ^ t#string ^ ")" ^ " " ) *)
(*       ("\nfn_sort : adding " ^ ((fun (_, t) -> t#string) x) ^ " to : \n") l) in *)

    let fn_inf (_, t1) (_, t2) = 
      let b = inf_sym t2#head t1#head in 
(*       let () = buffered_output ("\n " ^ t1#string ^ " < " ^ t2#string ^ ": " ^ (string_of_bool b)) in  *)
      b 
    in
    let fn_eq (_, t1) (_, t2) = (t1#head = t2#head) in
    insert_sorted_dup fn_inf fn_eq x l 
  in

(*   let () = buffered_output (List.fold_left (fun x (p, t) -> x ^ (sprint_clausal_position p) ^ "( t = " ^ t#string ^ ")" ^ " " ) ("\nPOS TERMEs [" ^ *)
(*   (string_of_int c#number) ^"] are: ") pos_subterms) in *)

  let pos_sorted = (List.fold_right (fun el l -> fn_sort el l) to_sort_terms []) @ lt in


(*   let () = buffered_output (List.fold_left (fun x (p, t) -> x ^ (sprint_clausal_position p) ^ "( t = " ^ t#string ^ ")" ^ " " ) ("\nPOS SORTED [" ^ *)
(*   (string_of_int c#number) ^"] are: ") pos_sorted) in *)

(*   let () = buffered_output "dico_order:"; *)
(*   dico_infs#iter *)
(*     (fun k v -> *)
(*        print_string (dico_const_string#find k); *)
(*        print_string " --> "; *)
(*        buffered_output (sprint_list ", " dico_const_string#find *)
(* 	 (* (fun x -> string_of_int x) *) v)) *)
  (*   in *)
  
  pos_sorted
    
(* Pretty printer in a CAML-like form. Takes care of integers and ac symbols. *)
let rec compute_string_caml t =
  
  let rec fn2 f v l_ar r_ar l =
    let rec fn3 l =
      let l_args, r_args = try list_split_at_n l_ar l with Failure "list_split_at_n" -> failwith "compute_string_caml" in
      let s = match l_args with
          [] -> ""
	    (*           | [h] -> if h#depth = 1 then (compute_string_caml h) ^ " " else "(" ^ (compute_string_caml h)^ ") " *)
        | _ -> if is_constructor f then  (sprint_list ", " (fun x -> compute_string_caml x) l_args)  else "(" ^ v ^" " ^ (sprint_list " " (fun x -> compute_string_caml x) l_args) ^ ") " 
      and s' =
        if List.length r_args = r_ar
        then
          match r_args with
              [] -> []
		(*               | [h] -> if h#depth = 1 && l_ar = 1 then [(compute_string_caml h)] else ["(" ^ (compute_string_caml h) ^ ")"] *)
            | _ -> if is_constructor f then [ (sprint_list ", " (fun x -> compute_string_caml x) r_args) ] else ["(" ^v ^ " " ^ (sprint_list " " (fun x -> compute_string_caml x) r_args) ^ ")"]
        else
          fn3 r_args in
      s::s' 
    in
    let fn' sep l =
      let rec fn =
	function
	    [] -> ""
	  | [h] -> "(" ^ h ^ ")"
	  | h :: t -> "(" ^ h ^ sep ^ fn t ^ ")"
      in
      fn l
    in      
    if is_constructor f then fn' (v ^ " ") (fn3 l) else sprint_string_list (" ") (fn3 l) in

      match t#content with
        Var_exist (x, s) -> sprint_var x s false | Var_univ (x, s) -> sprint_var x s true
      | Term (f, [], _) -> let v = try dico_const_string#find f with Not_found -> failwith ((string_of_int f) ^ ":  this symbol raised Not_found in compute_string_caml (1)")  in v
      | Term (f, l, _) ->
          if !specif_LA_defined && t#is_a_natural
          then string_of_int (t#depth - 1)
          else
            let l_ar, r_ar = try dico_arities#find f  with Not_found -> failwith "raising Not_found in compute_string_caml (2)" 
            and v = try dico_const_string#find f  with Not_found -> failwith "raising Not_found in compute_string_caml (3)" in
            if symbol_is_ac f
            then
              if l_ar = 0 && r_ar = 2
              then
                let l' = t#get_ac_f_args f in
                let ls = List.map (fun x -> compute_string_caml x) l' in
                (try dico_const_string#find f with Not_found -> failwith "raising Not_found in compute_string_caml (4)")  ^ " (" ^ (sprint_string_list ", " ls) ^ ")"
              else if l_ar = 1 && r_ar = 1
              then
                let l' = t#get_ac_f_args f in
                let ls = List.map (fun x -> compute_string_caml x) l' in
                sprint_string_list (" " ^ v ^ " ") ls
              else invalid_arg "string"
            else
              let _, _ = try list_split_at_n l_ar l with Failure "list_split_at_n" -> failwith "compute_string_caml" in
              fn2 f v l_ar r_ar l

