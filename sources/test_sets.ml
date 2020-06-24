
(*
   * Project: Spike ver 0.1
   * File: test_sets.ml
   * Content: induction positions, induction variables, test sets...
*)

open Values
open Io
open Diverse
open Dicos
open Symbols
open Terms
open Order
open Literals
open Clauses
open Dummies
	
(* Generate constructor terms of maximum depth d, satisfying:
   - all variables are at depth d
   - only variables are at depth d *)
let generate_constructor_terms d s expand_nullary =
  let _ = yy_tmp_param_sorts := [] in
  let tmp = ref ([]: Symbols.const list) in 
  let get_constr s = 
    let () = tmp := [] in
    let () = dico_const_profile#iter
      (fun k v ->
	if is_constructor k then 
	  let _ = yy_tmp_param_sorts := [] in
	  let sort_k = List.hd v in
	  if equal_sorts sort_k s then 
	    tmp := k :: !tmp 
	  else ()
      )
    in
    !tmp
  in
  let rec fn i s =
    (match s with 
	Def_sort _ -> 
	  if i = d then
	    if is_nullary_sort s && expand_nullary then
	      let l = try List.filter is_constructor (dico_const_profile#find_keys [s]) with Not_found -> [] in
	      match l with
		  [] -> [ new term (Var_univ (newvar (), s)) ]
		| _ -> List.map (fun x -> new term (Term (x, [], s))) l
	    else [ new term (Var_univ (newvar (), s)) ]
	  else (* i < d *)
	    let l = try List.filter is_constructor (dico_const_sort#find_keys s) with Not_found -> [] in
	    List.flatten (List.map (fn2 i s) l)
      | Abstr_sort0 _ -> [ new term (Var_univ (newvar (), s)) ]
      | Abstr_sort1 _ | Abstr_sort2 _ -> 
	  if i = d then [ new term (Var_univ (newvar (), s)) ] 
	  else (* i < d *)
	    let lsymb = get_constr s in 
(* 	    let () = print_string ("\n the symbols of sort " ^ (sprint_sort s) ^ " are : "); List.iter (fun x -> print_string *)
(* 		(dico_const_string#find x)) lsymb in *)
	    List.flatten (List.map (fn2 i s) lsymb)
    )
  and fn2 i s f =
    let _ = yy_tmp_param_sorts := [] in
    let profile = try dico_const_profile#find f with Not_found -> failwith "raising Not_found in generate_constructor_terms" in 
    if profile = [] then failwith "generate_constructor_terms" 
    else

	let dummy = try unify_sorts (Actual_sort (List.hd profile)) s with  Failure _ ->  failwith "generate_constructor_terms"  in
	let p = List.map (fun x -> expand_sorts x) (List.tl profile) in
	match p with
	    [] -> [ new term (Term (f, [], dummy)) ]
	  | _ ->
	      let args = List.map (fn (i + 1)) p in
	      let sets_of_args = megamix args in
	      List.map (fun l -> new term (Term (f, l, dummy))) sets_of_args
	
  in
  if d = 0
  then []
  else fn 1 s
    
let cs_terms () =
  try 
    let () = print_string "Entrer depth: " in
    let d = read_int () in
    let () = print_string "enter sort: " in
    let st = read_line () in
    let s = try dico_sort_string#find_key st with Failure _ -> failwith "raising find_key in cs_terms" in
    let l = generate_constructor_terms d s true in
    let () = buffered_output ("Constructor terms: depth " ^ (string_of_int d)
    ^ ", sort " ^ (dico_sort_string#find s) ^ "\n\t"
    ^ (sprint_list "\n\t" (fun x -> x#string) l)) in
    ()
  with Not_found -> failwith "raising Not_found in cs_terms"
    
(* Symbols on which induction will be tried. *)
type induction_position_specification =
    Ind_pos_void
  | Ind_pos_position of (const * (const * int) list) list
  | Ind_pos_path of path list


let sprint_induction_position_specification = function
    Ind_pos_void -> "(VOID)"
  | Ind_pos_position l -> "Ind_pos_position (" ^ (sprint_list " / " (fun (f, p) -> ( try dico_const_string#find f with Not_found
    -> failwith "raising Not_found in sprint_induction_position_specification") ^ " (" ^
      (sprint_position (List.map snd p)) ^ ")") l) ^ ")"
  | Ind_pos_path l -> "Ind_pos_path (" ^ (sprint_list " " sprint_path l) ^ ")"

let merge_induction_positions p p' =
  match p, p' with
    Ind_pos_position l, Ind_pos_position l' -> Ind_pos_position (generic_merge_sorted_lists l l')
  | Ind_pos_path l, Ind_pos_path l' -> Ind_pos_path (generic_merge_sorted_lists l l')
  | Ind_pos_void, Ind_pos_position _ | Ind_pos_void, Ind_pos_path _|Ind_pos_void, Ind_pos_void-> p'
  | Ind_pos_position _, Ind_pos_void | Ind_pos_path _, Ind_pos_void -> p
  | Ind_pos_position _, Ind_pos_path _| Ind_pos_path _, Ind_pos_position _ -> failwith "merge_induction_positions"

let induction_symbols_priorities = ref ([]: induction_position_specification list)

let print_induction_symbols_priorities () =
  buffered_output (sprint_list "\n" sprint_induction_position_specification !induction_symbols_priorities)

let fill_default_induction_positions_v0 lop =
  let () = buffered_output "Computing default priorities" in
  let l = ref [] in
  let fn f l1 =
    let p = list_remove_doubles (=) (List.flatten l1) in
    l := generic_merge_sorted_lists !l (List.map (fun x -> f, x) p) in
  let () = dico_ind_positions_v0#iter fn in
  let () = all_induction_positions := !l in
  let lop' = List.filter (function Ind_pos_void -> false | Ind_pos_path _| Ind_pos_position _ -> true) lop in
  if not (List.exists (function Ind_pos_position _ -> true | Ind_pos_void | Ind_pos_path _ -> false) lop')
  then
    let () = buffered_output "Using default priorities" in
    induction_symbols_priorities := [ Ind_pos_position !l ]
  else induction_symbols_priorities := lop'


let fill_default_induction_positions = ref fill_default_induction_positions_v0

let sprint_fun_path (f, p) = try (dico_const_string#find f) ^ " @ " ^ (sprint_int_list p) with Not_found -> failwith "raising Not_found in sprint_fun_path"
  
let compute_induction_posvar (t:term) =
  let k = t#head in
  let l1 = try dico_ind_positions_v0#find k  with Not_found -> [] in
  let lpos = list_remove_doubles (=) (List.flatten l1) in 
  let lpos' = List.map (fun l -> let l' = List.map snd l in list_all_but_last_el l')  lpos in
  let all_pos = list_remove_doubles (=) lpos' in
  let rec fn pos = 
    try 
      let trm =  t#subterm_at_position pos in
      if not trm#is_term then [trm, pos]
      else []
    with Failure _ -> []
  in
  List.fold_right (fun p l -> let res = fn p in if res = [] then l else insert_sorted ( = ) ( < ) (List.hd res) l) all_pos []


  (* Pattern Trees  *)
  

let update_dico_rules () = 
  let fn1 k = 
    let rec fn l =
      match l with
	  [] -> ()
	| c :: tl -> 
	    let () = fn tl in
	    let lhs = c#lefthand_side in
	    let head = lhs#head in
	    if k = head then 
	      try 
		let tmp = dico_rules#find k in 
		let () = dico_rules#remove k in
		dico_rules#add k (c :: tmp) 
	      with Not_found -> (dico_rules#add k [c])
		
    in
    fn rewrite_system#content
  in      
  dico_const_string#iter (fun k _ -> if is_defined k then fn1 k)  



(* OBSERVATIONAL STUFF *)


(* Selector *)
let test_set_version = ref 0

(* Some dictionaries for test sets.
   Explanations about the different versions are in terms.ml file *)
let dico_test_set_v0 = (new dictionary 101: (sort, term list) dictionary)
let dico_test_set_v1 = (new dictionary 101: ((int * sort), term list) dictionary)
let dico_test_set_v2 = (new dictionary 101: (path, term list) dictionary)

let print_dico_test_set_v0 () =
  print_dico_ind_positions_v0 () ;
  let rec f s l = buffered_output ((try dico_sort_string#find s with Not_found -> failwith "print_dico_test_set_v0")  ^ " [" ^ (sprint_sort s) ^ "]\n" ^
  (sprint_list "\n" (fun x -> "\t" ^ x#string) l)) in
  let () = buffered_output "dico_test_set_v0 =" in
  dico_test_set_v0#iter f
    
let print_dico_test_set_v1 () =
  print_dico_ind_positions_v1 () ;
  let rec f (d, s) l = buffered_output ("(" ^ (string_of_int d) ^ ", " ^ (try dico_sort_string#find s with Not_found -> failwith "print_dico_test_set_v0") ^ ")\n" ^
                                        (sprint_list "\n" (fun x -> "\t" ^ x#string) l)) in
  let () = buffered_output "dico_test_set_v1 =" in
  dico_test_set_v1#iter f

let print_dico_test_set_v2 () =
  let rec f p l = buffered_output ((sprint_path p) ^ "\n" ^
                                   (sprint_list "\n" (fun x -> "\t" ^ x#string) l)) in
  let () = buffered_output "dico_test_set_v2 =" in
  dico_test_set_v2#iter f

let print_dico_test_set = ref print_dico_test_set_v0


let fill_default_induction_positions_v1 lop =
  let () = buffered_output "Computing default priorities" in
  let l = ref [] in
  let fn p _ =
    l := generic_insert_sorted p !l in
  let () = dico_ind_positions_v1#iter fn in
  let () = all_induction_paths := !l in
  let lop' = List.filter (function Ind_pos_void -> false | Ind_pos_position _ | Ind_pos_path _ -> true) lop in
  if not (List.exists (function Ind_pos_path _ -> true | Ind_pos_void | Ind_pos_position _ -> false) lop')
  then
    let () = buffered_output "Using default priorities" in
    induction_symbols_priorities := [ Ind_pos_path !l ]
  else induction_symbols_priorities := lop'

let fill_default_induction_positions_v2 lop =
  let () = buffered_output "Computing default priorities" in
  let l = ref [] in
  let fn p _ =
    l := generic_insert_sorted p !l in
  let () = dico_test_set_v2#iter fn in
  let () = all_induction_paths := !l in
  let lop' = List.filter (function Ind_pos_void -> false | Ind_pos_position _| Ind_pos_path _ -> true) lop in
  if not (List.exists (function Ind_pos_path _ -> true | Ind_pos_void | Ind_pos_position _ -> false) lop')
  then
    let () = buffered_output "Using default priorities" in
    induction_symbols_priorities := [ Ind_pos_path !l ]
  else induction_symbols_priorities := lop'


(* Induction variables of a term t w.r.t. the dictionary dico_ind_positions_v0.
   We search the term only once. *)
let induction_variables_v0 los (tr: term) =

  let is_ind_pos (x,s,b) (f, p) =
    if List.mem (f, p) los
    then
      try
        let () = buffered_output (!indent_string ^ (sprint_var x s b) ^ " of sort " ^ (try dico_sort_string#find s with Not_found -> failwith "print_dico_test_set_v0") ^
                                  " is at induction position " ^ (sprint_position (List.map snd p)) ^
                                  " of " ^ (try dico_const_string#find f with Not_found -> failwith "induction_variables_v0")) in
        true
      with Not_found -> false
    else false in
  let rec fn l t =
    match t#content with
      Var_exist (x, s) ->
        if List.exists (is_ind_pos (x,s,false)) l
        then [(x, s, false)]
        else []
      | Var_univ (x, s) ->
        if List.exists (is_ind_pos (x,s,true)) l
        then [(x, s, true)]
        else []
    | Term (f, args, _) ->
        let l' = (f, [])::l in
        fn2 l' args

  and fn2 l =
    let rec fn3 i = function
        [] -> []
      | h::t ->
          let l' = List.map (fun (f, l'') -> f, (0, i) :: l'') l in
          generic_merge_sorted_lists (fn l' h) (fn3 (i + 1) t) in
    fn3 0 in
  match tr#content with
      Var_exist (x, s) -> [(x, s, false)]
    |  Var_univ (x, s) -> [(x, s, true)]
    | Term (_, _, _) ->
	let l' = fn [] tr in
	if !exclude_nullary_mode
	then l'
	else generic_merge_sorted_lists (List.filter is_nullary tr#variables) l'

(* Induction variables of a term, version 1.
   We check for each variable path in the term if it is a suffix of an induction position (path in this case).
   We return the associated key in the dictionary.
   Check is done w.r.t. dico_ind_positions_v1.
   Return type is (var * (depth * sort)).
*)
let induction_variables_v1 los (t:term) =
  let rec fn = function
      [] -> []
    | ((x, s, _), p)::t ->
        if not !exclude_nullary_mode && is_nullary_sort s
        then
          let d = fst (try dico_nullary_individuals#find s with Not_found -> failwith "induction_variables_v1") in
          max_assoc x (d, s) (fn t)
        else
          let l = List.filter (list_is_suffix p) los in
          try
            let ds =  generic_list_max (try List.map dico_ind_positions_v1#find l with Not_found -> failwith "induction_variables_v1") in
            max_assoc x ds (fn t)
          with (Failure _) -> fn t in
  fn t#variable_paths

(* Induction variables of a term, version 2.
   We check for each variable path in the term if it is a suffix of an induction position (path in this case).
   We return the variable, and the associated key in the dictionary.
   Check is done w.r.t. dico_test_set_v2 (no sharing in this case) *)
let induction_variables_v2 (t:term) =
  let v = List.map (fun ((x, _, _), p) -> x, p) t#variable_paths
  and l = ref [] in
  let fn x vp ip _ =
    if list_is_suffix vp ip
    then l := generic_assoc_insert_sorted (x, ip) !l
    else () in
  let fn2 (x, vp) = dico_test_set_v2#iter (fn x vp) in
  let () = List.iter fn2 v in
  !l

(* Updates the test set dictionary. In this version, only the sort,
   and associated system depth (capital D) are relevant *)
let compute_test_set_v0 rw_s =
  rw_s#compute_induction_positions_v0 ;
  let rec fn = function
      [] -> ()
    | (s, d)::t ->
        let () =
          try
            let _ = dico_test_set_v0#find s in
            ()
          with Not_found ->
            let l = generate_constructor_terms d s true in
            dico_test_set_v0#add s l in
        fn t in
  fn rw_s#capital_d_per_sort

(* Updates the test set dictionary.
   In this version, the whole path to the induction position is relevant *)
let compute_test_set_v1 rw_s =
  rw_s#compute_induction_positions_v1 ;
  let fn _ (d, s) =
    try
      let _ = dico_test_set_v1#find (d, s) in
      ()
    with Not_found ->
      let l = generate_constructor_terms d s true in
      dico_test_set_v1#add (d, s) l in
  dico_ind_positions_v1#iter fn

(* Compute test sets dictionary. These are all subterms at inductive positions *)
let compute_test_set_v2 rw_s =
  let term_eq t = t#equal in
  let fn (p, t) =
    try
      let l = dico_test_set_v2#find p in
      let l' = list_union term_eq (produce_nullary_instances t#rename) l in
      dico_test_set_v2#remove p ;
      dico_test_set_v2#add p l'
    with Not_found ->
      dico_test_set_v2#add p (produce_nullary_instances t#rename) in
  let fn2 c =

    let () = buffered_output ("Considering axiom " ^ c#string) in

    let lhs = c#lefthand_side
 (* and l = uncouple_list (List.map (fun x -> x#both_sides) c#negative_lits) *) (* REMOVED *)
 (* in let l' = List.flatten (List.map (fun x -> x#ind_positions_v2) (lhs::l)) *) (* REMOVED *) in
    List.iter fn lhs#ind_positions_v2 in
  let () = rw_s#iter fn2
  and fn3 p l =
    try
      let _ = list_special_exists (fun x -> x#var_content) (Failure "var_content") l in
      dico_test_set_v2#remove p
    with (Failure _) -> () 
      | Not_found -> failwith "raising Not_found in compute_test_set_v2" in
  dico_test_set_v2#iter fn3

let compute_test_set = ref (fun () -> compute_test_set_v0 rewrite_system)

(* Checks whether we have induction variables in one term.
   Dependant on the version of test sets we use *)
let has_induction_variables_v0 t =
  let v = induction_variables_v0 !all_induction_positions t in
  v <> []
let has_induction_variables_v1 (t:term) = induction_variables_v1 !all_induction_paths t <> []
let has_induction_variables_v2 (t:term) = induction_variables_v2 t <> []
let has_induction_variables = ref has_induction_variables_v0

(* Checks whether two terms have the same induction variables *)
let have_same_induction_variables_v0 t t' = induction_variables_v0 !all_induction_positions t = induction_variables_v0 !all_induction_positions t'
let have_same_induction_variables_v1 t t' = induction_variables_v1 !all_induction_paths t = induction_variables_v1 !all_induction_paths t'
let have_same_induction_variables_v2 t t' = induction_variables_v2 t = induction_variables_v2 t'
let have_same_induction_variables = ref have_same_induction_variables_v0

(* Generate test substitutions *)
let generate_test_substitutions_core_v0 v =
  let fn (x, s, _) =
    try
      let ts = dico_test_set_v0#find s in
      let ts' = List.map (fun x -> x#rename) ts in
      List.map (fun tr -> x, tr) ts'
    with Not_found -> [] in
  let l = List.map fn v in
  megamix l

let generate_test_substitutions_v0 los t =
  match los with
    Ind_pos_position l -> 
      let l' = (induction_variables_v0 l t) in
      generate_test_substitutions_core_v0 l'
  | Ind_pos_void | Ind_pos_path _ -> failwith "generate_test_substitutions_v0"

let generate_test_substitutions_for_clause_v0 los c =
  match los with
    Ind_pos_position l ->
      let lt = c#all_terms in
      let lt' = List.map (induction_variables_v0 l) lt in
      let v = generic_merge_set_of_lists lt' in
      generate_test_substitutions_core_v0 v
  | Ind_pos_void | Ind_pos_path _ -> failwith "generate_test_substitutions_for_clause_v0"

let generate_test_substitutions_core_v1 v =
  let fn (x, ds) =
    let ts = try dico_test_set_v1#find ds with Not_found -> snd (try dico_nullary_individuals#find (snd ds) with Not_found ->
      failwith "generate_test_substitutions_core_v1")  in
    let ts' = List.map (fun x -> x#rename) ts in
    List.map (fun tr -> x, tr) ts' in
  let l = List.map fn v in
  megamix l

let generate_test_substitutions_v1 los t =
  match los with
    Ind_pos_path l ->
      generate_test_substitutions_core_v1 (induction_variables_v1 l t)
  | Ind_pos_void | Ind_pos_position _ -> failwith "generate_test_substitutions_v1"

let generate_test_substitutions_for_clause_v1 los c =
  match los with
    Ind_pos_path l ->
      let lt = c#all_terms in
      let v = List.fold_left max_assoc_merge [] (List.map (induction_variables_v1 l) lt) in
      generate_test_substitutions_core_v1 v
  | Ind_pos_void | Ind_pos_position _ -> failwith "generate_test_substitutions_for_clause_v1"

let induction_sets los (t:term) =
  let v = List.map (fun ((x, _, _), p) -> x, p) t#variable_paths
  and l = ref [] in
  let fn x vp ip ts =
    if vp = ip && (* generic_list_sorted_mem (fst (List.hd vp)) los *) List.mem vp los
    then
      let () = buffered_output (!indent_string ^ (sprint_var x (Def_sort 0) true) ^ " is at induction position " ^ (sprint_path ip)) in
      l := generic_assoc_insert_sorted (x, ts) !l
    else () in
  let fn2 (x, vp) = dico_test_set_v2#iter (fn x vp) in
  let () = List.iter fn2 v in
  !l

let generate_test_substitutions_core_v2 l =
  let rec fn (x, tss) =
    let tss' = List.fold_left (list_union (fun x -> x#equal)) [] tss in
    let tss'' = List.map (fun x -> x#rename) tss' in
    List.map (fun tr -> x, tr) tss'' in
  List.map fn l

let generate_test_substitutions_v2 los t =
  match los with
    Ind_pos_path l ->
      let l = generate_test_substitutions_core_v2 (induction_sets l t) in
      megamix l
  | Ind_pos_void | Ind_pos_position _ -> failwith "generate_test_substitutions_v1"

let generate_test_substitutions_for_clause_v2 los (c: (peano_context) clause) =
  match los with
    Ind_pos_path l ->
      let lt = c#all_terms in
      let l' = List.map (induction_sets l) lt in
      let l'' = List.fold_right generic_assoc_merge_sorted_lists l' [] in
      let v = generate_test_substitutions_core_v2 l'' in
      megamix v
  | Ind_pos_void | Ind_pos_position _ -> failwith "generate_test_substitutions_for_clause_v2"

(* Generate test substitutions *)
let generate_test_substitutions = ref (fun los -> generate_test_substitutions_v0 los)
let generate_test_substitutions_for_clause = ref (fun los -> generate_test_substitutions_for_clause_v0 los)

let update_test_set_version = function
    0 ->
      let () = test_set_version := 0
      and () = fill_default_induction_positions := fill_default_induction_positions_v0
      and () = has_induction_variables := has_induction_variables_v0
      and () = have_same_induction_variables := have_same_induction_variables_v0
      and () = generate_test_substitutions := generate_test_substitutions_v0
      and () = generate_test_substitutions_for_clause := generate_test_substitutions_for_clause_v0
      and () = compute_test_set := fun () -> compute_test_set_v0 rewrite_system
      and () = print_dico_test_set := print_dico_test_set_v0 in
      ()
  | 1 ->
      let () = test_set_version := 1
      and () = fill_default_induction_positions := fill_default_induction_positions_v1
      and () = has_induction_variables := has_induction_variables_v1
      and () = have_same_induction_variables := have_same_induction_variables_v1
      and () = generate_test_substitutions := generate_test_substitutions_v1
      and () = generate_test_substitutions_for_clause := generate_test_substitutions_for_clause_v1
      and () = compute_test_set := fun () -> compute_test_set_v1 rewrite_system
      and () = print_dico_test_set := print_dico_test_set_v1 in
      ()
  | 2 ->
      let () = test_set_version := 2
      and () = fill_default_induction_positions := fill_default_induction_positions_v2
      and () = has_induction_variables := has_induction_variables_v2
      and () = have_same_induction_variables := have_same_induction_variables_v2
      and () = generate_test_substitutions := generate_test_substitutions_v2
      and () = generate_test_substitutions_for_clause := generate_test_substitutions_for_clause_v2
      and () = compute_test_set := fun () -> compute_test_set_v2 rewrite_system
      and () = print_dico_test_set := print_dico_test_set_v2 in
      ()
  | _ -> raise (Arg.Bad "test sets version must be 0, 1, or 2")

