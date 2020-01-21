type token =
  | TOK_EOF
  | TOK_COLUMN
  | TOK_COMA
  | TOK_ARROW
  | TOK_SEMICOLUMN
  | TOK_LPAR
  | TOK_RPAR
  | TOK_IMPLIES
  | TOK_EQUAL
  | TOK_DIFF
  | TOK_AND
  | TOK_OR
  | TOK_QUESTION_MARK
  | TOK_AROBAT
  | TOK_LBRACKET
  | TOK_RBRACKET
  | TOK_SPECIF
  | TOK_SORTS
  | TOK_CONSTRUCTORS
  | TOK_FUNCTIONS
  | TOK_FUNCTION_PROPS
  | TOK_EQUIV
  | TOK_STATUS
  | TOK_AXIOMS
  | TOK_OBS_SORTS
  | TOK_CONJECTURES
  | TOK_COMPLETE_TERMS
  | TOK_LEMMAS
  | TOK_STRATEGIES
  | TOK_USE
  | TOK_PROPERTIES
  | TOK_PRIORITIES
  | TOK_IND_PRIORITIES
  | TOK_TEST_SETS
  | TOK_NULLARY_SORTS
  | TOK_NORM
  | TOK_RPOCOMPARE
  | TOK_COMPARE
  | TOK_MAX_COMPARE
  | TOK_STOP_ON_CLAUSE
  | TOK_EXTRACT
  | TOK_MATCH
  | TOK_AC_SUBSUMES
  | TOK_CRITICAL_CONTEXT_SETS
  | TOK_CRITIC
  | TOK_HYPOTHESES
  | TOK_LEFTRIGHT
  | TOK_MULTISET
  | TOK_RIGHTLEFT
  | TOK_AC
  | TOK_ASSOC
  | TOK_TRY
  | TOK_SATURATE
  | TOK_ON
  | TOK_REDUCTION
  | TOK_REPEAT
  | TOK_REPEAT_PLUS
  | TOK_TAUTOLOGY
  | TOK_GENERATE
  | TOK_GENERATE_EQ
  | TOK_GENERATE_OBS
  | TOK_PARTIAL_CASE_REWRITING
  | TOK_TOTAL_CASE_REWRITING
  | TOK_CONTEXTUAL_REWRITING
  | TOK_CONGRUENCE_CLOSURE
  | TOK_EQUATIONAL_REWRITING
  | TOK_REWRITING
  | TOK_NEGATIVE_DECOMPOSITION
  | TOK_POSITIVE_DECOMPOSITION
  | TOK_POSITIVE_CLASH
  | TOK_ELIMINATE_TRIVIAL_LITERAL
  | TOK_ELIMINATE_REDUNDANT_LITERAL
  | TOK_AUTO_SIMPLIFICATION
  | TOK_COMPLEMENT
  | TOK_SUBSUMPTION
  | TOK_AUGMENTATION
  | TOK_NEGATIVE_CLASH
  | TOK_START_WITH
  | TOK_AUGMENTATION_STRATEGY
  | TOK_GOTO
  | TOK_ADDPREMISE
  | TOK_SIMPLIFY
  | TOK_GREATER
  | TOK_DELETE
  | TOK_ID
  | TOK_PRINT_GOALS
  | TOK_PRINT_CAML
  | TOK_PRINT_GOALS_HISTORY
  | TOK_OPEN_SUBSTITUTION
  | TOK_CLOSE_SUBSTITUTION
  | TOK_IDENT of (string)
  | TOK_STRING of (string)

open Parsing;;
let _ = parse_error;;
# 9 "sources/parser.mly"

open Values
open Context
open Critical_context_set
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Terms_parser
open Order
open Literals
open Clauses
open Dummies
open Strategies
open Test_sets
open Shell
open Extract

let introduce_var_exist c = 
  let rec fn_term lv t = 
    match t#content with
	Var_exist _ -> t
      | Var_univ (i, s) -> if List.mem (i, s, true) lv then t else new term (Var_exist (i, s))
      | Term (i, l, s) -> new term (Term (i, List.map (fn_term lv) l, s))
  in
  let fn_lit lv lit = 
    match lit#content with
	Lit_rule (t1, t2) -> new literal (Lit_rule ((fn_term lv t1), (fn_term lv t2)))
      | Lit_equal (t1, t2) -> new literal (Lit_equal ((fn_term lv t1), (fn_term lv t2)))
      |	Lit_diff (t1, t2) -> new literal (Lit_diff ((fn_term lv t1), (fn_term lv t2)))
  in
  let (x, y, c') = c in
  let (n, p) = c'#content in
  let var_lhs = (c'#lefthand_side)#variables in
  let n' = List.map (fn_lit var_lhs) n in
  let p' = List.map (fn_lit var_lhs) p in
  let new_c' = new clause (n', p') [] ("",0,([],[])) in
  (x, y, new_c')

(* If no ordering is specified in the specification file, we use a total ordering based on symbol codes *)
let default_fill_order_dico () =
  let fn c = 
    let ldef_symb = all_nonvariable_symbols c in
    let lhs,rhs = c#both_sides in
    let lhs_head_symbol = 
      try 
	(match lhs#content with
	    Term (f, _, _) -> f
	  | Var_exist _| Var_univ _ -> failwith "default_fill_order_dico"
	)
      with Not_Horn -> failwith "default_fill_order_dico"
    in
    let r_cond_symb = try 
      remove_el ( = ) lhs_head_symbol ldef_symb 
    with Failure "remove_el" -> failwith "default_fill_order_dico"
    in
    let () = if !debug_mode then 
      let () = buffered_output c#string in
      let () = print_string "\n" in
      let () = print_int lhs_head_symbol in
      let () = print_string "\n" in
      let () = print_list ", " print_int r_cond_symb in
      let () = print_string "\n" in
      let () = flush stdout in
	()
    in
    
    let is_orientable = 
      try 
	let rhs_head_symbol = 
	  try 
	    (match rhs#content with
		 Term (f, _, _) -> f
	       | Var_exist _| Var_univ _ -> failwith "variable"
	    )
	  with Not_Horn -> failwith "default_fill_order_dico"
	in
	  not (List.mem lhs_head_symbol (try dico_order#find rhs_head_symbol with Not_found -> [])) 
      with Failure "variable" -> true 
    in
      if is_orientable then
	List.iter (dico_order#add_couple lhs_head_symbol) r_cond_symb
  in
  let () = buffered_output "Setting default greater order for symbols" in
  let () = flush stdout in
  let axioms = List.map (fun (_, _, x) -> x) !yy_axioms in
  let () = if !debug_mode then 
    let () = print_string "\n Current axioms :" in
    let () = print_clause_list axioms in
    let () = print_dico_const_string () in
      ()
  in
  let _ = List.iter fn axioms in
  let () = 
    try
      dico_order#merge_equivalence_relation dico_equivalence ;
    with (Failure "rehash") ->
      parse_failwith "there are incompatibilities between the order and equivalence relations"
  in
  if !debug_mode then 
    let () = print_dico_order () in
    let () = print_dico_equivalence () in
    ()

let share_variables s s' = 
  let rec fn s = 
    match s with
	Def_sort _ -> []
      | Abstr_sort0 str -> [str]
      | Abstr_sort1 (_, sort) -> fn sort
      | Abstr_sort2 (_, s1, s2) -> (fn s1) @ (fn s2)
  in 
  let lvar_s = fn s in
  let lvar_s' = fn s' in
  List.exists (fun x -> List.mem x lvar_s) lvar_s'
      

  (* to be continued  *)



(* Parse a positive integer *)
let parse_positive_int s =
  let i =
    try int_of_string s
    with (Failure "int_of_string") -> parse_failwith "not a positive integer"
  in if i < 0
  then parse_failwith "not a positive integer"
  else i

(* Get sort id from string *)
let find_sort_id s =
  try dico_sort_string#find_key s
  with Failure "find_key" -> 
    if not (* !specif_paramete
rized  *) true
    then parse_failwith ("unknown sort \"" ^ s ^ "\"") 
    else 
      let () = if !debug_mode then print_string ("\nWARNING: the sort " ^ s ^ " is parameterized") in
      Abstr_sort0 s


(* Get symbol id from string *)
let find_symbol_id s =
  try dico_const_string#find_key s
  with Failure "find_key" -> parse_failwith ("undefined symbol \"" ^ s ^ "\"")

  (* Provided an integer reference i, a value, and a (int, _) dictionary, we add the couple
     (i, v) if v is not already t here and increment i (decrement if negative), do nothing otherwise.
     Returns key *)
let selective_add d i v =
  try d#find_key v with
    Failure "find_key" -> let n = !i in d#add n v; if n >= 0 then incr i else decr i; n
;;

let selective_add_sort d i v =
  try d#find_key v with
    Failure "find_key" -> let n = !i in d#add (Def_sort n) v; if n >= 0 then incr i else decr i; Def_sort n
;;


  (* tests if there is a parameterized sort in the clause content c  *)
let test_well_founded_cl c = 
  let fn_sort s = 
    match s with
	Def_sort _ -> true
      | Abstr_sort0 _| Abstr_sort1 _ | Abstr_sort2 _ -> let () = buffered_output ("\nThe sort " ^ (sprint_sort s) ^ " is parameterized") in false 
  in
  let fn_term t = 
    match t#content with
	Var_exist (_, s) | Var_univ (_, s) -> fn_sort s
      | Term (_, _, s) -> fn_sort s
  in
  let fn_lit l = 
    match l#content with
	Lit_rule (t1, t2) -> (fn_term t1) && (fn_term t2)
      | Lit_equal (t1, t2) -> (fn_term t1) && (fn_term t2)
      | Lit_diff (t1, t2) -> (fn_term t1) && (fn_term t2)
  in 
  let (negs, poss) = c in
  List.fold_right (fun x y -> fn_lit x && y) (negs @ poss) true

(*
   * Given:
   * - a counter (either variables or constants)
   * - a string
   * - a list of sorts (might be empty)
   * - a sort
   * updates the dictionaries to create a symbol with the given profile
*)
let process_specif_symbol counter s (l, rs) =
  let sym, l_ar, r_ar = process_underscores s
  in begin
    try
      let _ = dico_const_string#find_key sym
      in parse_failwith ("symbol \"" ^ sym ^ "\" already defined")
    with Failure "find_key" -> ()
  end ;
  if (l_ar + r_ar) <> List.length l
  then parse_failwith ("mismatch between declared arities and profile")
  else () ;
  let v = selective_add dico_const_string counter sym in
  let new_profile = update_profile (rs::l) in
  let sort_v = List.hd new_profile in
  dico_const_profile#add v new_profile ;
  dico_const_sort#add v sort_v ;
  dico_arities#add v (l_ar, r_ar) 

let process_function_props list_symb prop =
  let fn id =  
      try
	let sym = dico_const_string#find_key id in
    	let l_ar, r_ar = dico_arities#find sym in
    	if ((l_ar = 0 && r_ar = 2) || (l_ar = 1 && r_ar = 1))
    	then dico_properties#add sym prop
    	else parse_failwith ("symbol \"" ^ id ^ "\" has a profile incompatible with its " ^ 
    	(match prop with Prop_ac -> "AC" | Prop_assoc -> "ASSOC" | Prop_peano -> "") ^ " properties")
      with Failure "find_key" -> parse_failwith ("symbol \"" ^ id ^ "\" is not defined")
	| Not_found -> failwith "raising Not_found in process_function_props"
  in
  let () =  assert (  prop =  Prop_ac or prop = Prop_assoc) in
  let _ = List.map fn list_symb in
  ()
          

      
(* Given a string and a status, update the status dictionary accordingly *)
let add_to_status_dico c st =
  try
    let old_st = dico_id_status#find c
    in if old_st = st
    then ()
    else parse_failwith ("attempt to define different statuses to symbol \""
                         ^ (dico_const_string#find c)
                         ^ "\"")
  with Not_found -> dico_id_status#add c st




(* In the case where an explicit type is given to a variable, check that it is compatible with the remaining equation *)
let check_explicit_type v s =
  (* Checks that it is not a functional symbol *)
  let () =
    try
      let _ = dico_const_string#find_key v
      in parse_failwith ("attempting to redefine sort of functional symbol " ^ v)
    with Failure "find_key" -> ()
  and id = code_of_var v
  and sort_id = find_sort_id s in
  try
    let sort_id2 = List.assoc id !yy_tmp_sorts in
    if sort_id <> sort_id2
    then parse_failwith ("conflicting sorts "
                         ^ s
                         ^ " (declared) and "
                         ^ (dico_sort_string#find sort_id2)
                         ^ " (infered) for symbol "
                         ^ v)
    else ()
  with Not_found ->
    yy_tmp_sorts := generic_insert_sorted (id, sort_id) !yy_tmp_sorts

(*
   * The core function: add a new incomplete tree at the first undefined node in "yy_incomplete_tree".
   * This new tree can be either a Variable node, or a new node with at the root the id of the given symbol,
   * and as arguments, as many trees as the left arity picked from the stack yy_terms_stack, and as many
   * Undefined nodes as the right arity
   * If no place can be found (the tree is complete), the whole tree is pushed into the stack, and yy_incomplete_tree
   * becomes the produced tree
   * When the whole term has been parsed, we should have an empty stack and a complete tree
*)
let add_to_incomplete_tree tk =
  let fn1 tk =
    let () = if !debug_mode then (print_string "\n incomplete tree >>>>>  "; print_term_token tk) else () in
    match tk with
	TT_ident s ->
          begin
            try
	      let id = dico_const_string#find_key s in
	      let l_ar, r_ar = dico_arities#find id in
	(* let () = buffered_output ("Popping " ^ (string_of_int l_ar) ^ " elements from stack") ; flush stdout in *)
	      let l_args = pop_n_times l_ar yy_terms_stack in
	      let r_args = list_init r_ar (Undefined: incomplete_tree pointer)
	      in 
	      Defined (Iterm (id, l_args @ r_args))
            with Failure "find_key"
	      | Not_found -> let id = code_of_var s in Defined (Ivar id)
          end
      | TT_tree t -> Defined t
  in 
  let rec fn h t tk =
    match h with
      Undefined -> (fn1 tk) :: t
    | Defined (Ivar _) -> h :: (fn2 tk t)
    | Defined (Iterm (s', l)) ->
        try
          let l' = fn2 tk l in
          (Defined (Iterm (s', l'))) :: t
        with Failure "fn2" ->
          h :: (fn2 tk t)
  and fn2 tk = function
      [] -> failwith "fn2"
    | h :: t -> fn h t tk 
  in 
  if incomplete_tree_is_complete !yy_incomplete_tree
  then
    begin
      if !debug_mode then 
	buffered_output ("Pushing " ^ (sprint_incomplete_tree_pointer !yy_incomplete_tree) ^ " into stack")
      else () ;
      Stack.push !yy_incomplete_tree yy_terms_stack ;
      yy_incomplete_tree := fn1 tk
    end
  else
    yy_incomplete_tree := List.hd (fn !yy_incomplete_tree [] tk)


let sprint_bool flag = match flag with true -> "True" | false -> "False"

(* We now process a list of identifiers (tokens) *) 
let process_term_tokens =
  let rec fn = function
      [] ->
	let empty_stack = Stack.length yy_terms_stack = 0 in
	let complete_tree = incomplete_tree_is_complete !yy_incomplete_tree in
        if  (not empty_stack) or not complete_tree
        then parse_failwith "badly formed term"
        else
          let t = !yy_incomplete_tree in
          let () = yy_incomplete_tree := Undefined in
          t
    | h::t ->
        let () = add_to_incomplete_tree h in
        fn t
  in fn

let is_param_defined_sort s = 
  match s with
      Def_sort  _ -> true
    | Abstr_sort0 _| Abstr_sort1 _ | Abstr_sort2 _ -> false


let is_param_sort1 s = 
  match s with
      Abstr_sort1 _ -> true
    | Def_sort _| Abstr_sort0 _ | Abstr_sort2 _ -> false

let is_param_sort0 s = 
  match s with
      Abstr_sort0 _ -> true
    | Def_sort _| Abstr_sort1 _ | Abstr_sort2 _  -> false

let is_param_sort2 s = 
  match s with
      Abstr_sort2 _ -> true
    | Abstr_sort1 _ | Abstr_sort0 _ | Def_sort _  -> false

let get_id_param_sort s = 
  match s with
      Abstr_sort1 (i, _) -> i
    | Abstr_sort2 (i, _, _) -> i
    | Def_sort _| Abstr_sort0 _ -> failwith "get_id_param_sort"
	(*
   * Typecheck an incomplete tree, infer type of variables.
   * In one case, we need to delay typechecking: when a literal of the form x = y is present.
   * It means that the actual terms creation must be delayed to the end of the parsing of an axiom / clause.
*)

let rec typecheck_incomplete_tree ps t =
  let () = if !debug_mode then buffered_output ("\nenter typecheck_incomplete_tree: the parameters ps and t are: " ^ ((sprint_param_sort ps) ^ "  " ^ (sprint_incomplete_tree_pointer t)))  in
  match t with 
      Undefined -> invalid_arg "typecheck_incomplete_tree"
    | Defined (Ivar x) -> ( 
        try 
          let s' = List.assoc x !yy_tmp_sorts in
          let new_s' = 
	    match ps with
		Actual_sort s'' -> 
		  (try
		    unify_sorts ps s'
		  with Failure "unify_sorts" ->  parse_failwith ("\nConflicting types: " ^ (sprint_sort s') ^ " and " ^ (sprint_sort s''))
		  )
            | Variable_sort x' -> (* We have a sort for y in x = y ; we update the sort of x_{E} *)
		let l = yy_tmp_equiv_dico#find x' in
		 let () = List.iter (fun v -> yy_tmp_sorts := generic_insert_sorted (v, s') !yy_tmp_sorts) l in
		 let () = yy_tmp_equiv_dico#remove x' in
		 s'
	  in
	  if x < 0 then new term (Var_exist (x, new_s')) else new term (Var_univ (x, new_s'))
        with Not_found ->
          let new_s' = match ps with
	      Actual_sort s'' -> 
		let new_s'' = expand_sorts s'' in
		let () = yy_tmp_sorts := generic_insert_sorted (x, new_s'') !yy_tmp_sorts in 
		new_s''
            | Variable_sort x' -> 
		let () = yy_tmp_equiv_dico#add_couple x x' in (* x has a fresh sort *)
		let () = param_sort_counter := !param_sort_counter + 1 in
		let str = ("'Undefined" ^ (string_of_int !param_sort_counter)) in
		let () = yy_tmp_sorts := generic_insert_sorted (x, Abstr_sort0 str) !yy_tmp_sorts in 
		Abstr_sort0 str 
	  in
	  if x < 0 then new term (Var_exist (x, new_s')) else new term (Var_univ (x, new_s'))
      )
    | Defined (Iterm (x, l)) ->
        let p = 
	  try 
	    dico_const_profile#find x
	  with Not_found -> parse_failwith ("constant " ^ (string_of_int x) ^ "not found in dico_const_profile")
        in 
	let p' =  update_profile p  in
	let s' = List.hd p'
        and a' = List.tl p' in
        let () = match ps with
            Actual_sort s'' ->
              (try let _ = unify_sorts ps s' in () with Failure "unify_sorts" -> 
(* 		let () = if !debug_mode then print_string ("\ncall of unify_sorts in parser.mly:  the list yy_tmp_param_sorts before application is : " ^ *)
(* 		(List.fold_right (fun (x, s) y -> (x ^ " has associated the sort " ^ (sprint_sort s) ^ ", " ^ y)) !yy_tmp_param_sorts "")) else () in  *)
		parse_failwith ("\n Error: sort " ^ (sprint_sort s'') ^ " is not unifiable with " ^ (sprint_sort s')) )
          | Variable_sort x' ->
              try
                let new_x' = yy_tmp_equiv_dico#find x' in
                List.iter (fun v -> yy_tmp_sorts := generic_insert_sorted (v, s') !yy_tmp_sorts) new_x'; 
                yy_tmp_equiv_dico#remove x'
              with Not_found ->
                yy_tmp_sorts := generic_insert_sorted (x', s') !yy_tmp_sorts
        in
	let new_s' = unify_sorts ps s' in
        let a'' = List.map (fun v -> Actual_sort v) a' in
        let terms_l = List.map2 typecheck_incomplete_tree a'' l in
	new term (Term (x, terms_l, new_s'))

let term_with_new_sort t s =
  match t#content with
      Var_exist (i, _) -> new term (Var_exist (i, s))
    | Var_univ (i, _) -> new term (Var_univ (i, s))
    | Term (i, l, _) -> new term (Term (i, l, s))

let literal_of_incomplete_terms lit = 
  let x, x', tlit = lit in
  let new_tx = x#expand_sorts in
  let new_tx' = x'#expand_sorts in 
  let s = try unify_sorts (Actual_sort new_tx#sort) new_tx'#sort with Failure "unify_sorts" -> failwith "literal_of_incomplete_terms" in
  let t = term_with_new_sort new_tx s in
  let t' = term_with_new_sort new_tx' s in
  let () = if !debug_mode then ((print_detailed_term t); (print_detailed_term t')) in
  match tlit with 
      Lit_equal (_, _) -> new literal (Lit_equal (t, t'))
    | Lit_rule (_, _) -> new literal (Lit_rule (t, t'))
    | Lit_diff (_, _) -> new literal (Lit_diff (t, t'))

(* Table of oracles (string, boolean reference) *)
let oracles_table = Hashtbl.create 13

let _ = List.iter (fun (kwd, tok) -> Hashtbl.add oracles_table kwd tok)
    [ ("system_is_sufficiently_complete",               system_is_sufficiently_complete) ;
      ("system_is_strongly_sufficiently_complete",      system_is_strongly_sufficiently_complete) ;
      ("system_is_ground_convergent",                   system_is_ground_convergent) ]

(* Table of tests (string, () -> ()) *)
let tests_table = Hashtbl.create 13
let _ = List.iter (fun (kwd, tok) -> Hashtbl.add tests_table kwd tok)
    [ ("do_sufficient_completeness_test",               sufficient_completeness_test) ;
      ("do_strongly_sufficient_completeness_test",      strongly_sufficient_completeness_test) ;
      ("do_ground_convergence_test",                    ground_convergence_test) ]
;;

(* returns a list of clauses by deleting the min and max symbols from c *)

let del_minmax c = 
  let rec delt_minmax t = 
    match t#content with
      | Var_univ _ | Var_exist _ -> [([], t)]
      | Term (f, l, s) -> 
	  let  megamix12 =
	    megamix (List.fold_right (fun t lres -> (delt_minmax t) :: lres) l [])
	  in
	  let res = List.fold_right (
	    fun l1'  lres -> 
	      if f == id_symbol_min || f == id_symbol_max then
		(* let _ = buffered_output ("Here delt_minmax is " ^ (dico_const_string#find f) ^ " and value is " ^ (string_of_int f)) in *)
		let (l1, t1) = List.hd l1' in
		let (l2, t2) = List.hd (List.tl l1') in
		let tless = new term (Term (id_symbol_less, [t1;t2], id_sort_bool)) in
		let tge = new term (Term (id_symbol_geq, [t1;t2], id_sort_bool)) in
		let litless = new literal (Lit_equal (tless, new term (Term (id_symbol_true, [], id_sort_bool)))) in
		let litge = new literal (Lit_equal (tge, new term (Term (id_symbol_true, [], id_sort_bool)))) in
		if f == id_symbol_min then (litless :: (l1@l2), t1) :: ((litge:: (l1@l2), t2) :: lres)
		else if f == id_symbol_max then (litless:: (l1@l2), t2) :: ((litge:: (l1@l2), t1) :: lres)
		else ((l1@l2), new term (Term (f, [t1;t2], s))) :: lres
		else
		  let nl, l' =  (List.fold_right (fun (l1,t) (ll, lt) -> (l1 @ ll, t::lt)) l1' ([],[])) in
		  (nl, new term (Term (f, l',s))) :: lres
	  )  megamix12 [] 
	  in
	  if res == [] then [([], t)] else res

  in
  let dellit_minmax lit = 
       match lit#content with
	 | Lit_equal (tl, tr) -> 
	   let tl' = delt_minmax tl in
	   let tr' = delt_minmax tr in
	   let megamix12 = megamix [tl'; tr'] in
	   List.fold_right (fun l lres -> 
	     let (l1, t1) = List.hd l in
	     let (l2, t2) = List.hd (List.tl l) in 
	     [(l1@l2), new literal (Lit_equal (t1, t2))] @ lres) megamix12 []
	 | Lit_rule (tl, tr) -> 
	   let tl' = delt_minmax tl in
	   let tr' = delt_minmax tr in
	   let megamix12 = megamix [tl'; tr'] in
	   List.fold_right (fun l lres -> 
	     let (l1, t1) = List.hd l in
	     let (l2, t2) = List.hd (List.tl l) in 
	     [(l1@l2), new literal (Lit_rule (t1, t2))] @ lres) megamix12 []
	 | Lit_diff (tl, tr) -> 
	   let tl' = delt_minmax tl in
	   let tr' = delt_minmax tr in
	   let megamix12 = megamix [tl'; tr'] in
	   List.fold_right (fun l lres -> 
	     let (l1, t1) = List.hd l in
	     let (l2, t2) = List.hd (List.tl l) in 
	     [(l1@l2), new literal (Lit_diff (t1, t2))] @ lres) megamix12 []
  in 
  let rec split_f l l' len = 
    if len == 0 then (l, l') 
    else 
      try 
	let l1 = List.hd l' in
	split_f (l1::l) (List.tl l') (len - 1)
      with Failure "hd" ->
	failwith "split_f"
  in
  let lnegs = c#negative_lits in
  let len_nlits = List.length lnegs in
  let lpos = c#positive_lits in
  let nlits_mm = List.map (fun l -> (dellit_minmax l)) lnegs in
  let npos_mm = List.map (fun l -> (dellit_minmax l)) lpos in
  let mm = megamix (nlits_mm @ npos_mm) in
    (* if nlits_mm == [] then npos_mm  *)
    (* else if npos_mm == [] then nlits_mm  *)
    (* else megamix (nlits_mm @ npos_mm) in *)
  List.map (fun ll -> 
    let (ln', lp') = split_f [] ll len_nlits in 
    let (ln1, ln) = List.fold_right (fun (lnegs, lit) (lln, llits) -> (lnegs @ lln, lit :: llits)) ln' ([],[])  in
    let (lp1, lp) = List.fold_right (fun (lposs, lit) (llp, llits) -> (lposs @ llp, lit :: llits)) lp' ([],[])  in
    let nlneg = lp1 @ ln1 @ ln in
    let nlpos = lp in
    let nlneg' = expand_sorts_list nlneg in
    let nlpos' = expand_sorts_list nlpos in
    let () = if not !specif_parameterized && not (test_well_founded_cl (nlneg', nlpos')) then 
      failwith "clause3: undefined types"
    in
    new clause (nlneg', nlpos') [] ("",0,([],[])) 
    (* c#build nlneg' nlpos' *)
  ) mm
    
# 659 "sources/parser.ml"
let yytransl_const = [|
  257 (* TOK_EOF *);
  258 (* TOK_COLUMN *);
  259 (* TOK_COMA *);
  260 (* TOK_ARROW *);
  261 (* TOK_SEMICOLUMN *);
  262 (* TOK_LPAR *);
  263 (* TOK_RPAR *);
  264 (* TOK_IMPLIES *);
  265 (* TOK_EQUAL *);
  266 (* TOK_DIFF *);
  267 (* TOK_AND *);
  268 (* TOK_OR *);
  269 (* TOK_QUESTION_MARK *);
  270 (* TOK_AROBAT *);
  271 (* TOK_LBRACKET *);
  272 (* TOK_RBRACKET *);
  273 (* TOK_SPECIF *);
  274 (* TOK_SORTS *);
  275 (* TOK_CONSTRUCTORS *);
  276 (* TOK_FUNCTIONS *);
  277 (* TOK_FUNCTION_PROPS *);
  278 (* TOK_EQUIV *);
  279 (* TOK_STATUS *);
  280 (* TOK_AXIOMS *);
  281 (* TOK_OBS_SORTS *);
  282 (* TOK_CONJECTURES *);
  283 (* TOK_COMPLETE_TERMS *);
  284 (* TOK_LEMMAS *);
  285 (* TOK_STRATEGIES *);
  286 (* TOK_USE *);
  287 (* TOK_PROPERTIES *);
  288 (* TOK_PRIORITIES *);
  289 (* TOK_IND_PRIORITIES *);
  290 (* TOK_TEST_SETS *);
  291 (* TOK_NULLARY_SORTS *);
  292 (* TOK_NORM *);
  293 (* TOK_RPOCOMPARE *);
  294 (* TOK_COMPARE *);
  295 (* TOK_MAX_COMPARE *);
  296 (* TOK_STOP_ON_CLAUSE *);
  297 (* TOK_EXTRACT *);
  298 (* TOK_MATCH *);
  299 (* TOK_AC_SUBSUMES *);
  300 (* TOK_CRITICAL_CONTEXT_SETS *);
  301 (* TOK_CRITIC *);
  302 (* TOK_HYPOTHESES *);
  303 (* TOK_LEFTRIGHT *);
  304 (* TOK_MULTISET *);
  305 (* TOK_RIGHTLEFT *);
  306 (* TOK_AC *);
  307 (* TOK_ASSOC *);
  308 (* TOK_TRY *);
  309 (* TOK_SATURATE *);
  310 (* TOK_ON *);
  311 (* TOK_REDUCTION *);
  312 (* TOK_REPEAT *);
  313 (* TOK_REPEAT_PLUS *);
  314 (* TOK_TAUTOLOGY *);
  315 (* TOK_GENERATE *);
  316 (* TOK_GENERATE_EQ *);
  317 (* TOK_GENERATE_OBS *);
  318 (* TOK_PARTIAL_CASE_REWRITING *);
  319 (* TOK_TOTAL_CASE_REWRITING *);
  320 (* TOK_CONTEXTUAL_REWRITING *);
  321 (* TOK_CONGRUENCE_CLOSURE *);
  322 (* TOK_EQUATIONAL_REWRITING *);
  323 (* TOK_REWRITING *);
  324 (* TOK_NEGATIVE_DECOMPOSITION *);
  325 (* TOK_POSITIVE_DECOMPOSITION *);
  326 (* TOK_POSITIVE_CLASH *);
  327 (* TOK_ELIMINATE_TRIVIAL_LITERAL *);
  328 (* TOK_ELIMINATE_REDUNDANT_LITERAL *);
  329 (* TOK_AUTO_SIMPLIFICATION *);
  330 (* TOK_COMPLEMENT *);
  331 (* TOK_SUBSUMPTION *);
  332 (* TOK_AUGMENTATION *);
  333 (* TOK_NEGATIVE_CLASH *);
  334 (* TOK_START_WITH *);
  335 (* TOK_AUGMENTATION_STRATEGY *);
  336 (* TOK_GOTO *);
  337 (* TOK_ADDPREMISE *);
  338 (* TOK_SIMPLIFY *);
  339 (* TOK_GREATER *);
  340 (* TOK_DELETE *);
  341 (* TOK_ID *);
  342 (* TOK_PRINT_GOALS *);
  343 (* TOK_PRINT_CAML *);
  344 (* TOK_PRINT_GOALS_HISTORY *);
  345 (* TOK_OPEN_SUBSTITUTION *);
  346 (* TOK_CLOSE_SUBSTITUTION *);
    0|]

let yytransl_block = [|
  347 (* TOK_IDENT *);
  348 (* TOK_STRING *);
    0|]

let yylhs = "\255\255\
\001\000\001\000\013\000\014\000\015\000\016\000\016\000\033\000\
\033\000\033\000\033\000\033\000\033\000\033\000\033\000\033\000\
\033\000\033\000\033\000\033\000\033\000\033\000\033\000\033\000\
\017\000\017\000\017\000\018\000\018\000\018\000\051\000\051\000\
\019\000\019\000\019\000\052\000\052\000\021\000\021\000\021\000\
\020\000\020\000\020\000\054\000\054\000\053\000\053\000\055\000\
\022\000\022\000\022\000\022\000\022\000\057\000\057\000\058\000\
\056\000\056\000\056\000\059\000\059\000\060\000\060\000\061\000\
\061\000\023\000\023\000\023\000\029\000\029\000\029\000\029\000\
\064\000\064\000\065\000\065\000\024\000\024\000\024\000\066\000\
\067\000\067\000\069\000\025\000\025\000\025\000\068\000\070\000\
\070\000\071\000\026\000\026\000\026\000\072\000\072\000\073\000\
\073\000\073\000\030\000\030\000\030\000\074\000\074\000\031\000\
\031\000\031\000\075\000\075\000\076\000\076\000\077\000\077\000\
\077\000\079\000\081\000\081\000\080\000\080\000\082\000\027\000\
\027\000\027\000\083\000\083\000\084\000\084\000\028\000\028\000\
\028\000\086\000\086\000\087\000\088\000\088\000\090\000\091\000\
\092\000\092\000\032\000\032\000\032\000\038\000\038\000\093\000\
\093\000\094\000\037\000\037\000\034\000\034\000\035\000\035\000\
\036\000\036\000\096\000\096\000\097\000\097\000\097\000\099\000\
\099\000\100\000\102\000\098\000\063\000\063\000\104\000\089\000\
\011\000\103\000\103\000\103\000\105\000\105\000\106\000\106\000\
\107\000\108\000\108\000\108\000\010\000\109\000\109\000\110\000\
\110\000\110\000\111\000\111\000\039\000\039\000\112\000\112\000\
\113\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\115\000\115\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\003\000\003\000\003\000\
\003\000\003\000\003\000\003\000\003\000\114\000\114\000\116\000\
\116\000\004\000\004\000\117\000\040\000\040\000\041\000\041\000\
\042\000\042\000\043\000\043\000\044\000\044\000\045\000\045\000\
\046\000\046\000\047\000\047\000\048\000\048\000\049\000\049\000\
\120\000\120\000\118\000\119\000\006\000\006\000\006\000\005\000\
\005\000\005\000\121\000\121\000\078\000\078\000\122\000\122\000\
\007\000\101\000\101\000\123\000\008\000\009\000\085\000\085\000\
\062\000\095\000\012\000\012\000\050\000\050\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yylen = "\002\000\
\005\000\004\000\007\000\006\000\003\000\001\000\002\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\
\003\000\002\000\000\000\004\000\002\000\000\000\001\000\002\000\
\004\000\002\000\000\000\001\000\002\000\003\000\002\000\000\000\
\004\000\002\000\000\000\001\000\002\000\001\000\002\000\003\000\
\003\000\004\000\002\000\003\000\000\000\001\000\002\000\003\000\
\004\000\002\000\003\000\001\000\002\000\001\000\004\000\001\000\
\002\000\004\000\002\000\000\000\006\000\006\000\002\000\000\000\
\001\000\002\000\001\000\002\000\004\000\002\000\001\000\000\000\
\001\000\002\000\004\000\004\000\002\000\000\000\000\000\001\000\
\002\000\002\000\003\000\002\000\000\000\001\000\002\000\003\000\
\003\000\003\000\003\000\002\000\000\000\002\000\003\000\003\000\
\002\000\000\000\002\000\003\000\001\000\002\000\001\000\004\000\
\001\000\003\000\001\000\002\000\001\000\003\000\003\000\003\000\
\002\000\000\000\001\000\002\000\004\000\004\000\004\000\002\000\
\000\000\001\000\002\000\001\000\002\000\003\000\005\000\004\000\
\001\000\002\000\003\000\002\000\000\000\003\000\002\000\001\000\
\002\000\002\000\004\000\002\000\004\000\002\000\004\000\002\000\
\004\000\002\000\001\000\002\000\001\000\002\000\002\000\001\000\
\002\000\006\000\004\000\003\000\001\000\002\000\003\000\000\000\
\002\000\001\000\002\000\003\000\001\000\003\000\001\000\003\000\
\001\000\003\000\003\000\003\000\001\000\001\000\002\000\001\000\
\005\000\003\000\001\000\003\000\003\000\002\000\001\000\002\000\
\004\000\008\000\008\000\008\000\002\000\003\000\004\000\004\000\
\002\000\002\000\001\000\001\000\001\000\001\000\004\000\004\000\
\001\000\003\000\008\000\004\000\008\000\006\000\008\000\001\000\
\004\000\004\000\001\000\004\000\004\000\001\000\004\000\004\000\
\001\000\001\000\001\000\001\000\001\000\004\000\004\000\001\000\
\001\000\001\000\001\000\001\000\001\000\001\000\003\000\001\000\
\001\000\001\000\003\000\001\000\003\000\002\000\003\000\002\000\
\004\000\002\000\003\000\002\000\003\000\002\000\003\000\002\000\
\004\000\002\000\003\000\002\000\004\000\002\000\008\000\003\000\
\001\000\003\000\004\000\005\000\001\000\002\000\001\000\003\000\
\001\000\001\000\003\000\002\000\001\000\002\000\001\000\002\000\
\002\000\001\000\003\000\003\000\001\000\001\000\002\000\004\000\
\000\000\000\000\002\000\001\000\004\000\002\000\002\000\002\000\
\002\000\002\000\002\000\002\000\002\000\002\000\002\000\002\000\
\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\039\001\000\000\
\000\000\000\000\204\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\203\000\040\001\229\000\
\000\000\000\000\000\000\000\000\000\000\000\000\226\000\000\000\
\000\000\227\000\225\000\228\000\234\000\233\000\235\000\236\000\
\000\000\000\000\232\000\237\000\041\001\244\000\000\000\242\000\
\018\001\000\000\043\001\015\001\000\000\044\001\000\000\045\001\
\000\000\026\001\029\001\046\001\000\000\184\000\047\001\030\001\
\000\000\182\000\048\001\000\000\049\001\000\000\000\000\175\000\
\177\000\000\000\036\001\050\001\000\000\000\000\000\000\000\000\
\079\000\000\000\000\000\209\000\000\000\000\000\000\000\201\000\
\202\000\197\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\014\001\000\000\025\001\000\000\
\000\000\000\000\000\000\183\000\000\000\000\000\000\000\169\000\
\000\000\000\000\035\001\025\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\198\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\109\000\113\000\000\000\000\000\000\000\
\000\000\240\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\243\000\016\001\020\001\023\001\000\000\028\001\
\027\001\000\000\000\000\186\000\179\000\178\000\180\000\176\000\
\000\000\000\000\000\000\002\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\168\000\000\000\000\000\000\000\000\000\000\000\006\000\008\000\
\009\000\010\000\011\000\012\000\013\000\014\000\015\000\016\000\
\017\000\018\000\019\000\020\000\021\000\022\000\023\000\024\000\
\000\000\000\000\000\000\000\000\000\000\031\000\000\000\000\000\
\000\000\000\000\210\000\199\000\200\000\000\000\000\000\000\000\
\207\000\208\000\217\000\000\000\000\000\117\000\000\000\218\000\
\000\000\107\000\110\000\220\000\221\000\223\000\224\000\000\000\
\000\000\000\000\212\000\000\000\230\000\231\000\019\001\024\001\
\000\000\000\000\000\000\000\000\081\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\001\000\007\000\000\000\000\000\005\000\000\000\000\000\000\000\
\000\000\028\000\032\000\036\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\114\000\000\000\021\001\
\108\000\000\000\000\000\000\000\000\000\185\000\000\000\082\000\
\102\000\000\000\168\000\000\000\000\000\168\000\000\000\000\000\
\191\000\075\000\000\000\000\000\144\000\000\000\000\000\251\000\
\168\000\253\000\255\000\000\000\000\000\000\000\000\000\168\000\
\245\000\247\000\168\000\000\000\000\000\000\000\000\000\088\000\
\000\000\000\000\094\000\000\000\000\000\000\000\033\000\037\000\
\044\000\000\000\000\000\000\000\000\000\238\000\000\000\000\000\
\000\000\119\000\118\000\112\000\022\001\214\000\000\000\000\000\
\000\000\000\000\103\000\000\000\000\000\000\000\168\000\147\000\
\031\001\000\000\155\000\000\000\192\000\146\000\076\000\145\000\
\249\000\000\000\000\000\001\001\005\001\009\001\000\000\000\000\
\000\000\000\000\137\000\000\000\090\000\089\000\000\000\000\000\
\000\000\095\000\000\000\115\000\000\000\000\000\123\000\000\000\
\000\000\004\000\041\000\045\000\000\000\000\000\046\000\000\000\
\000\000\000\000\003\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\083\000\000\000\159\000\000\000\000\000\160\000\
\000\000\156\000\000\000\000\000\000\000\000\000\000\000\168\000\
\138\000\096\000\098\000\097\000\168\000\168\000\116\000\124\000\
\132\000\000\000\130\000\000\000\000\000\047\000\000\000\000\000\
\054\000\000\000\000\000\239\000\194\000\195\000\196\000\215\000\
\211\000\213\000\164\000\000\000\161\000\032\001\193\000\011\001\
\000\000\010\001\000\000\000\000\000\000\000\000\000\000\127\000\
\131\000\073\000\000\000\000\000\000\000\062\000\048\000\000\000\
\060\000\000\000\055\000\000\000\168\000\000\000\012\001\000\000\
\136\000\000\000\000\000\133\000\125\000\126\000\000\000\074\000\
\000\000\000\000\000\000\058\000\061\000\056\000\000\000\000\000\
\165\000\000\000\000\000\007\001\134\000\000\000\000\000\000\000\
\059\000\000\000\000\000\166\000\000\000\000\000\000\000\000\000\
\000\000\000\000\069\000\070\000\064\000\000\000\063\000\057\000\
\167\000\000\000\000\000\162\000\000\000\065\000\174\000\163\000\
\135\000"

let yydgoto = "\013\000\
\015\000\092\000\110\001\163\000\059\000\062\000\064\000\068\000\
\142\001\072\000\077\000\084\000\016\000\087\000\135\000\206\000\
\017\000\091\000\141\000\234\000\048\001\109\001\171\001\088\000\
\138\000\229\000\041\001\102\001\162\001\136\000\226\000\037\001\
\207\000\208\000\209\000\210\000\211\000\212\000\213\000\214\000\
\215\000\216\000\217\000\218\000\219\000\220\000\221\000\222\000\
\223\000\224\000\231\000\045\001\166\001\106\001\167\001\239\001\
\208\001\209\001\240\001\241\001\031\002\245\001\007\002\235\001\
\075\001\186\000\012\001\089\000\013\001\095\001\096\001\098\001\
\099\001\015\001\154\000\155\000\156\000\055\001\157\000\245\000\
\157\001\246\000\158\001\159\001\068\001\202\001\203\001\228\001\
\124\001\252\001\147\001\148\001\076\001\077\001\081\001\130\001\
\125\001\131\001\183\001\184\001\065\000\011\002\078\000\009\002\
\021\002\079\000\080\000\081\000\073\000\074\000\123\000\072\001\
\073\001\111\001\093\000\164\000\056\000\080\001\082\001\143\001\
\117\000\175\000\066\000"

let yysindex = "\241\000\
\065\255\141\255\239\000\225\254\031\255\052\255\001\255\099\255\
\047\255\047\255\047\255\043\255\000\000\197\255\000\000\124\255\
\180\255\141\255\000\000\218\255\255\255\141\255\141\255\142\255\
\002\000\026\000\048\000\060\000\064\000\000\000\000\000\000\000\
\068\000\072\000\073\000\074\000\075\000\076\000\000\000\077\000\
\078\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\079\000\080\000\000\000\000\000\000\000\000\000\033\000\000\000\
\000\000\181\255\000\000\000\000\081\000\000\000\084\000\000\000\
\195\255\000\000\000\000\000\000\064\255\000\000\000\000\000\000\
\047\255\000\000\000\000\253\255\000\000\089\000\095\255\000\000\
\000\000\141\255\000\000\000\000\007\000\099\000\082\000\069\000\
\000\000\108\000\093\000\000\000\201\255\141\255\141\255\000\000\
\000\000\000\000\239\000\239\000\239\000\024\000\027\000\060\255\
\081\255\084\255\080\255\141\255\141\255\052\255\029\000\080\255\
\080\255\225\254\081\000\018\255\000\000\047\255\000\000\001\255\
\114\000\047\255\223\255\000\000\047\255\047\255\047\255\000\000\
\047\255\047\255\000\000\000\000\000\000\115\000\047\011\087\000\
\119\000\100\000\031\000\122\000\101\000\141\255\000\000\251\255\
\252\255\124\000\125\000\127\000\118\000\126\000\128\000\040\000\
\131\000\072\255\033\255\000\000\000\000\133\000\073\255\134\000\
\076\255\000\000\033\000\129\000\139\000\140\000\141\000\143\000\
\142\000\144\000\000\000\000\000\000\000\000\000\062\255\000\000\
\000\000\043\000\047\255\000\000\000\000\000\000\000\000\000\000\
\147\000\056\000\063\000\000\000\150\000\153\000\154\000\155\000\
\156\000\160\000\164\000\165\000\166\000\167\000\168\000\169\000\
\000\000\170\000\172\000\173\000\174\000\068\011\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\175\000\116\000\000\000\177\000\146\000\000\000\049\255\097\000\
\187\000\171\000\000\000\000\000\000\000\178\000\188\000\190\000\
\000\000\000\000\000\000\192\000\058\255\000\000\081\000\000\000\
\037\255\000\000\000\000\000\000\000\000\000\000\000\000\052\255\
\080\255\080\255\000\000\080\255\000\000\000\000\000\000\000\000\
\185\000\047\255\209\000\056\000\000\000\221\000\137\000\000\000\
\000\000\000\000\138\000\148\000\000\000\000\000\000\000\000\000\
\149\000\148\000\000\000\228\000\000\000\141\255\141\255\000\000\
\000\000\000\000\015\255\229\000\000\000\148\000\148\000\230\000\
\198\000\000\000\000\000\000\000\050\255\151\000\232\000\215\000\
\239\000\239\000\239\000\152\000\040\000\000\000\069\255\000\000\
\000\000\231\000\243\000\244\000\245\000\000\000\148\000\000\000\
\000\000\236\000\000\000\128\255\047\255\000\000\240\000\138\000\
\000\000\000\000\051\255\148\000\000\000\154\255\047\255\000\000\
\000\000\000\000\000\000\247\000\159\000\248\000\047\255\000\000\
\000\000\000\000\000\000\015\255\176\000\053\255\148\000\000\000\
\165\255\148\000\000\000\020\255\253\000\237\000\000\000\000\000\
\000\000\054\255\179\000\166\255\242\000\000\000\111\255\120\255\
\163\255\000\000\000\000\000\000\000\000\000\000\052\255\031\255\
\052\255\057\255\000\000\047\255\000\000\180\000\000\000\000\000\
\000\000\000\000\000\000\141\255\000\000\000\000\000\000\000\000\
\000\000\249\000\047\255\000\000\000\000\000\000\002\001\000\000\
\000\000\005\001\000\000\176\000\000\000\000\000\003\001\004\001\
\013\001\000\000\017\001\000\000\176\255\020\255\000\000\204\000\
\059\001\000\000\000\000\000\000\062\001\179\000\000\000\234\000\
\063\001\064\001\000\000\239\000\056\001\067\001\068\001\069\001\
\071\001\072\001\000\000\065\001\000\000\001\255\180\000\000\000\
\047\255\000\000\066\001\047\255\073\001\047\255\075\001\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\059\255\000\000\015\001\039\255\000\000\106\001\234\000\
\000\000\234\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\066\255\000\000\000\000\000\000\000\000\
\047\255\000\000\047\255\104\001\095\001\213\255\028\000\000\000\
\000\000\000\000\019\255\071\255\023\001\000\000\000\000\035\255\
\000\000\039\255\000\000\234\000\000\000\081\001\000\000\039\000\
\000\000\095\001\047\255\000\000\000\000\000\000\189\255\000\000\
\041\255\071\255\071\255\000\000\000\000\000\000\000\000\047\255\
\000\000\100\001\047\255\000\000\000\000\117\001\132\001\133\001\
\000\000\061\255\044\255\000\000\136\001\184\255\000\000\051\001\
\138\001\054\001\000\000\000\000\000\000\139\001\000\000\000\000\
\000\000\047\255\131\001\000\000\134\001\000\000\000\000\000\000\
\000\000"

let yyrindex = "\000\000\
\058\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\133\007\
\198\004\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\066\000\158\000\000\000\000\000\000\000\
\009\000\014\000\025\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\149\002\000\000\
\000\000\020\000\000\000\000\000\022\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\010\000\000\000\000\000\000\000\000\000\000\000\214\009\000\000\
\000\000\000\000\000\000\000\000\128\004\000\000\235\009\224\007\
\000\000\000\000\040\005\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\030\255\052\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\034\010\000\000\000\000\090\001\000\000\000\000\193\010\
\000\000\059\008\227\004\000\000\138\005\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\046\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\058\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\089\010\000\000\110\010\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\102\011\157\001\000\000\181\000\000\000\000\000\069\005\
\000\000\235\005\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\061\000\000\000\195\007\000\000\000\000\172\010\181\001\
\237\001\005\002\123\011\157\011\061\002\085\002\141\002\165\002\
\178\011\212\011\221\002\000\000\245\002\233\011\011\012\045\003\
\000\000\000\000\248\010\000\000\000\000\000\000\121\008\000\000\
\047\009\000\000\000\000\000\000\000\000\167\005\000\000\105\006\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\032\012\
\000\000\000\000\000\000\066\012\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\087\012\000\000\121\012\000\000\
\000\000\000\000\000\000\013\011\142\012\000\000\030\008\000\000\
\000\000\150\008\000\000\212\008\000\000\138\009\000\000\000\000\
\000\000\000\000\008\006\000\000\104\007\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\069\003\125\003\000\000\000\000\
\000\000\149\003\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\146\001\205\003\
\229\003\000\000\000\000\176\012\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\241\008\000\000\076\009\
\000\000\000\000\000\000\000\000\000\000\076\006\000\000\172\006\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\029\004\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\159\009\000\000\000\000\000\000\201\006\
\000\000\012\007\250\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\140\001\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\041\007\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\061\001\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\055\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\004\000\001\000\150\002\033\001\161\255\000\000\000\000\
\249\255\246\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\206\001\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\251\000\184\000\
\203\000\117\254\101\254\218\254\000\000\000\000\000\000\000\000\
\143\255\000\000\000\000\188\001\148\001\000\000\070\001\000\000\
\074\001\000\000\174\255\113\255\132\255\000\000\077\255\000\000\
\000\000\109\001\000\000\006\001\247\254\000\000\217\000\000\000\
\068\255\182\000\018\001\000\000\000\000\091\001\199\255\092\255\
\000\000\040\255\000\000\246\000\020\001\000\000\149\254\197\000\
\000\000\131\255\130\255\000\000\206\255\191\255\000\000\000\000\
\099\001\227\255\238\000\172\255\060\002\152\001\151\001\235\000\
\148\255\000\000\091\002"

let yytablesize = 3591
let yytable = "\075\000\
\076\000\071\000\184\000\053\000\185\000\031\000\172\000\124\000\
\216\000\181\000\249\000\078\001\028\001\219\000\167\000\249\000\
\180\001\249\000\122\000\017\001\255\001\013\001\159\000\161\000\
\222\000\096\000\097\000\169\000\170\000\152\000\251\000\189\001\
\184\000\173\000\152\000\184\000\184\000\250\000\003\002\004\002\
\237\001\057\001\236\001\057\000\237\001\017\002\237\001\152\000\
\032\002\237\001\111\000\152\000\069\000\042\001\103\001\134\001\
\124\000\149\001\163\001\054\000\111\000\179\001\053\001\232\001\
\060\000\205\000\237\001\029\002\243\001\069\000\120\000\082\000\
\151\000\054\001\152\000\116\001\237\001\007\001\248\000\253\000\
\001\002\014\000\255\000\116\000\069\001\131\000\152\000\152\000\
\069\001\079\001\152\000\063\000\162\000\158\000\079\001\152\000\
\160\000\129\000\152\000\146\000\147\000\148\000\130\000\019\002\
\243\001\153\000\126\001\176\000\174\000\000\002\155\001\165\000\
\166\000\172\001\181\000\182\000\183\000\247\001\076\000\076\000\
\184\000\058\000\172\001\153\000\251\000\238\001\173\001\153\000\
\010\001\238\001\127\001\238\001\128\001\083\000\238\001\174\001\
\111\000\070\000\056\001\043\001\104\001\135\001\061\000\135\001\
\164\001\235\000\018\000\135\001\139\001\201\001\153\000\238\001\
\008\001\019\000\121\000\246\001\127\001\206\000\137\001\025\002\
\058\001\238\001\153\000\153\000\181\001\172\001\153\000\168\001\
\085\001\186\001\054\000\153\000\059\001\060\001\153\000\061\001\
\156\001\198\001\175\001\144\001\094\001\097\001\145\001\186\001\
\186\001\169\001\129\000\230\001\231\001\067\000\152\000\034\002\
\020\000\021\000\185\001\119\000\022\000\023\000\085\000\120\000\
\124\000\005\002\117\001\142\000\249\000\122\001\086\000\143\000\
\092\001\090\000\191\001\151\001\152\001\153\001\067\001\127\001\
\070\001\253\001\005\002\018\002\024\000\025\000\026\000\094\000\
\027\000\179\000\028\000\088\001\029\000\180\000\091\001\030\000\
\098\000\199\001\156\001\030\002\005\002\094\001\015\002\016\002\
\097\001\001\000\002\000\003\000\004\000\005\000\006\000\007\000\
\008\000\009\000\010\000\011\000\012\000\142\000\142\000\135\001\
\125\000\236\000\237\000\229\001\095\000\126\000\127\000\099\000\
\069\001\069\001\181\000\216\000\181\000\181\000\181\000\115\000\
\219\000\181\000\181\000\181\000\112\001\113\001\181\000\176\001\
\216\000\178\001\017\001\222\000\013\001\219\000\127\001\100\000\
\254\001\089\001\090\001\181\000\181\000\181\000\181\000\250\001\
\222\000\190\001\181\000\012\002\114\000\181\000\181\000\181\000\
\181\000\181\000\181\000\181\000\181\000\101\000\187\000\181\000\
\008\002\175\000\187\000\173\000\241\000\129\001\175\000\188\000\
\241\000\102\000\205\000\188\000\205\000\103\000\205\000\138\001\
\205\000\104\000\008\002\144\000\145\000\105\000\106\000\107\000\
\108\000\109\000\110\000\111\000\112\000\113\000\118\000\181\000\
\181\000\128\000\137\000\205\000\205\000\205\000\205\000\116\000\
\181\000\132\000\205\000\181\000\133\000\205\000\205\000\205\000\
\205\000\205\000\205\000\205\000\205\000\139\000\140\000\205\000\
\134\000\076\000\149\000\178\000\187\000\150\000\225\000\168\000\
\227\000\230\000\228\000\232\000\241\000\233\000\238\000\239\000\
\076\000\240\000\244\000\000\001\242\000\009\001\243\000\187\001\
\247\000\023\002\022\002\252\000\254\000\001\001\002\001\205\000\
\205\000\004\001\011\001\003\001\005\001\129\000\006\001\016\001\
\205\000\014\001\017\001\018\001\019\001\020\001\206\000\036\001\
\206\000\021\001\206\000\039\002\206\000\022\001\023\001\024\001\
\025\001\026\001\027\001\029\001\212\001\030\001\031\001\032\001\
\035\001\222\001\039\001\040\001\224\001\122\000\226\001\206\000\
\206\000\206\000\206\000\044\001\046\001\047\001\206\000\062\001\
\049\001\206\000\206\000\206\000\206\000\206\000\206\000\206\000\
\206\000\122\000\050\001\206\000\051\001\052\001\122\000\122\000\
\122\000\122\000\063\001\122\000\122\000\122\000\076\000\122\000\
\122\000\122\000\122\000\122\000\122\000\122\000\122\000\122\000\
\122\000\065\001\122\000\066\001\071\001\087\001\093\001\100\001\
\101\001\107\001\108\001\206\000\206\000\118\001\074\001\084\001\
\123\001\105\001\114\001\014\002\206\000\119\001\120\001\121\001\
\132\001\135\001\067\000\140\001\141\001\076\000\160\001\033\001\
\076\000\161\001\122\000\122\000\190\001\188\001\192\001\194\001\
\195\001\170\001\146\001\122\000\182\001\165\001\067\000\067\000\
\067\000\196\001\197\001\067\000\067\000\067\000\067\000\076\000\
\067\000\067\000\067\000\067\000\067\000\067\000\067\000\067\000\
\067\000\067\000\067\000\067\000\067\000\067\000\201\001\067\000\
\032\000\033\000\034\000\035\000\036\000\037\000\038\000\039\000\
\040\000\041\000\042\000\043\000\044\000\045\000\046\000\047\000\
\048\000\049\000\050\000\051\000\204\001\066\000\213\001\205\001\
\210\001\211\001\168\000\052\000\207\001\219\001\223\001\067\000\
\067\000\214\001\215\001\216\001\067\000\217\001\218\001\227\001\
\067\000\066\000\066\000\066\000\033\001\225\001\066\000\066\000\
\066\000\066\000\078\000\066\000\066\000\066\000\066\000\066\000\
\066\000\066\000\066\000\066\000\066\000\066\000\066\000\066\000\
\066\000\234\001\066\000\242\001\249\001\251\001\078\000\078\000\
\078\000\002\002\024\002\078\000\078\000\078\000\078\000\026\002\
\078\000\078\000\078\000\078\000\078\000\078\000\078\000\078\000\
\078\000\078\000\078\000\078\000\078\000\078\000\010\002\078\000\
\027\002\028\002\066\000\066\000\033\002\035\002\036\002\066\000\
\037\002\038\002\040\002\066\000\042\001\041\002\168\000\168\000\
\177\001\055\000\168\000\034\001\244\001\085\000\038\001\064\001\
\206\001\115\001\233\001\200\001\150\001\193\001\136\001\078\000\
\078\000\006\002\133\001\154\001\221\001\171\000\083\001\013\002\
\078\000\085\000\086\001\085\000\080\000\152\000\085\000\085\000\
\085\000\085\000\034\001\085\000\085\000\085\000\085\000\085\000\
\085\000\085\000\085\000\085\000\085\000\085\000\085\000\085\000\
\085\000\220\001\085\000\020\002\000\000\248\001\152\000\152\000\
\152\000\152\000\177\000\000\000\000\000\152\000\000\000\000\000\
\152\000\152\000\152\000\152\000\152\000\152\000\152\000\152\000\
\000\000\000\000\152\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\085\000\085\000\000\000\148\000\000\000\000\000\
\000\000\000\000\168\000\085\000\000\000\000\000\000\000\087\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\152\000\152\000\000\000\150\000\148\000\148\000\
\148\000\148\000\034\001\152\000\000\000\148\000\000\000\034\001\
\148\000\148\000\148\000\148\000\148\000\148\000\148\000\148\000\
\000\000\000\000\148\000\000\000\000\000\000\000\150\000\150\000\
\150\000\150\000\000\000\000\000\000\000\150\000\000\000\000\000\
\150\000\150\000\150\000\150\000\150\000\150\000\150\000\150\000\
\000\000\000\000\150\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\148\000\148\000\000\000\250\000\000\000\000\000\
\000\000\000\000\168\000\148\000\000\000\000\000\000\000\168\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\150\000\150\000\000\000\252\000\250\000\250\000\
\250\000\250\000\168\000\150\000\000\000\250\000\000\000\034\001\
\250\000\250\000\250\000\250\000\250\000\250\000\250\000\250\000\
\000\000\000\000\250\000\000\000\000\000\000\000\252\000\252\000\
\252\000\252\000\000\000\000\000\000\000\252\000\000\000\000\000\
\252\000\252\000\252\000\252\000\252\000\252\000\252\000\252\000\
\000\000\000\000\252\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\250\000\250\000\000\000\254\000\000\000\000\000\
\000\000\000\000\034\001\250\000\000\000\000\000\000\000\168\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\252\000\252\000\000\000\000\001\254\000\254\000\
\254\000\254\000\034\001\252\000\000\000\254\000\000\000\168\000\
\254\000\254\000\254\000\254\000\254\000\254\000\254\000\254\000\
\000\000\000\000\254\000\000\000\000\000\000\000\000\001\000\001\
\000\001\000\001\000\000\000\000\000\000\000\001\000\000\000\000\
\000\001\000\001\000\001\000\001\000\001\000\001\000\001\000\001\
\000\000\000\000\000\001\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\254\000\254\000\000\000\006\001\000\000\000\000\
\000\000\000\000\168\000\254\000\000\000\000\000\000\000\034\001\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\001\000\001\000\000\154\000\006\001\006\001\
\006\001\006\001\034\001\000\001\000\000\006\001\000\000\034\001\
\006\001\006\001\006\001\006\001\006\001\006\001\006\001\006\001\
\000\000\000\000\006\001\000\000\000\000\000\000\154\000\154\000\
\154\000\154\000\000\000\000\000\000\000\154\000\000\000\000\000\
\154\000\154\000\154\000\154\000\154\000\154\000\154\000\154\000\
\000\000\000\000\154\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\006\001\006\001\000\000\038\001\000\000\000\000\
\000\000\000\000\034\001\006\001\000\000\000\000\000\000\168\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\154\000\154\000\000\000\151\000\038\001\038\001\
\038\001\038\001\168\000\154\000\000\000\038\001\000\000\034\001\
\038\001\038\001\038\001\038\001\038\001\038\001\038\001\038\001\
\000\000\000\000\038\001\000\000\000\000\000\000\151\000\151\000\
\151\000\151\000\000\000\000\000\000\000\151\000\000\000\000\000\
\151\000\151\000\151\000\151\000\151\000\151\000\151\000\151\000\
\000\000\000\000\151\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\038\001\038\001\000\000\157\000\000\000\000\000\
\000\000\000\000\157\000\038\001\000\000\000\000\000\000\034\001\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\151\000\151\000\000\000\149\000\157\000\157\000\
\157\000\157\000\168\000\151\000\000\000\157\000\000\000\168\000\
\157\000\157\000\157\000\157\000\157\000\157\000\157\000\157\000\
\000\000\000\000\157\000\000\000\000\000\000\000\149\000\149\000\
\149\000\149\000\000\000\000\000\000\000\149\000\000\000\000\000\
\149\000\149\000\149\000\149\000\149\000\149\000\149\000\149\000\
\000\000\000\000\149\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\157\000\157\000\000\000\153\000\000\000\000\000\
\000\000\000\000\168\000\157\000\000\000\000\000\000\000\157\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\149\000\149\000\000\000\037\001\153\000\153\000\
\153\000\153\000\168\000\149\000\000\000\153\000\000\000\168\000\
\153\000\153\000\153\000\153\000\153\000\153\000\153\000\153\000\
\000\000\000\000\153\000\000\000\000\000\000\000\037\001\037\001\
\037\001\037\001\000\000\000\000\000\000\037\001\000\000\000\000\
\037\001\037\001\037\001\037\001\037\001\037\001\037\001\037\001\
\000\000\000\000\037\001\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\153\000\153\000\000\000\158\000\000\000\000\000\
\000\000\000\000\158\000\153\000\000\000\000\000\000\000\168\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\037\001\037\001\000\000\000\000\158\000\158\000\
\158\000\158\000\027\000\037\001\000\000\158\000\000\000\168\000\
\158\000\158\000\158\000\158\000\158\000\158\000\158\000\158\000\
\000\000\000\000\158\000\027\000\027\000\027\000\027\000\027\000\
\027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
\027\000\027\000\027\000\027\000\027\000\027\000\027\000\027\000\
\027\000\027\000\027\000\027\000\027\000\027\000\000\000\027\000\
\000\000\000\000\158\000\158\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\158\000\000\000\000\000\000\000\158\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\026\000\000\000\000\000\000\000\000\000\000\000\000\000\027\000\
\027\000\000\000\000\000\000\000\027\000\000\000\000\000\000\000\
\027\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
\026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
\026\000\026\000\026\000\026\000\026\000\026\000\026\000\026\000\
\026\000\026\000\026\000\026\000\000\000\026\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\030\000\000\000\
\000\000\000\000\000\000\000\000\000\000\026\000\026\000\000\000\
\000\000\000\000\026\000\000\000\000\000\000\000\026\000\030\000\
\030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
\030\000\030\000\030\000\029\000\030\000\030\000\030\000\030\000\
\030\000\030\000\030\000\030\000\030\000\030\000\030\000\030\000\
\030\000\030\000\000\000\030\000\029\000\029\000\029\000\029\000\
\029\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
\000\000\029\000\029\000\029\000\029\000\029\000\029\000\029\000\
\029\000\029\000\029\000\029\000\029\000\029\000\029\000\000\000\
\029\000\000\000\000\000\030\000\030\000\000\000\000\000\000\000\
\030\000\000\000\000\000\000\000\030\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\035\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\029\000\029\000\000\000\000\000\000\000\029\000\000\000\000\000\
\000\000\029\000\035\000\035\000\035\000\035\000\035\000\035\000\
\035\000\035\000\035\000\035\000\035\000\034\000\035\000\035\000\
\035\000\035\000\035\000\035\000\035\000\035\000\035\000\035\000\
\035\000\035\000\035\000\035\000\000\000\035\000\000\000\034\000\
\034\000\034\000\034\000\034\000\034\000\034\000\034\000\034\000\
\034\000\034\000\000\000\034\000\034\000\034\000\034\000\034\000\
\034\000\034\000\034\000\034\000\034\000\034\000\034\000\034\000\
\034\000\000\000\034\000\000\000\000\000\035\000\035\000\000\000\
\000\000\000\000\035\000\000\000\000\000\000\000\035\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\043\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\034\000\034\000\000\000\000\000\000\000\034\000\
\000\000\000\000\000\000\034\000\043\000\043\000\043\000\043\000\
\043\000\043\000\000\000\043\000\043\000\043\000\043\000\042\000\
\043\000\043\000\043\000\043\000\043\000\043\000\043\000\043\000\
\043\000\043\000\043\000\043\000\043\000\043\000\000\000\043\000\
\000\000\042\000\042\000\042\000\042\000\042\000\042\000\000\000\
\042\000\042\000\042\000\042\000\000\000\042\000\042\000\042\000\
\042\000\042\000\042\000\042\000\042\000\042\000\042\000\042\000\
\042\000\042\000\042\000\000\000\042\000\000\000\000\000\043\000\
\043\000\000\000\000\000\000\000\043\000\000\000\000\000\000\000\
\043\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\040\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\042\000\042\000\000\000\000\000\
\000\000\042\000\000\000\000\000\000\000\042\000\040\000\040\000\
\040\000\040\000\040\000\000\000\040\000\040\000\040\000\040\000\
\039\000\040\000\040\000\040\000\040\000\040\000\040\000\040\000\
\040\000\040\000\040\000\040\000\040\000\040\000\040\000\000\000\
\040\000\000\000\000\000\039\000\039\000\039\000\039\000\039\000\
\000\000\039\000\039\000\039\000\039\000\000\000\039\000\039\000\
\039\000\039\000\039\000\039\000\039\000\039\000\039\000\039\000\
\039\000\039\000\039\000\039\000\000\000\039\000\000\000\000\000\
\040\000\040\000\000\000\000\000\000\000\040\000\000\000\000\000\
\000\000\040\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\038\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\039\000\039\000\000\000\
\000\000\000\000\039\000\000\000\000\000\000\000\039\000\038\000\
\038\000\038\000\038\000\038\000\000\000\038\000\038\000\038\000\
\038\000\053\000\038\000\038\000\038\000\038\000\038\000\038\000\
\038\000\038\000\038\000\038\000\038\000\038\000\038\000\038\000\
\000\000\038\000\000\000\000\000\000\000\053\000\053\000\053\000\
\053\000\000\000\053\000\053\000\053\000\053\000\000\000\053\000\
\053\000\053\000\053\000\053\000\053\000\053\000\053\000\053\000\
\053\000\053\000\053\000\053\000\053\000\000\000\053\000\000\000\
\000\000\038\000\038\000\000\000\000\000\000\000\038\000\000\000\
\000\000\000\000\038\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\051\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\053\000\053\000\
\000\000\000\000\000\000\053\000\000\000\000\000\000\000\053\000\
\051\000\051\000\051\000\051\000\000\000\051\000\051\000\051\000\
\051\000\049\000\051\000\051\000\051\000\051\000\051\000\051\000\
\051\000\051\000\051\000\051\000\051\000\051\000\051\000\051\000\
\000\000\051\000\000\000\000\000\000\000\049\000\049\000\049\000\
\049\000\000\000\049\000\049\000\049\000\049\000\000\000\049\000\
\049\000\049\000\049\000\049\000\049\000\049\000\049\000\049\000\
\049\000\049\000\049\000\049\000\049\000\000\000\049\000\000\000\
\000\000\051\000\051\000\000\000\000\000\000\000\051\000\000\000\
\000\000\000\000\051\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\052\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\049\000\049\000\
\000\000\000\000\000\000\049\000\000\000\000\000\000\000\049\000\
\052\000\052\000\052\000\052\000\000\000\052\000\052\000\052\000\
\052\000\050\000\052\000\052\000\052\000\052\000\052\000\052\000\
\052\000\052\000\052\000\052\000\052\000\052\000\052\000\052\000\
\000\000\052\000\000\000\000\000\000\000\050\000\050\000\050\000\
\050\000\000\000\050\000\050\000\050\000\050\000\000\000\050\000\
\050\000\050\000\050\000\050\000\050\000\050\000\050\000\050\000\
\050\000\050\000\050\000\050\000\050\000\000\000\050\000\000\000\
\000\000\052\000\052\000\000\000\000\000\000\000\052\000\000\000\
\000\000\000\000\052\000\000\000\000\000\000\000\000\000\000\000\
\068\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\050\000\050\000\
\000\000\000\000\000\000\050\000\068\000\068\000\068\000\050\000\
\000\000\068\000\068\000\068\000\068\000\087\000\068\000\068\000\
\068\000\068\000\068\000\068\000\068\000\068\000\068\000\068\000\
\068\000\068\000\068\000\068\000\000\000\068\000\000\000\000\000\
\000\000\087\000\087\000\087\000\000\000\000\000\087\000\087\000\
\087\000\087\000\000\000\087\000\087\000\087\000\087\000\087\000\
\087\000\087\000\087\000\087\000\087\000\087\000\087\000\087\000\
\087\000\000\000\087\000\000\000\000\000\068\000\068\000\000\000\
\000\000\000\000\068\000\000\000\000\000\000\000\068\000\000\000\
\000\000\000\000\000\000\077\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\087\000\087\000\000\000\000\000\000\000\077\000\
\077\000\077\000\000\000\087\000\077\000\077\000\077\000\077\000\
\086\000\077\000\077\000\077\000\077\000\077\000\077\000\077\000\
\077\000\077\000\077\000\077\000\077\000\077\000\077\000\000\000\
\077\000\000\000\000\000\000\000\086\000\000\000\086\000\000\000\
\000\000\086\000\086\000\086\000\086\000\000\000\086\000\086\000\
\086\000\086\000\086\000\086\000\086\000\086\000\086\000\086\000\
\086\000\086\000\086\000\086\000\000\000\086\000\000\000\000\000\
\077\000\077\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\077\000\000\000\000\000\000\000\000\000\084\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\086\000\086\000\000\000\
\000\000\000\000\084\000\000\000\084\000\000\000\086\000\084\000\
\084\000\084\000\084\000\093\000\084\000\084\000\084\000\084\000\
\084\000\084\000\084\000\084\000\084\000\084\000\084\000\084\000\
\084\000\084\000\000\000\084\000\000\000\000\000\000\000\093\000\
\000\000\000\000\000\000\000\000\093\000\093\000\093\000\093\000\
\000\000\093\000\093\000\093\000\093\000\093\000\093\000\093\000\
\093\000\093\000\093\000\093\000\093\000\093\000\093\000\000\000\
\093\000\000\000\000\000\084\000\084\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\084\000\000\000\000\000\000\000\
\000\000\092\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\093\000\093\000\000\000\000\000\000\000\092\000\000\000\000\000\
\000\000\093\000\092\000\092\000\092\000\092\000\091\000\092\000\
\092\000\092\000\092\000\092\000\092\000\092\000\092\000\092\000\
\092\000\092\000\092\000\092\000\092\000\000\000\092\000\000\000\
\000\000\000\000\091\000\000\000\000\000\000\000\000\000\091\000\
\091\000\091\000\091\000\000\000\091\000\091\000\091\000\091\000\
\091\000\091\000\091\000\091\000\091\000\091\000\091\000\091\000\
\091\000\091\000\000\000\091\000\000\000\000\000\092\000\092\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\092\000\
\000\000\000\000\000\000\000\000\121\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\091\000\091\000\000\000\000\000\000\000\
\121\000\000\000\000\000\000\000\091\000\121\000\121\000\121\000\
\121\000\120\000\121\000\121\000\121\000\000\000\121\000\121\000\
\121\000\121\000\121\000\121\000\121\000\121\000\121\000\121\000\
\000\000\121\000\000\000\000\000\000\000\120\000\000\000\000\000\
\000\000\000\000\120\000\120\000\120\000\120\000\000\000\120\000\
\120\000\120\000\000\000\120\000\120\000\120\000\120\000\120\000\
\120\000\120\000\120\000\120\000\120\000\000\000\120\000\000\000\
\000\000\121\000\121\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\121\000\000\000\000\000\000\000\000\000\129\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\120\000\120\000\
\000\000\000\000\000\000\129\000\000\000\000\000\000\000\120\000\
\129\000\129\000\129\000\129\000\128\000\129\000\129\000\129\000\
\000\000\000\000\129\000\129\000\129\000\129\000\129\000\129\000\
\129\000\129\000\129\000\000\000\129\000\000\000\000\000\000\000\
\128\000\000\000\000\000\000\000\000\000\128\000\128\000\128\000\
\128\000\000\000\128\000\128\000\128\000\000\000\000\000\128\000\
\128\000\128\000\128\000\128\000\128\000\128\000\128\000\128\000\
\000\000\128\000\000\000\000\000\129\000\129\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\129\000\000\000\000\000\
\000\000\000\000\072\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\128\000\128\000\000\000\000\000\000\000\000\000\071\000\
\000\000\000\000\128\000\072\000\072\000\072\000\072\000\000\000\
\072\000\072\000\072\000\000\000\000\000\072\000\072\000\072\000\
\072\000\072\000\072\000\072\000\072\000\072\000\000\000\072\000\
\071\000\071\000\071\000\071\000\000\000\071\000\071\000\071\000\
\000\000\000\000\071\000\071\000\071\000\071\000\071\000\071\000\
\071\000\071\000\071\000\000\000\071\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\170\000\072\000\
\072\000\000\000\170\000\000\000\000\000\000\000\000\000\000\000\
\072\000\000\000\170\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\101\000\071\000\071\000\000\000\170\000\
\170\000\170\000\170\000\000\000\000\000\071\000\170\000\000\000\
\000\000\170\000\170\000\170\000\170\000\170\000\170\000\170\000\
\170\000\000\000\000\000\170\000\101\000\101\000\101\000\101\000\
\000\000\000\000\101\000\101\000\000\000\000\000\101\000\101\000\
\101\000\101\000\101\000\101\000\101\000\101\000\101\000\000\000\
\101\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\171\000\170\000\170\000\000\000\171\000\000\000\
\000\000\000\000\000\000\000\000\170\000\000\000\171\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\101\000\101\000\000\000\171\000\171\000\171\000\171\000\000\000\
\000\000\101\000\171\000\000\000\000\000\171\000\171\000\171\000\
\171\000\171\000\171\000\171\000\171\000\000\000\000\000\171\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\172\000\000\000\000\000\000\000\172\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\172\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\100\000\171\000\
\171\000\000\000\172\000\172\000\172\000\172\000\000\000\000\000\
\171\000\172\000\000\000\000\000\172\000\172\000\172\000\172\000\
\172\000\172\000\172\000\172\000\000\000\000\000\172\000\100\000\
\100\000\100\000\100\000\000\000\000\000\100\000\100\000\000\000\
\000\000\100\000\100\000\100\000\100\000\100\000\100\000\100\000\
\100\000\100\000\000\000\100\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\172\000\172\000\
\000\000\000\000\000\000\000\000\099\000\000\000\000\000\172\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\100\000\100\000\000\000\000\000\000\000\
\000\000\106\000\000\000\000\000\100\000\099\000\099\000\099\000\
\099\000\000\000\000\000\099\000\099\000\000\000\000\000\099\000\
\099\000\099\000\099\000\099\000\099\000\099\000\099\000\099\000\
\000\000\099\000\106\000\106\000\106\000\106\000\000\000\000\000\
\000\000\106\000\000\000\000\000\106\000\106\000\106\000\106\000\
\106\000\106\000\106\000\106\000\106\000\000\000\106\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\105\000\099\000\099\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\099\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\104\000\106\000\106\000\
\000\000\105\000\105\000\105\000\105\000\000\000\000\000\106\000\
\105\000\000\000\000\000\105\000\105\000\105\000\105\000\105\000\
\105\000\105\000\105\000\105\000\000\000\105\000\104\000\104\000\
\104\000\104\000\000\000\000\000\000\000\104\000\000\000\188\000\
\104\000\104\000\104\000\104\000\104\000\104\000\104\000\104\000\
\104\000\000\000\104\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\033\001\105\000\105\000\000\000\
\189\000\190\000\191\000\192\000\000\000\000\000\105\000\193\000\
\000\000\000\000\194\000\195\000\196\000\197\000\198\000\199\000\
\200\000\201\000\104\000\104\000\202\000\189\000\190\000\191\000\
\192\000\000\000\000\000\104\000\193\000\000\000\141\000\194\000\
\195\000\196\000\197\000\198\000\199\000\200\000\201\000\000\000\
\000\000\202\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\190\000\203\000\204\000\000\000\141\000\
\141\000\141\000\141\000\000\000\000\000\205\000\141\000\000\000\
\000\000\141\000\141\000\141\000\141\000\141\000\141\000\141\000\
\141\000\203\000\204\000\141\000\190\000\190\000\190\000\190\000\
\000\000\000\000\205\000\190\000\000\000\143\000\190\000\190\000\
\190\000\190\000\190\000\190\000\190\000\190\000\000\000\000\000\
\190\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\002\001\141\000\141\000\000\000\143\000\143\000\
\143\000\143\000\000\000\000\000\141\000\143\000\000\000\000\000\
\143\000\143\000\143\000\143\000\143\000\143\000\143\000\143\000\
\190\000\190\000\143\000\002\001\002\001\002\001\002\001\000\000\
\000\000\190\000\002\001\000\000\004\001\002\001\002\001\002\001\
\002\001\002\001\002\001\002\001\002\001\000\000\000\000\002\001\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\246\000\143\000\143\000\000\000\004\001\004\001\004\001\
\004\001\000\000\000\000\143\000\004\001\000\000\000\000\004\001\
\004\001\004\001\004\001\004\001\004\001\004\001\004\001\002\001\
\002\001\004\001\246\000\246\000\246\000\246\000\000\000\000\000\
\002\001\246\000\000\000\248\000\246\000\246\000\246\000\246\000\
\246\000\246\000\246\000\246\000\000\000\000\000\246\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\189\000\004\001\004\001\000\000\248\000\248\000\248\000\248\000\
\000\000\000\000\004\001\248\000\000\000\000\000\248\000\248\000\
\248\000\248\000\248\000\248\000\248\000\248\000\246\000\246\000\
\248\000\189\000\189\000\189\000\189\000\000\000\000\000\246\000\
\189\000\000\000\142\000\189\000\189\000\189\000\189\000\189\000\
\189\000\189\000\189\000\000\000\000\000\189\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\003\001\
\248\000\248\000\000\000\142\000\142\000\142\000\142\000\000\000\
\000\000\248\000\142\000\000\000\000\000\142\000\142\000\142\000\
\142\000\142\000\142\000\142\000\142\000\189\000\189\000\142\000\
\003\001\003\001\003\001\003\001\000\000\000\000\189\000\003\001\
\000\000\008\001\003\001\003\001\003\001\003\001\003\001\003\001\
\003\001\003\001\000\000\000\000\003\001\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\140\000\142\000\
\142\000\000\000\008\001\008\001\008\001\008\001\000\000\000\000\
\142\000\008\001\000\000\000\000\008\001\008\001\008\001\008\001\
\008\001\008\001\008\001\008\001\003\001\003\001\008\001\140\000\
\140\000\140\000\140\000\000\000\000\000\003\001\140\000\000\000\
\139\000\140\000\140\000\140\000\140\000\140\000\140\000\140\000\
\140\000\000\000\000\000\140\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\008\001\008\001\
\000\000\139\000\139\000\139\000\139\000\000\000\000\000\008\001\
\139\000\000\000\000\000\139\000\139\000\139\000\139\000\139\000\
\139\000\139\000\139\000\140\000\140\000\139\000\000\000\000\000\
\000\000\000\000\000\000\000\000\140\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\139\000\139\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\139\000"

let yycheck = "\010\000\
\011\000\009\000\129\000\003\000\130\000\002\000\115\000\073\000\
\000\000\000\000\154\000\021\001\201\000\000\000\110\000\159\000\
\124\001\161\000\069\000\000\000\002\001\000\000\105\000\106\000\
\000\000\022\000\023\000\112\000\113\000\015\001\155\000\139\001\
\003\001\016\001\015\001\006\001\007\001\005\001\004\001\005\001\
\006\001\005\001\004\001\013\001\006\001\005\001\006\001\015\001\
\005\001\006\001\005\001\015\001\006\001\005\001\005\001\005\001\
\122\000\005\001\005\001\091\001\015\001\005\001\005\001\005\001\
\013\001\000\000\006\001\007\001\208\001\006\001\005\001\029\001\
\013\001\016\001\015\001\007\001\006\001\016\001\007\001\007\001\
\236\001\017\001\007\001\015\001\017\001\082\000\015\001\015\001\
\021\001\022\001\015\001\091\001\013\001\013\001\027\001\015\001\
\013\001\003\001\015\001\099\000\100\000\101\000\008\001\003\002\
\244\001\091\001\067\001\118\000\091\001\091\001\091\001\108\000\
\109\000\003\001\125\000\126\000\127\000\225\001\129\000\130\000\
\091\001\091\001\003\001\091\001\249\000\091\001\016\001\091\001\
\179\000\091\001\003\001\091\001\005\001\091\001\091\001\016\001\
\091\001\091\001\247\000\091\001\091\001\091\001\091\001\091\001\
\091\001\142\000\006\001\091\001\081\001\091\001\091\001\091\001\
\091\001\013\001\091\001\090\001\003\001\000\000\005\001\011\002\
\000\001\091\001\091\001\091\001\125\001\003\001\091\001\002\001\
\026\001\130\001\091\001\091\001\001\001\002\001\091\001\004\001\
\100\001\002\001\016\001\088\001\038\001\039\001\091\001\144\001\
\145\001\020\001\003\001\197\001\198\001\091\001\015\001\008\001\
\052\001\053\001\127\001\001\001\056\001\057\001\002\001\005\001\
\010\001\240\001\055\001\003\001\092\001\063\001\083\001\007\001\
\035\001\030\001\143\001\047\001\048\001\049\001\016\001\003\001\
\018\001\005\001\001\002\002\002\080\001\081\001\082\001\006\001\
\084\001\003\001\086\001\029\001\088\001\007\001\032\001\091\001\
\091\001\157\001\158\001\018\002\019\002\095\001\050\001\051\001\
\098\001\001\000\002\000\003\000\004\000\005\000\006\000\007\000\
\008\000\009\000\010\000\011\000\012\000\003\001\003\001\091\001\
\004\001\007\001\007\001\192\001\006\001\009\001\010\001\006\001\
\197\001\198\001\001\001\003\001\003\001\004\001\005\001\091\001\
\003\001\008\001\009\001\010\001\050\001\051\001\013\001\119\001\
\016\001\121\001\007\001\003\001\007\001\016\001\003\001\006\001\
\005\001\030\001\031\001\026\001\027\001\028\001\029\001\228\001\
\016\001\003\001\033\001\005\001\012\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\006\001\003\001\046\001\
\245\001\003\001\007\001\005\001\003\001\069\001\008\001\003\001\
\007\001\006\001\001\001\007\001\003\001\006\001\005\001\079\001\
\007\001\006\001\007\002\094\000\095\000\006\001\006\001\006\001\
\006\001\006\001\006\001\006\001\006\001\006\001\003\001\078\001\
\079\001\001\001\022\001\026\001\027\001\028\001\029\001\015\001\
\087\001\091\001\033\001\090\001\002\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\002\001\018\001\046\001\
\031\001\124\001\091\001\002\001\002\001\091\001\032\001\091\001\
\002\001\091\001\023\001\002\001\007\001\025\001\003\001\003\001\
\139\001\003\001\091\001\003\001\007\001\091\001\007\001\132\001\
\006\001\008\002\008\002\007\001\007\001\003\001\003\001\078\001\
\079\001\003\001\091\001\007\001\007\001\003\001\007\001\002\001\
\087\001\091\001\002\001\002\001\002\001\002\001\001\001\044\001\
\003\001\002\001\005\001\034\002\007\001\002\001\002\001\002\001\
\002\001\002\001\002\001\002\001\172\001\002\001\002\001\002\001\
\002\001\185\001\002\001\034\001\188\001\001\001\190\001\026\001\
\027\001\028\001\029\001\091\001\002\001\019\001\033\001\007\001\
\015\001\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\043\001\021\001\015\001\046\001\015\001\014\001\026\001\027\001\
\028\001\029\001\002\001\031\001\032\001\033\001\225\001\035\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\044\001\005\001\046\001\091\001\091\001\002\001\002\001\002\001\
\035\001\002\001\020\001\078\001\079\001\007\001\091\001\091\001\
\005\001\091\001\091\001\251\001\087\001\003\001\003\001\003\001\
\009\001\091\001\001\001\005\001\005\001\008\002\002\001\006\001\
\011\002\021\001\078\001\079\001\003\001\013\001\002\001\005\001\
\005\001\024\001\091\001\087\001\089\001\091\001\021\001\022\001\
\023\001\005\001\002\001\026\001\027\001\028\001\029\001\034\002\
\031\001\032\001\033\001\034\001\035\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\044\001\091\001\046\001\
\058\001\059\001\060\001\061\001\062\001\063\001\064\001\065\001\
\066\001\067\001\068\001\069\001\070\001\071\001\072\001\073\001\
\074\001\075\001\076\001\077\001\002\001\001\001\007\001\002\001\
\002\001\002\001\006\001\085\001\091\001\005\001\005\001\078\001\
\079\001\007\001\007\001\007\001\083\001\007\001\007\001\005\001\
\087\001\021\001\022\001\023\001\091\001\013\001\026\001\027\001\
\028\001\029\001\001\001\031\001\032\001\033\001\034\001\035\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\044\001\091\001\046\001\002\001\005\001\015\001\021\001\022\001\
\023\001\091\001\015\001\026\001\027\001\028\001\029\001\003\001\
\031\001\032\001\033\001\034\001\035\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\044\001\054\001\046\001\
\005\001\005\001\078\001\079\001\005\001\091\001\005\001\083\001\
\091\001\007\001\016\001\087\001\000\000\016\001\005\001\091\001\
\120\001\004\000\015\001\206\000\210\001\001\001\227\000\012\001\
\166\001\053\001\202\001\158\001\095\001\148\001\076\001\078\001\
\079\001\242\001\072\001\098\001\183\001\114\000\024\001\250\001\
\087\001\021\001\027\001\023\001\091\001\001\001\026\001\027\001\
\028\001\029\001\006\001\031\001\032\001\033\001\034\001\035\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\044\001\182\001\046\001\007\002\255\255\227\001\026\001\027\001\
\028\001\029\001\120\000\255\255\255\255\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\255\255\255\255\
\255\255\255\255\006\001\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\026\001\027\001\
\028\001\029\001\006\001\087\001\255\255\033\001\255\255\091\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\026\001\027\001\
\028\001\029\001\255\255\255\255\255\255\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\255\255\255\255\
\255\255\255\255\006\001\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\026\001\027\001\
\028\001\029\001\006\001\087\001\255\255\033\001\255\255\091\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\026\001\027\001\
\028\001\029\001\255\255\255\255\255\255\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\255\255\255\255\
\255\255\255\255\006\001\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\026\001\027\001\
\028\001\029\001\006\001\087\001\255\255\033\001\255\255\091\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\026\001\027\001\
\028\001\029\001\255\255\255\255\255\255\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\255\255\255\255\
\255\255\255\255\006\001\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\026\001\027\001\
\028\001\029\001\006\001\087\001\255\255\033\001\255\255\091\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\026\001\027\001\
\028\001\029\001\255\255\255\255\255\255\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\255\255\255\255\
\255\255\255\255\006\001\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\026\001\027\001\
\028\001\029\001\006\001\087\001\255\255\033\001\255\255\091\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\026\001\027\001\
\028\001\029\001\255\255\255\255\255\255\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\255\255\255\255\
\255\255\255\255\006\001\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\026\001\027\001\
\028\001\029\001\006\001\087\001\255\255\033\001\255\255\091\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\026\001\027\001\
\028\001\029\001\255\255\255\255\255\255\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\255\255\255\255\
\255\255\255\255\006\001\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\026\001\027\001\
\028\001\029\001\006\001\087\001\255\255\033\001\255\255\091\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\026\001\027\001\
\028\001\029\001\255\255\255\255\255\255\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\001\001\255\255\255\255\
\255\255\255\255\006\001\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\255\255\026\001\027\001\
\028\001\029\001\001\001\087\001\255\255\033\001\255\255\091\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\255\255\255\255\046\001\018\001\019\001\020\001\021\001\022\001\
\023\001\024\001\025\001\026\001\027\001\028\001\029\001\030\001\
\031\001\032\001\033\001\034\001\035\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\044\001\255\255\046\001\
\255\255\255\255\078\001\079\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\087\001\255\255\255\255\255\255\091\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\001\001\255\255\255\255\255\255\255\255\255\255\255\255\078\001\
\079\001\255\255\255\255\255\255\083\001\255\255\255\255\255\255\
\087\001\018\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\030\001\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\043\001\044\001\255\255\046\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\001\001\255\255\
\255\255\255\255\255\255\255\255\255\255\078\001\079\001\255\255\
\255\255\255\255\083\001\255\255\255\255\255\255\087\001\018\001\
\019\001\020\001\021\001\022\001\023\001\024\001\025\001\026\001\
\027\001\028\001\029\001\001\001\031\001\032\001\033\001\034\001\
\035\001\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\043\001\044\001\255\255\046\001\018\001\019\001\020\001\021\001\
\022\001\023\001\024\001\025\001\026\001\027\001\028\001\029\001\
\255\255\031\001\032\001\033\001\034\001\035\001\036\001\037\001\
\038\001\039\001\040\001\041\001\042\001\043\001\044\001\255\255\
\046\001\255\255\255\255\078\001\079\001\255\255\255\255\255\255\
\083\001\255\255\255\255\255\255\087\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\001\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\078\001\079\001\255\255\255\255\255\255\083\001\255\255\255\255\
\255\255\087\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\001\001\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\043\001\044\001\255\255\046\001\255\255\019\001\
\020\001\021\001\022\001\023\001\024\001\025\001\026\001\027\001\
\028\001\029\001\255\255\031\001\032\001\033\001\034\001\035\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\044\001\255\255\046\001\255\255\255\255\078\001\079\001\255\255\
\255\255\255\255\083\001\255\255\255\255\255\255\087\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\001\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\255\255\255\255\083\001\
\255\255\255\255\255\255\087\001\019\001\020\001\021\001\022\001\
\023\001\024\001\255\255\026\001\027\001\028\001\029\001\001\001\
\031\001\032\001\033\001\034\001\035\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\044\001\255\255\046\001\
\255\255\019\001\020\001\021\001\022\001\023\001\024\001\255\255\
\026\001\027\001\028\001\029\001\255\255\031\001\032\001\033\001\
\034\001\035\001\036\001\037\001\038\001\039\001\040\001\041\001\
\042\001\043\001\044\001\255\255\046\001\255\255\255\255\078\001\
\079\001\255\255\255\255\255\255\083\001\255\255\255\255\255\255\
\087\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\001\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\078\001\079\001\255\255\255\255\
\255\255\083\001\255\255\255\255\255\255\087\001\020\001\021\001\
\022\001\023\001\024\001\255\255\026\001\027\001\028\001\029\001\
\001\001\031\001\032\001\033\001\034\001\035\001\036\001\037\001\
\038\001\039\001\040\001\041\001\042\001\043\001\044\001\255\255\
\046\001\255\255\255\255\020\001\021\001\022\001\023\001\024\001\
\255\255\026\001\027\001\028\001\029\001\255\255\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\043\001\044\001\255\255\046\001\255\255\255\255\
\078\001\079\001\255\255\255\255\255\255\083\001\255\255\255\255\
\255\255\087\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\001\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\078\001\079\001\255\255\
\255\255\255\255\083\001\255\255\255\255\255\255\087\001\020\001\
\021\001\022\001\023\001\024\001\255\255\026\001\027\001\028\001\
\029\001\001\001\031\001\032\001\033\001\034\001\035\001\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\043\001\044\001\
\255\255\046\001\255\255\255\255\255\255\021\001\022\001\023\001\
\024\001\255\255\026\001\027\001\028\001\029\001\255\255\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\046\001\255\255\
\255\255\078\001\079\001\255\255\255\255\255\255\083\001\255\255\
\255\255\255\255\087\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\001\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\078\001\079\001\
\255\255\255\255\255\255\083\001\255\255\255\255\255\255\087\001\
\021\001\022\001\023\001\024\001\255\255\026\001\027\001\028\001\
\029\001\001\001\031\001\032\001\033\001\034\001\035\001\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\043\001\044\001\
\255\255\046\001\255\255\255\255\255\255\021\001\022\001\023\001\
\024\001\255\255\026\001\027\001\028\001\029\001\255\255\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\046\001\255\255\
\255\255\078\001\079\001\255\255\255\255\255\255\083\001\255\255\
\255\255\255\255\087\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\001\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\078\001\079\001\
\255\255\255\255\255\255\083\001\255\255\255\255\255\255\087\001\
\021\001\022\001\023\001\024\001\255\255\026\001\027\001\028\001\
\029\001\001\001\031\001\032\001\033\001\034\001\035\001\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\043\001\044\001\
\255\255\046\001\255\255\255\255\255\255\021\001\022\001\023\001\
\024\001\255\255\026\001\027\001\028\001\029\001\255\255\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\046\001\255\255\
\255\255\078\001\079\001\255\255\255\255\255\255\083\001\255\255\
\255\255\255\255\087\001\255\255\255\255\255\255\255\255\255\255\
\001\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\078\001\079\001\
\255\255\255\255\255\255\083\001\021\001\022\001\023\001\087\001\
\255\255\026\001\027\001\028\001\029\001\001\001\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\043\001\044\001\255\255\046\001\255\255\255\255\
\255\255\021\001\022\001\023\001\255\255\255\255\026\001\027\001\
\028\001\029\001\255\255\031\001\032\001\033\001\034\001\035\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\044\001\255\255\046\001\255\255\255\255\078\001\079\001\255\255\
\255\255\255\255\083\001\255\255\255\255\255\255\087\001\255\255\
\255\255\255\255\255\255\001\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\078\001\079\001\255\255\255\255\255\255\021\001\
\022\001\023\001\255\255\087\001\026\001\027\001\028\001\029\001\
\001\001\031\001\032\001\033\001\034\001\035\001\036\001\037\001\
\038\001\039\001\040\001\041\001\042\001\043\001\044\001\255\255\
\046\001\255\255\255\255\255\255\021\001\255\255\023\001\255\255\
\255\255\026\001\027\001\028\001\029\001\255\255\031\001\032\001\
\033\001\034\001\035\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\043\001\044\001\255\255\046\001\255\255\255\255\
\078\001\079\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\087\001\255\255\255\255\255\255\255\255\001\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\078\001\079\001\255\255\
\255\255\255\255\021\001\255\255\023\001\255\255\087\001\026\001\
\027\001\028\001\029\001\001\001\031\001\032\001\033\001\034\001\
\035\001\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\043\001\044\001\255\255\046\001\255\255\255\255\255\255\021\001\
\255\255\255\255\255\255\255\255\026\001\027\001\028\001\029\001\
\255\255\031\001\032\001\033\001\034\001\035\001\036\001\037\001\
\038\001\039\001\040\001\041\001\042\001\043\001\044\001\255\255\
\046\001\255\255\255\255\078\001\079\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\087\001\255\255\255\255\255\255\
\255\255\001\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\078\001\079\001\255\255\255\255\255\255\021\001\255\255\255\255\
\255\255\087\001\026\001\027\001\028\001\029\001\001\001\031\001\
\032\001\033\001\034\001\035\001\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\046\001\255\255\
\255\255\255\255\021\001\255\255\255\255\255\255\255\255\026\001\
\027\001\028\001\029\001\255\255\031\001\032\001\033\001\034\001\
\035\001\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\043\001\044\001\255\255\046\001\255\255\255\255\078\001\079\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\087\001\
\255\255\255\255\255\255\255\255\001\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\078\001\079\001\255\255\255\255\255\255\
\021\001\255\255\255\255\255\255\087\001\026\001\027\001\028\001\
\029\001\001\001\031\001\032\001\033\001\255\255\035\001\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\043\001\044\001\
\255\255\046\001\255\255\255\255\255\255\021\001\255\255\255\255\
\255\255\255\255\026\001\027\001\028\001\029\001\255\255\031\001\
\032\001\033\001\255\255\035\001\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\046\001\255\255\
\255\255\078\001\079\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\087\001\255\255\255\255\255\255\255\255\001\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\078\001\079\001\
\255\255\255\255\255\255\021\001\255\255\255\255\255\255\087\001\
\026\001\027\001\028\001\029\001\001\001\031\001\032\001\033\001\
\255\255\255\255\036\001\037\001\038\001\039\001\040\001\041\001\
\042\001\043\001\044\001\255\255\046\001\255\255\255\255\255\255\
\021\001\255\255\255\255\255\255\255\255\026\001\027\001\028\001\
\029\001\255\255\031\001\032\001\033\001\255\255\255\255\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\043\001\044\001\
\255\255\046\001\255\255\255\255\078\001\079\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\087\001\255\255\255\255\
\255\255\255\255\001\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\078\001\079\001\255\255\255\255\255\255\255\255\001\001\
\255\255\255\255\087\001\026\001\027\001\028\001\029\001\255\255\
\031\001\032\001\033\001\255\255\255\255\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\044\001\255\255\046\001\
\026\001\027\001\028\001\029\001\255\255\031\001\032\001\033\001\
\255\255\255\255\036\001\037\001\038\001\039\001\040\001\041\001\
\042\001\043\001\044\001\255\255\046\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\001\001\078\001\
\079\001\255\255\005\001\255\255\255\255\255\255\255\255\255\255\
\087\001\255\255\013\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\001\001\078\001\079\001\255\255\026\001\
\027\001\028\001\029\001\255\255\255\255\087\001\033\001\255\255\
\255\255\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\043\001\255\255\255\255\046\001\026\001\027\001\028\001\029\001\
\255\255\255\255\032\001\033\001\255\255\255\255\036\001\037\001\
\038\001\039\001\040\001\041\001\042\001\043\001\044\001\255\255\
\046\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\001\001\078\001\079\001\255\255\005\001\255\255\
\255\255\255\255\255\255\255\255\087\001\255\255\013\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\078\001\079\001\255\255\026\001\027\001\028\001\029\001\255\255\
\255\255\087\001\033\001\255\255\255\255\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\255\255\255\255\046\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\001\001\255\255\255\255\255\255\005\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\013\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\001\001\078\001\
\079\001\255\255\026\001\027\001\028\001\029\001\255\255\255\255\
\087\001\033\001\255\255\255\255\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\255\255\255\255\046\001\026\001\
\027\001\028\001\029\001\255\255\255\255\032\001\033\001\255\255\
\255\255\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\043\001\044\001\255\255\046\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\078\001\079\001\
\255\255\255\255\255\255\255\255\001\001\255\255\255\255\087\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\078\001\079\001\255\255\255\255\255\255\
\255\255\001\001\255\255\255\255\087\001\026\001\027\001\028\001\
\029\001\255\255\255\255\032\001\033\001\255\255\255\255\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\043\001\044\001\
\255\255\046\001\026\001\027\001\028\001\029\001\255\255\255\255\
\255\255\033\001\255\255\255\255\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\044\001\255\255\046\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\001\001\078\001\079\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\087\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\001\001\078\001\079\001\
\255\255\026\001\027\001\028\001\029\001\255\255\255\255\087\001\
\033\001\255\255\255\255\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\043\001\044\001\255\255\046\001\026\001\027\001\
\028\001\029\001\255\255\255\255\255\255\033\001\255\255\001\001\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\044\001\255\255\046\001\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\001\001\078\001\079\001\255\255\
\026\001\027\001\028\001\029\001\255\255\255\255\087\001\033\001\
\255\255\255\255\036\001\037\001\038\001\039\001\040\001\041\001\
\042\001\043\001\078\001\079\001\046\001\026\001\027\001\028\001\
\029\001\255\255\255\255\087\001\033\001\255\255\001\001\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\043\001\255\255\
\255\255\046\001\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\001\001\078\001\079\001\255\255\026\001\
\027\001\028\001\029\001\255\255\255\255\087\001\033\001\255\255\
\255\255\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\043\001\078\001\079\001\046\001\026\001\027\001\028\001\029\001\
\255\255\255\255\087\001\033\001\255\255\001\001\036\001\037\001\
\038\001\039\001\040\001\041\001\042\001\043\001\255\255\255\255\
\046\001\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\001\001\078\001\079\001\255\255\026\001\027\001\
\028\001\029\001\255\255\255\255\087\001\033\001\255\255\255\255\
\036\001\037\001\038\001\039\001\040\001\041\001\042\001\043\001\
\078\001\079\001\046\001\026\001\027\001\028\001\029\001\255\255\
\255\255\087\001\033\001\255\255\001\001\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\255\255\255\255\046\001\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\001\001\078\001\079\001\255\255\026\001\027\001\028\001\
\029\001\255\255\255\255\087\001\033\001\255\255\255\255\036\001\
\037\001\038\001\039\001\040\001\041\001\042\001\043\001\078\001\
\079\001\046\001\026\001\027\001\028\001\029\001\255\255\255\255\
\087\001\033\001\255\255\001\001\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\255\255\255\255\046\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\001\001\078\001\079\001\255\255\026\001\027\001\028\001\029\001\
\255\255\255\255\087\001\033\001\255\255\255\255\036\001\037\001\
\038\001\039\001\040\001\041\001\042\001\043\001\078\001\079\001\
\046\001\026\001\027\001\028\001\029\001\255\255\255\255\087\001\
\033\001\255\255\001\001\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\043\001\255\255\255\255\046\001\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\001\001\
\078\001\079\001\255\255\026\001\027\001\028\001\029\001\255\255\
\255\255\087\001\033\001\255\255\255\255\036\001\037\001\038\001\
\039\001\040\001\041\001\042\001\043\001\078\001\079\001\046\001\
\026\001\027\001\028\001\029\001\255\255\255\255\087\001\033\001\
\255\255\001\001\036\001\037\001\038\001\039\001\040\001\041\001\
\042\001\043\001\255\255\255\255\046\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\001\001\078\001\
\079\001\255\255\026\001\027\001\028\001\029\001\255\255\255\255\
\087\001\033\001\255\255\255\255\036\001\037\001\038\001\039\001\
\040\001\041\001\042\001\043\001\078\001\079\001\046\001\026\001\
\027\001\028\001\029\001\255\255\255\255\087\001\033\001\255\255\
\001\001\036\001\037\001\038\001\039\001\040\001\041\001\042\001\
\043\001\255\255\255\255\046\001\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\078\001\079\001\
\255\255\026\001\027\001\028\001\029\001\255\255\255\255\087\001\
\033\001\255\255\255\255\036\001\037\001\038\001\039\001\040\001\
\041\001\042\001\043\001\078\001\079\001\046\001\255\255\255\255\
\255\255\255\255\255\255\255\255\087\001\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\255\
\255\255\255\255\255\255\255\255\255\255\078\001\079\001\255\255\
\255\255\255\255\255\255\255\255\255\255\255\255\087\001"

let yynames_const = "\
  TOK_EOF\000\
  TOK_COLUMN\000\
  TOK_COMA\000\
  TOK_ARROW\000\
  TOK_SEMICOLUMN\000\
  TOK_LPAR\000\
  TOK_RPAR\000\
  TOK_IMPLIES\000\
  TOK_EQUAL\000\
  TOK_DIFF\000\
  TOK_AND\000\
  TOK_OR\000\
  TOK_QUESTION_MARK\000\
  TOK_AROBAT\000\
  TOK_LBRACKET\000\
  TOK_RBRACKET\000\
  TOK_SPECIF\000\
  TOK_SORTS\000\
  TOK_CONSTRUCTORS\000\
  TOK_FUNCTIONS\000\
  TOK_FUNCTION_PROPS\000\
  TOK_EQUIV\000\
  TOK_STATUS\000\
  TOK_AXIOMS\000\
  TOK_OBS_SORTS\000\
  TOK_CONJECTURES\000\
  TOK_COMPLETE_TERMS\000\
  TOK_LEMMAS\000\
  TOK_STRATEGIES\000\
  TOK_USE\000\
  TOK_PROPERTIES\000\
  TOK_PRIORITIES\000\
  TOK_IND_PRIORITIES\000\
  TOK_TEST_SETS\000\
  TOK_NULLARY_SORTS\000\
  TOK_NORM\000\
  TOK_RPOCOMPARE\000\
  TOK_COMPARE\000\
  TOK_MAX_COMPARE\000\
  TOK_STOP_ON_CLAUSE\000\
  TOK_EXTRACT\000\
  TOK_MATCH\000\
  TOK_AC_SUBSUMES\000\
  TOK_CRITICAL_CONTEXT_SETS\000\
  TOK_CRITIC\000\
  TOK_HYPOTHESES\000\
  TOK_LEFTRIGHT\000\
  TOK_MULTISET\000\
  TOK_RIGHTLEFT\000\
  TOK_AC\000\
  TOK_ASSOC\000\
  TOK_TRY\000\
  TOK_SATURATE\000\
  TOK_ON\000\
  TOK_REDUCTION\000\
  TOK_REPEAT\000\
  TOK_REPEAT_PLUS\000\
  TOK_TAUTOLOGY\000\
  TOK_GENERATE\000\
  TOK_GENERATE_EQ\000\
  TOK_GENERATE_OBS\000\
  TOK_PARTIAL_CASE_REWRITING\000\
  TOK_TOTAL_CASE_REWRITING\000\
  TOK_CONTEXTUAL_REWRITING\000\
  TOK_CONGRUENCE_CLOSURE\000\
  TOK_EQUATIONAL_REWRITING\000\
  TOK_REWRITING\000\
  TOK_NEGATIVE_DECOMPOSITION\000\
  TOK_POSITIVE_DECOMPOSITION\000\
  TOK_POSITIVE_CLASH\000\
  TOK_ELIMINATE_TRIVIAL_LITERAL\000\
  TOK_ELIMINATE_REDUNDANT_LITERAL\000\
  TOK_AUTO_SIMPLIFICATION\000\
  TOK_COMPLEMENT\000\
  TOK_SUBSUMPTION\000\
  TOK_AUGMENTATION\000\
  TOK_NEGATIVE_CLASH\000\
  TOK_START_WITH\000\
  TOK_AUGMENTATION_STRATEGY\000\
  TOK_GOTO\000\
  TOK_ADDPREMISE\000\
  TOK_SIMPLIFY\000\
  TOK_GREATER\000\
  TOK_DELETE\000\
  TOK_ID\000\
  TOK_PRINT_GOALS\000\
  TOK_PRINT_CAML\000\
  TOK_PRINT_GOALS_HISTORY\000\
  TOK_OPEN_SUBSTITUTION\000\
  TOK_CLOSE_SUBSTITUTION\000\
  "

let yynames_block = "\
  TOK_IDENT\000\
  TOK_STRING\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'spec_fields) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'spec_ordering) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'spec_prop) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'spec_problem) in
    Obj.repr(
# 721 "sources/parser.mly"
  ( yy_queue )
# 2103 "sources/parser.ml"
               :  Strategies.problem_token Queue.t ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'spec_fields) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'spec_ordering) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'spec_prop) in
    Obj.repr(
# 723 "sources/parser.mly"
  (
    let q = Queue.create ()
    in let () = Queue.add (Message_token "Correct specification") q
    in q
  )
# 2116 "sources/parser.ml"
               :  Strategies.problem_token Queue.t ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 6 : 'opt_specif_name) in
    let _2 = (Parsing.peek_val __caml_parser_env 5 : 'opt_specif_use) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'opt_specif_sorts) in
    let _4 = (Parsing.peek_val __caml_parser_env 3 : 'opt_specif_obs_sorts) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'opt_specif_constructors) in
    let _6 = (Parsing.peek_val __caml_parser_env 1 : 'opt_specif_functions) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'opt_specif_axioms) in
    Obj.repr(
# 739 "sources/parser.mly"
  ( 
  update_dico_free_constructors () ;
    if !free_constructors
    then buffered_output "All constructors are free"
    else () ;
    all_defined_functions := List.map (fun x -> - x) (List.tl (list_create (- !function_counter))) ;
    all_constructors := list_create !constructor_counter 
(*     default_fill_order_dico_cc (); *)
  )
# 2137 "sources/parser.ml"
               : 'spec_fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 5 : 'opt_specif_greater) in
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'opt_specif_equivs) in
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'opt_specif_status) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'opt_specif_test_sets) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'opt_specif_nullary_sorts) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'opt_specif_function_props) in
    Obj.repr(
# 756 "sources/parser.mly"
  (
    let () = determine_ac_category () in
    (* Orient axioms *)
    let rec fn = function
      	[] -> [] 
      | (f, l, c)::t ->
          try
            let c' = c#orient in
            let () = buffered_output ("\t" ^ c'#string) in
            (f, l, c')::fn t
          with (Failure "orient") ->
            parsed_gfile := f ;
            linenumber := l ;
	    let concl = List.hd ((fun (_, p) -> p) c#content) in
	    match concl#content with
		Lit_equal _ 
	      | Lit_rule _ -> 
      		  let c' = c#force_orientation in
		  let () = buffered_output ("\t" ^ c'#string) in
		  (* let () = broken_order := true in  *)
		  let () = buffered_output ("\nWARNING: the axiom [" ^ (string_of_int c#number) ^ "] is not orientable in a rewrite rule using the current order") in
		  (f, l, c')::fn t

	      | Lit_diff _ -> parse_failwith ("The axiom [" ^ (string_of_int c#number) ^ "] is not orientable") 
    in 
    buffered_output "Orienting axioms" ;
(*     if !use_order *)
(*     then *)
    let l = fn !yy_axioms
    in let () = yy_axioms := l in
(*     else *)
(*       () ; *)
    rewrite_system#init (List.map (fun (_, _, x) -> x) !yy_axioms) ;

(*    print_clause_list rewrite_system#content ;*)
(*     buffered_output "\nThe current order is :"; *)
    print_dico_order (); 
    print_dico_equivalence ();
    buffered_output ("Computing nullary sorts") ;
    flush stdout ;
    update_dico_sort_nullarity () ;

    buffered_output ("Computing nullary individuals") ;
    flush stdout ;
    update_dico_nullary_individuals () ;

    if !observational_proof then 
      begin
	buffered_output ("Using test-sets version " ^ (string_of_int !test_set_version)) ;
	buffered_output "Computing test sets" ;
	if List.length !yy_axioms > 0
	then !compute_test_set () ;
	!print_dico_test_set () ;
	
	compute_critical_context_set ();
      end;
      
(*     buffered_output ("Using test-sets version " ^ (string_of_int !test_set_version)) ; *)
(*     buffered_output "Computing test sets" ; *)
(*     if (List.length !yy_axioms > 0) && (not !int_specif_defined) (* the int sort cannot be computed with the test set version 0 in "int" theory *) *)
(*     then !compute_test_set ()  *)
(*     else if (!int_specif_defined) then *)
(*       rewrite_system#compute_induction_positions_v0        *)
(*     else (); *)
    if !boolean_specification
    then buffered_output "We have a boolean specification"
    else buffered_output "We do not have a boolean specification" ;
)
# 2216 "sources/parser.ml"
               : 'spec_ordering))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'opt_specif_properties) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'opt_specif_priorities) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'opt_specif_critical_context_sets) in
    Obj.repr(
# 829 "sources/parser.mly"
  ( )
# 2225 "sources/parser.ml"
               : 'spec_prop))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'spec_problem_field) in
    Obj.repr(
# 833 "sources/parser.mly"
  ( [_1] )
# 2232 "sources/parser.ml"
               : 'spec_problem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'spec_problem) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'spec_problem_field) in
    Obj.repr(
# 835 "sources/parser.mly"
  ( _1 @ [_2] )
# 2240 "sources/parser.ml"
               : 'spec_problem))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_lemmas) in
    Obj.repr(
# 839 "sources/parser.mly"
  ( )
# 2247 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_conjectures) in
    Obj.repr(
# 841 "sources/parser.mly"
  ( )
# 2254 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_hypotheses) in
    Obj.repr(
# 843 "sources/parser.mly"
  ( )
# 2261 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_complete_terms) in
    Obj.repr(
# 845 "sources/parser.mly"
  ( )
# 2268 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_ind_priorities) in
    Obj.repr(
# 847 "sources/parser.mly"
  ( )
# 2275 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_strategies) in
    Obj.repr(
# 849 "sources/parser.mly"
  ( )
# 2282 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_startpoint) in
    Obj.repr(
# 851 "sources/parser.mly"
  ( )
# 2289 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_augmentation) in
    Obj.repr(
# 853 "sources/parser.mly"
  ( )
# 2296 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_norm) in
    Obj.repr(
# 855 "sources/parser.mly"
  ( )
# 2303 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_rpocompare) in
    Obj.repr(
# 857 "sources/parser.mly"
  ( )
# 2310 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_compare) in
    Obj.repr(
# 859 "sources/parser.mly"
  ( )
# 2317 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_max_compare) in
    Obj.repr(
# 861 "sources/parser.mly"
  ( )
# 2324 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_stop_on_clause) in
    Obj.repr(
# 863 "sources/parser.mly"
  ( )
# 2331 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_extract) in
    Obj.repr(
# 865 "sources/parser.mly"
  ( )
# 2338 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_match) in
    Obj.repr(
# 867 "sources/parser.mly"
  ( )
# 2345 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_ac_subsumes) in
    Obj.repr(
# 869 "sources/parser.mly"
  ( )
# 2352 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'print_caml) in
    Obj.repr(
# 871 "sources/parser.mly"
  ( )
# 2359 "sources/parser.ml"
               : 'spec_problem_field))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 877 "sources/parser.mly"
  ( spec_name := _3 )
# 2366 "sources/parser.ml"
               : 'opt_specif_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 879 "sources/parser.mly"
  ( )
# 2372 "sources/parser.ml"
               : 'opt_specif_name))
; (fun __caml_parser_env ->
    Obj.repr(
# 881 "sources/parser.mly"
  ( )
# 2378 "sources/parser.ml"
               : 'opt_specif_name))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_idents) in
    Obj.repr(
# 885 "sources/parser.mly"
  ( 
    let rec fn = function
      [] -> ()
    | h::_ ->
        try
          add_predefined_specif h
        with (Failure "add_predefined_specif") ->
          parse_failwith ("\"" ^ h ^ "\" is not a valid predefined specification") in
    fn _3 )
# 2393 "sources/parser.ml"
               : 'opt_specif_use))
; (fun __caml_parser_env ->
    Obj.repr(
# 895 "sources/parser.mly"
  ( )
# 2399 "sources/parser.ml"
               : 'opt_specif_use))
; (fun __caml_parser_env ->
    Obj.repr(
# 897 "sources/parser.mly"
  ( )
# 2405 "sources/parser.ml"
               : 'opt_specif_use))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 901 "sources/parser.mly"
  ( [ _1 ] )
# 2412 "sources/parser.ml"
               : 'list_of_idents))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_idents) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 903 "sources/parser.mly"
  ( _1 @ [ _2 ] )
# 2420 "sources/parser.ml"
               : 'list_of_idents))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'get_list_of_sorts) in
    Obj.repr(
# 907 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed sorts" ;
    flush stdout )
# 2428 "sources/parser.ml"
               : 'opt_specif_sorts))
; (fun __caml_parser_env ->
    Obj.repr(
# 910 "sources/parser.mly"
  ( )
# 2434 "sources/parser.ml"
               : 'opt_specif_sorts))
; (fun __caml_parser_env ->
    Obj.repr(
# 912 "sources/parser.mly"
  ( )
# 2440 "sources/parser.ml"
               : 'opt_specif_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 916 "sources/parser.mly"
  ( selective_add_sort dico_sort_string sort_counter _1 )
# 2447 "sources/parser.ml"
               : 'get_list_of_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'get_list_of_sorts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 918 "sources/parser.mly"
  ( selective_add_sort dico_sort_string sort_counter _2 )
# 2455 "sources/parser.ml"
               : 'get_list_of_sorts))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_constructors) in
    Obj.repr(
# 922 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed constructors" ;
    flush stdout )
# 2463 "sources/parser.ml"
               : 'opt_specif_constructors))
; (fun __caml_parser_env ->
    Obj.repr(
# 925 "sources/parser.mly"
  ( )
# 2469 "sources/parser.ml"
               : 'opt_specif_constructors))
; (fun __caml_parser_env ->
    Obj.repr(
# 927 "sources/parser.mly"
  ( )
# 2475 "sources/parser.ml"
               : 'opt_specif_constructors))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'get_list_of_obs_sorts) in
    Obj.repr(
# 931 "sources/parser.mly"
  ( buffered_output "Successfully parsed observable sorts" ;
    flush stdout )
# 2483 "sources/parser.ml"
               : 'opt_specif_obs_sorts))
; (fun __caml_parser_env ->
    Obj.repr(
# 934 "sources/parser.mly"
  ( )
# 2489 "sources/parser.ml"
               : 'opt_specif_obs_sorts))
; (fun __caml_parser_env ->
    Obj.repr(
# 936 "sources/parser.mly"
  ( )
# 2495 "sources/parser.ml"
               : 'opt_specif_obs_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 940 "sources/parser.mly"
  ( try
     let () = observational_proof := true in
     let k = (try (dico_sort_string#find_key _1) with Failure "find_key" -> failwith "get_list_of_obs_sorts") in
     match k with
	 Def_sort i -> 
	   let ref_i = ref i in 
	   selective_add_sort dico_obs_sort ref_i (*obs_sort_counter*) _1
       | Abstr_sort0 _| Abstr_sort1 _ | Abstr_sort2 _  -> failwith "get_list_of_obs_sorts"
     with Not_found ->
       selective_add_sort dico_sort_string sort_counter _1
     )
# 2512 "sources/parser.ml"
               : 'get_list_of_obs_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'get_list_of_obs_sorts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 952 "sources/parser.mly"
  ( 
    try
     let k = (try (dico_sort_string#find_key _2) with Failure "find_key" -> failwith "get_list_of_obs_sorts") in
     match k with
	 Def_sort i ->
	   let ref_i = ref i in
	   selective_add_sort dico_obs_sort ref_i (*obs_sort_counter*) _2
       |  Abstr_sort0 _| Abstr_sort1 _| Abstr_sort2 _  -> failwith "get_list_of_obs_sorts"
	     
    with Not_found ->
     selective_add_sort dico_sort_string sort_counter _2

(*    let a = selective_add dico_sort_string sort_counter $2 in
    selective_add dico_obs_sort obs_sort_counter $2*))
# 2533 "sources/parser.ml"
               : 'get_list_of_obs_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_constructor) in
    Obj.repr(
# 970 "sources/parser.mly"
  ( )
# 2540 "sources/parser.ml"
               : 'list_of_constructors))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_constructors) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_constructor) in
    Obj.repr(
# 972 "sources/parser.mly"
  ( )
# 2548 "sources/parser.ml"
               : 'list_of_constructors))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'specif_profile) in
    Obj.repr(
# 976 "sources/parser.mly"
  (process_specif_symbol constructor_counter _1 _3  )
# 2556 "sources/parser.ml"
               : 'specif_constructor))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_functions) in
    Obj.repr(
# 980 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed functions" ;
    flush stdout )
# 2564 "sources/parser.ml"
               : 'opt_specif_functions))
; (fun __caml_parser_env ->
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_functions) in
    Obj.repr(
# 983 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed functions" ;
    flush stdout )
# 2572 "sources/parser.ml"
               : 'opt_specif_functions))
; (fun __caml_parser_env ->
    Obj.repr(
# 986 "sources/parser.mly"
  ( )
# 2578 "sources/parser.ml"
               : 'opt_specif_functions))
; (fun __caml_parser_env ->
    Obj.repr(
# 988 "sources/parser.mly"
  ( )
# 2584 "sources/parser.ml"
               : 'opt_specif_functions))
; (fun __caml_parser_env ->
    Obj.repr(
# 990 "sources/parser.mly"
  ( )
# 2590 "sources/parser.ml"
               : 'opt_specif_functions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_function) in
    Obj.repr(
# 994 "sources/parser.mly"
  ( )
# 2597 "sources/parser.ml"
               : 'list_of_functions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_functions) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_function) in
    Obj.repr(
# 996 "sources/parser.mly"
  ( )
# 2605 "sources/parser.ml"
               : 'list_of_functions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'specif_profile) in
    Obj.repr(
# 1000 "sources/parser.mly"
  ( process_specif_symbol function_counter _1 _3 )
# 2613 "sources/parser.ml"
               : 'specif_function))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'list_of_sorts) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_sorts) in
    Obj.repr(
# 1004 "sources/parser.mly"
  ( if List.length _3 > 1 then parse_failwith "The function should return only one value" else (_1, List.hd _3) )
# 2621 "sources/parser.ml"
               : 'specif_profile))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_sorts) in
    Obj.repr(
# 1006 "sources/parser.mly"
  ( ([], List.hd _1) )
# 2628 "sources/parser.ml"
               : 'specif_profile))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_sorts) in
    Obj.repr(
# 1008 "sources/parser.mly"
  (  if List.length _2 > 1 then parse_failwith "The function should return only one value" else  ([], List.hd _2) )
# 2635 "sources/parser.ml"
               : 'specif_profile))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ident_sort) in
    Obj.repr(
# 1013 "sources/parser.mly"
  (_1)
# 2642 "sources/parser.ml"
               : 'list_of_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_sorts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'ident_sort) in
    Obj.repr(
# 1015 "sources/parser.mly"
      (_1 @ _2)
# 2650 "sources/parser.ml"
               : 'list_of_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1019 "sources/parser.mly"
  ( let s =
      find_sort_id _1
  in [ s ] )
# 2659 "sources/parser.ml"
               : 'ident_sort))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'ident_sort) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'end_of_sorts) in
    Obj.repr(
# 1023 "sources/parser.mly"
  (let arg = List.hd _3 in
   let s = find_sort_id _2 in 
   if _4 = [] then [ Abstr_sort1 ((def_sort_id s), arg)]
   else 
     let arg' = List.hd _4 in
     [ Abstr_sort2 ((def_sort_id s), arg, arg')]
 )
# 2674 "sources/parser.ml"
               : 'ident_sort))
; (fun __caml_parser_env ->
    Obj.repr(
# 1034 "sources/parser.mly"
  ([])
# 2680 "sources/parser.ml"
               : 'end_of_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'ident_sort) in
    Obj.repr(
# 1036 "sources/parser.mly"
  (_1)
# 2687 "sources/parser.ml"
               : 'end_of_sorts))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'pos_codes_true) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_horn_clauses) in
    Obj.repr(
# 1041 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed axioms" ; flush stdout ;
    yy_axioms := List.map introduce_var_exist _4 ;
    if !debug_mode then print_clause_list (List.map (fun (_, _, x) -> x) !yy_axioms) )
# 2697 "sources/parser.ml"
               : 'opt_specif_axioms))
; (fun __caml_parser_env ->
    Obj.repr(
# 1045 "sources/parser.mly"
  ( )
# 2703 "sources/parser.ml"
               : 'opt_specif_axioms))
; (fun __caml_parser_env ->
    Obj.repr(
# 1047 "sources/parser.mly"
  ( )
# 2709 "sources/parser.ml"
               : 'opt_specif_axioms))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'list_of_raw_symbols) in
    Obj.repr(
# 1053 "sources/parser.mly"
  (process_function_props _3 Prop_ac )
# 2716 "sources/parser.ml"
               : 'opt_specif_function_props))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'list_of_raw_symbols) in
    Obj.repr(
# 1055 "sources/parser.mly"
  (process_function_props _3 Prop_assoc )
# 2723 "sources/parser.ml"
               : 'opt_specif_function_props))
; (fun __caml_parser_env ->
    Obj.repr(
# 1057 "sources/parser.mly"
  ( )
# 2729 "sources/parser.ml"
               : 'opt_specif_function_props))
; (fun __caml_parser_env ->
    Obj.repr(
# 1059 "sources/parser.mly"
  ()
# 2735 "sources/parser.ml"
               : 'opt_specif_function_props))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1063 "sources/parser.mly"
  ( [ _1 ] )
# 2742 "sources/parser.ml"
               : 'list_of_raw_symbols))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_raw_symbols) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1065 "sources/parser.mly"
  ( _1 @ [ _2 ] )
# 2750 "sources/parser.ml"
               : 'list_of_raw_symbols))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1070 "sources/parser.mly"
  ( [ find_symbol_id _1 ] )
# 2757 "sources/parser.ml"
               : 'list_of_symbols))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_symbols) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1072 "sources/parser.mly"
  ( let s = find_symbol_id _2 in 
    if not (List.mem s _1) then _1 @ [ find_symbol_id _2 ] else parse_failwith (_2 ^ " is duplicated") )
# 2766 "sources/parser.ml"
               : 'list_of_symbols))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'init_order_dico) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_greater) in
    Obj.repr(
# 1079 "sources/parser.mly"
  (     (* print_dico_order () *))
# 2774 "sources/parser.ml"
               : 'opt_specif_greater))
; (fun __caml_parser_env ->
    Obj.repr(
# 1081 "sources/parser.mly"
  ( )
# 2780 "sources/parser.ml"
               : 'opt_specif_greater))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'init_equiv_dico) in
    Obj.repr(
# 1083 "sources/parser.mly"
  ( let () = buffered_output "No order provided" in default_fill_order_dico () )
# 2787 "sources/parser.ml"
               : 'opt_specif_greater))
; (fun __caml_parser_env ->
    Obj.repr(
# 1086 "sources/parser.mly"
  ( 
    print_dico_const_string ();
    dico_order#init (!all_defined_functions @ !all_constructors) ;
    flush stdout )
# 2796 "sources/parser.ml"
               : 'init_order_dico))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_greater) in
    Obj.repr(
# 1093 "sources/parser.mly"
  ( )
# 2803 "sources/parser.ml"
               : 'list_of_greater))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_greater) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_greater) in
    Obj.repr(
# 1095 "sources/parser.mly"
  ( )
# 2811 "sources/parser.ml"
               : 'list_of_greater))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_symbols) in
    Obj.repr(
# 1099 "sources/parser.mly"
  (  let v = find_symbol_id _1 in
     List.iter (fun x -> dico_order#add_couple v x) _3 )
# 2820 "sources/parser.ml"
               : 'specif_greater))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'init_equiv_dico) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_equivs) in
    Obj.repr(
# 1105 "sources/parser.mly"
  ( 
    if dico_order#empty
    then
      let () = buffered_output "Order dico is empty" in default_fill_order_dico ()
    else
      try
(* 	print_dico_equivalence (); *)
        dico_order#merge_equivalence_relation dico_equivalence ;
        buffered_output "\nSuccessfully parsed equivalence relation" ; flush stdout
      with (Failure "rehash") ->
        parse_failwith "t here are incompatibilities between the order and equivalence relations"
  )
# 2839 "sources/parser.ml"
               : 'opt_specif_equivs))
; (fun __caml_parser_env ->
    Obj.repr(
# 1118 "sources/parser.mly"
  ( if dico_order#empty
    then
      let () = buffered_output "Order dico is empty" in default_fill_order_dico ()
    else
      ()
  )
# 2850 "sources/parser.ml"
               : 'opt_specif_equivs))
; (fun __caml_parser_env ->
    Obj.repr(
# 1125 "sources/parser.mly"
  ( if dico_order#empty
    then
      let () = buffered_output "Order dico is empty" in default_fill_order_dico ()
    else
      ()
  )
# 2861 "sources/parser.ml"
               : 'opt_specif_equivs))
; (fun __caml_parser_env ->
    Obj.repr(
# 1134 "sources/parser.mly"
  ( 

(*     List.iter (fun x -> (buffered_output ("init_order_dico : x = " ^ (string_of_int x)))) (!all_defined_functions @ !all_constructors); *)
    dico_equivalence#init dico_order#keys; (* (!all_defined_functions @ !all_constructors) ; *)
    flush stdout )
# 2871 "sources/parser.ml"
               : 'init_equiv_dico))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_equiv) in
    Obj.repr(
# 1142 "sources/parser.mly"
  ( )
# 2878 "sources/parser.ml"
               : 'list_of_equivs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_equivs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_equiv) in
    Obj.repr(
# 1144 "sources/parser.mly"
  ( )
# 2886 "sources/parser.ml"
               : 'list_of_equivs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_symbols) in
    Obj.repr(
# 1148 "sources/parser.mly"
  ( match _1 with
      [] -> failwith "I'm bewildered"
      | _::_ ->  dico_equivalence#fill (fun _ _ -> true) _1;  )
# 2895 "sources/parser.ml"
               : 'specif_equiv))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_statuses) in
    Obj.repr(
# 1154 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed statuses" ; flush stdout ;
    print_dico_id_status () ;
    (try complete_status_dico ()
    with (Failure s) -> parse_failwith ("Symbol \"" ^ s ^ "\" is ac and must have multiset status") );
    try check_status_equivalent_symbols ()
    with (Failure "check_status_equivalent_symbols") -> parse_failwith "equivalent symbols must have the same status"
  )
# 2908 "sources/parser.ml"
               : 'opt_specif_status))
; (fun __caml_parser_env ->
    Obj.repr(
# 1162 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed statuses" ; flush stdout ;
    print_dico_id_status () ;
    (try complete_status_dico ()
    with (Failure s) -> parse_failwith ("Symbol \"" ^ s ^ "\" is ac and must have multiset status") );
    try check_status_equivalent_symbols ()
    with (Failure "check_status_equivalent_symbols") -> parse_failwith "equivalent symbols must have the same status"
  )
# 2920 "sources/parser.ml"
               : 'opt_specif_status))
; (fun __caml_parser_env ->
    Obj.repr(
# 1170 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed statuses" ; flush stdout ;
    print_dico_id_status () ;
    (try complete_status_dico ()
    with (Failure s) -> parse_failwith ("Symbol \"" ^ s ^ "\" is ac and must have multiset status") );
    try check_status_equivalent_symbols ()
    with (Failure "check_status_equivalent_symbols") -> parse_failwith "equivalent symbols must have the same status"
  )
# 2932 "sources/parser.ml"
               : 'opt_specif_status))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_status) in
    Obj.repr(
# 1180 "sources/parser.mly"
  ( )
# 2939 "sources/parser.ml"
               : 'list_of_statuses))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_statuses) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_status) in
    Obj.repr(
# 1182 "sources/parser.mly"
  ( )
# 2947 "sources/parser.ml"
               : 'list_of_statuses))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_symbols) in
    Obj.repr(
# 1186 "sources/parser.mly"
  (
    try
      let () = List.iter (fun x -> if symbol_is_ac x then failwith (dico_const_string#find x) else ()) _1
      in List.iter (fun x -> add_to_status_dico x Left) _1
    with (Failure s) -> parse_failwith ("Symbol \"" ^ s ^ "\" is ac and must have multiset status") 
      | Not_found -> failwith "raising Not_found in specif_status")
# 2959 "sources/parser.ml"
               : 'specif_status))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_symbols) in
    Obj.repr(
# 1193 "sources/parser.mly"
  ( try
      let () = List.iter (fun x -> if symbol_is_ac x then failwith (dico_const_string#find x) else ()) _1
      in List.iter (fun x -> add_to_status_dico x Right) _1
    with (Failure s) -> parse_failwith ("Symbol \"" ^ s ^ "\" is ac and must have multiset status") 
      | Not_found -> failwith "raising Not_found in specif_status")
# 2970 "sources/parser.ml"
               : 'specif_status))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_symbols) in
    Obj.repr(
# 1199 "sources/parser.mly"
      ( List.iter (fun x -> add_to_status_dico x Multiset) _1 )
# 2977 "sources/parser.ml"
               : 'specif_status))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_properties) in
    Obj.repr(
# 1203 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed properties" ; flush stdout )
# 2984 "sources/parser.ml"
               : 'opt_specif_properties))
; (fun __caml_parser_env ->
    Obj.repr(
# 1205 "sources/parser.mly"
  ( )
# 2990 "sources/parser.ml"
               : 'opt_specif_properties))
; (fun __caml_parser_env ->
    Obj.repr(
# 1207 "sources/parser.mly"
  ( )
# 2996 "sources/parser.ml"
               : 'opt_specif_properties))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 1211 "sources/parser.mly"
  ( try
      let p = Hashtbl.find oracles_table _1
      in p := true
    with Not_found ->
      try
        let p = Hashtbl.find tests_table _1
        in p ()
      with Not_found ->
        parse_failwith ("property \"" ^ _1 ^ "\" is not defined") )
# 3011 "sources/parser.ml"
               : 'list_of_properties))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_properties) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 1221 "sources/parser.mly"
  ( try
      let p = Hashtbl.find oracles_table _2
      in p := true
    with Not_found ->
      try
        let p = Hashtbl.find tests_table _2
        in p ()
      with Not_found -> parse_failwith ("property \"" ^ _2 ^ "\" is not defined") )
# 3026 "sources/parser.ml"
               : 'list_of_properties))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_priorities) in
    Obj.repr(
# 1232 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed priorities" ; flush stdout ;
    !fill_default_induction_positions _3 ;
    buffered_output "Generate will be attempted on the following positions:" ;
    print_induction_symbols_priorities () )
# 3036 "sources/parser.ml"
               : 'opt_specif_priorities))
; (fun __caml_parser_env ->
    Obj.repr(
# 1237 "sources/parser.mly"
  ( !fill_default_induction_positions [] ;
    buffered_output "Generate will be attempted on the following positions:" ;
    print_induction_symbols_priorities () )
# 3044 "sources/parser.ml"
               : 'opt_specif_priorities))
; (fun __caml_parser_env ->
    Obj.repr(
# 1241 "sources/parser.mly"
  ( !fill_default_induction_positions [] ;
     buffered_output "Generate will be attempted on the following positions:" ;
     print_induction_symbols_priorities ()
  )
# 3053 "sources/parser.ml"
               : 'opt_specif_priorities))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_function_symbols) in
    Obj.repr(
# 1248 "sources/parser.mly"
  ( [ _1 ] )
# 3060 "sources/parser.ml"
               : 'list_of_priorities))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_priorities) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_function_symbols) in
    Obj.repr(
# 1250 "sources/parser.mly"
  ( _1 @ [ _2 ] )
# 3068 "sources/parser.ml"
               : 'list_of_priorities))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_fun_with_positions) in
    Obj.repr(
# 1254 "sources/parser.mly"
  ( _1 )
# 3075 "sources/parser.ml"
               : 'list_of_function_symbols))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_function_symbols) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_fun_with_positions) in
    Obj.repr(
# 1256 "sources/parser.mly"
  ( merge_induction_positions _1 _2 )
# 3083 "sources/parser.ml"
               : 'list_of_function_symbols))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1260 "sources/parser.mly"
  (   
    let n =
      try
	let n = dico_const_string#find_key _1
	in if is_defined n
	then n
	else parse_failwith ("symbol " ^ _1 ^ " is not a defined function")
      with Failure "find_key" -> parse_failwith ("symbol " ^ _1 ^ " is not a defined function")
    in 
    try
      let l = (dico_ind_positions_v0#find n) in
      let all_ind_pos = Sort.list (<=) (List.map (fun p -> n, p) (list_remove_doubles (=) (List.flatten l))) in
      Ind_pos_position all_ind_pos
    with Not_found -> parse_failwith ("symbol \"" ^ _1 ^ "\" has no induction positions") )
# 3103 "sources/parser.ml"
               : 'specif_fun_with_positions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_positions) in
    Obj.repr(
# 1275 "sources/parser.mly"
  ( 
    let n =
      try
        let n = dico_const_string#find_key _1
        in if is_defined n
        then n
        else parse_failwith ("symbol " ^ _1 ^ " is not a defined function")
      with Failure "find_key" -> parse_failwith ("symbol " ^ _1 ^ " is not a defined function")
    in try
      let l = dico_ind_positions_v0#find n in
      let all_ind_pos = list_remove_doubles (=) (List.flatten l) in
      let _ = generic_setminus all_ind_pos _3
      in Ind_pos_position ((Sort.list (<=) (List.map (fun p -> n, p) _3)))
    with Not_found -> parse_failwith ("symbol \"" ^ _1 ^ "\" has no induction positions")
      | (Failure "setminus") -> parse_failwith ("provided induction positions of symbol \"" ^ _1 ^
        "\" are not a subset of actual positions") )
# 3126 "sources/parser.ml"
               : 'specif_fun_with_positions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_path) in
    Obj.repr(
# 1292 "sources/parser.mly"
  (
    Ind_pos_void
  )
# 3135 "sources/parser.ml"
               : 'specif_fun_with_positions))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_sym_int_couples) in
    Obj.repr(
# 1298 "sources/parser.mly"
  ( _2 )
# 3142 "sources/parser.ml"
               : 'specif_path))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_path) in
    Obj.repr(
# 1302 "sources/parser.mly"
  ( [_1] )
# 3149 "sources/parser.ml"
               : 'list_of_paths))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_paths) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_path) in
    Obj.repr(
# 1304 "sources/parser.mly"
  ( _1 @ [_2] )
# 3157 "sources/parser.ml"
               : 'list_of_paths))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'sym_int_couple) in
    Obj.repr(
# 1307 "sources/parser.mly"
  ( [ _1 ] )
# 3164 "sources/parser.ml"
               : 'list_of_sym_int_couples))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_sym_int_couples) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'sym_int_couple) in
    Obj.repr(
# 1309 "sources/parser.mly"
  ( _1 @ [ _3 ] )
# 3172 "sources/parser.ml"
               : 'list_of_sym_int_couples))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1313 "sources/parser.mly"
  ( let f = find_symbol_id _1
    and i = parse_positive_int _3
    in f, i )
# 3182 "sources/parser.ml"
               : 'sym_int_couple))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_test_sets) in
    Obj.repr(
# 1321 "sources/parser.mly"
  ( 
(*     buffered_output "\nSuccessfully parsed test sets" ;  *)
(*     flush stdout; *)
(*     !print_dico_test_set () *)
  )
# 3193 "sources/parser.ml"
               : 'opt_specif_test_sets))
; (fun __caml_parser_env ->
    Obj.repr(
# 1327 "sources/parser.mly"
  ( )
# 3199 "sources/parser.ml"
               : 'opt_specif_test_sets))
; (fun __caml_parser_env ->
    Obj.repr(
# 1329 "sources/parser.mly"
  ()
# 3205 "sources/parser.ml"
               : 'opt_specif_test_sets))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_test_set) in
    Obj.repr(
# 1333 "sources/parser.mly"
  ( )
# 3212 "sources/parser.ml"
               : 'list_of_test_sets))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_test_sets) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_test_set) in
    Obj.repr(
# 1335 "sources/parser.mly"
  ( )
# 3220 "sources/parser.ml"
               : 'list_of_test_sets))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_terms) in
    Obj.repr(
# 1339 "sources/parser.mly"
  ( 
  )
# 3229 "sources/parser.ml"
               : 'specif_test_set))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'list_of_paths) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_terms) in
    Obj.repr(
# 1342 "sources/parser.mly"
  ( )
# 3237 "sources/parser.ml"
               : 'specif_test_set))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_nullary_sorts) in
    Obj.repr(
# 1346 "sources/parser.mly"
 (
   let fn string = 
     let s = find_sort_id string in
     try 
       let _ = dico_sort_nullarity#find s in
       buffered_output ("The sort \"" ^ string ^ "\" is already in the dictionary of nullary sorts"); flush stdout 
     with Not_found -> dico_sort_nullarity#add s true
   in List.iter fn _3;
	
    buffered_output "\nSuccessfully parsed nullary sorts" ; 
    flush stdout;
     buffered_output "WARNING: The user introduced the following nullary sorts !" ; flush stdout;  
    print_dico_sort_nullarity ()
  )
# 3257 "sources/parser.ml"
               : 'opt_specif_nullary_sorts))
; (fun __caml_parser_env ->
    Obj.repr(
# 1361 "sources/parser.mly"
  ( )
# 3263 "sources/parser.ml"
               : 'opt_specif_nullary_sorts))
; (fun __caml_parser_env ->
    Obj.repr(
# 1363 "sources/parser.mly"
  ( )
# 3269 "sources/parser.ml"
               : 'opt_specif_nullary_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_nullary_sort) in
    Obj.repr(
# 1367 "sources/parser.mly"
    ([_1] )
# 3276 "sources/parser.ml"
               : 'list_of_nullary_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_nullary_sorts) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_nullary_sort) in
    Obj.repr(
# 1369 "sources/parser.mly"
    ( _1 @ [_2])
# 3284 "sources/parser.ml"
               : 'list_of_nullary_sorts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1373 "sources/parser.mly"
( _1
)
# 3292 "sources/parser.ml"
               : 'specif_nullary_sort))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'reset_tmp_vars) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'context) in
    Obj.repr(
# 1379 "sources/parser.mly"
  ( [ _2 ] )
# 3300 "sources/parser.ml"
               : 'list_of_contexts))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_contexts) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'reset_tmp_vars) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'context) in
    Obj.repr(
# 1381 "sources/parser.mly"
  ( _1 @ [ _3 ] )
# 3309 "sources/parser.ml"
               : 'list_of_contexts))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 :  Terms.term ) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 1385 "sources/parser.mly"
  ( let t = _2
    and x =
      try List.assoc _4 !yy_tmp_vars
      with Not_found -> parse_failwith "The contextual variable is not in the context"
    in let var_sort = try List.assoc x (List.map (fun (x,y,_) -> (x, y)) t#variables) with Not_found -> failwith "raising Not_found in context"
    in let c = new context t#content  x
    in let () = Critical_context_set.critical_context_set_by_var#add var_sort c 
    in c )
# 3324 "sources/parser.ml"
               : 'context))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_contexts) in
    Obj.repr(
# 1396 "sources/parser.mly"
   ( let declared_sort = find_sort_id _1
     and contexts = _3
     in if not (List.for_all (fun c -> c#sort = declared_sort)contexts)
            then 
               parse_failwith "A context is not of the declared sort"
            else
               (*Critical_context_set.critical_context_set#add declared_sort contexts*)
               critical_context_set#replace declared_sort (( let old = ref [] in let () = try old := critical_context_set#find declared_sort with _ -> () in !old ) @ contexts)

   )
# 3341 "sources/parser.ml"
               : 'context_specif))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'context_specif) in
    Obj.repr(
# 1409 "sources/parser.mly"
  ( [ _1 ] )
# 3348 "sources/parser.ml"
               : 'list_of_context_specif))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_context_specif) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'context_specif) in
    Obj.repr(
# 1411 "sources/parser.mly"
  ( _1 @ [ _2 ] )
# 3356 "sources/parser.ml"
               : 'list_of_context_specif))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_context_specif) in
    Obj.repr(
# 1415 "sources/parser.mly"
  ( buffered_output "Successfully parsed critical context sets" ;print_critical_context_set ();flush stdout )
# 3363 "sources/parser.ml"
               : 'opt_specif_critical_context_sets))
; (fun __caml_parser_env ->
    Obj.repr(
# 1417 "sources/parser.mly"
  ( )
# 3369 "sources/parser.ml"
               : 'opt_specif_critical_context_sets))
; (fun __caml_parser_env ->
    Obj.repr(
# 1419 "sources/parser.mly"
  ( )
# 3375 "sources/parser.ml"
               : 'opt_specif_critical_context_sets))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_infs) in
    Obj.repr(
# 1425 "sources/parser.mly"
  ( )
# 3382 "sources/parser.ml"
               : 'specif_ind_priorities))
; (fun __caml_parser_env ->
    Obj.repr(
# 1427 "sources/parser.mly"
  ( )
# 3388 "sources/parser.ml"
               : 'specif_ind_priorities))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_infs) in
    Obj.repr(
# 1431 "sources/parser.mly"
  ( )
# 3395 "sources/parser.ml"
               : 'list_of_infs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_infs) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_infs) in
    Obj.repr(
# 1433 "sources/parser.mly"
  ( )
# 3403 "sources/parser.ml"
               : 'list_of_infs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_symbols) in
    Obj.repr(
# 1437 "sources/parser.mly"
  ( 
(*     let l = list_2_list_of_couples $1 *)
(*     in List.iter (fun (x, y) -> dico_infs#add_couple y x) l  *)
    let () = dico_infs#clear in
    let () = dico_infs_flag := true in
    let rec fn l =
      match l with
	  [] -> ()
	| h :: t -> let () = List.iter (fun x -> dico_infs#add h x) t in
	  fn t
    in
    let lst = if _1 <> [] then let () = list_ind_priorities := _1 in _1 @ [last_el _1] else [] in
    fn (List.rev lst)
  )
# 3423 "sources/parser.ml"
               : 'specif_infs))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_terms) in
    Obj.repr(
# 1454 "sources/parser.mly"
  (Queue.add (Cterm_token _3) yy_queue )
# 3430 "sources/parser.ml"
               : 'specif_complete_terms))
; (fun __caml_parser_env ->
    Obj.repr(
# 1456 "sources/parser.mly"
  ( )
# 3436 "sources/parser.ml"
               : 'specif_complete_terms))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'pos_codes_false) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_clauses) in
    Obj.repr(
# 1463 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed lemmas" ; flush stdout ;
    print_clause_list _4 ;
    Queue.add (Lemmas_token _4) yy_queue )
# 3446 "sources/parser.ml"
               : 'specif_lemmas))
; (fun __caml_parser_env ->
    Obj.repr(
# 1467 "sources/parser.mly"
  ( )
# 3452 "sources/parser.ml"
               : 'specif_lemmas))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'pos_codes_false) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_clauses_history) in
    Obj.repr(
# 1471 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed conjectures" ;
    print_clause_list _4 ;
    let lc = 
      if !specif_LA_defined && not !specif_Rmaxs0_defined && not !specif_Rmins0_defined && not !specif_Rzmm_defined then  let res = List.fold_right (fun c l -> (del_minmax c) @ l) _4 [] in res
      else _4
    in
    Queue.add (Conjectures_token lc) yy_queue
  )
# 3467 "sources/parser.ml"
               : 'specif_conjectures))
; (fun __caml_parser_env ->
    Obj.repr(
# 1480 "sources/parser.mly"
  ( )
# 3473 "sources/parser.ml"
               : 'specif_conjectures))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'pos_codes_false) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_clauses) in
    Obj.repr(
# 1484 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed hypotheses" ;
    print_clause_list _4 ;
    Queue.add (Hypotheses_token _4) yy_queue )
# 3483 "sources/parser.ml"
               : 'specif_hypotheses))
; (fun __caml_parser_env ->
    Obj.repr(
# 1488 "sources/parser.mly"
  ( )
# 3489 "sources/parser.ml"
               : 'specif_hypotheses))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'reset_and_clause) in
    Obj.repr(
# 1492 "sources/parser.mly"
  ( [_1] )
# 3496 "sources/parser.ml"
               : 'list_of_clauses))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_clauses) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'reset_and_clause) in
    Obj.repr(
# 1494 "sources/parser.mly"
  ( _1 @ [_2] )
# 3504 "sources/parser.ml"
               : 'list_of_clauses))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'reset_and_clause) in
    Obj.repr(
# 1498 "sources/parser.mly"
  ( [_1] )
# 3511 "sources/parser.ml"
               : 'list_of_clauses_history))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'reset_and_clause) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'history_clause) in
    Obj.repr(
# 1500 "sources/parser.mly"
  ( let () = _1#set_history _2 in [_1])
# 3519 "sources/parser.ml"
               : 'list_of_clauses_history))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_clauses_history) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'reset_and_clause) in
    Obj.repr(
# 1502 "sources/parser.mly"
  ( _1 @ [_2] )
# 3527 "sources/parser.ml"
               : 'list_of_clauses_history))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'one_history) in
    Obj.repr(
# 1506 "sources/parser.mly"
([_1])
# 3534 "sources/parser.ml"
               : 'history_clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'history_clause) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'one_history) in
    Obj.repr(
# 1508 "sources/parser.mly"
(_1 @ [_2])
# 3542 "sources/parser.ml"
               : 'history_clause))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : 'specif_substitution2) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'garbage_history) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'specif_clause) in
    Obj.repr(
# 1512 "sources/parser.mly"
((_2, _5))
# 3551 "sources/parser.ml"
               : 'one_history))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 1516 "sources/parser.mly"
()
# 3558 "sources/parser.ml"
               : 'garbage_history))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'reset_tmp_vars) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'specif_clause) in
    Obj.repr(
# 1520 "sources/parser.mly"
  ( _2 )
# 3566 "sources/parser.ml"
               : 'reset_and_clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'reset_and_horn_clause) in
    Obj.repr(
# 1524 "sources/parser.mly"
  ( [_1] )
# 3573 "sources/parser.ml"
               : 'list_of_horn_clauses))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_horn_clauses) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'reset_and_horn_clause) in
    Obj.repr(
# 1526 "sources/parser.mly"
  ( _1 @ [_2] )
# 3581 "sources/parser.ml"
               : 'list_of_horn_clauses))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'reset_tmp_vars) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'specif_horn_clause) in
    Obj.repr(
# 1530 "sources/parser.mly"
  ( (!parsed_gfile, !linenumber, _2) )
# 3589 "sources/parser.ml"
               : 'reset_and_horn_clause))
; (fun __caml_parser_env ->
    Obj.repr(
# 1533 "sources/parser.mly"
  ( yy_tmp_vars := [] ;
    yy_tmp_sorts := [] ;
(*     if !debug_mode then print_string "\nReset of yy_tmp_param_sorts"; *)
    yy_tmp_param_sorts := [] ;
    yy_tmp_equiv_dico#clear )
# 3599 "sources/parser.ml"
               : 'reset_tmp_vars))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'specif_clause) in
    Obj.repr(
# 1540 "sources/parser.mly"
  ( _1 )
# 3606 "sources/parser.ml"
               :  Clauses.peano_context Clauses.clause ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_literals) in
    Obj.repr(
# 1544 "sources/parser.mly"
  ( 
    let l' = List.map literal_of_incomplete_terms _1 in
    let new_l' = expand_sorts_list l' in
    let () = if not !specif_parameterized  && not (test_well_founded_cl ([], new_l')) then 
      failwith "clause1: undefined types"
    in
    let res = new clause ([], new_l') [] ("",0,([],[])) in
(*     let () = print_detailed_clause res in *)
    res
  )
# 3622 "sources/parser.ml"
               : 'specif_clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_literals) in
    Obj.repr(
# 1555 "sources/parser.mly"
  ( 
    let l = List.map literal_of_incomplete_terms _1 in
    let new_l = expand_sorts_list l in
    let () = if not !specif_parameterized && not (test_well_founded_cl (new_l, [])) then 
      failwith "clause2: undefined types"
    in
    let res = new clause (new_l, []) [] ("",0,([],[])) in
(*     let () = print_detailed_clause res in *)
    res
  )
# 3638 "sources/parser.ml"
               : 'specif_clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_literals) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_literals) in
    Obj.repr(
# 1566 "sources/parser.mly"
  (
    let l = List.map literal_of_incomplete_terms _1 in
    let l' = List.map literal_of_incomplete_terms _3 in
    let new_l' = expand_sorts_list l' in
    let new_l = expand_sorts_list l in
    let () = if not !specif_parameterized && not (test_well_founded_cl (new_l, new_l')) then 
      failwith "clause3: undefined types"
    in
    let res = new clause (new_l, new_l') [] ("",0,([],[])) in
(*     let () = print_detailed_clause res in *)
    res
  )
# 3657 "sources/parser.ml"
               : 'specif_clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_literal) in
    Obj.repr(
# 1581 "sources/parser.mly"
  ( 
    let l' = [ literal_of_incomplete_terms _1 ] in
    let new_l' = expand_sorts_list l' in
    let lhs, _ = (List.hd new_l')#both_sides in
    let arg_lhs = lhs#sons in 
    let () = if List.exists (fun t -> not (t#is_constructor_term)) arg_lhs then failwith ("one of the arguments is not a constructor term" ) in
    let () = if not !specif_parameterized && not (test_well_founded_cl ([], new_l')) then 
      failwith "clause4: undefined types"
    in
    let res = new clause ([], new_l') [] ("",0,([],[])) in
(*     let () = print_detailed_clause res in *)
    res
  )
# 3676 "sources/parser.ml"
               : 'specif_horn_clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_literals) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'specif_literal) in
    Obj.repr(
# 1595 "sources/parser.mly"
  ( 
    let l = List.map literal_of_incomplete_terms _1
    and l' = [ literal_of_incomplete_terms _3 ] in
    let new_l' = expand_sorts_list l' in
    let new_l = expand_sorts_list l in
    let lhs, _ = (List.hd new_l')#both_sides in
    let arg_lhs = lhs#sons in 
    let () = if List.exists (fun t -> not (t#is_constructor_term)) arg_lhs then failwith ("one of the arguments is not a constructor term" ) in
    let () = if not !specif_parameterized && not (test_well_founded_cl (new_l, new_l')) then 
      failwith "clause5: undefined types"
    in
    let res = new clause (new_l, new_l') [] ("",0,([],[])) in
(*     let () = print_detailed_clause res in *)
    res
  )
# 3698 "sources/parser.ml"
               : 'specif_horn_clause))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_literal) in
    Obj.repr(
# 1613 "sources/parser.mly"
  ( [ _1 ] )
# 3705 "sources/parser.ml"
               : 'list_of_literals))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_literals) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'specif_literal) in
    Obj.repr(
# 1615 "sources/parser.mly"
  ( _1 @ [ _3 ] )
# 3713 "sources/parser.ml"
               : 'list_of_literals))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'literal_get_sides) in
    Obj.repr(
# 1619 "sources/parser.mly"
  ( 
  let lhs, rhs, type_lit = _1 in
    let t = process_term_tokens lhs
    and t' = process_term_tokens rhs in
    let content = try (defined_content t) with
	(Failure "defined_content") -> failwith "defined_content"
    in 
    let term_t, term_t' =  
      match content with
	  Ivar x -> (* t is a variable *)
	    begin (* dicards PM on exceptions *)
              try
		let s = List.assoc x !yy_tmp_sorts
		in 
		if x < 0 then ((new term (Var_exist (x, s))), typecheck_incomplete_tree (Actual_sort s) t')
		else ((new term (Var_univ (x, s))), typecheck_incomplete_tree (Actual_sort s) t')
              with Not_found -> (* t has a fresh unknown sort *)
		let () = param_sort_counter := !param_sort_counter + 1 in
		let str = ("Undefined" ^ (string_of_int !param_sort_counter)) in
		let s' = Abstr_sort0 str in
		let new_t' = typecheck_incomplete_tree (Actual_sort s') t' in
		let () = yy_tmp_sorts := generic_insert_sorted (x, new_t'#sort) !yy_tmp_sorts in
		if x < 0 then ((new term (Var_exist (x, new_t'#sort))), new_t')
		else ((new term (Var_univ (x, new_t'#sort))), new_t')
            end
	| Iterm (x, _) -> (* t is a term *)
            let s = try dico_const_sort#find x with Not_found -> failwith "raising Not_found in specif_literal" in
	    let s' = List.hd (update_profile [s]) in (* the abstract sorts are renamed *)
            ((typecheck_incomplete_tree (Actual_sort s') t), typecheck_incomplete_tree (Actual_sort s')  t')
    in
    term_t, term_t', type_lit )
# 3750 "sources/parser.ml"
               : 'specif_literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 :  Terms_parser.term_token list ) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Terms_parser.term_token list ) in
    Obj.repr(
# 1653 "sources/parser.mly"
  ( (_1,_3, Lit_equal (term_true, term_true)) )
# 3758 "sources/parser.ml"
               : 'literal_get_sides))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 :  Terms_parser.term_token list ) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Terms_parser.term_token list ) in
    Obj.repr(
# 1655 "sources/parser.mly"
  ( (_1,_3, Lit_rule (term_true, term_true)))
# 3766 "sources/parser.ml"
               : 'literal_get_sides))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 :  Terms_parser.term_token list ) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Terms_parser.term_token list ) in
    Obj.repr(
# 1657 "sources/parser.mly"
  ( (_1,_3, Lit_diff (term_true, term_true)) )
# 3774 "sources/parser.ml"
               : 'literal_get_sides))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_tokens) in
    Obj.repr(
# 1662 "sources/parser.mly"
  (_1 )
# 3781 "sources/parser.ml"
               :  Terms_parser.term_token list ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'one_token) in
    Obj.repr(
# 1666 "sources/parser.mly"
  ( _1 )
# 3788 "sources/parser.ml"
               : 'list_of_tokens))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_tokens) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'one_token) in
    Obj.repr(
# 1668 "sources/parser.mly"
  ( _1 @ _2 )
# 3796 "sources/parser.ml"
               : 'list_of_tokens))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1672 "sources/parser.mly"
  ( [ TT_ident _1 ] )
# 3803 "sources/parser.ml"
               : 'one_token))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 1676 "sources/parser.mly"
  ( let () = check_explicit_type _2 _4 in
    [ TT_ident _2 ] )
# 3812 "sources/parser.ml"
               : 'one_token))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_term_tokens) in
    Obj.repr(
# 1679 "sources/parser.mly"
  ( let () = if !debug_mode then (print_string"\n token list <<<<< " ; List.iter (fun x -> print_term_token x) _2) else () 
  in _2)
# 3820 "sources/parser.ml"
               : 'one_token))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_tokens) in
    Obj.repr(
# 1684 "sources/parser.mly"
  ( let content = (try defined_content (process_term_tokens _1) with
      (Failure "defined_content") -> failwith "defined_content")
  in [ TT_tree content ] )
# 3829 "sources/parser.ml"
               : 'list_of_term_tokens))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_term_tokens) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_tokens) in
    Obj.repr(
# 1688 "sources/parser.mly"
  ( let content = (try (defined_content (process_term_tokens _3)) with
      (Failure "defined_content") -> failwith "defined_content")
  in _1 @ [ TT_tree content ] )
# 3839 "sources/parser.ml"
               : 'list_of_term_tokens))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_strategies) in
    Obj.repr(
# 1694 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed strategies" ;
    Queue.add (Strat_token _3) yy_queue )
# 3847 "sources/parser.ml"
               : 'specif_strategies))
; (fun __caml_parser_env ->
    Obj.repr(
# 1697 "sources/parser.mly"
  ( )
# 3853 "sources/parser.ml"
               : 'specif_strategies))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_strategy) in
    Obj.repr(
# 1701 "sources/parser.mly"
  ( [_1] )
# 3860 "sources/parser.ml"
               : 'list_of_strategies))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_strategies) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'specif_strategy) in
    Obj.repr(
# 1703 "sources/parser.mly"
  ( _1 @ [_2] )
# 3868 "sources/parser.ml"
               : 'list_of_strategies))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 :  Strategies.strategy ) in
    Obj.repr(
# 1707 "sources/parser.mly"
  ( (_1, _3) )
# 3876 "sources/parser.ml"
               : 'specif_strategy))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 :  Strategies.reasoning_module ) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_reasoning_modules) in
    Obj.repr(
# 1711 "sources/parser.mly"
    (new strategy (Inference_rule (AddPremise (_3, new strategy (Try_ _6)))))
# 3884 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 :  Strategies.reasoning_module ) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_reasoning_modules) in
    Obj.repr(
# 1713 "sources/parser.mly"
    (new strategy (Inference_rule (Simplify (_3, new strategy (Try_ _6)))))
# 3892 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 :  Strategies.reasoning_module ) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_reasoning_modules) in
    Obj.repr(
# 1715 "sources/parser.mly"
    (new strategy (Inference_rule (Delete (_3, new strategy (Try_ _6)))))
# 3900 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1717 "sources/parser.mly"
  ( match _2 with
      "smallest" -> new strategy (Inference_rule (Goto Goto_smallest))
    | "greatest" -> new strategy (Inference_rule (Goto Goto_greatest))
    | _ ->
        let i = parse_positive_int _2
        in new strategy (Inference_rule (Goto (Goto_number i))) )
# 3912 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_strategy_terms) in
    Obj.repr(
# 1724 "sources/parser.mly"
  ( new strategy (Series _2) )
# 3919 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_strategy_terms) in
    Obj.repr(
# 1726 "sources/parser.mly"
  ( new strategy (Try_ _3) )
# 3926 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_strategy_terms) in
    Obj.repr(
# 1728 "sources/parser.mly"
  ( new strategy (Saturate _3) )
# 3933 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.strategy ) in
    Obj.repr(
# 1730 "sources/parser.mly"
  ( new strategy (Repeat _2) )
# 3940 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.strategy ) in
    Obj.repr(
# 1732 "sources/parser.mly"
  ( new strategy (Repeat_plus _2) )
# 3947 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1734 "sources/parser.mly"
  ( new strategy (Named_strategy _1) )
# 3954 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1736 "sources/parser.mly"
  ( new strategy Query )
# 3960 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1738 "sources/parser.mly"
  ( new strategy (Print_goals (false, false)) )
# 3966 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1740 "sources/parser.mly"
  ( new strategy (Print_goals (false, true)) )
# 3972 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 1742 "sources/parser.mly"
  ( match String.lowercase _3 with
      "t" | "true" -> new strategy (Print_goals (true, false))
    | "f" | "false" -> new strategy (Print_goals (false, false))
    | _ -> parse_failwith "Bad argument for strategy \"print_goals\"" )
# 3982 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 1748 "sources/parser.mly"
  ( match String.lowercase _3 with
      "t" | "true" -> new strategy (Print_goals (true, true))
    | "f" | "false" -> new strategy (Print_goals (false, true))
    | _ -> parse_failwith "Bad argument for strategy \"print_goals_history\"" )
# 3992 "sources/parser.ml"
               :  Strategies.strategy ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.strategy ) in
    Obj.repr(
# 1755 "sources/parser.mly"
  ( [ _1 ] )
# 3999 "sources/parser.ml"
               : 'list_of_strategy_terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_strategy_terms) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.strategy ) in
    Obj.repr(
# 1757 "sources/parser.mly"
  ( _1 @ [ _3 ] )
# 4007 "sources/parser.ml"
               : 'list_of_strategy_terms))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 :  Strategies.strategy ) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'specif_list_of_systems) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 :  Dummies.position_argument ) in
    Obj.repr(
# 1761 "sources/parser.mly"
  ( Contextual_rewriting (_3, _5, _7) )
# 4016 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 :  Dummies.position_argument ) in
    Obj.repr(
# 1763 "sources/parser.mly"
  ( (Equational_rewriting _3) )
# 4023 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'specif_list_of_systems) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 :  Dummies.position_argument ) in
    Obj.repr(
# 1765 "sources/parser.mly"
  ( match _3 with
      "rewrite" -> (Rewriting (false, _5, _7))
    | "normalize" -> (Rewriting (true, _5, _7))
    | _ -> parse_failwith "argument of rewriting must be either \"rewrite\" or \"normalize\"" )
# 4035 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'specif_list_of_systems) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 :  Dummies.position_argument ) in
    Obj.repr(
# 1770 "sources/parser.mly"
  ( Partial_case_rewriting (_3, _5) )
# 4043 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 :  Strategies.strategy ) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'specif_list_of_systems) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 :  Dummies.position_argument ) in
    Obj.repr(
# 1772 "sources/parser.mly"
  ( Total_case_rewriting (_3, _5, _7) )
# 4052 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1774 "sources/parser.mly"
  ( Generate (true, []) )
# 4058 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1776 "sources/parser.mly"
  (Generate (false, []) )
# 4064 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_priorities) in
    Obj.repr(
# 1778 "sources/parser.mly"
  ( Generate (true, _3) )
# 4071 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1780 "sources/parser.mly"
  ( Generate_eq (true, []) )
# 4077 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1782 "sources/parser.mly"
  (Generate_eq (false, []) )
# 4083 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_priorities) in
    Obj.repr(
# 1784 "sources/parser.mly"
  ( Generate_eq (true, _3) )
# 4090 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1786 "sources/parser.mly"
  ( ((Generate_obs (true, []))) )
# 4096 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1788 "sources/parser.mly"
  ( ((Generate_obs (false, []))) )
# 4102 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_priorities) in
    Obj.repr(
# 1790 "sources/parser.mly"
  ( ( (Generate_obs (true, _3))) )
# 4109 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1792 "sources/parser.mly"
  ( Positive_decomposition )
# 4115 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1794 "sources/parser.mly"
  ( Congruence_closure )
# 4121 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1796 "sources/parser.mly"
  ( Negative_decomposition )
# 4127 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1798 "sources/parser.mly"
  ( Positive_clash )
# 4133 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1800 "sources/parser.mly"
  ( Tautology )
# 4139 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'specif_list_of_systems) in
    Obj.repr(
# 1802 "sources/parser.mly"
  ( Subsumption (_3))
# 4146 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'specif_list_of_systems) in
    Obj.repr(
# 1804 "sources/parser.mly"
  ( Augmentation (_3))
# 4153 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1806 "sources/parser.mly"
  ( Negative_clash )
# 4159 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1808 "sources/parser.mly"
  ( Eliminate_redundant_literal )
# 4165 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1810 "sources/parser.mly"
  ( Eliminate_trivial_literal )
# 4171 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1812 "sources/parser.mly"
  ( Auto_simplification )
# 4177 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1814 "sources/parser.mly"
  ( Complement )
# 4183 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1816 "sources/parser.mly"
  ( Id )
# 4189 "sources/parser.ml"
               :  Strategies.reasoning_module ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.reasoning_module ) in
    Obj.repr(
# 1821 "sources/parser.mly"
  ( [ new strategy (Inference_rule (Id_st _1)) ] )
# 4196 "sources/parser.ml"
               : 'list_of_reasoning_modules))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'list_of_reasoning_modules) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.reasoning_module ) in
    Obj.repr(
# 1823 "sources/parser.mly"
  ( _1 @ [ new strategy (Inference_rule (Id_st _3)) ] )
# 4204 "sources/parser.ml"
               : 'list_of_reasoning_modules))
; (fun __caml_parser_env ->
    Obj.repr(
# 1829 "sources/parser.mly"
  ( LOS_query )
# 4210 "sources/parser.ml"
               : 'specif_list_of_systems))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 :  Clauses.which_system list ) in
    Obj.repr(
# 1831 "sources/parser.mly"
  ( LOS_defined _1 )
# 4217 "sources/parser.ml"
               : 'specif_list_of_systems))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_system) in
    Obj.repr(
# 1835 "sources/parser.mly"
  ( [ _1 ] )
# 4224 "sources/parser.ml"
               :  Clauses.which_system list ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 :  Clauses.which_system list ) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'specif_system) in
    Obj.repr(
# 1837 "sources/parser.mly"
  ( _1 @ [ _3 ] )
# 4232 "sources/parser.ml"
               :  Clauses.which_system list ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1841 "sources/parser.mly"
  ( match _1 with
    | "r"| "R" -> R
    | "c"| "C" -> C
    | "l"| "L" -> L
    | _ -> parse_failwith "bad systems specification" )
# 4243 "sources/parser.ml"
               : 'specif_system))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.strategy ) in
    Obj.repr(
# 1869 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed startpoint" ;
    Queue.add (Startpoint_token _3) yy_queue )
# 4251 "sources/parser.ml"
               : 'specif_startpoint))
; (fun __caml_parser_env ->
    Obj.repr(
# 1872 "sources/parser.mly"
  ( )
# 4257 "sources/parser.ml"
               : 'specif_startpoint))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.strategy ) in
    Obj.repr(
# 1876 "sources/parser.mly"
  ( buffered_output "\nSuccessfully parsed the augmentation strategy" ;
    Queue.add (Augmentation_token _3) yy_queue )
# 4265 "sources/parser.ml"
               : 'specif_augmentation))
; (fun __caml_parser_env ->
    Obj.repr(
# 1879 "sources/parser.mly"
  ( )
# 4271 "sources/parser.ml"
               : 'specif_augmentation))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_terms) in
    Obj.repr(
# 1883 "sources/parser.mly"
  ( Queue.add (Norm_token _3) yy_queue )
# 4278 "sources/parser.ml"
               : 'specif_norm))
; (fun __caml_parser_env ->
    Obj.repr(
# 1885 "sources/parser.mly"
  ( )
# 4284 "sources/parser.ml"
               : 'specif_norm))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'two_terms) in
    Obj.repr(
# 1889 "sources/parser.mly"
  ( 
     let t, t' = _3 in
    Queue.add (Rpo_token (t, t')) yy_queue )
# 4293 "sources/parser.ml"
               : 'specif_rpocompare))
; (fun __caml_parser_env ->
    Obj.repr(
# 1893 "sources/parser.mly"
  ( )
# 4299 "sources/parser.ml"
               : 'specif_rpocompare))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'two_clauses) in
    Obj.repr(
# 1897 "sources/parser.mly"
  ( let c, c' = _3 in
    Queue.add (Compare_token (c, c')) yy_queue )
# 4307 "sources/parser.ml"
               : 'specif_compare))
; (fun __caml_parser_env ->
    Obj.repr(
# 1900 "sources/parser.mly"
  ( )
# 4313 "sources/parser.ml"
               : 'specif_compare))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'two_clauses) in
    Obj.repr(
# 1904 "sources/parser.mly"
  ( let c, c' = _3 in
    Queue.add (Compare_max_token (c, c')) yy_queue )
# 4321 "sources/parser.ml"
               : 'specif_max_compare))
; (fun __caml_parser_env ->
    Obj.repr(
# 1907 "sources/parser.mly"
  ( )
# 4327 "sources/parser.ml"
               : 'specif_max_compare))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 1912 "sources/parser.mly"
  (
    stop_clause := int_of_string _3)
# 4335 "sources/parser.ml"
               : 'specif_stop_on_clause))
; (fun __caml_parser_env ->
    Obj.repr(
# 1915 "sources/parser.mly"
  ()
# 4341 "sources/parser.ml"
               : 'specif_stop_on_clause))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_symbols) in
    Obj.repr(
# 1919 "sources/parser.mly"
  ( extract_specification _3)
# 4348 "sources/parser.ml"
               : 'specif_extract))
; (fun __caml_parser_env ->
    Obj.repr(
# 1921 "sources/parser.mly"
  ( )
# 4354 "sources/parser.ml"
               : 'specif_extract))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'two_terms) in
    Obj.repr(
# 1925 "sources/parser.mly"
  ( let t, t' = _3 in
    Queue.add (Match_token (t, t')) yy_queue )
# 4362 "sources/parser.ml"
               : 'specif_match))
; (fun __caml_parser_env ->
    Obj.repr(
# 1928 "sources/parser.mly"
  ( )
# 4368 "sources/parser.ml"
               : 'specif_match))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 6 : 'reset_tmp_vars) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'set_of_terms) in
    let _5 = (Parsing.peek_val __caml_parser_env 3 : 'reset_tmp_vars) in
    let _7 = (Parsing.peek_val __caml_parser_env 1 : 'set_of_terms) in
    Obj.repr(
# 1932 "sources/parser.mly"
  ( Queue.add (Ac_token (_4, _7)) yy_queue )
# 4378 "sources/parser.ml"
               : 'specif_ac_subsumes))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'reset_tmp_vars) in
    Obj.repr(
# 1934 "sources/parser.mly"
  ( )
# 4385 "sources/parser.ml"
               : 'specif_ac_subsumes))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 :  Terms.term ) in
    Obj.repr(
# 1938 "sources/parser.mly"
  ( [ _1 ] )
# 4392 "sources/parser.ml"
               : 'set_of_terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'set_of_terms) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Terms.term ) in
    Obj.repr(
# 1940 "sources/parser.mly"
  ( _1 @ [ _3 ] )
# 4400 "sources/parser.ml"
               : 'set_of_terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'reset_tmp_vars) in
    let _2 = (Parsing.peek_val __caml_parser_env 2 :  Terms.term ) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 :  Terms.term ) in
    Obj.repr(
# 1944 "sources/parser.mly"
  ( (_2, _4) )
# 4409 "sources/parser.ml"
               : 'two_terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 4 : 'pos_codes_false) in
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'reset_tmp_vars) in
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'specif_clause) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'specif_clause) in
    Obj.repr(
# 1948 "sources/parser.mly"
  ( (_3, _5) )
# 4419 "sources/parser.ml"
               : 'two_clauses))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1952 "sources/parser.mly"
  ( match _1 with
      "*" -> Pos_all
    | _ -> Pos_litdefined (true, parse_positive_int _1) )
# 4428 "sources/parser.ml"
               :  Dummies.position_argument ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'bracket_enclosed_list_of_positive_ints) in
    Obj.repr(
# 1956 "sources/parser.mly"
  ( Pos_defined (true, parse_positive_int _1, _2) )
# 4436 "sources/parser.ml"
               :  Dummies.position_argument ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1958 "sources/parser.mly"
  ( Pos_query )
# 4442 "sources/parser.ml"
               :  Dummies.position_argument ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'bracket_enclosed_list_of_positive_ints) in
    Obj.repr(
# 1962 "sources/parser.mly"
  ( let i = parse_positive_int _1
    in let b =
      match i with
        0 -> false
      | 1 -> true
      | _ -> parse_failwith "clausal position must start with 0 or 1"
    in Pos_defined (b, parse_positive_int _2, _3) )
# 4457 "sources/parser.ml"
               :  Dummies.position_argument ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1970 "sources/parser.mly"
  ( match _1 with
      "*" -> Pos_all
    | _ -> parse_failwith "clausal position is either \"*\" or a real position" )
# 4466 "sources/parser.ml"
               :  Dummies.position_argument ))
; (fun __caml_parser_env ->
    Obj.repr(
# 1974 "sources/parser.mly"
  ( Pos_query )
# 4472 "sources/parser.ml"
               :  Dummies.position_argument ))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_positive_ints) in
    Obj.repr(
# 1978 "sources/parser.mly"
  ( _2 )
# 4479 "sources/parser.ml"
               : 'bracket_enclosed_list_of_positive_ints))
; (fun __caml_parser_env ->
    Obj.repr(
# 1980 "sources/parser.mly"
  ( [] )
# 4485 "sources/parser.ml"
               : 'bracket_enclosed_list_of_positive_ints))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'bracket_enclosed_list_of_positive_ints) in
    Obj.repr(
# 1984 "sources/parser.mly"
  ( [List.map (fun x -> (0,x)) _1 ] )
# 4492 "sources/parser.ml"
               : 'list_of_positions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_positions) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'bracket_enclosed_list_of_positive_ints) in
    Obj.repr(
# 1986 "sources/parser.mly"
  ( _1 @ [List.map (fun x -> (0,x))  _2 ] )
# 4500 "sources/parser.ml"
               : 'list_of_positions))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1990 "sources/parser.mly"
  ( [(parse_positive_int _1) - 1] )
# 4507 "sources/parser.ml"
               : 'list_of_positive_ints))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'list_of_positive_ints) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 1992 "sources/parser.mly"
  ( _1 @ [(parse_positive_int _2) - 1] )
# 4515 "sources/parser.ml"
               : 'list_of_positive_ints))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'specif_substitution2) in
    Obj.repr(
# 1995 "sources/parser.mly"
  ( _1 )
# 4522 "sources/parser.ml"
               :  (Symbols.var * Terms.term) list ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'specif_var_term) in
    Obj.repr(
# 1999 "sources/parser.mly"
  ( [_1] )
# 4529 "sources/parser.ml"
               : 'specif_substitution2))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'specif_substitution2) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'specif_var_term) in
    Obj.repr(
# 2001 "sources/parser.mly"
  ( insert_sorted (fun (x, _) (x', _) -> x = x') (fun (x, _) (x', _) -> x < x') _3 _1 )
# 4537 "sources/parser.ml"
               : 'specif_substitution2))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 :  Terms_parser.term_token list ) in
    Obj.repr(
# 2005 "sources/parser.mly"
  ( 
    let v =
      try List.assoc _1 !yy_tmp_vars
      with Not_found -> let tmp_v = newvar () in let () = yy_tmp_vars := (_1, tmp_v) :: !yy_tmp_vars in tmp_v
      in
      
(*     let s = try List.assoc v !yy_tmp_sorts2 with Not_found -> failwith "raising Not_found in specif_var_term" in *)
    let t = process_term_tokens _3 in
    let term = typecheck_incomplete_tree (Variable_sort 0) t in
    (v,  term)
  )
# 4555 "sources/parser.ml"
               : 'specif_var_term))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 2019 "sources/parser.mly"
  ( parse_positive_int _1 )
# 4562 "sources/parser.ml"
               :  int ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 :  Terms_parser.term_token list ) in
    Obj.repr(
# 2024 "sources/parser.mly"
  ( let t = process_term_tokens _1 in
    let term_t =
      match t with
          Defined (Iterm (f, _)) -> 
	    begin
	      let s = 
		try 
		  dico_const_sort#find f
		with Not_found -> parse_failwith "get_term"
	      in 
	      typecheck_incomplete_tree (Actual_sort s) t
	    end
	| Defined (Ivar x) ->
            begin
              let s = 
		try
		  List.assoc x !yy_tmp_sorts
		with Not_found -> parse_failwith "unbound types"
	      in
	      typecheck_incomplete_tree (Actual_sort s) t
            end
	| Undefined -> parse_failwith "unbound types"
    in term_t )
# 4591 "sources/parser.ml"
               :  Terms.term ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'reset_tmp_vars) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 :  Terms.term ) in
    Obj.repr(
# 2050 "sources/parser.mly"
  ( [_2] )
# 4599 "sources/parser.ml"
               : 'list_of_terms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 3 : 'list_of_terms) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'reset_tmp_vars) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 :  Terms.term ) in
    Obj.repr(
# 2052 "sources/parser.mly"
  ( _1 @ [_4] )
# 4608 "sources/parser.ml"
               : 'list_of_terms))
; (fun __caml_parser_env ->
    Obj.repr(
# 2055 "sources/parser.mly"
  ( pick_pos_codes := true )
# 4614 "sources/parser.ml"
               : 'pos_codes_true))
; (fun __caml_parser_env ->
    Obj.repr(
# 2058 "sources/parser.mly"
  ( pick_pos_codes := false )
# 4620 "sources/parser.ml"
               : 'pos_codes_false))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 :  Strategies.strategy ) in
    Obj.repr(
# 2064 "sources/parser.mly"
  ( Command_strategy _2 )
# 4627 "sources/parser.ml"
               :  Dummies.shell_commands ))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 2066 "sources/parser.mly"
  ( match _1 with
      "p" -> Command_previous
    | "n" -> Command_next
    | "r" -> Command_run
    | "d" -> Command_display
    | "exit" -> Command_exit
    | _ -> Command_error )
# 4640 "sources/parser.ml"
               :  Dummies.shell_commands ))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'pos_codes_false) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'list_of_clauses) in
    Obj.repr(
# 2076 "sources/parser.mly"
  (
    buffered_output (sprint_list "\n\nThe CAML version :" compute_string_clause_caml _4);
  )
# 4650 "sources/parser.ml"
               : 'print_caml))
; (fun __caml_parser_env ->
    Obj.repr(
# 2081 "sources/parser.mly"
  ( )
# 4656 "sources/parser.ml"
               : 'print_caml))
(* Entry specif *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry strategy_term *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry reasoning_module *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry list_of_systems *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry specif_clausal_position *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry specif_literal_position_in_clause *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry specif_substitution *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry specif_positive_int *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry get_term *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry specif_term *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry specif_clause2 *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
(* Entry specif_shell_command *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let specif (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf :  Strategies.problem_token Queue.t )
let strategy_term (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 2 lexfun lexbuf :  Strategies.strategy )
let reasoning_module (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 3 lexfun lexbuf :  Strategies.reasoning_module )
let list_of_systems (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 4 lexfun lexbuf :  Clauses.which_system list )
let specif_clausal_position (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 5 lexfun lexbuf :  Dummies.position_argument )
let specif_literal_position_in_clause (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 6 lexfun lexbuf :  Dummies.position_argument )
let specif_substitution (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 7 lexfun lexbuf :  (Symbols.var * Terms.term) list )
let specif_positive_int (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 8 lexfun lexbuf :  int )
let get_term (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 9 lexfun lexbuf :  Terms.term )
let specif_term (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 10 lexfun lexbuf :  Terms_parser.term_token list )
let specif_clause2 (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 11 lexfun lexbuf :  Clauses.peano_context Clauses.clause )
let specif_shell_command (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 12 lexfun lexbuf :  Dummies.shell_commands )
