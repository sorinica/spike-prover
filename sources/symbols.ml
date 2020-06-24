

(*
   * Project: Spike ver 0.1
   * File: symbols.ml
   * Content: symbol definitions
*)

open Values
open Diverse
open Io
open Dicos

(*************************************************************************)

type var = int
and const = int
and sort = Def_sort of int | Abstr_sort0 of string | Abstr_sort1 of int * sort | Abstr_sort2 of int * sort * sort
and position = int list
and path = (const * int) list
and arity = int * int
;;

(*
   * For type checking, we need to compare the profile of the current subterm with an actual sort
   * or the undefined sort of another variable
*)
type parameterized_sort =
    Actual_sort of sort
  | Variable_sort of var

  (* page 26 Baader & Nipkow book  *)
type order = GR | EQ | NGE


let var_equal = ( = )
and var_inf = ( < )
and const_equal = ( = )
and const_inf = ( < )
and sort_equal = ( = )
and sort_inf = ( < );;

let def_sort_id s = match s with
    Def_sort id_s -> id_s
  | Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _-> failwith "def_sort_id"


let rec is_abstract s' = match s' with
    Abstr_sort0 _  -> true
  | Abstr_sort1 (_, _) -> false (* is_abstract s *)
  | Abstr_sort2 (_, _, _) -> false (* is_abstract s1 or is_abstract s2 *)
  | Def_sort _ -> false
	
let sprint_var x s is_univ =
  let quantif = if is_univ then "u" else "e" in 
  let abstract_str = if is_abstract s then "a" else "" in
  let str_x = if x < 0 then string_of_int (- x) else string_of_int x in
  quantif ^ abstract_str ^ str_x
;;

(* Dictionaries *)

(* String - code correspondence for sorts *)
let dico_sort_string : (sort, string) bijective_dictionary =
  new bijective_dictionary 101
;;

let print_dico_sort_string () =
  buffered_output "dico_sort_string:";
  let fn k v = 
    let () = match k with
	Def_sort s -> print_int s 
      | Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _ -> failwith "print_dico_sort_string"
    in 
    buffered_output " --> "; buffered_output v
  in
  dico_sort_string#iter fn
;;

let rec sprint_sort s = 
  match s with
      Def_sort _ ->  (try dico_sort_string#find s with Not_found -> failwith "raising Not_found in sprint_sort")
    | Abstr_sort0 str ->  str
    | Abstr_sort1 (i, sarg) -> 
	(try 
	  let str = (dico_sort_string#find (Def_sort i)) in 
	  "(" ^ str ^  " " ^  (sprint_sort sarg) ^ ")"
	with Not_found -> failwith "raising Not_found in sprint_sort")
    | Abstr_sort2 (i, sarg1, sarg2) -> 
	(try 
	  let str = (dico_sort_string#find (Def_sort i)) in 
      "(" ^ str ^ " " ^ (sprint_sort sarg1) ^ " " ^ (sprint_sort sarg2) ^ ")" 
	with Not_found -> failwith "raising Not_found in sprint_sort")

let sprint_subst l =
  let f (x, t) = sprint_var x (Def_sort 0) true ^ ", " ^ t#string ^ ((* if !maximal_output then (" of sort " ^ (sprint_sort t#sort)) else *)
    "") in
  "<! " ^ sprint_list " ; " f l ^ " !>"
;;

(* Peano arithmetics. We trigger its use with the "use" token. *)
let specif_LA_defined = ref false;;

(* Theory of max, s and 0. We trigger its use with the "use" token. *)
let specif_Rmaxs0_defined = ref false;;

(* Theory of min, s and 0. We trigger its use with the "use" token. *)
let specif_Rmins0_defined = ref false;;

(* Theory of zero, max min . We trigger its use with the "use" token. *)
let specif_Rzmm_defined = ref false;;

(* Theory of mult, plus, s and 0. We trigger its use with the "use" token. *)
let specif_Rmps0_defined = ref false;;

(* Theory of lists + nats: len, rev, @, single, cons, nil, mult, plus, s and 0. We trigger its use with the "use" token. *)
let specif_Rnatlist_defined = ref false;;

  (* intermediate function for subsumption  *)

let subsumes proceed_fun matchfun sigma l l' fn_arith =
  
  let rec fn s i =
    function
      [] -> proceed_fun s
    | (b', lit') :: t ->
(* 	let () = buffered_output ("\n" ^ (n_spaces i) ^ "treating the literal " ^ ((fun (i, x) -> x#string) h) ^ " with s = " ^	(sprint_subst s)) in *)
        let proceed_fun' s' = proceed_fun (fn s' (i+2) t) in
	
        let res = list_special_exists (fun (b, lit) -> 
	  try  
	    let r =  matchfun proceed_fun' s (b', lit')  (b, lit) in 
(* 	    let () = buffered_output ("\n" ^ (n_spaces i) ^ " lit = " ^ lit#string ^ " \n\tr = " ^ (sprint_subst r) ^  "\n\ts = " ^ (sprint_subst s)) in *)
	    r
	  with Failure _ -> 
	    if(*  !specif_LA_defined *) false  then 
	      if (b = b') && (b = false) && fn_arith lit then s else failwith "matching"
	    else failwith "matching") (Failure "matching") l' 
	in
	res
  in
  fn sigma 0 l
;;

(* The same function dedicated to the interface with a matching
   function (carrying a substitution). We provide the remaining of the second list
   ex is the exception raised when matching fails. *)

  (* not used  *)

let subsumes_w_rest matchfun ex =
  let rec fn s h t l =
    let rec fn2 acc =
      function
        [] -> failwith "ac_eq"
      | h' :: t' ->
          try let s' = matchfun s h h' in fn3 s' t (acc @ t') with
            e -> if e = ex then fn2 (acc @ [h']) t' else raise e
    in
    fn2 [] l
  and fn3 s l l' =
    match l, l' with
      [], _ -> s, l'
    | h :: t, _ -> fn s h t l'
  in
  fn3
;; 


let sprint_position p = if p = [] then "[]" else sprint_list "-" (fun x -> string_of_int (x + 1)) p;;

let is_constructor f = f >= 0;;
let is_defined f = f < 0;;

(* Keep track of greatest values *)
let greatest_var = ref 0;;
let newvar () = let i = !greatest_var in incr greatest_var; i;;

let update_greatest_var c =
  try greatest_var := 1 + c#greatest_varcode with
    Failure _ -> ()
;;

let sort_counter = ref 0;;
let new_sort () = let i = !sort_counter in let () = incr sort_counter in Def_sort i;;

let obs_sort_counter = ref 0

let constructor_counter = ref 0;;
let new_constructor () =
  let i = !constructor_counter in let () = incr constructor_counter in i
;;

let function_counter = ref (-1);;
let new_function () =
  let i = !function_counter in let () = decr function_counter in i
;;

(* These lists hold symbols ids *)
let all_defined_functions = ref ([] : const list);;
let all_constructors = ref ([] : const list);;

let all_induction_positions = ref ([] : (const * (const * int) list) list);;
let all_induction_paths = ref ([] : path list);;

let clause_counter = ref 0;;
let new_clause_number () =
  let i = !clause_counter in let () = incr clause_counter in i
;;


let rec occurs_str str s =
  match s with 
    | Abstr_sort0 str' -> str = str' 
    | Abstr_sort1 (_, s') -> occurs_str str s'
    | Abstr_sort2 (_, s', s'') -> (occurs_str str s') || (occurs_str str s'')
    | Def_sort _ -> false


let yy_tmp_param_sorts = ref ([]: (string * sort) list) (* id <-> param sort assoc for variables *)

let insert_shorten (str, s) l = 
(*   let () = if !debug_mode then print_string ("\n The list yy_tmp_param_sorts before applying insert_shorten is: " ^ *)
(*   (List.fold_right (fun (x, s) y -> (x ^ " has associated the sort " ^ (sprint_sort s) ^ ", " ^ y)) !yy_tmp_param_sorts "")) else () in *)
  let rec fn1 (str, s) s' = 
    match s' with 
	Abstr_sort0 str' -> if str = str' then s else s'
      | Abstr_sort1 (i, s'') -> Abstr_sort1 (i, fn1 (str, s) s'')
      | Abstr_sort2 (i, s1, s2) -> Abstr_sort2 (i, (fn1 (str, s) s1), (fn1 (str, s) s2))
      | Def_sort _ -> s'
  in
  let rec fn (str, s) l = 
    match l with
	[] -> if str = (sprint_sort s) then [] else 
(* 	  let () =  if !debug_mode then print_string ("\n" ^ (n_spaces 3) ^ "Associating to " ^ str ^ " the sort " ^ (sprint_sort s)) in *)
	  [(str, s)]
      | (str', s') :: tl -> let new_s' = if occurs_str str s' then fn1 (str, s) s' else s' in
	if str' = (sprint_sort new_s') 
	then (fn (str, s) tl) 
	else 
(* 	  let () = if !debug_mode then print_string ("\n" ^ (n_spaces 3) ^ "Associating to " ^ str' ^ " the sort " ^ *)
(* 	(sprint_sort new_s')) else () in  *)
	generic_insert_sorted (str', new_s') (fn (str, s) tl)
  in
  match s with 
      Abstr_sort0 str' -> 
	let new_s = (try List.assoc str' l with Not_found -> s) in
	fn (str, new_s) l
    | Def_sort _| Abstr_sort1 _ | Abstr_sort2 _ ->  fn (str, s) l



let unify_sorts ps s0 = 
(*   let () = if !debug_mode then print_string ("\nunify_sorts:  the list yy_tmp_param_sorts before application is : " ^ *)
(*   (List.fold_right (fun (x, s) y -> (x ^ " has associated the sort " ^ (sprint_sort s) ^ ", " ^ y)) !yy_tmp_param_sorts "")) else () in *)

  let rec fn s1 s2 spaces = 
(*     let () = if !debug_mode then print_string ("\n" ^ (n_spaces spaces) ^ "Trying to unify s1: " ^ (sprint_sort s1) ^ "  with s2: " ^ (sprint_sort s2)) else () in *)
    let fn1 str s1 sp = 
      try 
	let new_s = List.assoc str !yy_tmp_param_sorts in
	fn s1 new_s sp
      with Not_found ->  
	let () = yy_tmp_param_sorts := insert_shorten (str, s1) !yy_tmp_param_sorts in s1
    in
    let res = 
      try 
	match s1 with
	    Def_sort x1 -> (
	      match s2 with
		  Def_sort x2 -> if x1 = x2 then s1 else failwith "fn"
		| Abstr_sort0 x -> fn1 x s1 (spaces + 3)
		| Abstr_sort1 _ | Abstr_sort2 _ -> failwith "fn"
	    )
	  | Abstr_sort0 x -> if x = (sprint_sort s2) || (not (occurs_str x s2)) then fn1 x s2 (spaces + 3) else failwith "fn"
	  | Abstr_sort1 (i, s) -> (
	      match s2 with 
		  Abstr_sort0 x -> if x = (sprint_sort s1) || not (occurs_str x s1) then fn1 x s1 (spaces + 3) else failwith "fn"
		| Abstr_sort1 (i', s') -> if i = i' then Abstr_sort1(i', fn s s' (spaces + 3)) else failwith "fn"
		| Def_sort _ | Abstr_sort2 _ -> failwith "fn"
	    )
	  | Abstr_sort2 (i, s', s'') -> (
	      match s2 with 
		  Abstr_sort0 x -> if x = (sprint_sort s1) || not (occurs_str x s1) then fn1 x s1 (spaces + 3) else failwith "fn" 
		| Abstr_sort2 (i', s1', s1'') -> if i = i' then Abstr_sort2(i', (fn s' s1' (spaces + 3)), (fn s'' s1'' (spaces + 3))) else failwith "fn"
		| Def_sort _ | Abstr_sort1 _ -> failwith "fn"
	    )
	with Failure _ -> failwith "unify_sorts"
    in 
(*     let () = if !debug_mode then print_string ("\n" ^ (n_spaces spaces) ^ "The result of unification of s1: " ^ (sprint_sort s1) ^ "  with s2: " ^ (sprint_sort s2) ^ " is " ^ (sprint_sort res)) else () in *)
    res
  in
  match ps with
      Variable_sort _ -> s0
    | Actual_sort s -> fn s s0 0
        

let equal_sorts s1 s2 = 
  if !specif_parameterized then 
    try let _ = unify_sorts (Actual_sort s1) s2 in true with Failure _ -> false  
  else
    s1 == s2


let sprint_param_sort s = 
  match s with 
      Actual_sort s' -> "Actual_sort(" ^ (sprint_sort s') ^ ")"
    | Variable_sort v -> "Variable_var(" ^ (sprint_var v (Def_sort 0) true) ^ ")"


let rec expand_sorts s = 
  match s with 
      Abstr_sort0 str -> (
	try 
	  let s' = List.assoc str !yy_tmp_param_sorts  in 
	  let () = if !debug_mode then buffered_output ("\n Expand the sort " ^ str ^ " to the sort " ^ (sprint_sort s')) else () in
	  s'
	with Not_found -> s
      )
    | Abstr_sort1 (i, s') -> Abstr_sort1 (i, expand_sorts s')
    | Abstr_sort2 (i, s', s'') -> Abstr_sort2 (i, (expand_sorts s'), expand_sorts s'')
    | Def_sort _ -> s

(* String - code correspondence for observable sorts *)
let dico_obs_sort = (new bijective_dictionary 101: (sort, string) bijective_dictionary)

(*let is_obs_sort s = let name = dico_sort_string#find s in try let r = dico_obs_sort#find_key name in true with _ -> false*)
let is_obs_sort s = try let _ = dico_obs_sort#find s in true with _ -> false

let print_dico_obs_sort () =
  buffered_output "dico_obs_sort:" ;
  dico_obs_sort#iter (fun k v ->     
    let () = match k with
	Def_sort s -> print_int s 
      | Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _ -> failwith "print_dico_sort_string"
  in 
  buffered_output " --> " ; buffered_output v)


(* String - code correspondence for functions *)
let dico_const_string : (const, string) bijective_dictionary =
  new bijective_dictionary 101
;;

let print_dico_const_string () =
  buffered_output "dico_const_string:";
  dico_const_string#iter
    (fun k v -> print_int k; buffered_output (" --> " ^ v))
;;

  (* sort_main_string gives the main string of a sort  *)
let sort_main_string s = 
  try 
    (match s with
	Def_sort i -> dico_const_string#find i
      | Abstr_sort0 str -> str
      | Abstr_sort1 (i, _) -> dico_const_string#find i
      | Abstr_sort2 (i, _, _) -> dico_const_string#find i
    )
  with Not_found -> failwith "sort_main_string"


(* Profile of functions *)
let dico_const_profile : (const, sort list) reversible_dictionary =
  new reversible_dictionary 101
;;

let sprint_profile l =
  if l = [] then failwith "sprint_profile" 
  else
    let (h, t) = List.hd l, List.tl l in
    sprint_list " " sprint_sort t ^ " -> " ^ sprint_sort h
;;

let print_dico_const_profile () =
  buffered_output "dico_const_profile:";
  dico_const_profile#iter

    (fun k v ->
       buffered_output (try dico_const_string#find k with Not_found -> failwith "raising Not_found in print_dico_const_profile");
       buffered_output ": ";
       buffered_output (sprint_profile v))
;;

(* Sort of functions *)
let dico_const_sort : (const, sort) reversible_dictionary =
  new reversible_dictionary 101
;;

let print_dico_const_sort () =
  buffered_output "dico_const_sort:";
  dico_const_sort#iter
    (fun k v ->
       buffered_output
         (try dico_const_string#find k ^ " --> " ^ sprint_sort v with Not_found -> failwith "raising Not_found in print_dico_const_sort"))
;;

(* properties of symbols. Each of them may have many properties  *)
type symbol_prop = Prop_ac | Prop_assoc | Prop_peano;;

let string_of_prop =
  function
    Prop_ac -> "AC"
  | Prop_assoc -> "ASSOC"
  | Prop_peano -> "PEANO"
;;

let dico_properties : (const, symbol_prop) assoc_dictionary =
  new assoc_dictionary 101
;;

let print_dico_properties () =
  buffered_output "dico_properties:";
  dico_properties#iter
    (fun k v ->
       buffered_output (dico_const_string#find k);
       buffered_output " --> ";
       buffered_output (sprint_list ", " string_of_prop v))
;;

(* shortcuts *)
let symbol_is_ac v =
  try List.mem Prop_ac (dico_properties#find v) with
    Not_found -> false
;;
let symbol_is_assoc v =
  try List.mem Prop_assoc (dico_properties#find v) with
    Not_found -> false
;;
let symbol_is_peano v =
  try List.mem Prop_peano (dico_properties#find v) with
    Not_found -> false
;;

(* Dictionary for arities of symbols *)
class dictionary_arities size =
  object (self)
    inherit [const, int * int] dictionary size
    method left_ar k = try fst (self#find k) with Not_found -> failwith "left_ar"
    method right_ar k = try snd (self#find k) with Not_found -> failwith "right_ar"
    method total_ar k = try let (l, r) = self#find k in l + r with Not_found -> failwith "total_ar"
  end;;

let dico_arities = new dictionary_arities 101;;

let print_dico_arities () =
  buffered_output "dico_arities:";
  dico_arities#iter
    (fun k v ->
       buffered_output (try dico_const_string#find k with Not_found -> failwith "raising Not_found in print_dico_arities");
       buffered_output " --> ";
       buffered_output
         ("(" ^ string_of_int (fst v) ^ ", " ^ string_of_int (snd v) ^ ")"))
;;

(* A dictionary for nullary types *)
let dico_sort_nullarity : (sort, bool) dictionary = new dictionary 101;;

let print_dico_sort_nullarity () =
  let fn s b =
    try buffered_output (dico_sort_string#find s ^ " --> " ^ string_of_bool b) with Not_found -> failwith "raising Not_found in print_dico_sort_nullarity" 
  in
  let () = buffered_output "dico_sort_nullarity:" in
  dico_sort_nullarity#iter fn
;;

(* Nullarity test *)
let is_nullary (_, s, _) = try dico_sort_nullarity#find s with Not_found -> false;;
let is_nullary_sort s = try dico_sort_nullarity#find s with Not_found -> false ;;

(* Compute nullarity of sort *)
let compute_sort_nullarity l_profiles =
  let rec fn l s =
    match s with 
	Def_sort _ -> 
	  (
	    if List.mem s l then false
	    else if is_nullary_sort s 
	    then true
	    else
	      let args_s =
		(try List.assoc s l_profiles with
		    Not_found ->
		      let () = try
			buffered_output
			  ("Sort \"" ^ dico_sort_string#find s ^
			  "\" has no constructors")
		      with Not_found -> failwith "compute_sort_nullarity"
		      in
		      let () = flush stdout in [])
	      in
	      match args_s with
		  [] ->
		    let () = dico_sort_nullarity#add s false in
		    let () = try
		      buffered_output
			("Sort \"" ^ dico_sort_string#find s ^ "\" is not nullary")
		    with Not_found -> failwith "compute_sort_nullarity"
		    in
		    false
		| _ ->
		    if List.for_all (fn2 (s :: l)) args_s then
		      let () = dico_sort_nullarity#add s true in
		      let () = try
			buffered_output
			  ("Sort \"" ^ dico_sort_string#find s ^ "\" is nullary")
		      with Not_found -> failwith "compute_sort_nullarity"
		      in
		      true
		    else
		      let () = dico_sort_nullarity#add s false in
		      let () = (try
			buffered_output
			  ("Sort \"" ^ dico_sort_string#find s ^ "\" is not nullary")
		      with Not_found -> failwith "compute_sort_nullarity")
		      in
		      false
	  )
      | Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _ -> false

and fn2 l =
      function
	  [] -> invalid_arg "compute_sort_nullarity"
	| [_] -> true
	| _ :: t -> List.for_all (fn l) t
  in
  fn []
;;

(* Update the dictionary above browsing the profile dico *)
let update_dico_sort_nullarity () =
  let l = ref [] in
  let fn x v =
    try 
      if is_constructor x then
	l := generic_assoc_insert_sorted (dico_const_sort#find x, v) !l
    with Not_found -> failwith ("failure : update_dico_sort_nullarity on the symbol " ^ (string_of_int x))
  in
  let () = dico_const_profile#iter fn in
  dico_sort_string#iter (fun s _ -> let _ = compute_sort_nullarity !l s in ())
;;

(* A dictionary holding free constructors. *)
let dico_free_constructors : (const, bool) dictionary = new dictionary 101;;

let print_dico_sort_nullarity () =
  let fn s b =
    try buffered_output (dico_sort_string#find s ^ " --> " ^ string_of_bool b) with Not_found -> failwith "raising Not_found in print_dico_sort_nullarity"
  in
  let () = buffered_output "dico_sort_nullarity:" in
  dico_sort_nullarity#iter fn
;;

let print_dico_free_constructors () =
  buffered_output "dico_free_constructors:";
  dico_free_constructors#iter
    (fun k v ->
       buffered_output (string_of_int k ^ " --> " ^ string_of_bool v))
;;

(* This dictionary associates to one symbol code all codes of lesser symbols *)
let dico_order = new order_dictionary 101;;

(* This dictionary associates to one symbol code all codes of infs symbols *)
let dico_infs = new assoc_dictionary 101;;

  (* dico_order_cc to be used for CC  *)

let dico_order_cc = new order_dictionary 101;;

let print_dico_order () =
  buffered_output "dico_order:";
  dico_order#iter
    (fun k l -> if k <> 0 && k <> 1 && l <> [] then
       try buffered_output ((dico_const_string#find k) ^ ": " ^
        (sprint_list " " dico_const_string#find
	 (* (fun x -> string_of_int x) *) l )^ ";") with Not_found -> failwith ("raising Not_found in print_dico_order with symbol k = " ^ (string_of_int k)))
;;



let print_dico_equivalence () =
  buffered_output "dico_equivalence:";
  dico_equivalence#iter
    (fun k v -> if k <> 0 && k <> 1&& List.length v <> 1 then
	try 
	  (* buffered_output (" k = " ^ (string_of_int k)); *)
	  (* buffered_output (dico_const_string#find k); *)
	  (* buffered_output " --> "; *)
	  buffered_output (sprint_list " ~ " 
			     (fun x -> (* let () = buffered_output (" x = " ^ (string_of_int x)) in *) dico_const_string#find x) v)
	with Not_found -> failwith "raising Not_found in print_dico_equivalence")
;;

let print_dico_eq f d =
  d#iter (fun k v -> buffered_output (f k ^ " --> " ^ sprint_list ", " f v))
;;

(* Status of operators *)
type status = Left | Right | Multiset;;

let sprint_status =
  function
    Left -> "Left"
  | Right -> "Right"
  | Multiset -> "Multiset"
;;

let default_status = ref Multiset;;

let change_default_status =
  function
    "LR" | "lr" -> default_status := Left
  | "RL" | "rl" -> default_status := Right
  | "MS" | "ms" -> default_status := Multiset
  | _ -> raise (Arg.Bad "Status must be LR | RL | MS")
;;

(* A dictionary for statuses *)
let dico_id_status : (int, status) dictionary = new dictionary 101;;

let print_dico_id_status () =
  buffered_output "dico_id_status:";
  dico_id_status#iter
    (fun k v ->
       try 
	 buffered_output (dico_const_string#find k);
       buffered_output " --> ";
       buffered_output (sprint_status v)
       with Not_found -> failwith "raising Not_found in print_dico_id_status")
;;

(* Complete status dictionary with the default value.
   AC symbols must have multiset status *)
let complete_status_dico () =
  let () =
    buffered_output
      ("Completing status dico with default status \"" ^
         sprint_status !default_status ^ "\"")
  in
  let () = flush stdout in
  let fn id _ =
    try let _ = dico_id_status#find id in () with
      Not_found ->
        if symbol_is_ac id then dico_id_status#add id Multiset
        else dico_id_status#add id !default_status
  in
  dico_const_string#iter fn
;;

let get_status id = try dico_id_status#find id with Not_found -> failwith  "get_status" ;;

let greater is_total x y =
  try
    ((* if is then List.mem y (dico_order_cc#find x) *)
    (* else *)
      List.mem y (dico_order#find x))
  with
    Not_found -> false
;;


let equivalent x y =
  x = y ||
  (try
     List.mem y (dico_equivalence#find x) &&
     (let () =
        do_nothing
          (dico_const_string#find x ^ " = " ^ dico_const_string#find y)
      in
      true)
   with
     Not_found -> false)
;;

let inf_sym x y =
(*   let () = buffered_output ("\ninf_sym -> compare: " ^ (dico_const_string#find x ^ " with " ^ dico_const_string#find y)) in *)
  try
    (List.mem x (if !dico_infs_flag then dico_infs#find y else dico_order#find y)) ||
     (List.mem y (dico_infs#find_keys x))
  with
    Not_found -> 
      if !dico_infs_flag then 
	try List.mem x (dico_order#find y) 
	with Not_found -> false 
      else false
;;


(* Is a symbol minimal in Sigma \ l ? *)
let minimal l x =
  try
    let v = dico_order#find x in
    match generic_remove_sorted_lists v l with
      [] -> true
    | _ -> false
  with
    Not_found -> false
;;

(* Check that equivalent symbols have the same status *)
let check_status_equivalent_symbols () =
  let fn k v =
    let s = try get_status k with _ -> !default_status in
    let _ =
      List.for_all (fun x -> (try get_status x with _ -> !default_status) = s) v ||
      failwith "check_status_equivalent_symbols"
    in
    ()
  in
  dico_equivalence#iter fn
;;

(* Print a path *)
let sprint_path p =
  try "[ " ^
    sprint_list " ; "
      (fun (x, y) -> dico_const_string#find x ^ " @ " ^ string_of_int y) p ^
    " ]"
  with Not_found -> failwith "raising Not_found in sprint_path"
;;

(* We have implemented three ways of computing test sets:
   - one relies on the maximum depth of the whole rewrite system (v0)
   - the second on the maximum depth of subterms w.r.t. a given position and path (v1)
   - the third is the set of subterms present in the axioms.
   In the first two cases, we have two dictionaries: one for induction positions and the key
   for retrieving test-sets, the other binding the key to the actual test-set.
   In the third case, we have only one dictionary, since we don't perform term sharing.
*)

let dico_ind_positions_v0 : (const, (const * int) list list) assoc_dictionary =
  new assoc_dictionary 101
;;
let dico_ind_positions_v1 : (path, (int * sort)) dictionary =
  new dictionary 101
;;

let print_dico_ind_positions_v0 () =
  let fn c (l: ((const * int) list list list)) =
    let fn1 (l1: ((const * int) list list )) =
      
      let fn' (l': ((const * int) list )) = 
	let pos = List.map snd l' in
	let path = List.map fst l' in
	try
	(sprint_position (list_all_but_last_el pos)) ^ " having the path [" ^ (sprint_list ",  " (fun c ->
	  dico_const_string#find c) path) ^ " ]"  
	with Not_found -> failwith "raising Not_found in print_dico_ind_positions_v0"
      in
      (sprint_list " / " fn' l1) 
    in
    try 
      buffered_output
	(dico_const_string#find c ^ " [" ^ string_of_int c ^ "] --> " ^
	(sprint_list "\n\t " fn1 l) )
    with Not_found -> failwith "raising Not_found in print_dico_ind_positions_v0"
  in
  let () = buffered_output "\n\ndico_ind_positions_v0 =" in
  dico_ind_positions_v0#iter fn
;;

let print_dico_ind_positions_v1 () =
  let fn p (d, s) =
    try 
      buffered_output
	(sprint_path p ^ " --> (" ^ string_of_int d ^ ", " ^
        dico_sort_string#find s ^ ")")
    with Not_found -> failwith "raising Not_found in print_dico_ind_positions_v1"
  in
  let () = buffered_output "dico_ind_positions_v1 =" in
  dico_ind_positions_v1#iter fn
;;


let default_fill_order_dico_cc () =
  let () = buffered_output "Setting default order for symbols" in
  let () = flush stdout in
  let rec fn =
    function
      [] -> ()
    | h :: t -> let () = List.iter (dico_order_cc#add_couple h) t in fn t
  in
  let l = List.rev (!all_defined_functions @ !all_constructors) in
  let () =
    try 
      buffered_output (sprint_list " > " dico_const_string#find l) 
    with Not_found -> failwith "raising Not_found in print_dico_ind_positions_v0"
  in
  fn l
;;


let update_profile ls = 
  let treated_sorts = ref [] in
  let rec f s = 
    match s with 
	Abstr_sort0 str -> 
	  let new_str = 
	    try 
	      List.assoc str !treated_sorts 
	    with Not_found -> (* str is not defined *)
	      let () = param_sort_counter := !param_sort_counter + 1 in
	      let str' = (str ^ (string_of_int !param_sort_counter)) in
	      let ()  = treated_sorts := (str, str') :: !treated_sorts in
	      str'
	  in Abstr_sort0 new_str
      | Abstr_sort1 (i, s') -> Abstr_sort1 (i, f s')
      | Abstr_sort2 (i, s', s'') -> Abstr_sort2 (i, (f s'), f s'')
      | Def_sort _ -> s
  in
  List.map f ls

let all_specifs = ref ([] : string list);;
    
(* We can add a complete pre-defined specification with the "use" token in the specification file.
   The arguments are
   [ (sort_code, sort_string) ]
   [ (symbol_code, symbol_string, [ sort_codes ], left_ar, right_ar, props) ] *)
let add_specif name l_sorts l_syms =
  let rec fn =
    function
      [] -> ()
    | (s, sym) :: t ->
	match s with 
	    Def_sort s_id -> 
              let () = buffered_output
		("adding sort " ^ string_of_int s_id ^ "/" ^ sym ^
		" into sorts dictionary")
	      in
	      dico_sort_string#add s sym; fn t
	  | Abstr_sort0 _ | Abstr_sort1 _ | Abstr_sort2 _ -> fn t
  and fn2 =
    function
      [] -> ()
    | (cod, str, prof, l_ar, r_ar, props) :: t ->
        let () =
          buffered_output
            ("adding symbol " ^ string_of_int cod ^ "/" ^ str ^
               " into symbols dictionary")
        in
        dico_const_string#add cod str;
        let v = List.hd prof in
        dico_const_sort#add cod v;
        dico_const_profile#add cod prof;
        dico_arities#add cod (l_ar, r_ar);
        List.iter (dico_properties#add cod) props;
        fn2 t
  in
  fn l_sorts; fn2 l_syms; all_specifs := name :: !all_specifs
;;

(* The table for specif_name - function combos *)
let predefined_specif_table : (string, (unit -> unit)) Hashtbl.t =
  Hashtbl.create 101
;;
let add_predefined_specif s =
  try Hashtbl.find predefined_specif_table s () with
   Not_found -> failwith "add_predefined_specif"
;;

(* We always add definition of booleans *)
let id_sort_bool = new_sort ()
and id_symbol_true = new_constructor ()
and id_symbol_false = new_constructor ();;

let add_bool_specif () =
  let l_sorts = [id_sort_bool, "bool"]
  and l_symbols =
    [id_symbol_true, "true", [id_sort_bool], 0, 0, [];
     id_symbol_false, "false", [id_sort_bool], 0, 0, []]
  in
  add_specif "bool" l_sorts l_symbols
;;

(* let () = add_bool_specif ();; *)

(* Basic specification for naturals *)
let nat_specif_defined = ref false;;
let id_sort_nat = new_sort ();;
let id_symbol_zero = new_constructor ();;
let id_symbol_s = new_constructor ();;


  (* defined but not used *)
let add_lists_specif () =
  let list_sort = new_sort () 
  and nat_sort = try dico_sort_string#find_key "nat" with Failure _ -> failwith "raising find_key in add_lists_specif" in
  let l_sorts = [list_sort, "list"]
  and l_symbols =
    [new_constructor (), "nil", [list_sort], 0, 0, [];
     new_constructor (), "cons", [list_sort; nat_sort; list_sort], 0, 2,
     [Prop_assoc]]
  in
  sort_counter := 2; (* because we have list, bool *)
  constructor_counter := 4; (* because we have true and false, nil and cons*)
  function_counter := -1; 
  add_specif "list" l_sorts l_symbols
;;

(* Peano arithmetics. We trigger its use with the "use" token. *)

let id_symbol_less = new_function ();;
let id_symbol_leq = new_function ();;
let id_symbol_greater = new_function ();;
let id_symbol_geq = new_function ();;
let id_symbol_plus = new_function ();;
let id_symbol_times = new_function ();;
let id_symbol_minus = new_function ();;
let id_symbol_minus_nat = new_function ();;

(* extra arithmetics functions. *)

let id_symbol_min = new_function ();;
let id_symbol_max = new_function ();;

(* let id_dummy = new_function ();; *)

let add_nat_specif () =
  let () = add_bool_specif () in
  let nat_incompatible_types = ["int"] in
  let () = if List.exists (fun x -> List.mem x !all_specifs) nat_incompatible_types then failwith "nat" in
  let l_sorts = [id_sort_nat, "nat"]
  and l_symbols =
    [
      id_symbol_zero, "0", [id_sort_nat], 0, 0, [Prop_peano];
      id_symbol_s, "s", [id_sort_nat; id_sort_nat], 0, 1, [Prop_peano];
      id_symbol_minus_nat, "minus", [id_sort_nat; id_sort_nat; id_sort_nat], 1, 1,
      [Prop_peano];
      id_symbol_less, "<", [id_sort_bool; id_sort_nat; id_sort_nat], 1, 1,
      [Prop_peano];
      id_symbol_leq, "<=", [id_sort_bool; id_sort_nat; id_sort_nat], 1, 1,
      [Prop_peano];
      id_symbol_greater, ">", [id_sort_bool; id_sort_nat; id_sort_nat], 1,
      1, [Prop_peano];
      id_symbol_geq, ">=", [id_sort_bool; id_sort_nat; id_sort_nat], 1,
      1, [Prop_peano];
      id_symbol_plus, "+", [id_sort_nat; id_sort_nat; id_sort_nat], 1, 1,
      [Prop_peano(* ; Prop_ac *)];
      id_symbol_times, "*", [id_sort_nat; id_sort_nat; id_sort_nat], 1,
      1, [Prop_peano(* ; Prop_ac *) ];
      id_symbol_min, "min", [id_sort_nat; id_sort_nat; id_sort_nat], 0, 2,
     [];
      id_symbol_max, "max", [id_sort_nat; id_sort_nat; id_sort_nat], 0, 2,
     []
    ]
  in
  sort_counter := 2; (* because we have nat, bool *)
  constructor_counter := 4; (* true and false, 0 and s*)
  function_counter := -11; (* <, <=, >, >=, +, *, -, minus, min, max *)
  add_specif "nat" l_sorts l_symbols;
  nat_specif_defined := true;
  specif_LA_defined := true
;;

Hashtbl.add predefined_specif_table "nats" add_nat_specif;;

(* Basic representation for integers *)

let int_specif_defined = ref false;;
let id_sort_int = new_sort ();;
let id_symbol_p = new_constructor ();;

let add_int_specif () =
  let int_incompatible_types = ["nat"] in
  let () = if List.exists (fun x -> List.mem x !all_specifs)
    int_incompatible_types then failwith "int" in
  let l_sorts = [id_sort_int, "int"]
  and l_symbols =
    [
      id_symbol_zero, "0", [id_sort_int], 0, 0, [];
      id_symbol_s, "s", [id_sort_int; id_sort_int], 0, 1, [];      
      id_symbol_p, "p", [id_sort_int; id_sort_int], 0, 1, [];      
      id_symbol_less, "<", [id_sort_bool; id_sort_int; id_sort_int], 1, 1,
      [Prop_peano];
      id_symbol_leq, "<=", [id_sort_bool; id_sort_int; id_sort_int], 1, 1,
      [Prop_peano];
      id_symbol_greater, ">", [id_sort_bool; id_sort_int; id_sort_int], 1,
      1, [Prop_peano];
      id_symbol_geq, ">=", [id_sort_bool; id_sort_int; id_sort_int], 1,
      1, [Prop_peano];
      id_symbol_plus, "+", [id_sort_int; id_sort_int; id_sort_int], 1, 1,
      [Prop_peano(* ; Prop_ac *)];
      id_symbol_times, "*", [id_sort_int; id_sort_int; id_sort_int], 1,
      1, [Prop_peano(* ; Prop_ac *)];
      id_symbol_minus, "-", [id_sort_int; id_sort_int; id_sort_int], 1, 1,
      [Prop_peano]
    ]
  in
  sort_counter := 3; (* because we have nat, int, bool *)
  constructor_counter := 5; (* true and false, 0, p and s*)
  function_counter := -8; (* <, <=, >, >=, +, *, - *)
  add_specif "int" l_sorts l_symbols; 
  specif_LA_defined := true;
  int_specif_defined := true
;;

Hashtbl.add predefined_specif_table "int" add_int_specif;;

(* Theory of natural lists. We trigger its use with the "use" token. *)

(* Basic representation for integers *)

let list_specif_defined = ref false;;
let id_sort_list = new_sort ();;
let id_symbol_nil = new_constructor ();;
let id_symbol_cons = new_constructor ();;


let id_symbol_rev = new_function ();;
let id_symbol_len = new_function ();;
let id_symbol_app = new_function ();;
let id_symbol_single = new_function ();;



let add_list_specif () =
  let () = add_nat_specif () in
  let list_incompatible_types = ["int"] in
  let () = if List.exists (fun x -> List.mem x !all_specifs) list_incompatible_types then failwith "lists" in
  let l_sorts = [id_sort_list, "natlist"]
  and l_symbols =
    [
      id_symbol_nil, "nil", [id_sort_list], 0, 0, [];
      id_symbol_cons, "cons", [id_sort_list; id_sort_nat; id_sort_list], 0, 2, [];
      id_symbol_single, "single", [id_sort_list; id_sort_nat], 0,
      1, [];
      id_symbol_len, "len", [id_sort_nat; id_sort_list], 0, 1,
      [];
      id_symbol_rev, "rev", [id_sort_list; id_sort_list], 0, 1,
      [];
      id_symbol_app, "app", [id_sort_list; id_sort_list; id_sort_list], 0, 2,
      []
    ]
  in
  sort_counter := 3; (* because we have nat, list, bool *)
  constructor_counter := 6; (* true and false, 0 and s, nil, cons*)
  function_counter := -14; (* <, <=, >, >=, +, *, -, minus, min, max, len, rev, app, single *)
  add_specif "natlist" l_sorts l_symbols;
  specif_LA_defined := true;
  list_specif_defined := true;
;;

Hashtbl.add predefined_specif_table "lists" add_list_specif;;


(*************************************************************************)

let sprint_term_list l = sprint_list " ; " (fun x -> x#string) l;;

(*************************************************************************)

(* stores the variables that abstracted terms of the form len(xs) *)

let lenvar_l = ref [] 
