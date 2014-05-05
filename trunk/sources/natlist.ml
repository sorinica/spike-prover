open Values
open Diverse
open Symbols
open Terms
open Order
open Io

let rec fn_spaces n = 
  if n == 0 then "\n" else (fn_spaces (n-1)) ^ "  "

let rec natlist_propagate_min t i = 
  (* let () = buffered_output ((fn_spaces i) ^ "natlist_propagate_min t = " ^ t#string) in *)
 match t#content with
    | Var_univ _ | Var_exist _ -> t
    | Term (f, l, _) ->
      if f == id_symbol_zero then t
      else if f == id_symbol_max then 
	let arg1 = natlist_propagate_min (List.hd l) (i+1) in
	let arg2 = natlist_propagate_min (List.hd (List.tl l)) (i+1) in
	(match arg1#content with 
	     | Var_univ _ | Var_exist _ -> new term (Term (id_symbol_max,[arg1;arg2], id_sort_nat))
	     | Term (f1, _, _) -> 
	       if f1 == id_symbol_zero then arg2
	       else 
		 (match arg2#content with 
		   | Var_univ _ | Var_exist _ -> new term (Term (id_symbol_max,[arg1;arg2], id_sort_nat))
		   | Term (f2, _, _) -> 
		     if f2 == id_symbol_zero then arg1
		     else new term (Term (id_symbol_max, [arg1;arg2], id_sort_nat))
		 )
	)
      else if f == id_symbol_min then 
	let arg1' = (List.hd l) in
	let arg2' = (List.hd (List.tl l)) in
	let arg1 = natlist_propagate_min arg1' (i+1) in
	let arg2 = natlist_propagate_min arg2' (i+1) in 
	(match arg1#content with 
	     | Var_univ _ | Var_exist _ -> 
		 (match arg2#content with
		   | Var_univ _ | Var_exist _ -> new term (Term (id_symbol_min, [arg1; arg2], id_sort_nat))
		   | Term (f2, l2, _) -> 
		     if f2 == id_symbol_zero then arg2
		     else if f2 == id_symbol_min then new term (Term (id_symbol_min, [arg1; arg2], id_sort_nat))
		     else if f2 == id_symbol_max then 
		       let arg21 = (List.hd l2) in
		       let arg22 = (List.hd (List.tl l2)) in
		       let t1 = new term (Term (id_symbol_min, [arg1;arg21], id_sort_nat)) in
		       let t2 = new term (Term (id_symbol_min, [arg1;arg22], id_sort_nat)) in
		       let t1' = natlist_propagate_min t1 (i+1) in
		       let t2' = natlist_propagate_min t2 (i+1) in
		       new term (Term (id_symbol_max,[t1'; t2'], id_sort_nat))
		     else 
		       let () = if !maximal_output then buffered_output ("natlist_propagate_min: symbol " ^ (dico_const_string#find f2) ^ " not managed by Rnatlist") in
		       failwith "outside Rnatlist"
		 )
	     | Term (f1, l1, _) -> 
	       if f1 == id_symbol_zero then arg1
	       else if f1 == id_symbol_max then
		 let arg11 = (List.hd l1) in
		 let arg12 = (List.hd (List.tl l1)) in
		 let t1 = new term (Term (id_symbol_min, [arg11;arg2], id_sort_nat)) in
		 let t2 = new term (Term (id_symbol_min, [arg12;arg2], id_sort_nat)) in
		 let t1' = natlist_propagate_min t1 (i+1) in
		 let t2' = natlist_propagate_min t2 (i+1) in
		 new term (Term (id_symbol_max,[t1'; t2'], id_sort_nat))
	       else if f1 == id_symbol_min then
		 (match arg2#content with 
		   | Var_univ _ | Var_exist _ ->  new term (Term (id_symbol_min, [arg1; arg2], id_sort_nat))
		   | Term (f2, l2, _) -> 
		     if f2 == id_symbol_zero then arg2
		     else if f2 == id_symbol_min then new term (Term (id_symbol_min, [arg1; arg2], id_sort_nat))
		     else if f2 == id_symbol_max then 
		       let arg21 = (List.hd l2) in
		       let arg22 = (List.hd (List.tl l2)) in
		       let t1 = new term (Term (id_symbol_min, [arg1;arg21], id_sort_nat)) in
		       let t2 = new term (Term (id_symbol_min, [arg1;arg22], id_sort_nat)) in
		       let t1' = natlist_propagate_min t1 (i+1) in
		       let t2' = natlist_propagate_min t2 (i+1) in
		       new term (Term (id_symbol_max,[t1'; t2'], id_sort_nat))
		     else
		       let () = if !maximal_output then buffered_output ("natlist_propagate_min: symbol " ^ (dico_const_string#find f2) ^ " not managed by Rnatlist") in
		       failwith "outside Rnatlist"
		 )
	       else 
		 let () = if !maximal_output then buffered_output ("natlist_propagate_min: symbol " ^ (dico_const_string#find f) ^ " not managed by Rnatlist") in
		 failwith "outside Rnatlist"
	)
      else  
	let () = if !maximal_output then buffered_output ("natlist_propagate_min: symbol " ^ (dico_const_string#find f) ^ " not managed by Rnatlist") in
	failwith "outside Rnatlist"
 
let rec natlist_greater x l  = 
(* fn_subset l l checks if l is a strict subset of l'  *)
  let fn_subset l1 l2 =
    List.for_all (fun x -> list_member (fun u v -> u#syntactic_equal v) x l2) l1 &&
     not (List.for_all (fun x -> list_member (fun u v -> u#syntactic_equal v) x l1) l2)
  in
  if l == [] then false
  else 
    (fn_subset (List.hd l) x) || (natlist_greater x (List.tl l))
    
(* delete subsumed subsets *)

let rec natlist_delete l l_orig = 
  if l == [] then [] 
  else 
    let tail_ordered =  natlist_delete (List.tl l) l_orig  in
    let fst = List.hd l in
    if natlist_greater fst l_orig  then
      tail_ordered
    else (fst :: tail_ordered)
	     
(* convert t into a list of sublists, where each sublist is a min-term *)

let rec natlist_list t =
  let rec fn_min t = 
    match t#content with
      | Var_univ _ | Var_exist _ -> [t]
      | Term (f, l, _) ->
	if f == id_symbol_min then
	  let arg1_l = fn_min (List.hd l) in
	  let arg2_l = fn_min (List.hd (List.tl l)) in
	  arg1_l @ arg2_l
	else failwith "fn_min"
  in
  match t#content with
    | Var_univ _ | Var_exist _ -> [[t]]
    | Term (f, l, _) ->
      if f == id_symbol_zero then [[t]]
      else if f == id_symbol_min then
	[fn_min t]
      else if f == id_symbol_max then
	let arg1_l = natlist_list (List.hd l) in
	let arg2_l = natlist_list (List.hd (List.tl l)) in
	arg1_l @ arg2_l
      else failwith "natlist_list"


(* converts a list of terms into a min term *)

let rec min_term l =
  if l == [] then failwith "min_term"
  else 
    let h = List.hd l in
    let tl = List.tl l in
    if tl == [] then h
    else new term (Term (id_symbol_min, [h; (min_term tl)], id_sort_nat))

let l_sorted l = 
  let rec fn_sorted l l' =
    match l with
      | [] -> l'
      | h::tl -> 
	let hl' = insert_sorted (fun x y -> x#syntactic_equal y) (fun x y -> ground_greater x y) h l' in
	fn_sorted tl hl'
  in
  fn_sorted l []

let rec natlist_ordered l l' = 
  match l with
    | [] -> l'
    | x :: ls -> 
      let fn_eq l1 l2 = (List.for_all (fun x -> list_member (fun u v -> u#syntactic_equal v) x l1) l2) && (List.for_all (fun x -> list_member (fun u v -> u#syntactic_equal v) x l2) l1) in
      let fn_inf l1 l2 = 
	let ls1 = l_sorted l1 in
	let ls2 = l_sorted l2 in
	let mint1 = min_term ls1 in
	let mint2 = min_term ls2 in
	ground_greater mint1 mint2
      in
      let lx' = insert_sorted fn_eq fn_inf x l' in
      natlist_ordered ls lx'

let rec build_natlist l = 
  match l with
    |  [] -> failwith "build_natlist"
    | x :: ls -> 
      let minx = min_term x in
      if ls == [] then minx
      else 
	let ls_natlist = build_natlist ls in
	new term (Term (id_symbol_max, [minx; ls_natlist], id_sort_nat))
  
let natlist_norm t i = 
  let ts = 
    try 
      natlist_propagate_min t 0 
    with Failure "outside Rnatlist" -> failwith "natlist_norm" 
  in
  (* let () = buffered_output ("\nAfter natlist_propagate_min, t = " ^ ts#string) in *)
  let list_ts = natlist_list ts in
  let lres = natlist_ordered list_ts [] in
  let del_l = natlist_delete lres lres in
    build_natlist del_l 
