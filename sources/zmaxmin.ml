open Values
open Diverse
open Symbols
open Terms
open Order
open Io


let zero_t = new term (Term (id_symbol_zero,[], id_sort_nat))

let rec fn_spaces n = 
  if n == 0 then "\n" else (fn_spaces (n-1)) ^ "  "

let rec zmm_propagate_min t i = 
  (* let () = buffered_output ((fn_spaces i) ^ "zmm_propagate_min t = " ^ t#string) in *)
 match t#content with
    | Var_univ _ | Var_exist _ -> t
    | Term (f, l, _) ->
      if f == id_symbol_zero then t
      else if f == id_symbol_max then 
	let arg1 = zmm_propagate_min (List.hd l) (i+1) in
	let arg2 = zmm_propagate_min (List.hd (List.tl l)) (i+1) in
	if arg1#syntactic_equal arg2 then arg1
	else if arg1#syntactic_equal zero_t then arg2
	else if arg2#syntactic_equal zero_t then arg1
	else new term (Term (id_symbol_max, [arg1;arg2], id_sort_nat))
      else if f == id_symbol_min then 
	let arg1' = (List.hd l) in
	let arg2' = (List.hd (List.tl l)) in
	let arg1 = zmm_propagate_min arg1' (i+1) in
	let arg2 = zmm_propagate_min arg2' (i+1) in 
	if arg1#syntactic_equal arg2 then arg1
	else
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
		       let t1' = zmm_propagate_min t1 (i+1) in
		       let t2' = zmm_propagate_min t2 (i+1) in
		       if t1'#syntactic_equal t2' then t1'
		       else if t1'#syntactic_equal zero_t then t2'
		       else if t2'#syntactic_equal zero_t then t1'
		       else  
			 new term (Term (id_symbol_max,[t1'; t2'], id_sort_nat))
		     else 
		       let () = if !maximal_output then buffered_output ("zmm_propagate_min: symbol " ^ (dico_const_string#find f2) ^ " not managed by Rzmm") in
		       failwith "outside Rzmm"
		 )
	     | Term (f1, l1, _) -> 
	       if f1 == id_symbol_zero then arg1
	       else if f1 == id_symbol_max then
		 let arg11 = (List.hd l1) in
		 let arg12 = (List.hd (List.tl l1)) in
		 let t1 = new term (Term (id_symbol_min, [arg11;arg2], id_sort_nat)) in
		 let t2 = new term (Term (id_symbol_min, [arg12;arg2], id_sort_nat)) in
		 let t1' = zmm_propagate_min t1 (i+1) in
		 let t2' = zmm_propagate_min t2 (i+1) in
		 if t1'#syntactic_equal t2' then t1'
		 else if t1'#syntactic_equal zero_t then t2'
		 else if t2'#syntactic_equal zero_t then t1'
		 else  
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
		       let t1' = zmm_propagate_min t1 (i+1) in
		       let t2' = zmm_propagate_min t2 (i+1) in
		       new term (Term (id_symbol_max,[t1'; t2'], id_sort_nat))
		     else
		       let () = if !maximal_output then buffered_output ("zmm_propagate_min: symbol " ^ (dico_const_string#find f2) ^ " not managed by Rzmm") in
		       failwith "outside Rzmm"
		 )
	       else 
		 let () = if !maximal_output then buffered_output ("zmm_propagate_min: symbol " ^ (dico_const_string#find f) ^ " not managed by Rzmm") in
		 failwith "outside Rzmm"
	)
      else  
	let () = if !maximal_output then buffered_output ("zmm_propagate_min: symbol " ^ (dico_const_string#find f) ^ " not managed by Rzmm") in
	failwith "outside Rzmm"
 
let rec zmm_greater x l  = 
(* fn_subset l l checks if l is a strict subset of l'  *)
  let fn_subset l1 l2 =
    List.for_all (fun x -> list_member (fun u v -> u#syntactic_equal v) x l2) l1 &&
     not (List.for_all (fun x -> list_member (fun u v -> u#syntactic_equal v) x l1) l2)
  in
  if l == [] then false
  else 
    (fn_subset (List.hd l) x) || (zmm_greater x (List.tl l))
    
(* delete subsumed subsets *)

let rec zmm_delete l l_orig = 
  if l == [] then [] 
  else 
    let tail_ordered =  zmm_delete (List.tl l) l_orig  in
    let fst = List.hd l in
    if (zmm_greater fst l_orig)  (* || (list_member (fun x y -> x#syntactic_equal y) zero_t fst) *)  then
      tail_ordered
    else (fst :: tail_ordered)
	     
(* convert t into a list of sublists, where each sublist is a min-term *)

let rec zmm_list t =
  let rec fn_min t = 
    match t#content with
      | Var_univ _ | Var_exist _ -> [t]
      | Term (f, l, _) ->
	if f == id_symbol_min then
	  let arg1_l = fn_min (List.hd l) in
	  let arg2_l = fn_min (List.hd (List.tl l)) in
	  List.fold_right (fun h l -> insert_sorted (fun x y -> x#syntactic_equal y) (fun x y -> ground_greater x y) h l) arg1_l  arg2_l
	else failwith "fn_min"
  in
  match t#content with
    | Var_univ _ | Var_exist _ -> [[t]]
    | Term (f, l, _) ->
      if f == id_symbol_zero then [[t]]
      else if f == id_symbol_min then
	[fn_min t]
      else if f == id_symbol_max then
	let arg1_l = zmm_list (List.hd l) in
	let arg2_l = zmm_list (List.hd (List.tl l)) in
	arg1_l @ arg2_l
      else failwith "zmm_list"


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

let rec zmm_ordered l l' = 
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
      zmm_ordered ls lx'

let rec build_zmm l = 
  match l with
    |  [] -> failwith "build_zmm"
    | x :: ls -> 
      let minx = min_term x in
      if ls == [] then minx
      else 
	let ls_zmm = build_zmm ls in
	new term (Term (id_symbol_max, [minx; ls_zmm], id_sort_nat))
  
let zmm_norm t i = 
  let ts = 
    try 
      zmm_propagate_min t 0 
    with Failure "outside Rzmm" -> failwith "zmm_norm" 
  in
  (* let () = buffered_output ("\nAfter zmm_propagate_min, t = " ^ ts#string) in *)
  let list_ts = zmm_list ts in
  let lres = zmm_ordered list_ts [] in
  let del_l = zmm_delete lres lres in
    build_zmm del_l 
