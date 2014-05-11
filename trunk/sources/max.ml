open Values
open Diverse
open Symbols
open Terms
open Order
open Io

let zero_t = new term (Term (id_symbol_zero, [], id_sort_nat))

let rec max_propagate_s t = 
 match t#content with
    | Var_univ _ | Var_exist _ -> t
    | Term (f, l, _) ->
      if f == id_symbol_zero then t
      else if f == id_symbol_s then 
 	let arg_s = List.hd l in
	let arg_s_n = max_propagate_s arg_s in
	(match arg_s_n#content with
	  | Var_univ _ | Var_exist _ -> new term (Term (id_symbol_s, [arg_s_n], id_sort_nat))
	  | Term (f', l', _) ->
	    if f'== id_symbol_zero then new term (Term (id_symbol_s, [arg_s_n], id_sort_nat))
	    else if f'== id_symbol_s then 
	       new term (Term (id_symbol_s, [arg_s_n], id_sort_nat))
	    else if f' == id_symbol_max then 
	      let arg1 = List.hd l' in
	      let arg2 = List.hd (List.tl l') in
	      let arg1' = new term (Term (id_symbol_s, [arg1], id_sort_nat)) in
	      let arg2' = new term (Term (id_symbol_s, [arg2], id_sort_nat)) in
	      let arg1'_s = max_propagate_s arg1' in
	      let arg2'_s = max_propagate_s arg2' in
	      new term (Term (id_symbol_max, [arg1'_s;arg2'_s], id_sort_nat))
	    else
	      let () = if !maximal_output then buffered_output ("max_propagate_s: symbol " ^ (dico_const_string#find f') ^ " not managed by Rmaxs0") in failwith "outside Rmax"
	)
      else if f == id_symbol_max then
	let arg1 = List.hd l in
	let arg2 = List.hd (List.tl l) in
	let arg1' = max_propagate_s arg1 in
	let arg2' = max_propagate_s arg2 in
	if arg1'#syntactic_equal zero_t then arg2'
	else if arg2'#syntactic_equal zero_t then arg1'
	else new term (Term (id_symbol_max, [arg1';arg2'], id_sort_nat))
      else
	let () = if !maximal_output then buffered_output ("max_propagate_s: symbol " ^ (dico_const_string#find f) ^ " not managed by Rmaxs0") in failwith "outside Rmax"

let rec max_smaller x l = 
  let rec fn_smaller t t' =
    match t#content with
	 | Var_univ _ | Var_exist _ -> 
	   (match t'#content with 
	        | Var_univ _ | Var_exist _ -> false
		| Term (f, _, _) ->
		  if f == id_symbol_zero then false
		  else if f == id_symbol_s then 
		     list_member (fun (i, _, _) (j, _, _) -> i == j) (List.hd t#variables) t'#variables
		  else  let () = if !maximal_output then buffered_output ("fn_smaller: symbol " ^ (dico_const_string#find f) ^ " not managed by Rmaxs0") in failwith "fn_smaller"
	   )
	 | Term (f1, l1, _) ->
	   if f1 == id_symbol_zero then 
	     not (t#syntactic_equal t')
	   else if f1 == id_symbol_s then 
	     (match t'#content with 
	        | Var_univ _ | Var_exist _ -> false
		| Term (f2, l2, _) ->
		  if f2 == id_symbol_zero then false
		  else if f2 == id_symbol_s then 
		     fn_smaller (List.hd l1) (List.hd l2)
		  else  let () = if !maximal_output then buffered_output ("fn_smaller: symbol " ^ (dico_const_string#find f2) ^ " not managed by Rmaxs0") in failwith "fn_smaller"
	     )
	   else  let () = if !maximal_output then buffered_output ("fn_smaller: symbol " ^ (dico_const_string#find f1) ^ " not managed by Rmaxs0") in failwith "fn_smaller"
  in
  if l == [] then false
  else 
    (fn_smaller x (List.hd l)) || (max_smaller x (List.tl l))
    


let rec max_delete l l_orig = 
  if l == [] then [] 
  else 
    let tail_ordered =  max_delete (List.tl l) l_orig  in
    let fst = List.hd l in
    if max_smaller fst l_orig then
      tail_ordered
    else (fst :: tail_ordered)
	     
let rec max_list t =
  match t#content with
    | Var_univ _ | Var_exist _ -> [t]
    | Term (f, l, _) ->
      if f == id_symbol_zero then [t]
      else if f == id_symbol_s then
	(* let arg1 = max_list (List.hd l) in  *)
	[t]
      else if f == id_symbol_max then
	let arg1_l = max_list (List.hd l) in
	let arg2_l = max_list (List.hd (List.tl l)) in
	arg1_l @ arg2_l
      else failwith "max_list"

let rec build_max l = 
  match l with
    |  [] -> failwith "build_max"
    | x :: ls -> 
      if ls == [] then x
      else 
	let ls_max = build_max ls in
	new term (Term (id_symbol_max, [x; ls_max], id_sort_nat))

let rec max_ordered l l' = 
  match l with
    | [] -> l'
    | x :: ls -> 
      let lx' = insert_sorted (fun x y -> x#syntactic_equal y) (fun x y -> ground_greater y x) x l' in
      max_ordered ls lx'
  
let max_norm t i = 
  let ts = try max_propagate_s t 
    with Failure "outside Rmax" -> failwith "max_norm" 
  in
  (* let () = buffered_output ("\nAfter max_propagate, t = " ^ t#string) in *)
  let list_ts = max_list ts in
  let del_l = max_delete list_ts list_ts in
  let lres = max_ordered del_l [] in
  build_max lres
