open Values
open Diverse
open Symbols
open Terms
open Order
open Npolynoms
open Io

let nil_term = new term (Term (id_symbol_nil, [], id_sort_list))

let rec fn_spaces n = 
  if n == 0 then "\n" else (fn_spaces (n-1)) ^ "  "

let rec purify t = 
   match t#content with
    | Var_univ _ | Var_exist _ -> t
    | Term (f, l, s) -> 
      if f == id_symbol_len then 
	let arg = List.hd l in
	(match arg#content with
	  | Var_univ (i,_) -> let () = lenvar_l := (i :: !lenvar_l) in new term (Var_univ (i, id_sort_nat))
	  | Var_exist (i,_) ->let () = lenvar_l := (i :: !lenvar_l) in  new term (Var_exist (i, id_sort_nat))
	  | Term _ -> let arg_p = purify arg in
		      new term (Term (id_symbol_len, [arg_p], id_sort_nat))
	)
      else if f == id_symbol_app || f == id_symbol_cons || f == id_symbol_plus || f == id_symbol_times then
	let arg1 = List.hd l in
	let arg2 = List.hd (List.tl l) in
	let arg1_p = purify arg1 in
	let arg2_p = purify arg2 in
	new term (Term (f, [arg1_p;arg2_p], s))
      else if f == id_symbol_rev || f == id_symbol_single || f == id_symbol_s then
	let arg = List.hd l in
	let arg_p = purify arg in
	new term (Term (f, [arg_p], s))
      else if f == id_symbol_nil || f == id_symbol_zero then t
      else failwith "purify"


let rec list_propagate t i = 
  (* let () = buffered_output ((fn_spaces i) ^ "list_propagate t = " ^ t#string) in *)
  match t#content with
    | Var_univ _ | Var_exist _ -> t
    | Term (f, l, _) -> 
      if f == id_symbol_app then
	let arg1 = List.hd l in
	let arg2 = List.hd (List.tl l) in
	let arg1' = list_propagate arg1 (i+1) in
	let arg2' = list_propagate arg2 (i+1) in
	if arg1'#syntactic_equal nil_term then arg2'
	else if arg2'#syntactic_equal nil_term then arg1'
	else
	  (match arg1'#content with 
	    | Term (f1,l1,_) ->
	      if f1 == id_symbol_app then
		let arg21 = List.hd l1 in
		let arg22 = List.hd (List.tl l1) in
		let newt = list_propagate (new term (Term (id_symbol_app, [arg22; arg2'], id_sort_list))) (i+1) in
		new term (Term (id_symbol_app, [arg21; newt], id_sort_list)) 
	      else (new term (Term (id_symbol_app,[arg1';arg2'], id_sort_list)))
	    | _ ->  (new term (Term (id_symbol_app,[arg1';arg2'], id_sort_list)))
	  )
	else if f == id_symbol_cons then 
	  let arg1 = List.hd l in
	  let arg2 = List.hd (List.tl l) in
	  let arg2' = list_propagate arg2 (i+1) in
	  let t1 = new term (Term (id_symbol_single,[arg1], id_sort_list)) in
	  let t1'  = list_propagate t1 (i+1) in
	  new term (Term (id_symbol_app, [t1';arg2'], id_sort_list))
	else if f == id_symbol_rev then 
	  let arg = List.hd l in
	  (match arg#content with
	    | Var_univ _ | Var_exist _ -> t
	    | Term (f', l', _) -> 
	      if f' == id_symbol_nil then new term (Term (id_symbol_nil,[],id_sort_list))
	      else if f' == id_symbol_single then 
		list_propagate arg (i+1)
	      else if f' == id_symbol_rev then
		let arg1 = List.hd l' in
		list_propagate arg1 (i+1)
	      else if f' == id_symbol_app then
		let arg1 = List.hd l' in
		let arg2 = List.hd (List.tl l') in
		let arg1_r = new term (Term (id_symbol_rev, [arg1], id_sort_list)) in
		let arg2_r = new term (Term (id_symbol_rev, [arg2], id_sort_list)) in
		let tres = new term (Term (id_symbol_app, [arg2_r; arg1_r], id_sort_list)) in
		list_propagate tres (i+1)
	      else
		let arg_p = list_propagate arg (i+1) in
		(new term (Term (id_symbol_rev, [arg_p], id_sort_list)))
	  )
	else if f == id_symbol_single then 
	  let arg1 = List.hd l in
	  let arg' = nat_propagate arg1 (i+1) in
	  new term (Term (id_symbol_single,[arg'], id_sort_list))
	else if f == id_symbol_nil then t
	else 
	  let () = if !maximal_output then buffered_output ("list_propagate: symbol " ^ (dico_const_string#find f) ^ " not managed by Rnatlist") in
	  failwith "outside natlist"
	    
and  nat_propagate t i = 
  let () = buffered_output ((fn_spaces i) ^ "nat_propagate t = " ^ t#string) in
  match t#content with
    | Var_univ _ | Var_exist _ -> t
    | Term (f, l, _) ->
      if f == id_symbol_len then 
	let arg = List.hd l in
	let arg' = list_propagate arg (i+1) in
	(match arg'#content with
	  | Var_univ (x,_)  -> let () = lenvar_l := (x :: !lenvar_l) in new term (Var_univ (x, id_sort_nat))
	  | Var_exist (x,_) -> let () = lenvar_l := (x :: !lenvar_l) in new term (Var_exist (x, id_sort_nat))
	  | Term (f', l', _) -> 
	    if f' == id_symbol_nil then new term (Term (id_symbol_zero, [], id_sort_nat))
	    else if f' == id_symbol_single then 
	      let t' = new term (Term (id_symbol_zero,[], id_sort_nat)) in
	      new term (Term (id_symbol_s,[t'], id_sort_nat))
	    else if f' == id_symbol_rev then
	      let arg1 = List.hd l' in
	      let arg1' = list_propagate arg1 (i+1) in
	      new term (Term (id_symbol_len,[arg1'],id_sort_nat)) 
	    else if f' == id_symbol_app then
	      let arg1 = List.hd l' in 
	      let arg2 = List.hd (List.tl l') in
	      let arg1' = list_propagate arg1 (i+1) in
	      let arg2' = list_propagate arg2 (i+1) in
	      let t1 = new term (Term (id_symbol_len, [arg1'], id_sort_nat)) in
	      let t2 = new term (Term (id_symbol_len, [arg2'], id_sort_nat)) in
	      nat_propagate (new term (Term (id_symbol_plus, [t1; t2], id_sort_nat))) (i+1)
	    else new term (Term (id_symbol_len, [arg'], id_sort_nat))
	)
      else if f == id_symbol_zero then t
      else if f == id_symbol_s then
	let arg = List.hd l in
	let arg' = nat_propagate arg (i+1) in
	let t' = new term (Term (id_symbol_s, [arg'], id_sort_nat))
	in np_norm (purify t') 0
      else if f == id_symbol_plus then
	let arg1 = List.hd l in 
	let arg2 = List.hd (List.tl l) in
	let arg1' = nat_propagate arg1 (i+1) in
	let arg2' = nat_propagate arg2 (i+1) in
	let t' = new term (Term (id_symbol_plus, [arg1'; arg2'], id_sort_nat))
	in np_norm (purify t') 0
      else if f == id_symbol_times then
	let arg1 = List.hd l in 
	let arg2 = List.hd (List.tl l) in
	let arg1' = nat_propagate arg1 (i+1) in
	let arg2' = nat_propagate arg2 (i+1) in
	let t' = new term (Term (id_symbol_times, [arg1'; arg2'], id_sort_nat))
	in np_norm (purify t') 0
      else
	let () = if !maximal_output then buffered_output ("nat_propagate: symbol " ^ (dico_const_string#find f) ^ " not managed by Rnatlist") in
	failwith "outside natlist"


      
let natlist_norm t i = 
  match t#content with
    | Var_univ _ | Var_exist _ -> failwith "natlist_norm"
    | Term (f, l, s) -> 
      try 
	if s == id_sort_nat then nat_propagate t 0
	else if s == id_sort_list then list_propagate t 0
	else failwith "natlist_norm"
      with Failure "outside natlist" ->
	let () = buffered_output "Here !!! "  in
	failwith "natlist_norm"
	
	
