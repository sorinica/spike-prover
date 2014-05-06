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

let rec list_propagate t = 
  match t#content with
    | Var_univ _ | Var_exist _ -> t
    | Term (f, l, _) -> 
      if f == id_symbol_app then
	let arg1 = List.hd l in
	let arg2 = List.hd (List.tl l) in
	let arg1' = list_propagate arg1 in
	let arg2' = list_propagate arg2 in
	if arg1'#syntactic_equal nil_term then arg2'
	else if arg2'#syntactic_equal nil_term then arg1'
	else (new term (Term (id_symbol_app,[arg1';arg2'], id_sort_list)))
      else if f == id_symbol_cons then 
	let arg1 = List.hd l in
	let arg2 = List.hd (List.tl l) in
	let arg1' = nat_propagate arg1 in
	let arg2' = list_propagate arg2 in
	let t1 = new term (Term (id_symbol_single,[arg1'], id_sort_list)) in
	 new term (Term (id_symbol_app, [t1;arg2'], id_sort_list))
      else if f == id_symbol_rev then 
	let arg = List.hd l in
	let argn = list_propagate arg in
	(match argn#content with
	  | Var_univ _ | Var_exist _ -> t
	  | Term (f', l', _) -> 
	    if f' == id_symbol_nil then new term (Term (id_symbol_nil,[],id_sort_list))
	    else if f' == id_symbol_single then 
	      argn
	    else if f' == id_symbol_rev then
	      let arg1 = List.hd l' in
	      list_propagate arg1
	    else if f' == id_symbol_app then
	      let arg1 = List.hd l' in
	      let arg2 = List.hd (List.tl l') in
	      let t1 = new term (Term (id_symbol_rev, [arg2], id_sort_list)) in
	      let t2 = new term (Term (id_symbol_rev, [arg1], id_sort_list)) in
	      list_propagate (new term (Term (id_symbol_app, [t1;t2], id_sort_list)))
	    else 
	       (new term (Term (id_symbol_rev, [argn], id_sort_list)))
	)
      else if f == id_symbol_single then 
	let arg1 = List.hd l in
	let arg' = nat_propagate arg1 in
	new term (Term (id_symbol_single,[arg'], id_sort_list))
      else if f == id_symbol_nil then t
      else 
	let () = if !maximal_output then buffered_output ("list_propagate: symbol " ^ (dico_const_string#find f) ^ " not managed by Rnatlist") in
	failwith "outside natlist"
	
and  nat_propagate t = 
  (* let () = buffered_output ((fn_spaces i) ^ "natlist_propagate_min t = " ^ t#string) in *)
 match t#content with
    | Var_univ _ | Var_exist _ -> t
    | Term (f, l, _) ->
      if f == id_symbol_len then 
	let arg = List.hd l in
	let arg' = list_propagate arg in
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
	      let arg1' = list_propagate arg1 in
	      new term (Term (id_symbol_len,[arg1'],id_sort_nat)) 
	    else if f' == id_symbol_app then
	      let arg1 = List.hd l' in 
	      let arg2 = List.hd (List.tl l') in
	      let arg1' = list_propagate arg1 in
	      let arg2' = list_propagate arg2 in
	      let t1 = new term (Term (id_symbol_len, [arg1'], id_sort_nat)) in
	      let t2 = new term (Term (id_symbol_len, [arg2'], id_sort_nat)) in
	      new term (Term (id_symbol_plus, [nat_propagate t1; nat_propagate t2], id_sort_nat))
	    else new term (Term (id_symbol_len, [arg'], id_sort_nat))
	)
      else if f == id_symbol_zero then t
      else if f == id_symbol_s then
	let arg = List.hd l in
	let arg' = nat_propagate arg in
	let t' = new term (Term (id_symbol_s, [arg'], id_sort_nat))
	in np_norm t' 0
      else if f == id_symbol_plus then
	let arg1 = List.hd l in 
	let arg2 = List.hd (List.tl l) in
	let arg1' = nat_propagate arg1 in
	let arg2' = nat_propagate arg2 in
	let t' = new term (Term (id_symbol_plus, [arg1'; arg2'], id_sort_nat))
	in np_norm t' 0
      else if f == id_symbol_times then
	let arg1 = List.hd l in 
	let arg2 = List.hd (List.tl l) in
	let arg1' = nat_propagate arg1 in
	let arg2' = nat_propagate arg2 in
	let t' = new term (Term (id_symbol_times, [arg1'; arg2'], id_sort_nat))
	in np_norm t' 0
      else
	let () = if !maximal_output then buffered_output ("nat_propagate: symbol " ^ (dico_const_string#find f) ^ " not managed by Rnatlist") in
	failwith "outside natlist"


      
let natlist_norm t i = 
  match t#content with
    | Var_univ _ | Var_exist _ -> failwith "natlist_norm"
    | Term (f, l, s) -> 
      try 
	if s == id_sort_nat then nat_propagate t
	else if s == id_sort_list then list_propagate t
	else failwith "natlist_norm"
      with Failure "outside natlist" ->
	let () = buffered_output "Here !!! "  in
	failwith "natlist_norm"
	
	
