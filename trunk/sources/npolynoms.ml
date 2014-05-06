
(*
   * Project: Spike ver 0.1
   * File: npolynoms.ml
   * Content: non-linear polynoms definitions
*)

open Values
open Symbols
open Terms
open Order
open Io

(* Normalize a term using the Rmps0 theory *)
 
(* constants *)

let zero_t = new term (Term (id_symbol_zero, [], id_sort_nat))
let one_t = new term (Term (id_symbol_s, [zero_t], id_sort_nat)) 
let two_t = new term (Term (id_symbol_s, [one_t], id_sort_nat))

let rec fn_spaces n = 
  if n == 0 then "\n" else (fn_spaces (n-1)) ^ "  "

let measure t = 
  match t#content with
       | Var_univ _ | Var_exist _ -> t
       | Term (f, l, _) -> 
	 if f == id_symbol_s then t	  
	 else if f == id_symbol_times then 
	   let fst_arg = List.hd l in
	   let snd_arg = List.hd (List.tl l) in
	   if fst_arg#variables == [] then snd_arg else t
	 else failwith "measure"

let heavier t1 t2 = 
  ground_greater (measure t1) (measure t2)

let rec propagate_one t = 
  match t#content with
    | Var_univ _ | Var_exist _ -> new term (Term (id_symbol_plus, [t; one_t], id_sort_nat)) (* u -> u + 1 *)
    | Term (f, l, _) -> 
      if f == id_symbol_zero then
	one_t (* 0 + 1 = s(0) *)
      else if f == id_symbol_s then 
	new term (Term (id_symbol_s, [t], id_sort_nat)) (* c -> s(c) *)
      else if f == id_symbol_plus then
	let fst_arg = List.hd l in
	let snd_arg = List.hd (List.tl l) in
	let snd_plus_one = propagate_one snd_arg in
	new term (Term (id_symbol_plus, [fst_arg;snd_plus_one], id_sort_nat)) (* m1 + mn -> m1 + (propagate_one mn) *)
      else if f == id_symbol_times then
	new term (Term (id_symbol_plus, [t; one_t], id_sort_nat)) (* m1*mn -> m1*mn + s(0)) *)
      else failwith "propagate_one"

(* c1 + c2 *)

let rec add_nat t1 t2 i = 
  (* let () = buffered_output ((fn_spaces i) ^ "add_nat: t1 = " ^ t1#string ^ " t2 = "  ^ t2#string) in *)
  match t1#content with
    | Var_univ _ | Var_exist _ -> failwith "add_nat"
    | Term (f, l, _) ->
      if f == id_symbol_zero then t2
      else if f == id_symbol_s then 
	let sum = add_nat (List.hd l) t2 (i+1) in
	new term (Term (id_symbol_s, [sum], id_sort_nat))
      else failwith "add_nat"

(* c1 * c2 *)

let rec mult_nat t1 t2 i = 
  (* let () = buffered_output ((fn_spaces i) ^ "mult_nat: t1 = " ^ t1#string ^ " t2 = "  ^ t2#string) in *)
   match t1#content with
    | Var_univ _ | Var_exist _ -> failwith "mult_nat"
    | Term (f, l, _) ->
      if f == id_symbol_zero then zero_t
      else if f == id_symbol_s then 
	add_nat t2 (mult_nat (List.hd l) t2 (i+1)) (i+1)
      else failwith "mult_nat"
	  
(* t1 + t2, where t1 and t2 are in normal forms *)
let rec np_add t1 t2 i =
  (* let t1 = np_norm t1' (i+1) in *)
  (* let t2 = np_norm t2' (i+1) in *)
  (* let () = buffered_output ((fn_spaces i) ^ "np_add: t1 = " ^ t1#string ^ " t2 = "  ^ t2#string) in *)
  match t1#content with
    | Var_univ _ | Var_exist _ -> 
      (match t2#content with
	| Var_univ _ | Var_exist _ -> 
	  if compare t1#string t2#string == 0 then
	    new term (Term (id_symbol_times, [two_t; t1], id_sort_nat)) (* u1 + u1 -> 2* u1 *)
	  else 
	    if heavier t1 t2 then new term (Term(id_symbol_plus, [t1; t2], id_sort_nat)) (* u1 + u2 -> u1 + u2 *)
	    else new term (Term(id_symbol_plus, [t2; t1], id_sort_nat))
	| Term (f, l, _) -> 
	  if f == id_symbol_zero then t1
	  else if f == id_symbol_s then
	    new term (Term (id_symbol_plus, [t1; t2], id_sort_nat)) (* u1 + c -> u1 + c *)
	  else if f == id_symbol_plus then
	    let fst_arg = List.hd l in
	    let snd_arg = List.hd (List.tl l) in
	    if compare t1#string fst_arg#string == 0 then (* x + (n*x +...) -> (n+1)*x + ... *)
	      (match fst_arg#content with
		| Var_univ _ | Var_exist _ ->
		  new term (Term (id_symbol_plus, [(new term (Term (id_symbol_times,[two_t;fst_arg], id_sort_nat)));snd_arg],id_sort_nat))
		| Term (f, l, _) -> 
		  if f == id_symbol_times then (* fst_arg is of the form c*v *)
		    let coeff = List.hd l in
		    let var = List.hd (List.tl l) in
		    if coeff#variables == [] then
		      let s_fst_arg = new term (Term (id_symbol_s, [coeff], id_sort_nat)) in
		      new term (Term (id_symbol_plus, [(new term (Term (id_symbol_times,[s_fst_arg;var],id_sort_nat))); snd_arg], id_sort_nat))
		    else failwith "np_add: impossible coefficient"
		  else failwith "np_add: impossible case"
	      )
	    else 
	      if heavier t1 fst_arg then
		new term (Term (id_symbol_plus, [t1;t2], id_sort_nat))
	      else 
		let snd_arg_norm = np_add t1 snd_arg (i+1) in
		new term (Term (id_symbol_plus, [fst_arg;snd_arg_norm], id_sort_nat))
	  else if f == id_symbol_times then
	    let fst_arg = List.hd l in
	    let snd_arg = List.hd (List.tl l) in
	    if fst_arg#variables == [] && compare t1#string snd_arg#string == 0 then (* u + c*u -> s(c) * u *)
	      new term (Term (id_symbol_times, [(new term (Term (id_symbol_s,[fst_arg],id_sort_nat)));snd_arg], id_sort_nat))
	    else if heavier t1 t2 then 
	      new term (Term (id_symbol_plus, [t1;t2], id_sort_nat))
	    else
	      new term (Term (id_symbol_plus, [t2;t1], id_sort_nat))
	    else failwith "np_add"
      )
    | Term (f1, l1, _) -> 
      if f1 == id_symbol_zero then t2
      else if f1 == id_symbol_s then
	(match t2#content with
	  | Var_univ _ | Var_exist _ -> new term (Term (id_symbol_plus, [t2; t1], id_sort_nat))
	  | Term (f2, l2, _) -> 
	    if f2 == id_symbol_zero then t1
	    else if f2 == id_symbol_s then 
	      let add_tail = np_add t1 (List.hd l2) (i+1) in
	      new term (Term (id_symbol_s, [add_tail], id_sort_nat))
	    else if f2 == id_symbol_plus then
	      let fst_arg2 = List.hd l2 in
	      let snd_arg2 = List.hd (List.tl l2) in
	      let add_tail = np_add t1 snd_arg2 (i+1) in
	      new term (Term (id_symbol_plus, [fst_arg2; add_tail], id_sort_nat))
	    else if f2 == id_symbol_times then
	      new term (Term (id_symbol_plus, [t2; t1], id_sort_nat))
	    else failwith "np_add"
	)
      else if f1 == id_symbol_plus then
	let fst_arg1 = List.hd l1 in
	let snd_arg1 = List.hd (List.tl l1) in
	(match t2#content with
	  | Var_univ _ | Var_exist _ -> np_add t2 t1 (i+1)
	  | Term (f2, _, _) -> 
	    if f2 == id_symbol_plus || f2 == id_symbol_times then (* (u1 + u2) + (u3 + u4) -> u2 + (u1 + u3 + u4) *)
	      let plus_1arg1_t2 = np_add fst_arg1 t2 (i+1) in
	      np_add snd_arg1 plus_1arg1_t2 (i+1)
	    else 
	      np_add t2 t1 (i+1)
	)
      else if f1 == id_symbol_times then
	let fst_arg1 = List.hd l1 in
	let snd_arg1 = List.hd (List.tl l1) in
	  (* let fstarg1_times_sndarg1 = np_times fst_arg1 snd_arg1 (i+1) in *)
	  (* let  () = buffered_output ((fn_spaces i) ^ "fstarg1_times_sndarg1 is " ^ fstarg1_times_sndarg1#string) in *)
	  (* if compare t1#string fstarg1_times_sndarg1#string == 0 then *)
	(match t2#content with
	  | Var_univ _ | Var_exist _ -> np_add t2 t1 (i+1)
	  | Term (f2, l2, _) -> 
	    if f2 == id_symbol_times then 
	      if heavier t1 t2 then 
		new term (Term (id_symbol_plus, [t1;t2], id_sort_nat))
	      else if heavier t2 t1 then
		new term (Term (id_symbol_plus, [t2;t1], id_sort_nat))
	      else 
		let fst_arg2 = List.hd l2 in
		let snd_arg2 = List.hd (List.tl l2) in
		if fst_arg1#variables == [] then
		  if fst_arg2#variables == [] then
		    if compare snd_arg1#string snd_arg2#string == 0 then
		      let fstarg1_plus_fst_arg2 = add_nat fst_arg1 fst_arg2 (i+1) in
		      new term (Term (id_symbol_times, [fstarg1_plus_fst_arg2;snd_arg2], id_sort_nat))
		    else failwith "np_add: impossible case"
		  else if compare snd_arg1#string t2#string == 0 then
		    let fstarg1_plus_one = new term (Term (id_symbol_s, [fst_arg1], id_sort_nat)) in
		    new term (Term (id_symbol_times, [fstarg1_plus_one; t2], id_sort_nat))
		  else failwith "np_add: impossible case"
		  else if fst_arg2#variables == [] then
		    if compare t1#string snd_arg2#string == 0 then
		      let fstarg2_plus_one = new term (Term (id_symbol_s, [fst_arg2], id_sort_nat)) in
		      new term (Term (id_symbol_times, [fstarg2_plus_one; t1], id_sort_nat))
		    else failwith "np_add: impossible case"
		  else if compare t1#string t2#string == 0 then
		    new term (Term (id_symbol_times, [two_t;t1], id_sort_nat))
		  else failwith "np_add: impossible case"		       
		    
		  else if f2 == id_symbol_plus then
		    let fst_arg2 = List.hd l2 in
		    let snd_arg2 = List.hd (List.tl l2) in
		    (match fst_arg2#content with
		      | Var_univ _ | Var_exist _ -> 
			new term (Term (id_symbol_plus, [t1; t2], id_sort_nat))
		      | Term(f3, l3, _) ->
			if f3 == id_symbol_zero then np_add t1 snd_arg2 (i+1)
			else if f3 == id_symbol_s then failwith "np_add: t2 is not in normal form"
			else if f3 == id_symbol_plus then failwith "np_add: t2 is not in normal form"
			else if f3 == id_symbol_times then
			  let fst_arg3 = List.hd l3 in
			  let snd_arg3 = List.hd (List.tl l3) in
			  if fst_arg1#variables == [] && fst_arg3#variables == [] then
			    if compare snd_arg1#string snd_arg3#string == 0 then
			      let fstarg1_plus_fstarg3 = add_nat fst_arg1 fst_arg3 (i+1) in
			      let newt = new term (Term (id_symbol_times, [fstarg1_plus_fstarg3;snd_arg3], id_sort_nat)) in
			      new term (Term (id_symbol_plus, [newt; snd_arg2], id_sort_nat)) 
			    else if heavier t1 fst_arg2 then
			      new term (Term (id_symbol_plus, [t1; t2], id_sort_nat)) 
			    else
			      let newt = np_add t1 snd_arg2 (i+1) in
			      new term (Term (id_symbol_plus, [fst_arg2; newt], id_sort_nat))
			    else if heavier t1 fst_arg2 then
			      new term (Term (id_symbol_plus, [t1; t2], id_sort_nat)) 
			    else 
			      let newt = np_add t1 snd_arg2 (i+1) in
			      new term (Term (id_symbol_plus, [fst_arg2; newt], id_sort_nat))
			    else failwith "np_add"
		    )	
		  else np_add t2 t1 (i+1)
	)  
      (* else np_add fstarg1_times_sndarg1 t2 (i+1) *)
      else failwith "np_add"
	

(* t1 * t2, where t1 and t2 are in normal forms *)

and np_times t1 t2 i = 
  (* let t1 = np_norm t1' (i+1) in *)
  (* let t2 = np_norm t2' (i+1) in *)
  (* let () = buffered_output ((fn_spaces i) ^ "np_times: t1 = " ^ t1#string ^ " t2 = "  ^ t2#string) in *)
  match t1#content with 
    | Var_univ _ | Var_exist _ ->
      (match t2#content with
	| Var_univ _ | Var_exist _ ->
	  if heavier t1 t2 then 
	    new term (Term (id_symbol_times, [t1;t2], id_sort_nat))
	  else 
	    new term (Term (id_symbol_times, [t2;t1], id_sort_nat))
	| Term (f, l, _) -> 
	  if f == id_symbol_zero then zero_t
	  else if f == id_symbol_s then np_add t1 (np_times t1 (List.hd l) (i+1)) (i+1)
	  else if f == id_symbol_plus then 
	    let fst_arg = List.hd l in
	    let snd_arg = List.hd (List.tl l) in
	    np_add (np_times t1 fst_arg (i+1)) (np_times t1 snd_arg (i+1)) (i+1)
	  else if f == id_symbol_times then 
	    let fst_arg = List.hd l in
	    let snd_arg = List.hd (List.tl l) in
	    if fst_arg#variables == [] then 
	      let t1_mult_sndarg = np_times t1 snd_arg (i+1) in
	      new term (Term (id_symbol_times, [fst_arg;t1_mult_sndarg], id_sort_nat))
	    else
	      if heavier t1 fst_arg 
	      then new term (Term (id_symbol_times, [t1;t2], id_sort_nat))
	      else 
		let t1_mult_sndarg = np_times t1 snd_arg (i+1) in
		new term (Term (id_symbol_times, [fst_arg;t1_mult_sndarg], id_sort_nat))
	  else failwith "np_times"
      )
    | Term (f1, l1, _) ->
      if f1 == id_symbol_zero then zero_t
      else if f1 == id_symbol_s then np_add (np_times (List.hd l1) t2 (i+1)) t2 (i+1)
      else if f1 == id_symbol_plus then 
	let fst_arg1 = List.hd l1 in
	let snd_arg1 = List.hd (List.tl l1) in
	np_add (np_times t2 fst_arg1 (i+1)) (np_times t2 snd_arg1 (i+1)) (i+1)
      else if f1 == id_symbol_times then 
	let fst_arg1 = List.hd l1 in
	let snd_arg1 = List.hd (List.tl l1) in
	(match t2#content with 
	  | Var_univ _ | Var_exist _ -> np_times t2 t1 (i+1)
	  | Term (f2, l2, _) ->
	    if f2 == id_symbol_times then
	      let fst_arg2 = List.hd l2 in
	      let snd_arg2 = List.hd (List.tl l2) in
	      if fst_arg1#variables == [] then
		if fst_arg2#variables == [] then
		  let fstarg1_times_fstarg2 = mult_nat fst_arg1 fst_arg2 (i+1) in
		  let sndarg1_times_sndarg2 = np_times snd_arg1 snd_arg2 (i+1) in
		  new term (Term (id_symbol_times, [fstarg1_times_fstarg2;sndarg1_times_sndarg2], id_sort_nat))
		else
		  let sndarg1_times_t2 = np_times snd_arg1 t2 (i+1) in
		  new term (Term (id_symbol_times, [fst_arg1;sndarg1_times_t2], id_sort_nat))
	      else
		if fst_arg2#variables == [] then
		  let t1_times_sndarg2 = np_times t1 snd_arg2 (i+1) in
		  new term (Term (id_symbol_times, [fst_arg2; t1_times_sndarg2], id_sort_nat))
		else
		  np_times snd_arg1 (np_times fst_arg1 t2 (i+1)) (i+1)
	    else np_times t2 t1 (i+1)
	)
      else failwith "np_times"
	
let rec np_norm t i = 
  (* let () = buffered_output ((fn_spaces i) ^ "np_norm: t = " ^ t#string) in *)
  match t#content with
    | Var_univ _ -> t
    | Var_exist _ -> t
    | Term (f, l, _) -> 
      if f == id_symbol_zero then t
      else if f == id_symbol_s then
	let s_arg = List.hd l in 
	let s_arg_norm = np_norm s_arg (i+1) in
	propagate_one s_arg_norm
      else
	let fst_arg = List.hd l in
	let snd_arg = List.hd (List.tl l) in
	let fst_norm = np_norm fst_arg (i+1) in
	let snd_norm = np_norm snd_arg (i+1) in
	if f == id_symbol_plus then np_add fst_norm snd_norm (i+1)
	else if f == id_symbol_times then np_times fst_norm snd_norm (i+1)
	else 
	  let () =  if !maximal_output then  buffered_output ("np_norm symbol " ^ (dico_const_string#find f) ^ " not managed by Rmps0")  in
	  failwith "np_norm"
	

