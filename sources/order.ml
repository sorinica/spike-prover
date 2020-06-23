
(*
   * Project: Spike ver 0.1
   * File: order.ml
   * Content: associative path ordering compatible with ac theory.
   *          Delor / Puel, RTA 93
*)

open Values
open Diverse
open Io
open Symbols
open Terms

(* page 27 Baader & Nipkow book  *)
let rec lex ord = function
  |([], []) -> EQ
  |(x::xs, y::ys) -> 
      (match ord (x,y) with 
      | GR ->  GR
      | EQ -> lex ord (xs,ys) 
      | NGE -> NGE
      )
  | (_,_) -> NGE
     
 

  (* remove the element y from a list xs  *)
let rec rem1 ord = function
  | ([],_) -> []
  | (x::xs,y) -> 
      (match ord (x, y) with
	| EQ -> xs
	| GR
	| NGE -> x :: (rem1 ord (xs, y))
      )

  (* multiset difference  *)
let rec mdiff ord = function
  | (xs, []) -> xs
  | (xs, y::ys) -> mdiff ord ((rem1 ord (xs,y)), ys)

let rec mul ord (ms, ns) = 
  let nms = mdiff ord (ns, ms) 
  and mns = mdiff ord (ms, ns) in
  if nms == [] && mns == [] then EQ
  else if List.for_all (fun n -> List.exists (fun m -> (ord (m, n)) == GR) mns) nms then GR
  else NGE
  
let multiset_greater ord ms ns = mul ord (ms, ns) == GR

let multiset_equivalent ord ms ns = mul ord (ms, ns) == EQ

let multiset_geq ord ms ns = mul ord (ms, ns) <> NGE

(* page 123 Baader & Nipkow book, extended to treat total orders over variables *)

let rec rpo is_total ((s:term),(t:term)) = 
  try 
    dico_rpo_greater#find (s#string, t#string)
  with Not_found ->
    let res = 
      match (s#content, t#content) with
	| Var_exist(x,_), Var_exist(y,_) 
 	| Var_univ(x,_), Var_exist(y,_) 	
	| Var_exist (x,_), Var_univ (y,_)
	| Var_univ (x,_), Var_univ (y,_) -> if var_equal x  y then EQ else if x > y && is_total then GR else NGE
	| (Term _, Var_univ (x,_))
	| (Term _, Var_exist (x,_)) -> 
	    if s#occur x then GR else NGE
	| (Var_univ _, Term _) 
	| (Var_exist _, Term _) -> NGE
	| (Term (f, ss, _), Term (g, ts, _)) -> 
	    if List.for_all (fun si -> (rpo is_total (si,t) == NGE)) ss then
	      if greater is_total f g then 
		if List.for_all (fun ti -> (rpo is_total (s,ti) == GR)) ts then
		  GR else NGE
	      else if equivalent f g then
		((* if List.for_all (fun ti -> (rpo is_total (s,ti) == GR)) ts then *)
		   let st = try get_status f with Failure "raising Not_found in get_status_id" -> Multiset in
		     match st with
		       | Left -> lex (rpo is_total) (ss,ts)
		       | Right -> 
			   let inv_ss = List.rev ss
			   and inv_ts = List.rev ts in
			     lex (rpo is_total) (inv_ss,inv_ts)
		       | Multiset -> mul (rpo is_total) (ss,ts)
		 (* else NGE *)
		)
	      else NGE
	    else GR
    in
    let () = dico_rpo_greater#add (s#string, t#string) res
    in res
 


let rpo_greater is_total t t' = rpo is_total (t, t') == GR

let rpo_equivalent t t' = rpo true (t, t') == EQ

let rpo_geq is_total t t' =  rpo is_total (t, t') <> NGE

let rpo_incomparable is_total (t:term) (t': term) = rpo is_total (t, t') == NGE && rpo is_total (t', t) == NGE

(* Are all these elements totally ordered.
   We produce an ordered list in decreasing order *)

let rec consecutive_elements = function
    [] -> []
  | l ->
      let l1, l2 = list_select_maximal_elements (greater false) l in
      l1 @ consecutive_elements l2

let unary_symbols () =
  let l = ref [] in
  let fn x (l_ar, r_ar) =
    if l_ar + r_ar = 1
    then l := generic_insert_sorted x !l
    else () in
  let () = dico_arities#iter fn in
  !l

let constant_symbols () =
  let l = ref [] in
  let fn x (l_ar, r_ar) =
    if l_ar = 0 && r_ar = 0
    then l := generic_insert_sorted x !l
    else () in
  let () = dico_arities#iter fn in
  !l

(* Lexicographic order *)
(* let lex_greater is_total equiv_f greater_f l l' = *)
(*   let rec fn l l' = *)
(*     match l, l' with *)
(*       [], _ -> false *)
(*     | _::_, [] -> true *)
(*     | h::t, h'::t' -> *)
(* 	greater_f is_total h h' || (equiv_f h h' && fn t t') in *)
(*   fn l l' *)

(* (* Remove common elements from two multisets *) *)
(* let remove_common_elements equiv_f l l' = *)
(*   let rec fn l l' = *)
(*     match l, l' with *)
(*       [], _ as c -> c *)
(*     | _, [] as c -> c *)
(*     | h::t, v -> *)
(*         try *)
(*           let v' = remove_el equiv_f h v in *)
(*           fn t v' *)
(*         with Failure "remove_el" -> *)
(*           let l1, l2 = fn t v in *)
(*           h::l1, l2 in *)
(*   fn l l' *)

(* (* Multiset extension to an order *) *)
(* let rec multiset_greater is_total equiv_f greater_f l l'  = *)
(*   let l1, l2 = remove_common_elements equiv_f l l' in *)
(*   match l1, l2 with *)
(*     [], [] -> false *)
(*   | _ -> *)
(*       let f y = List.exists (fun x -> greater_f is_total x y ) l1 in *)
(*       List.for_all f l2 *)

(* (* Multiset extension to an order *) *)
(* let rec multiset_geq is_total equiv_f greater_f l l' = *)
(*   let l1, l2 = remove_common_elements (fun x -> x#syntactic_equal) l l' in *)
(*   match l1, l2 with *)
(*     [], [] -> true *)
(*   | _ -> *)
(*       let f y = List.exists (fun x -> greater_f is_total x y) l1 in *)
(*       List.for_all f l2 *)

(* (* Extension of an order w.r.t a status *) *)
(* let extended_greater is_total equiv_f greater_f status_v l l' = *)
(*   match status_v with *)
(*     Left -> lex_greater is_total  equiv_f greater_f l l' *)
(*   | Right -> let l1 = List.rev l  *)
(* 	     and l1' = List.rev l' in  *)
(*     lex_greater is_total equiv_f greater_f l1 l1' *)
(*   | Multiset -> multiset_greater is_total equiv_f greater_f l l' *)

(* (* Recursive path ordering with status *) *)
(* let rec rpo_equivalent t t' = *)
(*   let res =  *)
(*     match t#content, t'#content with *)
(* 	Term (f, l, s), Term (f', l', s') -> *)
(* 	  let st = get_status f in *)
(* 	  equivalent f f' && List.length l = List.length l' && *)
(* 	      ((st = Multiset && check_on_permutations rpo_equivalent l l') *)
(* 	      || *)
(* 	      (st <> Multiset && List.for_all2 rpo_equivalent l l')) *)
(*       | Var_exist (x, _), Var_exist (x', _)  *)
(*       | Var_exist (x, _), Var_univ (x', _)  *)
(*       | Var_univ (x, _), Var_exist (x', _)  *)
(*       | Var_univ (x, _), Var_univ (x', _) -> var_equal x x' *)
(*       | Var_exist _, Term _ | Term _, Var_exist _ | Var_univ _, Term _| Term _, Var_univ _ -> false *)
(*   in *)
(*   res *)


(* let rec rpo_greater is_total (t: term) (t': term) = *)
(*   try  *)
(*     dico_rpo_greater#find (t#string, t'#string)  *)
(*   with Not_found ->  *)
(*     let res =  *)
(*       match t#content, t'#content with *)
(* 	  Term (f, l, s), Term (f', l', s') -> *)
(* 	    begin *)
(*       	      let st = get_status f in *)
(*       	      (greater is_total f f' && multiset_greater is_total rpo_equivalent rpo_greater [t] l') *)
(* 	      || *)
(*       	      (equivalent f f' && st = Multiset && multiset_greater *)
(* 		is_total rpo_equivalent rpo_greater l l') *)
(* 	      || *)
(*       	      (equivalent f f' && st <> Multiset && extended_greater is_total *)
(* 		rpo_equivalent rpo_greater st l l' && not (List.exists *)
(* 		  (t#syntactic_equal) l') && List.for_all (rpo_greater *)
(* 		  is_total t) l') *)
(* 	      || *)
(* 	      (multiset_geq is_total rpo_equivalent rpo_greater l [t']) *)
(* 	    end *)
(* 	| Term (_, _, _), Var_exist (x, _)   *)
(* 	| Term (_, _, _), Var_univ (x, _) -> (t#occur x) or  *)
(* 	    (is_total && (List.for_all (fun (v,_, _) -> v > x) t#variables)) *)
(* 	| Var_exist(x,_), Var_univ(y,_) *)
(* 	| Var_exist(x,_), Var_exist(y,_) *)
(* 	| Var_univ(x,_), Var_exist(y,_) *)
(* 	| Var_univ(x,_), Var_univ(y,_) -> is_total &&  x > y  *)
(* 	| Var_exist _, Term _ | Var_univ _, Term _ -> false *)
(*     in  *)
(*     let () = dico_rpo_greater#add (t#string, t'#string) res in *)
(*     res *)

(* let rpo_geq is_total t t' =  rpo_equivalent t t' || rpo_greater is_total t t' *)
	
(* let rpo_incomparable is_total (t:term) (t': term) =  *)
(*   not ((rpo_greater is_total t t') or (rpo_greater is_total t' t)) *)

  (* a total order on ground terms  *)
  (* as in ACL2 (see term-order in
     ACL2 doc)  *)

let ground_greater t1 t2 = 
  let nr_var1 = List.length t1#variable_positions 
  and nr_var2 = List.length t2#variable_positions 
  and nr_symb1 = List.length t1#all_positions
  and nr_symb2 = List.length t2#all_positions
  in 
  let nr_func1 = nr_symb1 - nr_var1 
  and nr_func2 = nr_symb2 - nr_var2
  in
  (nr_var1 > nr_var2) or (nr_var1 = nr_var2 && nr_func1 > nr_func2) or
  (nr_var1 = nr_var2 && nr_func1 = nr_func2 && (t1#string > t2#string))
  
let rpos_greater = ref rpo_greater
and rpos_geq = ref rpo_geq 
and rpos = ref rpo


let heavier t t' = ground_greater t t'

(*   let n = List.length t#variables *)
(*   and n' = List.length t'#variables *)
(*   in *)
(*   let d = t#treesize - n *)
(*   and d' = t'#treesize - n'  *)
(*   in n > n' or  (n = n' && d > d')  or  *)
(* (try  t#var_content > t'#var_content with Failure "var_content" -> false) ||  *)
(* (n = n' && d = d' && rpo_greater is_total t t') *)
    
(* Order on clauses using the multiset extension*)
let clause_greater is_max is_total c c' =
  let l = if is_max then c#all_maximal_terms is_total else c#all_terms
  and l' = if is_max then c'#all_maximal_terms is_total else c'#all_terms 
  and order_on_terms = !rpos  in
(*   let strl = List.fold_left (fun s t -> s ^ "   " ^ t#string) "" l in *)
(*   let strl' = List.fold_left (fun s t -> s ^ "   " ^ t#string) "" l' in *)
(*   let _ = buffered_output ("\nThe terms involved in clausal comparison are: \n" ^ strl ^ "\nand: " ^ strl') in *)
  multiset_greater (order_on_terms is_total)  l l'


let clause_equiv is_max is_total c c' =
  let l = if is_max then c#all_maximal_terms is_total else c#all_terms
  and l' = if is_max then c'#all_maximal_terms is_total else c'#all_terms 
  and order_on_terms = !rpos  in
(*   let strl = List.fold_left (fun s t -> s ^ "   " ^ t#string) "" l in *)
(*   let strl' = List.fold_left (fun s t -> s ^ "   " ^ t#string) "" l' in *)
(*   let _ = buffered_output ("\nThe terms involved in clausal comparison are: \n" ^ strl ^ "\nand: " ^ strl') in *)
  multiset_equivalent (order_on_terms is_total)  l l'

let clause_geq is_max is_total c c' =
  let l = if is_max then c#all_maximal_terms is_total else c#all_terms
  and l' = if is_max then c'#all_maximal_terms is_total else c'#all_terms 
  and order_on_terms = !rpos  in
  multiset_geq (order_on_terms is_total)  l l'


(* Normalization of a term with AC symbols.
   It doesn't preserve typing *)

(* f (g (x, y), z) -> g (f (x, z), f (y, z)) *)
let ac_distribute_ac_ac f g t =
  let rec fn t =
    match t#content with
      Var_univ _ | Var_exist _ -> t
    | Term (f', l, s) ->
        if const_equal f f'
        then
          try
            let l' = megamix (fn2 l) in
            let l'' = List.map (List.map (fun x -> try fn x with (Failure "fn2") -> x)) l' in
            new term (Term (g, List.map (fun x -> new term (Term (f, x, s))) l'', s))
          with (Failure "fn2") ->
            new term (Term (f, List.map fn l, s))
        else new term (Term (f, List.map fn l, s))

  and fn2 = function
      [] -> failwith "fn2"
    | h::t ->
        match h#content with
          Var_exist _ | Var_univ _ -> [h]::fn2 t
        | Term (g', l, _) ->
            if const_equal g g'
            then
              let t' = try fn2 t with (Failure "fn2") -> List.map (fun x -> [x]) t in
              l::t'
            else [h]::fn2 t in
  fn t

      (* u1 (u2 (x)) -> u2 (u1 (x)) *)
let ac_distribute_un_un h t f =
  let rec fn t =
    match t#content with
      Var_exist _ | Var_univ _ -> t
    | Term (g, [a], s) ->
        if const_equal g h
        then
          match a#content with
            Var_exist _ | Var_univ _ -> t
          | Term (g', [a'], s') ->
              if const_equal g' f
              then new term (Term (f, [ new term (Term (h, [a'], s')) ], s))
              else t
          | Term (_, [], _) | Term (_, _::_::_, _) -> t
        else t
    | Term (_, [], _) | Term (_, _::_::_, _) -> t in
  fn t

(* u (u (x)) -> u (x) *)
let ac_distribute_un t f =
  let rec fn t =
    match t#content with
      Var_exist _ | Var_univ _ -> t
    | Term (g, [a], s) ->
        if const_equal g f
        then
          match a#content with
            Var_exist _ | Var_univ _ -> t
          | Term (g', [a'], _) ->
              if const_equal g' f
              then new term (Term (f, [a'], s))
              else t
          | Term (_, [], _) | Term (_, _::_::_, _) -> t
        else t
    | Term (_, [], _) | Term (_, _::_::_, _) -> t in
  fn t

(* g (u (x), y) -> u (g (x, y)) *)
let ac_distribute_ac_un h f t =
  let rec fn t =
    match t#content with
      Var_exist _ | Var_univ _ -> t
    | Term (g, l, s) ->
        if const_equal g h
        then
          let i, _ = fn2 l in
          match i with
            0 -> t
          | _ -> make_unary_term h f l s i
        else t
  and fn2 = function
      [] -> 0, []
    | h::t ->
        let i, t' = fn2 t in
        match h#content with
          Var_exist _ | Var_univ _ -> i, h::t'
        | Term (f', l', _) ->
            if const_equal f' f
            then i + 1, l' @ t'
            else i, h::t' in
  fn t

(* First case: all AC symbols are totally ordered.
   Exemple: f < g < h, h minimal otherwise.
   h (f (x, y), z) -> f (h (x, z), h (y, z))
   h (g (x, y), z) -> g (h (x, z), h (y, z))
   g (f (x, y), z) -> f (g (x, z), g (y, z))
   Order of application is relevant.
*)
let ac_normalize_1 t =
  let rec fn t = function
      [] -> t
    | [_] -> t
    | hd::tl ->
        let t' = List.fold_right (ac_distribute_ac_ac hd) tl t in
        fn t' tl in
  fn t !ac_symbols_ordered

(* Second case: one AC symbol is greater than all the others *)
let ac_normalize_2 t =
  match !ac_symbols_ordered with
    [] -> t
  | [_] -> t
  | hd::tl -> List.fold_right (ac_distribute_ac_ac hd) tl t

(* Determine category which ac_symbols belong to:
   Sets:
   ac_symbols_category (bool ref)
   ac_symbols_ordered (const list).
*)
let ac_normalize_3 t = t (* TODO *)

(* Tests must be performed in the right order *)
let determine_ac_category () =
  let l_ac = try List.sort (fun x y -> if x < y then -1 else if x == y then 0 else 1) (dico_properties#find_keys Prop_ac) with Not_found -> []
  and l_const = constant_symbols ()
  and l_un = unary_symbols () in
  let fn l = 
    try dico_const_string#find l with Not_found -> failwith "raising Not_found in determine_ac_category"
  in
  let () = buffered_output ("AC symbols: " ^ (sprint_list ", " fn l_ac)) in
  let test1 l =
    match l with
      [] -> false
    | [_] -> false
    | _ ->
        try
          let l' = consecutive_elements l in
          match l' with
            [] -> false
          | h::t ->
              if minimal (generic_merge_sorted_lists l_const t) h
              then
                let () = ac_symbols_ordered := l' in
                true
              else
                let () = ac_symbols_ordered := [] in
                false
        with (Failure "consecutive_elements") ->
          let () = ac_symbols_ordered := [] in
          false in
  let rec test2 = function
      [] -> false
    | [_] -> false
    | h::t ->
        let l = generic_remove_sorted h l_ac in
        if List.for_all ((greater false) h) l && minimal (generic_merge_sorted_lists l_const l) h
        then
          let () = ac_symbols_ordered := h::l in
          true
        else test2 t in
  let test3 l =
    match l with
      [h1 ; h2] ->
        let fn h1 h2 =
          if greater false h1 h2 &&
            minimal l_const h2 &&
            minimal (generic_insert_sorted h2 (generic_merge_sorted_lists l_const l_un)) h1
          then
            let l_un_2 = generic_intersection_sorted_lists l_un (try dico_order#find h1 with Not_found -> failwith "raising Not_found in determine_ac_category" ) in
            try
              let l' = consecutive_elements l_un_2 in
              let () = ac_symbol_1 := h1
              and () = ac_symbol_2 := h2
              and () = unary_symbols_ordered := l' in
              true
            with (Failure "consecutive_elements") -> false
          else false in
        fn h1 h2 or fn h2 h1
    | _ -> false in
  let test4 l =
    match l with
      [h1 ; h2] ->
        let fn h1 h2 =
          if greater false h1 h2
          then
            let l' = generic_remove_sorted h2 (generic_remove_sorted_lists (try dico_order#find h1  with Not_found -> failwith "raising Not_found in determine_ac_category") l_const) in
            match l' with
              [h] ->
                if dico_arities#total_ar h = 1 && greater false h2 h
                then
                  let () = ac_symbol_1 := h1
                  and () = ac_symbol_2 := h2
                  and () = unary_symbol_1 := h in
                  true
                else false
            | _ -> false
          else false in
        fn h1 h2 or fn h2 h1
    | _ -> false in
  let rec test5 l =
    try
      let l' = consecutive_elements l in
      match l' with
        [] -> false
      | [_] -> false
      | h1::(h2::_ as tl) ->
          let h_n = 
	    try last_el l' 
	    with (Failure "last_el") -> failwith "determine_ac_category"
	  in
          let l_min = generic_remove_sorted_lists (try dico_order#find h_n  with Not_found -> failwith "raising Not_found in determine_ac_category") l_const in
          match l_min with
            [h] ->
              if dico_arities#total_ar h = 1
              then
                let l_mixed = generic_remove_sorted_lists (generic_remove_sorted_lists (try dico_order#find h1  with Not_found -> failwith "raising Not_found in determine_ac_category") l_const) l in
                let l_mixed' = generic_remove_sorted h l_mixed in
                if List.for_all (fun x -> dico_arities#total_ar x = 1
		  && greater false x h2) l_mixed'
                then
                  try
                    let l_unaries = consecutive_elements l_mixed' in
                    let () = ac_symbol_1 := h1
                    and () = unary_symbol_1 := h
                    and () = ac_symbols_ordered := tl
                    and () = unary_symbols_ordered := l_unaries in
                    true
                  with (Failure "consecutive_elements") -> false
                else
                  false
              else
                false
          | _ -> false
    with (Failure "consecutive_elements") -> false in
  let fn l = 
    try dico_const_string#find l with Not_found -> failwith "raising Not_found in determine_ac_category"
  in
  if test1 l_ac
  then
    let () = buffered_output ("Case 1: n totally ordered AC symbols, h_0 minimal in AC \\ { h_i }\n" ^
                              (sprint_list " > " fn !ac_symbols_ordered  )) in
    let () = rpos_greater := fun b t t' -> rpo_greater b (ac_normalize_1 t) (ac_normalize_1 t') in
    ac_symbols_category := 1
  else if test2 l_ac
  then
    let () = buffered_output ("Case 2: n AC symbols, ¥i, h_i < h, h minimal in AC \\ { h_i }\n" ^
                              (match !ac_symbols_ordered with
                                [] -> failwith "determine_ac_category"
                              | h::t ->
                                  (try dico_const_string#find h with Not_found -> failwith "raising Not_found in determine_ac_category") ^ " > " ^
                                  (sprint_list ", " fn t))) in
    let () = rpos_greater := fun b t t' -> rpo_greater b (ac_normalize_2 t) (ac_normalize_2 t') in
    ac_symbols_category := 2
  else if test3 l_ac
  then
    let () = 
      try 
	buffered_output ("Case 3: f > u1 > ... > un > g\n" ^
        (dico_const_string#find !ac_symbol_1) ^ " (ac) > " ^
        (sprint_list " > " dico_const_string#find !unary_symbols_ordered) ^
        " > " ^ (dico_const_string#find !ac_symbol_2) ^ " (ac)") 
	with Not_found -> failwith "raising Not_found in determine_ac_category" 
	in
    let () = rpos_greater := fun b t t' -> rpo_greater b (ac_normalize_3 t) (ac_normalize_3 t') in
    ac_symbols_category := 3
  else if test4 l_ac
  then
    let () = 
      try 
	buffered_output ("Case 4: f > g > u\n" ^
        (dico_const_string#find !ac_symbol_1) ^ " (ac) > " ^
        (dico_const_string#find !ac_symbol_2) ^ " (ac) > " ^
        (dico_const_string#find !unary_symbol_1))
      with Not_found -> failwith "raising Not_found in determine_ac_category" 
    in
    let () = rpos_greater := !rpos_greater (* TODO *) in
    ac_symbols_category := 4
  else if test5 l_ac
  then
    let () = 
      try
	buffered_output ("Case 5: f1 > u1 > u2 > ... > f2 > f3 > ... > fn > um\n" ^
                              (dico_const_string#find !ac_symbol_1) ^ " (ac) > " ^
                              (sprint_list " > " dico_const_string#find !unary_symbols_ordered) ^
                              " > " ^ (sprint_list " > " dico_const_string#find !ac_symbols_ordered) ^
                              " > " ^ (dico_const_string#find !unary_symbol_1)) 
      with Not_found -> failwith "raising Not_found in determine_ac_category" 
    in
    let () = rpos_greater := !rpos_greater (* TODO *) in
    ac_symbols_category := 5
  else
    let () = buffered_output "Case 0: no AC symbols" in
    ac_symbols_category := 0

let orient  (t:ground_term) (t':ground_term) =
  if ground_greater  t t' then t, t'
  else if ground_greater  t' t then t', t
  else failwith "orient"
