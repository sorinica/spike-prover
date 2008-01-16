(*
* Project: Spike ver 0.1
  * File: extract.ml
* Content: extracts a SPIKE subspecification given a list of functional symbols
    *)

open Dicos
open Clauses
open Diverse
open Symbols
open Io

let filedefault : out_channel ref = ref stdout;;

let appended_file s =
  try let _, res = openin s in res
    with Sys_error err -> 
      raise (MyExit ("cannot open " ^ s))
 
(* initialization function *)
let filedefault_init () = filedefault := stdout;;

(* set function *)
let filedefault_set (st:string) = 
  let fname = (st ^ ".spike") in
  if Sys.file_exists fname then
    (prerr_string ("\nthe file "^ fname ^
    " already exists and its contents will be deleted \n");
    flush stderr); filedefault := open_out (fname) ;;

let sprint_underscore n = 
  let rec fn i = 
    if i > 0 then let str = fn (i - 1) in str ^  "_" 
    else ""
  in
  fn n

let rec extract_specification ls = 
  (* getting all the defined symbols  *)
  if ls = [] then failwith "extract_specification";
  let rec fn0 ls' = 
    let fn s = 
      let fn1 (r:peano_context clause) = 
	let lhs = r#lefthand_side in
	let hd = lhs#head in
	if hd = s then 
	  let all_defsymbs = List.fold_right 
	    (fun ((b, n, p), lp) l -> 
	      let llp = List.fold_right 
		(fun p' l' -> 
		  let t = r#subterm_at_position (b, n, p @ p') in 
		  insert_sorted ( = ) ( < ) t#head l') 
		lp [] in 
	      merge_sorted_lists ( < ) llp l) 
	    (all_defined_positions r#content) [] 
	  in
	  all_defsymbs
	else [s]
      in
      List.fold_right (fun x l -> merge_sorted_lists ( < ) (fn1 x) l) rewrite_system#content []
    in
    let l =  List.fold_right (fun x l' -> merge_sorted_lists ( < ) (fn x) l') ls' [] in
    if l = ls' then 
      ls'
    else fn0 l
  in 

  let all_symbs = fn0 ls in
  (* getting the sorts  *)

  let sorts = List.flatten (List.map (fun s -> dico_const_profile#find s) all_symbs) in
  
  let fn6 s1 = 
    let rec fn s = 
      match s with 
	  Def_sort _ -> [s]
	| Abstr_sort0 _ -> []
	| Abstr_sort1 (id, s') -> fn s'
	| Abstr_sort2 (id, s', s'') -> (fn s') @ (fn s'')
    in
    fn s1
  in

  let rec fn4 ls lc =

    let ls' = List.flatten (List.map fn6 ls) in
    let all_sorts = list_remove_doubles ( fun x y -> let s1 = sprint_sort x in let s2 = sprint_sort y in s1 = s2) ls' in
    
    (* getting the constructors  *)
    
    let all_c = 
      let l = ref [] in 
      let () = dico_const_string#iter (fun i _ -> if is_constructor i then l := i :: !l ) in !l 
    in
    let fn5 c = 
      let p = List.hd (dico_const_profile#find c) in
      if List.exists (fun s -> list_member (fun x y -> try let _ = unify_sorts (Actual_sort x) y in true with Failure "unify_sorts" -> false) s all_sorts) [p] then [c] else []
    in

    let current_c = List.fold_right (fun x y -> merge_sorted_lists ( < ) x y) (List.map fn5 all_c) [] in

    let all_symbs = merge_sorted_lists ( < ) lc current_c in 
    if all_symbs = lc then (ls, lc) (* finished *)
    else 
      let new_s = List.flatten (List.map (fun s -> dico_const_profile#find s) (merge_sorted_lists ( < ) lc current_c)) in
      fn4 new_s all_symbs

(*     let fn2 s = try List.filter is_constructor (List.map (fun x dico_const_profile#find_keys [s]) with Not_found -> [] in *)
(*     let l_c = list_remove_doubles ( = ) (List.flatten (List.map fn2 all_sorts)) in *)
(*     let () = buffered_output "\nI am here4" in *)

  in 

  let c_s, c_symbs = fn4 sorts all_symbs in
  let c_constr = List.filter is_constructor c_symbs in
  let c_sorts = list_remove_doubles ( fun x y -> let s1 = sprint_sort x in let s2 = sprint_sort y in s1 = s2) c_s in
(*   let c_sorts = List.flatten (List.map fn6 c_sorts') in *)

  (* let's print the specification  *)
  
  
  let file_name = dico_const_string#find (List.hd ls) in
  let () = filedefault_set file_name in
  
  let () = output_string !filedefault ("\n\n specification: " ^ file_name) in

  let () = output_string !filedefault "\n\n sorts:\n" in
  
  let () = output_string !filedefault "\n\toption\n\tlist\n\tprod\tsum" in
  let () = List.iter (fun s ->  try let id_s = dico_sort_string#find s in output_string !filedefault ("\n\t" ^ id_s) with Not_found -> ()) c_sorts in

  let () = output_string !filedefault ";\n\n constructors:\n" in


  let () = output_string !filedefault ("\n\tTrue: -> bool;\n\tFalse: -> bool;\n\tNil:  -> (list 'A );\n\tCons__:  'A (list 'A) -> (list 'A );\n\tPair__:  'A 'B -> (prod 'A 'B );\n\tSome_:  'A -> (option 'A );\n\tNone:  -> (option 'A );\n\tInl_: 'a -> (sum 'a 'b);\n\tInr_: 'b -> (sum 'a 'b);") in


  let () = List.iter (fun c -> 
    let profile = dico_const_profile#find c in 
    let (lar, rar) = dico_arities#find c in
    let constr = dico_const_string#find c in
    if (String.lowercase constr) <> "true" && (String.lowercase constr) <> "false" then
      output_string !filedefault ("\n\t" ^ (sprint_underscore lar) ^ constr ^ (sprint_underscore rar) ^ ": " ^ (sprint_profile profile) ^ ";")) c_constr
  in

  let () = output_string !filedefault "\n\n defined functions:\n" in

  let () = List.iter (fun c -> 
    let profile = dico_const_profile#find c in 
    let (lar, rar) = dico_arities#find c in
    output_string !filedefault ("\n\t" ^ (sprint_underscore lar) ^ (dico_const_string#find c) ^ (sprint_underscore rar) ^ ": " ^ (sprint_profile profile)^ ";"))
    all_symbs in

  let () = output_string !filedefault "\n\n axioms:" in

  let sprint_clause c = 
    (let l, r = c#content
     and f x = x#string in
    match l, r with
        [], [] -> "[]"
      | [], _ -> sprint_list ", " f r
      | _, [] -> (sprint_list ", " f l) ^ " => "
      | _ -> (sprint_list ", " f l) ^ " => " ^ (sprint_list ", " f r)) ^ " ;"
  in
  
  let fn3 s = 
    let i = ref 1 in
    let () = output_string !filedefault ("\n\n\n\t% " ^ " **** " ^  (dico_const_string#find s) ^ " **** ") in
    List.iter (fun x -> 
      let lhs = x#lefthand_side in
      let hd = lhs#head in 
      if hd = s then  
	let () = output_string !filedefault ("\n\n% " ^ (dico_const_string#find s) ^ " :" ^ (string_of_int !i) ^ "\n") in
	let () = i := !i + 1 in
	output_string !filedefault ("\n\t" ^ (sprint_clause x))) 
      rewrite_system#content 
  in

  let () = List.iter fn3 all_symbs in

  (* print properties  *)

  let () = output_string !filedefault "\n\nProperties:\nsystem_is_sufficiently_complete ;\nsystem_is_strongly_sufficiently_complete ;\nsystem_is_ground_convergent ;" in

  (* print induction priorities  *)

  let main_str = List.hd ls in
  let snd_str = List.hd (List.tl ls) in

  let l = List.filter (fun x -> not (is_constructor x)) (dico_order#find main_str) in
  let l' = List.filter (fun x -> not (is_constructor x)) (dico_order#find snd_str) in
  let fn s = 
    let str_s = dico_const_string#find s in
    let str_s' = "o" ^ str_s  in
    try 
      let id = dico_const_string#find_key str_s' in 
      if list_member ( = ) id l' then str_s' else "" 
    with  Failure "find_key" -> "" 
  in 
  
  let () = output_string !filedefault "\n\nind_priorities:" in

  let () = output_string !filedefault ("\n\n" ^ (dico_const_string#find main_str) ^ " " ^ (dico_const_string#find snd_str)) in

  let () = List.iter (fun x -> 
    let () = output_string !filedefault (" " ^ (dico_const_string#find x)) in 
    let x' = fn x in 
    if x' <> "" then output_string !filedefault (" " ^ x')) (List.rev l)
  in

  let () = output_string !filedefault ";\n\n" in
  
  (* appending the extra file  *)

  let fname = file_name ^ ".txt" in
  let () = prerr_string ("\n ... appending the file " ^ fname) in 
  let fhandle = appended_file fname in
  try 
    while true do 
      let s = input_line fhandle in
      let () = output_string !filedefault (s ^ "\n") in
      ()
    done
  with End_of_file -> 
    
  (* close file_name  *)
    let () = close_in fhandle in
    let () = close_out !filedefault in
    prerr_string ("\n The file " ^ file_name ^ " was written. \n")



  
    
    
