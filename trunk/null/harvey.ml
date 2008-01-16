(*
 * Project: Spike ver 0.1
 * File: spike.ml
 * Content: symbol definitions
 *)

open Diverse
open Symbols
open Dicos
open Clauses
open Literals
open Terms

let openout =
  function
      "" ->  stdout
    | s ->
	open_out s
;;

let outputfile f = 
  let full_f = f ^ ".rv" in
  let out = openout full_f in
  out

let print_constructors out =
  let () = Printf.fprintf out "\n;; relations between constructors\n" in

  let treat c1 c2 =
    
    let id1 = dico_const_string#find_key c1 in
    let id2 = dico_const_string#find_key c2 in

    let num_var = ref 0 in
    let f_print c = 
      let id = dico_const_string#find_key c in
      let l_ar, r_ar = dico_arities#find id in
      if (l_ar+r_ar) > 0 then
	let l = list_init (l_ar+r_ar) 1 in

	let listvar =  (List.fold_left (fun x _ -> let () = num_var := !num_var + 1 in (x ^ " x" ^ (string_of_int !num_var))) "" l) in
(* 	let () = num_var := 0 in *)
	(listvar, c) 
      else ("", c)

    in
    if c1 = "0" || c2 = "0" then Printf.fprintf out ""
    else
      if id1 > id2 && (dico_const_sort#find id1) =  (dico_const_sort#find id2) then
	let (lv1, c1) = f_print c1 in
	let (lv2, c2) = f_print c2 in
	
	let cons1 = if lv1 = "" then c1 else Printf.sprintf "(%s %s)" c1 lv1 in
	let cons2 = if lv2 = "" then c2 else Printf.sprintf  "(%s %s)" c2 lv2 in
	if (lv1 ^ lv2) = "" then
	  Printf.fprintf out "\n(not (= (%s %s))" cons1 cons2
	else
	  Printf.fprintf out "\n(forall %s (not (= %s %s)))" (lv1 ^ lv2) cons1 cons2

  in
  let list_constructors = ref [] in
  let () = dico_const_string#iter (fun k c' -> if k > 0 then list_constructors := c' :: !list_constructors) in
  let fn1 c = 
    let () = dico_const_string#iter
      (fun k c' -> if k > 0 && c != c' then treat c c') in
    ()
  in
  List.iter (fun c -> fn1 c) !list_constructors


let rec sprint_term t = 
  match t#content with
      Var_exist (x, _) -> ("e" ^ (if x < 0 then string_of_int (- x) else string_of_int x))
    | Var_univ (x, _) -> ("u" ^ (if x < 0 then string_of_int (- x) else string_of_int x))
    | Term (f, l, _) ->            
	let v = try dico_const_string#find f with Not_found -> failwith "raising sprint_term" in
	let v' = if v = "s" || v = "S" then "+ 1" else v in
        let a = sprint_list " " (fun x -> sprint_term x) l in
        if l <> [] then 
(* 	  if List.length l <> 1 then  *)
	    " (" ^ v' ^ " " ^ a ^ ")" 
(* 	  else v ^ " " ^ a   *)
	else v'

let print_axiom out c is_axiom =
  let vars = c#variables in
  let ln = c#negative_lits in
  let lp = c#positive_lits in

  let body () = 
    let list_var lv = 
      if List.length lv <> 0 then
	List.fold_left (fun x (id, _, _) -> x ^ " u" ^ (string_of_int id)) "" lv
      else ""
    in
    
    let sprint_lit lit =
      let fun_print t1 t2 is_eq =
	let s1 = t1#sort in
	let eq_symb = if dico_sort_string#find s1 = "bool" then "<->" else "=" in
	let string_t1 = (sprint_term t1) in
	let string_t2 = (sprint_term t2) in
	if ((string_t1 = "true" || string_t1 = "True") && is_eq) || ((string_t1 = "false" || string_t1 = "False") && (not is_eq))  then Printf.sprintf "%s" string_t2
	else if ((string_t2 = "true" || string_t2 = "True") && is_eq) || ((string_t2 = "false" || string_t2 = "False") && (not is_eq))
	then Printf.sprintf "%s" string_t1
	else if ((string_t1 = "false" || string_t1 = "False") && is_eq) || ((string_t1 = "true" || string_t1 = "True") && (not is_eq))
	then Printf.sprintf "(not %s)" string_t2
	else if ((string_t2 = "false" || string_t2 = "False") && is_eq) || ((string_t2 = "true" || string_t2 = "True") && (not is_eq)) then Printf.sprintf "(not %s)" string_t1
	else 
	  if is_eq then Printf.sprintf "(%s %s %s)" eq_symb string_t1 string_t2
	  else Printf.sprintf "(not (%s %s %s))" eq_symb  string_t1 string_t2
      in
      match lit#content with
	  Lit_equal (t1,t2) -> fun_print t1 t2  true
	| Lit_rule (t1, t2) -> fun_print t1 t2 true
	| Lit_diff (t1, t2) -> fun_print t1 t2 false
    in
    
    let print_and l = 
      if l = [] then ""
      else if List.length l = 1 then let fst = (List.hd l) in sprint_lit fst
      else
	Printf.sprintf "(and %s)" (List.fold_left (fun x y -> x ^ " " ^ (sprint_lit y)) "" l)
    in
    
    let print_or l = 
      if l = [] then ""
      else if List.length l = 1 then let fst = (List.hd l) in sprint_lit fst
      else
	Printf.sprintf "(or %s)" (List.fold_left (fun x y -> x ^ " " ^ (sprint_lit y)) "" l)
    in 
    
    let lvars = list_var vars in
    
    if List.length ln = 0 then 
      if lvars <> "" then Printf.fprintf out "\n(forall %s %s)\n" lvars  (print_or lp) 
      else  Printf.fprintf out "\n%s\n"  (print_or lp) 
    else
      if lvars <> "" then Printf.fprintf out "\n(forall %s (-> %s %s))\n" lvars (print_and ln) (print_or lp)
      else Printf.fprintf out "\n(-> %s %s)\n" (print_and ln) (print_or lp)
  in
  if is_axiom then
    match (c#lefthand_side)#content with
	Var_exist _| Var_univ _ -> Printf.fprintf out ""
      | Term (f, _, _) -> 
	  let symb_f = dico_const_string#find f in
	  if (symb_f = "<=" || symb_f = ">=" || symb_f = ">" || symb_f = "<" || symb_f = "+" || symb_f = "-") then Printf.fprintf out "" else body ()
  else
    body ()

let print_axioms out =
  let () = Printf.fprintf out "\n\n;; axioms\n" in
  rewrite_system#iter (fun c -> print_axiom out c true)


let print_conjectures out =
  let () = Printf.fprintf out ";; conjectures\n" in
  all_conjectures_system#iter (fun c -> print_axiom out c false)

let print_harvey name = 
  (* get filename  *)
  let out = outputfile name in
  let () = Printf.fprintf out ";; This file is generated automatically from Spike\n\n\n" in
  let () = flush out in

  let () = Printf.fprintf out "(\n" in
  (* write relation between constructors  *)
  let () = print_constructors out in
  (* write axioms  *)
  let () = print_axioms out in
  let () = Printf.fprintf out ")\n\n\n" in
  (* write conjectures  *)
  let () = print_conjectures out in
  (* close fd  *)
  let () = close_out out in
  
()
