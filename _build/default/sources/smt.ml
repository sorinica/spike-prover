(*
 * Project: Spike ver 0.1
 * File: spike.ml
 * Content: symbol definitions
 *)

open Diverse
open Symbols
open Dicos
open Literals
open Terms
open Polynoms
open Values
open Context
open Critical_context_set
open Io
open Terms_parser
open Order
open Dummies
(* open Strategies *)
open Test_sets
open Shell
open Extract


let openout =
  function
      "" ->  stdout
    | s ->
	open_out s
;;

let outputfile f = 
  let full_f = f ^ ".smt2" in
  let out = openout full_f in out



let print_constructors out =
  let () = Printf.fprintf out "\n;; relations between constructors\n" in

  let treat c1 c2 =
    
    let id1 = dico_const_string#find_key c1 in
    let id2 = dico_const_string#find_key c2 in

    let num_var = ref 0 in
    let f_print c = 
      let id = dico_const_string#find_key c in
      let l_ar, r_ar = dico_arities#find id in
     let l_sym = dico_const_string#find id in
    (* let () = Printf.printf "#Test: l_sym: %s \n%!" l_sym in *)
 

      if (l_ar+r_ar) > 0 then
	let l = list_init (l_ar+r_ar) 1 in

	let listvar =  sprint_list " " (fun x -> let () = num_var := !num_var + 1 in "x" ^ (string_of_int !num_var)) l in
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
	    "(" ^ v' ^ " " ^ a ^ ")" 
(* 	  else v ^ " " ^ a   *)
	else v'


let sprint_sort_smt srt = 
  let s = (dico_sort_string#find srt) in
  if compare s "bool" == 0 then "Bool" else
    if compare s "nat" == 0 then "Int" else s 

let sprint_lit lit =
  let fun_print t1 t2 is_eq =
    let s1 = t1#sort in
    let eq_symb = "=" in
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



let print_and l lnat = 
  if l == [] then
    if lnat == [] then ""
    else 
      if List.length lnat == 1 then List.hd lnat
      else Printf.sprintf "(and %s)" (sprint_list "  " (fun y -> y) lnat)
  else
    if lnat == [] then 
      if List.length l = 1 then let fst = (List.hd l) in sprint_lit fst
      else
	Printf.sprintf "(and %s)" (sprint_list "  " (fun y -> sprint_lit y) l)
    else
      Printf.sprintf "(and %s %s)" (sprint_list "  " (fun y -> sprint_lit y) l) (sprint_list "  " (fun y -> y) lnat)

let print_or l = 
  if l = [] then ""
  else if List.length l = 1 then let fst = (List.hd l) in sprint_lit fst
  else
    Printf.sprintf "(or %s)" (sprint_list "  " (fun y -> sprint_lit y) l)

let print_axiom out c is_axiom =
  let vars = c#variables in
  let ln = c#negative_lits in
  let lp = c#positive_lits in
  let lnat = ref [] in
  let body () = 
    let list_var lv = 
      if List.length lv <> 0 then
	sprint_list " " (fun id -> (string_of_int id)) lv
      else ""
    in
    
    
    let lvars = sprint_list " " (fun (id, s, _) -> 
      let _ = if String.compare (sprint_sort_smt s) "Int" == 0 then lnat := ("(<= 0 u" ^ (string_of_int id) ^ ")") :: !lnat  in "(u" ^ (string_of_int id) ^ " " ^ (sprint_sort_smt s) ^ ")") vars in 
    let _ = if is_axiom then Printf.fprintf out "\n(assert " else Printf.fprintf out "\n(assert (not " in
    let _ = if List.length ln == 0 then 
      if lvars <> "" then Printf.fprintf out "(forall (  %s  ) %s)" lvars  (print_or lp) 
      else  Printf.fprintf out "%s"  (print_or lp) 
      else
	let conseq = (print_or lp) in
	if lvars <> "" then 
	  if List.length lp == 0 then 	Printf.fprintf out "(forall (  %s  ) (not %s))" lvars (print_and ln !lnat)
	  else 	Printf.fprintf out "(forall (  %s  ) (=> %s %s))" lvars (print_and ln !lnat) (print_or lp)
	else 
	  if List.length lp == 0 then Printf.fprintf out "not %s" (print_and ln !lnat) 
	  else Printf.fprintf out "=> %s %s" (print_and ln !lnat) conseq
    in 
    if is_axiom then Printf.fprintf out ")\n" else Printf.fprintf out "))\n"
  in
  body ()
  (* let () = if is_axiom then *)
  (*  match (c#lefthand_side)#content with *)
  (*     Var_exist _| Var_univ _ -> Printf.fprintf out "" *)
  (*   | Term (f, _, _) ->  *)
  (*     let symb_f = dico_const_string#find f in *)
  (*     if (symb_f = "<=" || symb_f = ">=" || symb_f = ">" || symb_f = "<" || symb_f = "+" || symb_f = "-") then  *)
  (* 	Printf.fprintf out ""  *)
  (*     else body () *)
  (*   else body () *)
  (* in *)
 

let print_axioms l2 out =
  let () = Printf.fprintf out "\n\n;; axioms\n" in
  List.iter (fun c -> print_axiom out c true) l2
 
let sprint_profile_smt l =
  if l = [] then failwith "sprint_profile_smt" 
  else
    let (h, t) = List.hd l, List.tl l in
    sprint_list " " sprint_sort_smt t

let print_function out k v =
  let id = dico_const_string#find_key v in
  let l_ar, r_ar = dico_arities#find id in
  let l_sym =dico_const_string#find id in
  let sort_sym = dico_const_sort#find id in
  let profile = dico_const_profile#find id  in 
  let sort_sym_s = sprint_sort_smt sort_sym in
  (* if (r_ar = 0) then*)
  Printf.fprintf out "\n(declare-fun %s (%s) %s ) \n" l_sym ( sprint_profile_smt profile) sort_sym_s

              


let print_functions out =
  let () = Printf.fprintf out "\n\n;; defined functions\n" in
 
(*let() = print_dico_const_profile() in *)

   dico_const_string#iter (fun k v ->
     let id = dico_const_string#find_key v in 
     let l = dico_const_string#find id in
      if list_member (fun c1 c2 -> compare c1 c2 == 0) l ["S"; "minus"; "False"; "min"; "max"; "+"; "0"; "<"; "<="; ">"; ">="; "plus"; "*"; "zero"; "True"; "true"; "false"; "s"] then ()
      else
	print_function out k v
   )



 (* List.iter (fun x -> (buffered_output ("defined functions: " ^ (string_of_int x)))) (!all_defined_functions @ !all_constructors @ !l_sorts)*)

(* let print_conj out c is_axiom = *)
(*   let vars = c#variables in *)
(*   let ln = c#negative_lits in *)
(*   let lp = c#positive_lits in *)

(*   let body () =  *)
(*     let list_var lv =  *)
(*       if List.length lv <> 0 then *)
(* 	sprint_list " " (fun id -> (string_of_int id)) lv *)
(*       else "" *)
(*     in *)
    
    
(*     let lvars = sprint_list " " (fun (id, s, _) -> "(u" ^ (string_of_int id) ^ " " ^ (sprint_sort_smt s) ^ ")") vars in  *)

(*     if List.length ln = 0 then  *)
(*       if lvars <> "" then Printf.fprintf out "\n(assert (not (forall (  %s  ) %s)))\n" lvars  (print_or lp)  *)
(*       else  Printf.fprintf out "\n(assert (not %s))\n"  (print_or lp)  *)
(*     else *)
(*       if lvars <> "" then Printf.fprintf out "\n(assert (not (forall (  %s  ) (=> %s %s))))\n" lvars (print_and ln) (print_or lp) *)
(*       else Printf.fprintf out "\n(assert (not (=> %s %s)))\n" (print_and ln) (print_or lp) *)
(*   in *)
(*   if is_axiom then *)
(*     match (c#lefthand_side)#content with *)
(* 	Var_exist _| Var_univ _ -> Printf.fprintf out "" *)
(*       | Term (f, _, _) ->  *)
(* 	  let symb_f = dico_const_string#find f in *)
(* 	  if (symb_f = "<=" || symb_f = ">=" || symb_f = ">" || symb_f = "<" || symb_f = "+" || symb_f = "-") then Printf.fprintf out "" else body () *)
(*   else *)
(*     body () *)



let print_conjectures c out =
  let () = Printf.fprintf out ";; the negation of the conjecture to be proved\n" in
    print_axiom out c false
 




let print_smt c l1 l2 = 
  (* get filename  *)
  if not (c#has_bit smt_bit) then
    let () = c#set_bit smt_bit in
    let name = ("c" ^ (string_of_int c#number) ^ ".tmp") in 
    let out = outputfile name in
    let () = Printf.fprintf out ";; This file is generated automatically from Spike\n\n\n" in
    let () = Printf.fprintf out " ;; (set-logic  AUFLIA )\n\n\n%s"  !smt_inline in
    let () = flush out in
    
    let () = Printf.fprintf out "\n" in


  (* write relation between constructors  *)
  (*let () = print_constructors out in *)
    
  (* write function declarations  *)
    let  () = print_functions out in 
  (* write axioms  *)
    let () = print_axioms l2 out in
    let () = Printf.fprintf out "\n\n\n" in
  (* write conjectures  *)
    let () = print_conjectures c out in
    let () = Printf.fprintf out "\n\n(check-sat) \n\n\n " in
    let () = Printf.fprintf out "(exit)" in 
  (* close fd  *)



    let () =flush out in
    let () = close_out out in
    let n_print_string s = buffered_output s in 
    let oc_in, oc_out = Unix.open_process  ( !z3_path ^ " -T:1" ^ " " ^ name ^ ".smt2") in
    let () = try 
	       while true do
		 let line = input_line oc_in in
		 buffered_output ("\nSTDERR: " ^ line ^ "\n" );
		 if Str.string_match (Str.regexp "^unsat") line 0 then
                   raise Inconsistent
		 else 
		   if Str.string_match (Str.regexp "^sat") line 0 then
                     buffered_output ("\nSat")
		   else
		     if Str.string_match (Str.regexp "^timeout") line 0 then
                     (* let () =  buffered_output ("\nTimeout") in *)
		       ()
               done
      with 
	  End_of_file -> (* Printf.printf "\nEnd of file !!!  \n"; *)
	  (*Unix.Unix_error _ ->    Printf.printf "\nNANANA: \n";*)
	    let _ = Unix.close_process (oc_in, oc_out) in ()
    in  ()


