
(*
   * Project: Spike ver 0.1
   * File: eliminate_set.ml
   * Content: Eliminate set
*)

open Values
open Diverse
open Io
open Symbols
open Terms
open Clauses
open Dummies
open Literals
open Terms

  (* Eliminate negative redundant literals *)
let eliminate_redundant_literal verbose c level =

  let n, p = c#content in
  
  (* 0: display *)
  let rec fn c =
    let rec fn2 b = function
        [] -> []
      | h :: t ->
	  let rec fn1 el l = 
	    match l with
		[] -> []
	      | hd :: tl -> 
		  if el#syntactic_equal hd then 
		    fn1 el tl
		  else  hd  :: fn1 el tl
	  in  
          let t' = fn1 h t in
          h :: fn2 b t' 
    in
    let n' = fn2 false n in
    let p' = fn2 true p in
    if List.length n > List.length n' or List.length p > List.length p'
    then
      let c' = c#build n' p' in
      let () = c'#set_bit eliminate_redundant_literal_bit in
      let () =
        if verbose
        then
          let () = buffered_output (!indent_string ^ "ELIMINATE REDUNDANT LITERAL: simplify\n" ^
          !indent_string ^ "\171 " ^ c#string ^ "\n" ^
          !indent_string ^ "\187 " ^ c'#string) in
(* 	  let () = write_pos_term_clause c' in *)
          buffered_output ""
        else () 
      in
      
      
      c'
    else
        let () = c#set_bit eliminate_redundant_literal_bit in
        failwith "fn" 
  in
  if c#has_bit eliminate_redundant_literal_bit
  then failwith "eliminate_redundant_literal"
  else
    let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule ELIMINATE REDUNDANT LITERAL " ^ " on " ^ (string_of_int c#number)) in
(*     let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
    let new_c = try fn c with (Failure "fn") -> failwith "eliminate_redundant_literal" in
    [new_c]

            (* Eliminate trivial literal  and literals of the form v = t, where v is a unique variable in the clause *)
let eliminate_trivial_literal verbose c level =

  let rec vars_term t = 
    match t#content with
	Term (i, l, s) -> List.flatten (List.map vars_term l)
      | Var_exist _| Var_univ _ -> [t#string]
  in
  let vars_lit lit = 
    let lhs, rhs = lit#both_sides in 
    (vars_term lhs) @ (vars_term rhs)
  in
  let n, p = c#content in
  let vars_c = List.flatten (List.map vars_lit (n @ p)) in
  
  (* list of eliminated literals strings   *)
  let elits = ref "" in

  (* the substitutions (u,t) from  u = t =>  *)
  let lsubst = ref [] in

  let elim_lit lit is_pos = 
    (* true if lit has as a lhs or rhs a unique variable in c *)
    let lhs', rhs' = lit#both_sides in
    let fn t t_subst = 
      let not_apply_exist = t#is_term or (is_pos && is_existential_var t) or ((not is_pos) && (not (is_existential_var t))) in
      if not_apply_exist then 
	let not_apply_univ = t#is_term or 
(is_pos && 
  ((not (is_existential_var t) && (not lit#is_diff))) or
   ((is_existential_var t) && lit#is_diff))
   or
((not is_pos) && 
        ((is_existential_var t) && (not lit#is_diff) or 
	(not (is_existential_var t) && lit#is_diff))) in
	if not_apply_univ then 
	  false
	else 
	  let vars_c' = try remove_el (=) t#string vars_c with Failure "remove_el" -> failwith "elim_lit" in
    	  let is_unique = (not (list_member (=) t#string vars_c')) in
	  if is_unique then 
	    let () = lsubst := (t#var_content, t_subst) :: !lsubst in
	    true
	  else false
      else 
	let vars_c' = try remove_el (=) t#string vars_c with Failure "remove_el" -> failwith "elim_lit" in
    	(not (list_member (=) t#string vars_c'))
    in
(*     let are_both_vars = (not lhs'#is_term) && (not rhs'#is_term) in *)
(*     if not are_both_vars then  *)
    (fn lhs' rhs') or (fn rhs' lhs') 
  in
  
  (* 0: display *)
  let fn c =
    let rec fn2 b = function
        [] ->[]
      | h :: t ->

          let lhs, rhs = h#both_sides in
          if (lhs#syntactic_equal rhs && ((b && h#is_diff) or ((not b) && (not h#is_diff)))) or elim_lit h b
          then 
	    let () = elits:= !elits ^ ("\n\t" ^ h#string ^ " is eliminated\n")  in
	    fn2 b t
          else 
	  h :: fn2 b t in

    let n' = fn2 false n in
    let p' = fn2 true p in
    if List.length n' < List.length n or List.length p' < List.length p
    then
  (* at least a literal is eliminated  *)
      let c' = c#build n' p' in
      let () = c'#set_bit eliminate_trivial_literal_bit in
      let () =
        if verbose
        then
          let () = buffered_output (!indent_string ^ "ELIMINATE TRIVIAL LITERAL: simplify\n" ^
          !indent_string ^ "\171 " ^ c#string ^ "\n" ^ !elits ^ "\n" ^
                                      !indent_string ^ "\187 " ^ c'#string) in
(* 	  let () = write_pos_term_clause c' in *)
          buffered_output ""

        else () in
           
  (* add the substitutions to the history  *)
      let () = if !lsubst <> [] then c'#add_history (!lsubst, c) in

      c'
      else
        let () = c#set_bit eliminate_trivial_literal_bit in
        failwith "fn" 
  in
  if c#has_bit eliminate_trivial_literal_bit
  then failwith "eliminate_trivial_literal"
  else
    let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule ELIMINATE TRIVIAL LITERAL " ^ " on " ^ (string_of_int c#number)) in
(*     let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ c#string); flush stdout  in *)
    let new_c = try fn c with (Failure "fn") -> failwith "eliminate_trivial_literal" in
(*     let n, p = new_c#content in *)
(*     if List.length n = 0 && List.length p = 0 then [] else *)
    [new_c]

