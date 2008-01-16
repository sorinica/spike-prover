(*
 *)

open Diverse
open Symbols
open Dicos
open Clauses
open Literals
open Terms

module Io = struct
  
  let coq_proof = ref [""]
      
  let coq_clause_numbers = ref []
    
  let coq_find_clause_number spike_num =
    fst (List.assoc spike_num !coq_clause_numbers)


  let coq_add_to_proof spike_num coq_rule =
    let coq_num =
      try
        coq_find_clause_number spike_num
      with Not_found -> spike_num
    in
    match !coq_proof with
      [] -> assert false
    | h :: t -> coq_proof := (h ^ "  " ^ (string_of_int coq_num) ^ ":" ^ coq_rule) :: t

end;;

let last_ind = ref [];;



(*TODO more induction*)
let induction vars =
  let () = last_ind := vars in
  match !Io.coq_proof with
    [] -> assert false
  | h :: t ->
      match vars with
      | [v] -> Io.coq_proof := (h ^ ("  intros.\n  induction " ^ v ^ ".\n")) :: t
      | [v1; v2] ->
          let str = "  double induction " ^ v2 ^ " " ^ v1 ^ ".\n" in
          let str = str ^ "  1:intros.2:intros.3:intros.4:intros.\n" in
          Io.coq_proof := (h ^ str) :: t
      | _ -> failwith "Coq.induction: unimplemented"
;;


let add_to_proof str =
  match !Io.coq_proof with
    [] -> assert false
  | h :: t -> Io.coq_proof := (h ^ str) :: t
;;


let todo str = add_to_proof ("  " ^ str ^ ".      (*Coq.todo*)\n");;

let next_proof () =
  Io.coq_proof := "" :: !Io.coq_proof
;;


let string_list_of_string str sep =
  let rec slos_aux str ans =
    if str = "" then ans else
    try
      let first_sep = String.index str sep in
      if first_sep = 0 then
        slos_aux (String.sub str 1 (String.length str - 1)) ans
      else
        slos_aux
          (String.sub str (first_sep + 1) (String.length str - 1 - first_sep))
          ((String.sub str 0 (first_sep)) :: ans)
    with
      Not_found ->
        List.rev ((String.lowercase str) :: ans)
  in slos_aux str []
;;


let outputfile f =
  let full_f = f ^ ".v" in
  let out = open_out full_f in
  out
;;

let rev_types l =
  let subrev = function
    | [] -> assert false
    | h :: t -> h :: List.rev t
  in
  List.rev (subrev (List.rev l))
;;

let front_to_back l =
  match l with
  | [] -> assert false
  | h :: t -> List.rev (h :: (List.rev t))
;;

let print_types out =
  let hash = Hashtbl.create 10 in
  let insert k c =
    let profile = dico_const_profile#find k in
    let types = List.map sprint_sort profile in
    let gen_type = List.hd types in
    try
      Hashtbl.replace hash gen_type ((c, (*rev_types*) types) :: (Hashtbl.find hash gen_type))
    with Not_found ->
      Hashtbl.replace hash gen_type [(c, (*rev_types*) types)]
  in
  let iterator k c = if k < 0 then () else insert k c in
  let () = dico_const_string#iter iterator in
  let print_iterator gen_type constructors =
    let () = Printf.fprintf out "Inductive sp_%s : Set :=\n" gen_type in
    let print_const_iter (name, types) =
      let sp_types = List.map (fun f -> "sp_" ^ f) (front_to_back types) in
      let types_str = String.concat " -> " sp_types in
      Printf.fprintf out "  | sp_%s : %s\n" name types_str
    in
    let () = List.iter print_const_iter (List.rev constructors) in
    Printf.fprintf out ".\n\n"
  in
  Hashtbl.iter print_iterator hash
;;

let replace_special = function
  | "-" -> "minus'"
  | "+" -> "plus"
  | "*" -> "mult"
  | ">=" -> "ge"
  | ">" -> "gt"
  | "<=" -> "le"
  | "<" -> "lt"
  | x -> x
;;

let print_funs out =
  let process k c =
    let profile = dico_const_profile#find k in
    let types = List.map sprint_sort profile in
    let sp_types = List.rev_map (fun f -> "sp_" ^ f) types in
    let types_str = String.concat " -> " (rev_types sp_types) in
    Printf.fprintf out "Variable sp_%s : %s.\n" (replace_special c) types_str
  in
  let iterator k c = if k >= 0 then () else process k c in
  dico_const_string#iter iterator
;;

let rec sprint_term t =
  match t#content with
      Var_exist (x, _) -> ("e" ^ (if x < 0 then string_of_int (- x) else string_of_int x))
    | Var_univ (x, _) -> ("u" ^ (if x < 0 then string_of_int (- x) else string_of_int x))
    | Term (f, l, _) ->
	let v = try dico_const_string#find f with Not_found -> failwith "raising sprint_term" in
        let a = sprint_list " " (fun x -> sprint_term x) l in
        let sp_v = "sp_" ^ (replace_special v) in
        if l <> [] then "(" ^ sp_v ^ " " ^ a ^ ")" else sp_v
;;

let sprint_forall vars =
  let hash = Hashtbl.create 10 in
  let iterator (id, sort, _) =
    let id_str = "u" ^ (string_of_int id) in
    try Hashtbl.replace hash sort (id_str :: Hashtbl.find hash sort)
    with Not_found -> Hashtbl.replace hash sort [id_str]
  in
  let () = List.iter iterator vars in
  let folder sort ids str =
    str ^ "forall " ^ (String.concat " " ids) ^ " : sp_" ^ (sprint_sort sort) ^ ", "
  in
  Hashtbl.fold folder hash ""
;;

(*TODO*)
let sprint_lit l =
  match l#content with
    Lit_equal (t1,t2) -> Printf.sprintf "%s = %s" (sprint_term t1) (sprint_term t2)
  | Lit_rule (t1, t2)-> Printf.sprintf "%s = %s" (sprint_term t1) (sprint_term t2)
  | Lit_diff (t1, t2) -> Printf.sprintf "%s <> %s" (sprint_term t1) (sprint_term t2)
;;

let sprint_or_and lst con =
  match List.length lst with
  | 1 -> (sprint_lit (List.hd lst))
  | n ->
      let lst_strs = List.map sprint_lit lst in
      "(" ^ (String.concat con lst_strs) ^ ")"
;;

let sprint_conj c =
  let quant = sprint_forall c#variables in
  let ln = c#negative_lits in
  let lp = c#positive_lits in
  if List.length ln = 0 then quant ^ (sprint_or_and lp " \\/ ")
  else quant ^ (sprint_or_and ln " /\\ ") ^ " -> " ^ (sprint_or_and lp " \\/ ")
;;


let print_axioms out =
  let iterator c =
    let text = sprint_conj c in
    Printf.fprintf out "Axiom sp_axiom_%i : %s.\n" c#number text
  in
  rewrite_system#iter iterator
;;

let print_conjectures out =
  let iterator c =
    let text = sprint_conj c in
    let () = Printf.fprintf out "Lemma sp_lemma_%i : %s.\n" c#number text in
    let () =
      try Printf.fprintf out "%sQed.\n\n" (List.hd !Io.coq_proof)
      with Failure "hd" -> flush out; failwith "Coq.print_conjectures"
    in
    Io.coq_proof := List.tl !Io.coq_proof
  in
  all_conjectures_system#iter iterator;
;;

let print_coq name =
  let () = Io.coq_proof := List.tl (List.rev !Io.coq_proof) in
  let out = outputfile name in
  let () = print_types out in
  let () = output_string out "\n" in
  let () = print_funs out in
  let () = output_string out "\n" in
  let () = print_axioms out in
  let () = output_string out "\n" in
  let () = print_conjectures out in
  let () = close_out out in
  ()
;;

let clause_numbers = Io.coq_clause_numbers;;

let regenerate_clause_numbers () =
  let () = clause_numbers := [] in
  let num = ref 0 in
  let iterator clause =
    incr num;
    clause_numbers := (clause#number, (!num, "")) :: !clause_numbers;
  in
  conjectures_system#iter iterator
;;

let remove_clause_number () =
  let iterator (spi_num, (coq_num, last)) =
    if conjectures_system#exists (fun clause -> clause#number = spi_num)
    then () else begin
      let () = clause_numbers := List.remove_assoc spi_num !clause_numbers in
      let iterator (spi_num, (new_coq_num, last)) =
        if new_coq_num > coq_num then
          let () = clause_numbers := List.remove_assoc spi_num !clause_numbers in
          clause_numbers := (spi_num, (new_coq_num - 1, last)) :: !clause_numbers
        else ()
      in
      List.iter iterator !clause_numbers;
    end
  in
  List.iter iterator !clause_numbers
;;

let reassign_clause_number () =
  let to_assign = ref (-1) in
  let iterator clause =
    if List.exists (fun (spi_num, _) -> clause#number = spi_num) !clause_numbers
    then () else to_assign := clause#number
  in
  let () = conjectures_system#iter iterator in
  let iterator (spi_num, (coq_num, last)) =
    if conjectures_system#exists (fun clause -> clause#number = spi_num)
    then () else begin
      let () = clause_numbers := List.remove_assoc spi_num !clause_numbers in
      clause_numbers := (!to_assign, (coq_num, last)) :: !clause_numbers
    end
  in
  List.iter iterator !clause_numbers
;;

let renumber_clauses () =
  let () =
    if conjectures_system#length > List.length !clause_numbers then
      regenerate_clause_numbers ()
    else if conjectures_system#length = List.length !clause_numbers then
      reassign_clause_number ()
    else remove_clause_number ()
  in
  let fold_fun str (sp_num, (coq_num, last)) =
    str ^ "(" ^ (string_of_int coq_num) ^ ":" ^ (string_of_int sp_num) ^ ") "
  in
  let str = List.fold_left fold_fun "  (* Conjs: " !clause_numbers in
  add_to_proof (str ^ " *)\n")
;;

let find_clause_number sp_num =
  try fst (List.assoc sp_num !clause_numbers)
  with Not_found -> (-1) (*failwith "Coq.find_clause_number"*)
;;

let delete_set num =
  let coq_num = find_clause_number num in
  add_to_proof ("  " ^ (string_of_int coq_num) ^ ":trivial.                      (* OK: delete_set *)\n")
;;

let inconsistency num =
  let coq_num = find_clause_number num in
  add_to_proof ("  " ^ (string_of_int coq_num) ^ ":auto.                      (* OK: inconsistency *)\n")
;;

let rewrite_nonum coq_num axiom =
  add_to_proof ("  " ^ (string_of_int coq_num) ^ ":try rewrite " ^ axiom ^ ".     (*Coq.rewrite*)\n")
;;

let rewrite_last_induction () =
  match !last_ind with
  | [x] -> add_to_proof ("  rewrite IH" ^ x ^ ".\n")
  | _ -> add_to_proof  ("  rewrite H0.\n")
;;


let rewrite sp_num axiom =
  let coq_num = find_clause_number sp_num in
  rewrite_nonum coq_num axiom
;;

let prepared_rewrites = ref [];;

let prepare_rewrite str =
  prepared_rewrites := ("try rewrite " ^ str ^ ".\n") :: !prepared_rewrites
;;

let prepare_rewrite_last_induction () =
  match !last_ind with
  | [x] -> prepared_rewrites := ("rewrite IH" ^ x ^ ".\n") :: !prepared_rewrites
  | _ -> prepared_rewrites := ("rewrite H0.\n") :: !prepared_rewrites
;;

let contextual_rewriting sp_num =
  let coq_num = find_clause_number sp_num in
  add_to_proof ("  (* Contextual rewriting: " ^ (string_of_int coq_num) ^ " *)\n");
  let iterator str =
    add_to_proof ("  " ^ (string_of_int coq_num) ^ ":" ^ str)
  in
  List.iter iterator (List.rev !prepared_rewrites);
  prepared_rewrites := []
;;
