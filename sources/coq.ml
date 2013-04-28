(*
 *)

open Values
open Diverse
open Symbols
open Dicos
open Clauses
open Literals
open Terms
open Io
  
 
let dummy_term f max_var = 
    let i = ref max_var in 
    let profile_f = dico_const_profile#find f in
    new term (Term (f, List.map (fun s -> let () = i := !i + 1 in new term (Var_univ (!i, s))) (List.tl profile_f), List.hd profile_f))
;;


(* the Coq proof using Coccinelle *)


let buffered_output_coq f s =
 let () = output_string f s in flush f
;;


let print_coq_specification f = 
  let prec_l = 

      (*     constructor symbols *)
    let i = ref (-1) in
    let res_constr = [] in  (* List.map (fun x -> i:= !i + 1; (x,!i)) (List.filter (fun f -> f <> 1 && f <> 0) !all_constructors) in
 *)
      
    (* defined symbols *)

    let res_def' = List.map (fun x -> (x, !i + 1 + try List.length ((* List.filter (fun x-> x < 0) *) (dico_order#find x)) with Not_found -> 0)) (!all_constructors @ !all_defined_functions) in  
    let res_def_sorted = List.sort (fun (_, x) (_, y)  -> compare x  y) res_def' in
    let treated_symb = ref [] in
    let j = ref ((snd (List.hd res_def_sorted))) in
    let j' = ref 0 in
    let res_def = List.map (fun (f, k) -> 
(* 			      let () = buffered_output ("\nk = " ^ (string_of_int k) ^ " treating the symbol " ^ (dico_const_string#find f)) in *)
(* 			      let () = buffered_output ("\nj = " ^ (string_of_int !j)) in *)
(* 			      let () = buffered_output ("\nj' = " ^ (string_of_int !j')) in *)
			     
			      let new_k = 
				if k == !j then 
				  let listf'_eq_f = List.filter (fun (f', _) -> equivalent f f') !treated_symb in
				  if listf'_eq_f <> [] then (snd (List.hd listf'_eq_f)) else  let () = j' := !j' + 1 in k + !j' - 1
				else (* k > !j *)          
				  let () = j:= k in k + !j' - 1 
			      in
(* 			      let () = buffered_output ("\nnew_k = " ^ (string_of_int new_k)) in *)
				treated_symb := (f, new_k) :: !treated_symb; (f, new_k)) res_def_sorted in 
      res_constr @ res_def
  in 
  let intro =
"Require Export List.

Require Import term.
Require Import rpo.

Require Export utils.
Require Export coccinelle_utils.

(** Translation of the specification *)
Module Specif.
  
  Inductive symb : Set := \n"
  in
  let all_symb = List.fold_right (fun f l -> if f == 0 || f == 1 then l else f :: l) (!all_constructors @ !all_defined_functions) [] in
  let symb = List.fold_right (fun f l -> "  | id_" ^ (dico_const_string#find f) ^ "\n" ^ l)  all_symb   "" in 
  let arity = "  .

  Definition arity (f:symb) := 
    match f with\n" in
  let arity_iter =  List.fold_right (fun f l -> let (l_ar,r_ar) = dico_arities#find f in ("    | id_" ^ (dico_const_string#find f) ^ " => term_spec.Free " ^ (string_of_int (l_ar+r_ar)) ^ "\n" ^ l)) all_symb "" in
  let arity_final = "    end. 
  
" in
  let status = "Definition status (f:symb) := 
     match f with\n" in
  let status_iter = List.fold_right (fun f l -> ("    | id_" ^ (dico_const_string#find f) ^ " => rpo." ^ (match dico_id_status#find f with Left| Right -> "Lex"| Multiset -> "Mul") ^ "\n") ^ l)  all_symb   "" in
  let status_final = "\n    end." in
  let prec = "\n  Definition index (f:symb) := 
     match f with\n" in
  let prec_iter = List.fold_right (fun f l -> ("    | id_" ^ (dico_const_string#find f) ^ " => " ^ (string_of_int (List.assoc f prec_l)) ^ "\n") ^ l)  all_symb  "" in
  let prec_final = "    end. 

  Definition max_size := " ^ (string_of_int 100 (*  (2 * max_term_size + 1) *) ) ^ ".

End Specif.


(* Nat and comparisons *)
Module Nat <: decidable_set.S.

  Definition A:=nat.
  Definition eq_bool := utils.beq_nat.
  Definition eq_bool_ok := utils.beq_nat_ok.

End Nat. (*: decidable_set.S*)


(** Initialisation of Coccinelle *)
Module Symbols <: term_spec.Signature.

  Module Symb <: decidable_set.S.

    Definition A:=Specif.symb.

    Theorem symb_eq_dec: forall x y:A, {x=y}+{x<>y}.
    Proof.
    decide equality.
    Defined.

    Definition eq_bool := utils.eq_bool A symb_eq_dec.
    Definition eq_bool_ok := utils.eq_bool_ok A symb_eq_dec.

  End Symb. (* Symb : decidable_set.S *)

  Definition arity := Specif.arity.

End Symbols. (* Symbols : term_spec.Signature *)


Module Prec <: rpo.Precedence.

  Definition A := Specif.symb.
  Definition status := Specif.status.

  Definition prec_bool (x y:A) : bool :=
    utils.blt_nat (Specif.index x) (Specif.index y).
  Definition prec (x y:A) := prec_bool x y = true.

  Definition prec_bool_ok := utils.prec_bool_ok A Specif.index.
  Definition prec_antisym := utils.prec_antisym A Specif.index.
  Definition prec_transitive := utils.prec_transitive A Specif.index.
  Definition prec_eq := utils.prec_eq A Specif.index.
  Definition prec_eq_bool := utils.prec_eq_bool A Specif.index.
  Definition prec_eq_bool_ok := utils.prec_eq_bool_ok A Specif.index.
  Definition prec_eq_transitive := utils.prec_eq_transitive A Specif.index.
  Definition prec_eq_sym := utils.prec_eq_sym A Specif.index.
  Definition prec_eq_refl := utils.prec_eq_refl A Specif.index.
  Definition prec_eq_prec1 := utils.prec_eq_prec1 A Specif.index.
  Definition prec_eq_prec2 := utils.prec_eq_prec2 A Specif.index.
  Definition prec_not_prec_eq := utils.prec_not_prec_eq A Specif.index.
  Definition prec_wf := utils.prec_wf A Specif.index.

  Theorem prec_eq_status : forall f g, prec_eq f g -> status f = status g.
  Proof.
  intros f g; case f; case g; reflexivity.
  Qed.

End Prec. (* Prec : rpo.Precedence *)


Module Terms <: term_spec.Term := term.Make' Symbols Nat.
Module Rpo := coccinelle_utils.Make Terms Prec.

Export Specif.
Export Rpo.

Notation less := (rpo_mul (bb (empty_rpo_infos max_size))).


(* Coq version of the specification. *) (* TODO: should be in Spec module but model_* *)
  " ^ !coq_inline ^ "



(** Initialisation of proof process *)
" in  
 
(*   let max_term_size = List.fold_right (fun t v -> max t#treesize v) (List.flatten (List.map (fun c -> c#all_terms) !coq_formulas)) 0 in 
  let max_size = "\n\nDefinition max_size := " ^ (string_of_int 100 (*  (2 * max_term_size + 1) *) ) ^ "." in

  let less = "\n\nDefinition rpo_infos := Peano_rpo.empty_rpo_infos max_size.

Definition rpo_eval  :=  Peano_rpo.rpo_eval rpo_infos max_size.

Definition rpo := Peano_rpo.rpo max_size.

Definition less_rpo_mult_eval l1 l2 := Peano_rpo.rpo_mult_eval rpo_infos max_size l1 l2 = Some ordered_set.Less_than.

Definition less := Peano_rpo.rpo_mul_rest max_size.

 (* order theorems *)

" in*)


let constr_symbols = List.fold_right (fun f l -> if f == 0 || f == 1 then l else f :: l) (!all_constructors) [] in  
let hyps_symbols = List.fold_right (fun f l ->
				      let dummy = dummy_term f 0 in
				      let vars_s =  sprint_list ", " (fun (i, s, _) -> "forall (u" ^ (string_of_int i) ^ ": " ^ (dico_sort_string#find s) ^ ")") dummy#variables in
					("Lemma model_" ^ (sprint_sort dummy#sort) ^ "_" ^ (dico_const_string#find f) ^ ": " ^ (if String.compare vars_s "" = 0 then "" else (vars_s ^ ", ")) ^ "model_" ^ (sprint_sort dummy#sort) ^ " " ^ (dummy#compute_string_coq_with_quantifiers []) ^ " = " ^ dummy#compute_string_coq true  ^ ".\nProof.\nauto.\nQed.\n\n") ^ l) constr_symbols "\n\n" in
let hint_rewrite =
  let hyps_sort s = List.fold_right (fun f l ->  let str = if s == (List.hd (dico_const_profile#find f)) then ("model_" ^ (sprint_sort s) ^ "_" ^ (dico_const_string#find f) ^ " ") else ""  in str ^ l) constr_symbols "" in
  let res = ref "" in
  let () = dico_sort_string#iter (fun s _ -> res := (!res ^ "Hint Rewrite " ^ hyps_sort s ^ ": model_" ^ (sprint_sort s) ^".\n") ) in
    !res
in


(* let hyps_symbols = List.fold_right (fun f l ->  *)
(* 					let dummy = dummy_term f 0 in  *)
(* 					let vars_s =  sprint_list ", " (fun (i, s, _) -> "forall (u" ^ (string_of_int i) ^ ": " ^ (dico_sort_string#find s) ^ ")") dummy#variables in *)
(* 					  ("Hypothesis model_" ^ (sprint_sort dummy#sort) ^ "_" ^ (dico_const_string#find f) ^ ": " ^ (if String.compare vars_s "" = 0 then "" else (vars_s ^ ", ")) ^ "model_" ^ (sprint_sort dummy#sort) ^ " " ^ (dummy#compute_string_coq_with_quantifiers []) ^ " = " ^ dummy#compute_string_coq true  ^ ".\n\n") ^ l) all_symb "\n\n" in *)
(*   let hint_rewrite =  *)
(*     let hyps_sort s = List.fold_right (fun f l ->  let str = if s == (List.hd (dico_const_profile#find f)) then ("model_" ^ (sprint_sort s) ^ "_" ^ (dico_const_string#find f) ^ " ") else ""  in str ^ l) all_symb "" in  *)
(*     let res = ref "" in *)
(*     let () = dico_sort_string#iter (fun s _ -> res := (!res ^ "Hint Rewrite " ^ hyps_sort s ^ ": model_" ^ (sprint_sort s) ^".\n\n") ) in *)
(*     !res *)
(*   in *)
  let ltac_model =
    let model_sorts =
      let res = ref "" in
      let () = dico_sort_string#iter (fun s _ -> res := (!res ^ " model_" ^ (sprint_sort s))) in
	!res
    in
      "\n\nLtac rewrite_model := autorewrite with" ^ model_sorts ^ "."
  in
  let final = intro ^ symb ^  arity ^ arity_iter ^ arity_final ^ status ^ status_iter ^ status_final ^ prec ^ prec_iter ^ prec_final  (*^ max_size ^ less ^ wf_precedence ^ notations ^ !coq_inline*) ^ hyps_symbols ^ hint_rewrite ^ ltac_model  in
  let () = if !maximal_output && !coqc_mode then buffered_output final  in 
    buffered_output_coq f final;;

 

  
  let print_coq_proof f = 

 
(* processing lemmas *)

  let j = ref 0 in
  let lemmas = List.fold_right (fun lem s -> 
				  let lvars = List.map (fun (i, s, _) ->  (i, s)) lem#variables in
				  let args_str = let () = j:= 0 in List.fold_right (fun (i, s) str -> "(" ^ (if i == 0 then let () = j:= !j + 1 in "_u" ^ (string_of_int !j) else ("u" ^ (string_of_int i))) ^ ": " ^ (dico_sort_string#find s) ^ ")" ^ (if compare str "" == 0 then "" else " ") ^  str) lvars "" in
				  let title = "\n\nHypothesis true_" ^ (string_of_int lem#number) ^ ": " ^ (* (if compare args_str "" == 0 then "" else "forall ") ^ args_str ^ (if compare args_str "" == 0 then "" else ", ") ^ *) lem#compute_string_coq_with_quantifiers true ^ ".\n" in
				  let () =  coq_all_lemmas := (lem#number, (title, lvars)):: !coq_all_lemmas in
				    title ^ s) !coq_spec_lemmas "" in
  let () = coq_spec_lemmas := [] in
    
(* processing conjectures *)
    (* vsl will count the maximal number of variables of same sort, for each sort *)
  let vsl = ref [] in
  let () = dico_sort_string#iter (fun s _ -> vsl := (s, 0) :: !vsl) in
  let () = List.iter (fun f -> let vsl_temp = ref [] in 
		      let () = dico_sort_string#iter (fun s _ -> vsl_temp := (s, 0) :: !vsl_temp) in
		      let () = List.iter (fun (_, s, _) -> let n = List.assoc s !vsl_temp in vsl_temp := (s, n + 1) :: (List.remove_assoc s !vsl_temp)) f#variables in
																					List.iter (fun (s, n) -> let n' = List.assoc s !vsl in if n > n' then vsl := (List.remove_assoc s !vsl)@[ (s, n)]) !vsl_temp)
    !coq_formulas in
  let coq_formulas_with_numbers = ref [] in
  let id = sprint_list "_" (fun cl -> (string_of_int cl#number)) !initial_conjectures in
 

 let constructor_term_res sort_res =
    let lcons = ref [] in
      (dico_const_profile#iter (fun i ls -> if (List.length ls) == 1 && List.hd ls == sort_res && is_constructor i then lcons := (dico_const_string#find i) :: !lcons ));
      if !lcons == [] then
  	(* 	give a new chance to	build a constructor term  *)
  	let lcons_i = ref [] in
  	let () = dico_const_profile#iter (fun (i:int) ls ->  if  List.hd ls == sort_res  then lcons_i := i :: !lcons_i ) in
  	  if !lcons_i == [] then failwith ("coq_induction_schema: No constructors for sort " ^ (dico_sort_string#find sort_res))
  	  else
  	    let symb = List.hd (List.filter (fun i -> let arity = dico_const_profile#find i in List.for_all (fun s -> s <> sort_res) (List.tl arity)) !lcons_i)  in
  	    let arity = dico_const_profile#find symb in
  	    let fn_constr_arg s =
  	      let lcons_arg = ref [] in
  	      let () = (dico_const_profile#iter (fun i ls -> if (List.length ls) == 1 && List.hd ls == s && is_constructor i then lcons_arg := (dico_const_string#find i) :: !lcons_arg )) in
  		if !lcons_arg == [] then failwith ("coq_induction_schema: No constant constructor  for sort " ^ (dico_sort_string#find sort_res))
  		else List.hd !lcons_arg
  	    in
  	      "(" ^ (dico_const_string#find symb) ^ " " ^ (List.fold_right (fun arg s -> let arg_s = fn_constr_arg arg in arg_s ^ " " ^ s) (List.tl arity) "") ^ ")"
      else List.hd !lcons
  in
 let fn_string_f f =
    let vars_i = ref [] in
    let vars = List.map (fun (s, n)  -> 
 			 let var_f_s = List.filter (fun (_, v, _) -> v = s) f#variables in
			 let vars_n = ref [] in 
			 let vars_z = ref [] in
			 let var_s = sprint_list " " (fun (x, _, _) -> let () = vars_n := (x, s) :: !vars_n  in ("u" ^ (string_of_int x))) var_f_s in
			 let rec fn  = function 
			     0 -> ""
			   | i ->  let () = vars_z := (0, s) :: !vars_z in " _" ^ fn (i-1) in
			 let var_s_empty = fn (n - (List.length var_f_s)) in
			 let () = vars_i := !vars_i @ (!vars_n @ !vars_z) in
			   var_s ^ var_s_empty) !vsl 
    in
    let vars_str = sprint_list " " (fun s -> s) vars in  
    let num = "Definition F_" ^ (string_of_int f#number) ^ " : type_LF_" ^ id ^ ":= " in 
    let str' = "(fun " ^ vars_str ^ " => (" ^ (f#compute_string_coq_with_quantifiers false) ^ ", " ^ (f#compute_string_coq_for_order true) ^ ")" in
    let str = num ^ str' in
    let () =  coq_formulas_with_numbers := (f#number, (str', !vars_i, f#number)):: !coq_formulas_with_numbers in
      str
 in
  let () = if !maximal_output && !coqc_mode then  buffered_output ("The number of formulas in set_F is " ^ (string_of_int (List.length !coq_formulas)) ^ " and the number of less_clauses is " ^ (string_of_int (List.length !coq_less_clauses))) in
 let rec fn_var_sort i k str sort is_universal with_sort separator=
    match i with
	0 -> ""
      | n ->  str ^ " " ^ (if is_universal then "u" else "e") ^ (string_of_int k) ^  (if with_sort then ": " ^ (dico_sort_string#find sort) else "") ^ (if n = 1 then "" else separator) ^ fn_var_sort (n-1) (k + 1) str sort  is_universal with_sort separator 
 in
 let rec fn_sort i k str sort separator=
    match i with
	0 -> ""
      | n ->  str ^ " " ^ (dico_sort_string#find sort) ^ (if n = 1 then "" else separator) ^ fn_sort (n-1) (k + 1) str sort separator 
 in
 let j = ref 1 in
 let sort_str = (j:= 1; List.fold_right (fun (s, i) str -> j:= !j + i; let res = (fn_sort i (!j - i) "" s " -> ") in str ^ (if compare str "" == 0 then "" else " -> ") ^ res) (List.rev !vsl) "") in
  let set_F = 
    let init = "\n\nDefinition type_LF_" ^ id ^ " := " ^ sort_str ^ " -> (Prop * (List.list term)).\n\n" in
    let l_formulas = sprint_list ").\n" fn_string_f  !coq_formulas  in
    let () = let size_F = List.length !coq_formulas in buffered_output ("\n size of LF_" ^id ^ " is : " ^ (string_of_int size_F) ^  "\n") in
    let fin = ").\n\nDefinition LF_" ^ id ^ " := [" ^ (sprint_list ", " (fun c -> "F_" ^ (string_of_int c#number)) !coq_formulas) ^ "].\n\n" in
      init ^ l_formulas ^ fin 
  in

(*   let comparison_lemmas = List.fold_right (fun (c1, c2) l ->  (f_less c1 c2 true) ^ "\n"  ^ l) !coq_less_clauses "" in *)
  let total_number_vars = List.fold_right (fun (_, i) s -> i + s) !vsl 0 in
  let () = j := 1 in
  let rec fn_var i k is_universal =
    match i with
      0 -> ""
      | n -> (if is_universal then "u" else "e") ^ (string_of_int k) ^ (if n = 1 then "" else " ") ^ fn_var (n-1) (k + 1) is_universal
  in
  let main_lemma = "\nLemma main_" ^ id ^ " : forall F, In F LF_" ^ id ^ " -> " ^ (j:= 1; List.fold_right (fun (s, i) str -> j:= !j + i; let res = (fn_var_sort i (!j - i) "forall" s true false ", ") in str ^  (if compare str "" == 0 then "" else ", ") ^ res) (List.rev !vsl) "") ^ ", (forall F', In F' LF_" ^ id ^ " -> " ^ (j:= 1; List.fold_right (fun (s, i) str -> j:= !j + i; let res = (fn_var_sort i (!j - i) "forall" s false false ", ") in str ^ (if compare str "" == 0 then "" else ", ") ^ res) (List.rev !vsl) "")  ^ ", less (snd (F' " ^ (fn_var total_number_vars 1 false)  ^ ")) (snd (F " ^ (fn_var total_number_vars 1 true)   ^ ")) -> fst (F' " ^  (fn_var total_number_vars 1 false) ^ ")) -> fst (F " ^ (fn_var total_number_vars 1 true)  ^ ").
Proof.
intros F HF " ^ (fn_var total_number_vars 1 true) ^ "; case_In HF; intro Hind.\n\n"
    
  in
  let rec rename_t t l = 
    match t#content with
	Var_univ (i, s) -> let new_i = List.assoc i l in new term (Var_univ (new_i, s))
      | Var_exist _ -> failwith "existential variables not yet treated"
      | Term (f, l', s) -> new term (Term (f,  List.map (fun t' -> rename_t t' l) l', s))
  in 
  let rec npos n str l =
    match l with
      |	[] -> failwith "npos: not found"
      | (_, (str1, _, _)) :: tl -> if compare str str1 == 0 then n else npos (n+1) str tl
  in
  let fn_case_generate orig_case n_case (subst: (Symbols.var * Terms.term) list) vars_pattern init intros1 case_eq_str write_case_eq =
    let subst_h = ref [] in
    let (n_case_string, vars_case, num_case) = try List.assoc n_case !coq_formulas_with_numbers with Not_found ->  (try let ch, sh, _ =  List.assoc n_case !coq_replacing_clauses  in let () = subst_h := sh in List.assoc ch#number !coq_formulas_with_numbers with Not_found ->  failwith ("fn_case_generate: clause " ^ (string_of_int n_case) ^ " used but not registered")) in
    let new_vars = ref [] in
    let rec intros_extra_vars t =
      match t#content with
	| Var_univ (i, _) ->   " intro u" ^ (string_of_int i) ^ ". " 
	| Var_exist _ -> failwith "intros_extra_vars: existential variables not yet treated ! "
	| Term (_, l, _) -> 
	    let str_niv0 = List.fold_right (fun t s -> match t#content with 
					     Var_univ (i, _) -> "intro u" ^ (string_of_int i) ^ ". " ^ s 
					   | Var_exist _ -> failwith "intros_extra_vars: existential variables not yet treated ! " 
					   | Term _ -> "intro. " ^ s   
					) l "" in 
	    let str_niv1 = List.fold_right (fun t s -> let str_t =  if t#is_term then  (intros_extra_vars t) else "" in str_t ^ s) l "" in 
	      str_niv0 ^ "intro. " ^ str_niv1
    in
    let intros2 =  (List.fold_right (fun (_, t) s -> 
				       s ^ (intros_extra_vars t) 
 				    ) subst "") ^ " intro HFabs0.\n" 
    in
    (*let stuff1 = "split. trivial_in " ^ (string_of_int (npos 0 n_case_string !coq_formulas_with_numbers)) ^ ".
unfold snd.
unfold fst.\n" 
     in*)
     let str_case = string_of_int num_case in
     let orig_str = string_of_int orig_case in
    let ind_case = (string_of_int (npos 0 n_case_string !coq_formulas_with_numbers)) in
    let stuff1 = "assert (Hind := HFabs0 F_" ^ str_case ^ "). clear HFabs0.
assert (HFabs0 : fst (F_" ^ str_case ^ " "
    in
(*     let exists_f = "\nexists " ^ n_case_string ^ ").\n" in *)
    let () = if !maximal_output && !coqc_mode then buffered_output ("the case " ^ (string_of_int n_case) ^ " has subst = " ^ (sprint_subst subst) ^ " and vars_case : " ^ (sprint_int_list (List.map fst vars_case))  ^ " and new_vars: " ^ (sprint_int_list !new_vars)  ^ " and vars_pattern: " ^ (sprint_int_list vars_pattern)  ) in 
    let exists =  sprint_list " " (fun (i, sort) -> (
						 if i == 0 then constructor_term_res sort  else 
				       let i_subst = 
					 try
					   let trm = List.assoc i !subst_h in 
					     trm#compute_string_coq_with_quantifiers [] 
					 with Not_found -> (
							    ((if List.mem i (vars_pattern) then "_" else "") ^ "u" ^ (string_of_int i)))  
				       in 
					 i_subst) ) vars_case    
    in
    let stuff2 = ")).\napply Hind. trivial_in " ^ ind_case ^ ". unfold snd. unfold F_" ^ str_case ^ ". unfold F_" ^ orig_str ^ ". rewrite_model. abstract solve_rpo_mul.\nunfold fst. unfold F_" ^ orig_str ^ ". unfold F_" ^ str_case ^ "." ^ (if not write_case_eq then " simpl in H. repeat(simpl; rewrite H). repeat(simpl in HFabs0; rewrite H in HFabs0). try (auto || (intro H0; contradict H0)). " else "")
      ^ "\nauto.\n" in
(*     let less_clause, greater_clause = try List.hd (List.filter (fun (c1, _) -> try let hyp,subst = List.assoc n_case !coq_replacing_clauses in let inst_hyp = hyp#substitute subst in inst_hyp#syntactic_equal c1 with Not_found -> n_case == c1#number) !coq_less_clauses) with Failure "hd" -> failwith ("less_clause [ " ^ (string_of_int n_case) ^ " ] not found !") in *)
(*    let less_lemma = "apply less_" ^ (string_of_int less_clause#number) ^ "_" ^ (string_of_int greater_clause#number) ^ ".\n" in*)
   
    let preambule = 
      if compare case_eq_str "" == 0 then 
	if write_case_eq then init ^ intros1 ^ intros2 else init ^ "\n" 
      else if not write_case_eq then intros1 ^ intros2 ^ case_eq_str ^ init ^ "\n"  else   "(\* this case is not possible *\)\n"  in
preambule (*^ exists_f*) ^ stuff1 ^ exists ^ stuff2 
  in

  let fn_case_rew orig n_case (subst: (Symbols.var * Terms.term) list) (*auxiliary_clauses*) info_rewriting = 
    let _, los, ax_inst, pat_subst = try List.hd info_rewriting with Failure "hd" -> failwith "fn_case_rew: there should be something" in
    let trm = ax_inst#lefthand_side in
  let has_hyp  = compare los "C1" == 0 or compare los "C2" == 0 in
  let has_lemma = compare los "L" == 0 in
  let h_subst = ref [] in
  let (n_case_string, vars_case, num_case) = try List.assoc n_case !coq_formulas_with_numbers with Not_found ->  (try let ch, subst_h, _ = List.assoc n_case !coq_replacing_clauses in let () = h_subst := subst_h in List.assoc ch#number !coq_formulas_with_numbers with Not_found ->  failwith ("fn_case_rew: clause " ^ (string_of_int n_case) ^ " used but not registered")) in
  let str_case = string_of_int num_case in
     let orig_str = string_of_int orig in
    let ind_case = (string_of_int (npos 0 n_case_string !coq_formulas_with_numbers)) in
    let stuff1 = "assert (H := Hind F_" ^ str_case ^ "). clear Hind.
assert (HFabs0 : fst (F_" ^ str_case ^ " "
    in
(*     let exists_f = "\nexists " ^ n_case_string ^ ").\n" in *)
    let exists = sprint_list " " (fun (i, sort) -> (
				     if i == 0 then constructor_term_res sort else 
				       let i_subst = 
					 try
					   let trm = List.assoc i !h_subst in 
					     trm#compute_string_coq_with_quantifiers [] 
					 with Not_found -> (
					   try let trm = List.assoc i subst in
					     trm#compute_string_coq_with_quantifiers []
					   with Not_found ->
							    ( "u" ^ (string_of_int i)))  
				       in 
					  i_subst)) vars_case    
    in
    let stuff12 = ")).\napply H. trivial_in " ^ ind_case ^ ". unfold snd. unfold F_" ^ str_case ^ ". unfold F_" ^ orig_str ^ ". rewrite_model. abstract solve_rpo_mul.\nunfold fst. unfold F_" ^ orig_str ^ ". unfold F_" ^ str_case ^ ". unfold fst in HFabs0. unfold F_" ^ str_case ^ " in HFabs0. "  
    in
     let pat_str =
      if has_lemma   then "" else 
	let pat_args = (sprint_list ", " (fun (_, t) -> t#compute_string_coq_with_quantifiers []) pat_subst) in 
	  if compare pat_args "" == 0 then "" else 
	    let fun_str = 
	      match trm#content with 
		| Term (f, _, _) -> (try dico_const_string#find f with Not_found -> failwith "fn_case_rew: symbol not found" )
		| Var_exist _ | Var_univ _ -> failwith "fn_case_rew : lhs is a variable" 
	    in
	      (if has_hyp then "try rewrite HFabs0.\n" else "pattern " ^ pat_args ^ ".\nsimpl " ^ fun_str ^ ". cbv beta.\n")
    in

    let lemma_str = 
      if has_lemma then 
	let lemma, lemma_subst = List.hd (List.map (fun (c,_,_,s) -> (c, s)) (List.filter (fun (_, los, _, _) -> compare los "L" == 0) info_rewriting)) in
	let  (_, lemma_vars_case) = try List.assoc lemma#number !coq_all_lemmas with Not_found -> failwith "lemma not found" in
	let subst_str = (sprint_list " " (fun (i, _) -> if i == 0 then "" else let t = List.assoc i lemma_subst in "(u" ^ (string_of_int i) ^ " := " ^ t#compute_string_coq_with_quantifiers [] ^ ")" ) lemma_vars_case) in
	  "specialize true_" ^ (string_of_int lemma#number) ^ " with " ^ subst_str ^ ". intro L. try rewrite L.\n" 
      else "" 
    in
    let stuff2 =   lemma_str ^ " " ^ pat_str ^ " auto.\n" in
(*     let less_clause = if not has_hyp then n_case else let hyp = List.hd auxiliary_clauses in hyp in *)
(*     let greater_clause = try List.assoc less_clause (List.map (fun (c1, c2) -> (c1#number, c2#number)) !coq_less_clauses) with Not_found -> failwith "less_clause not found !" in *)
(*     let less_lemma = "apply less_" ^ (string_of_int less_clause) ^ "_" ^ (string_of_int greater_clause) ^ ".\n" in *)
      (*exists_f ^*) stuff1 ^ exists ^ stuff12 ^ " " ^ stuff2 
  in
  let fn_case_negdec orig_case n_case = 
 let h_subst = ref [] in 
     let (n_case_string, nvars_case, num_case) = try List.assoc n_case !coq_formulas_with_numbers with Not_found ->  (try let ch, s, _ = List.assoc n_case !coq_replacing_clauses  in h_subst := s; List.assoc ch#number !coq_formulas_with_numbers with Not_found ->  failwith ("fn_case_negdec: clause " ^ (string_of_int n_case) ^ " used but not registered")) in
     (*let stuff1 = "split. trivial_in " ^ (string_of_int (npos 0 n_case_string !coq_formulas_with_numbers)) ^ ".
unfold snd.
unfold fst.\n" in
*)
     let orig_str = string_of_int orig_case in
     let str_case = string_of_int num_case in
     let nth_str = string_of_int (npos 0 n_case_string !coq_formulas_with_numbers) in 
     let stuff1 = "assert (H := Hind F_" ^ str_case ^ "). 
assert (HFabs0 : fst (F_" ^ str_case ^ " "  in
(*     let exists_f = "\nexists " ^ n_case_string ^ ").\n" in *)
 

(*     let () = buffered_output ("vars_case: " ^ (sprint_list " " (fun i -> (string_of_int i)) vars_case)) in *)
(*     let () = buffered_output ("nvars_case: " ^ (sprint_list " " (fun i -> (string_of_int i)) nvars_case)) in *)
(*     let () = buffered_output ("h_subst: " ^ (sprint_subst !h_subst)) in *)
    let exists =  sprint_list " " (fun (i, sort) -> (
				     if i == 0 then constructor_term_res sort else 
				       let i_subst = 
					 try
					   let trm = List.assoc i !h_subst in 
					     trm#compute_string_coq_with_quantifiers [] 
					 with Not_found -> (
					   (  "u" ^ (string_of_int i)))  
				       in 
					 i_subst )) nvars_case  
    in
     let stuff2 = ")).\napply H. trivial_in " ^ nth_str ^ ". unfold snd. unfold F_" ^ str_case ^ ". unfold F_" ^ orig_str ^ ". rewrite_model. abstract solve_rpo_mul.\nunfold fst. unfold F_" ^ orig_str ^ ". unfold F_" ^ str_case ^ ".\n\nunfold fst in HFabs0. unfold F_" ^ str_case
      ^ " in HFabs0.\nauto.\n" in 
(*     let less_clause = n_case in *)
(*     let greater_clause = try List.assoc less_clause (List.map (fun (c1, c2) -> (c1#number, c2#number)) !coq_less_clauses) with Not_found -> failwith "less_clause not found !" in *)
(*     let less_lemma = "apply less_" ^ (string_of_int less_clause) ^ "_" ^ (string_of_int greater_clause) ^ ".\n" in *)
    
      (*exists_f ^*) stuff1 ^ exists ^ stuff2
  in
  let fn_case_posdec orig_case n_case i = 
    let h_subst = ref [] in 
     let (n_case_string, nvars_case, num_case) = try List.assoc n_case !coq_formulas_with_numbers with Not_found ->  (try let ch, s, _ = List.assoc n_case !coq_replacing_clauses  in h_subst := s; List.assoc ch#number !coq_formulas_with_numbers with Not_found ->  failwith ("fn_case_posdec: clause " ^ (string_of_int n_case) ^ " used but not registered")) in
     let orig_str = string_of_int orig_case in
     let str_case = string_of_int num_case in
     let nth_str = string_of_int (npos 0 n_case_string !coq_formulas_with_numbers) in 
     let stuff1 = "assert (H" ^ (string_of_int i) ^ " := Hind F_" ^ str_case ^ "). 
assert (HFabs" ^ (string_of_int i) ^ " : fst (F_" ^ str_case ^ " "  in
(*     let exists_f = "\nexists " ^ n_case_string ^ ").\n" in *)

(*     let () = buffered_output ("vars_case: " ^ (sprint_list " " (fun i -> (string_of_int i)) vars_case)) in *)
(*     let () = buffered_output ("nvars_case: " ^ (sprint_list " " (fun i -> (string_of_int i)) nvars_case)) in *)
(*     let () = buffered_output ("h_subst: " ^ (sprint_subst !h_subst)) in *)
    
let exists =  sprint_list " " (fun (i, sort) -> (
				     if i == 0 then constructor_term_res sort else 
				       let i_subst = 
					 try
					   let trm = List.assoc i !h_subst in 
					     trm#compute_string_coq_with_quantifiers [] 
					 with Not_found -> (
							    (  "u" ^ (string_of_int i)))  
				       in 
					 i_subst)) nvars_case 
    in
       let stuff2 = ")).\napply H" ^ (string_of_int i) ^ ". trivial_in " ^ nth_str ^ ". unfold snd. unfold F_" ^ str_case ^ ". unfold F_" ^ orig_str ^ ". rewrite_model. abstract solve_rpo_mul.\nunfold fst. unfold F_" ^ orig_str ^ ". unfold F_" ^ str_case ^ ".\n\nunfold fst in HFabs" ^ (string_of_int i) ^ ". unfold F_" ^ str_case
      ^ " in HFabs" ^ (string_of_int i) ^ ".\n\n" in 
(*     let less_clause = n_case in *)
(*     let greater_clause = try List.assoc less_clause (List.map (fun (c1, c2) -> (c1#number, c2#number)) !coq_less_clauses) with Not_found -> failwith "less_clause not found !" in *)
(*     let less_lemma = "apply less_" ^ (string_of_int less_clause) ^ "_" ^ (string_of_int greater_clause) ^ ".\n" in *)
          (*exists_f ^*) stuff1 ^ exists ^ stuff2
  in

  let fn_case_totalrew orig_case cl_case trm subst orig_clause_number= 
  let init = "(* rewriting with the axiom [ " ^ (string_of_int orig_clause_number) ^ " ] *)\n\n" in
  let h_subst = ref [] in 
     let (n_case_string, nvars_case, num_case) = try List.assoc cl_case#number !coq_formulas_with_numbers with Not_found ->  (try let ch, s, _ = List.assoc cl_case#number !coq_replacing_clauses  in h_subst := s; List.assoc ch#number !coq_formulas_with_numbers with Not_found ->  failwith ("fn_case_totalrew: clause " ^ (string_of_int cl_case#number) ^ " used but not registered")) in
  let pat_str = List.fold_right (fun (_, t) s -> let tstr = t#compute_string_coq_with_quantifiers [] in " pattern " ^  tstr ^ "." ^ s) subst "" in
  (*let stuff1 = "split. trivial_in " ^ (string_of_int (npos 0 n_case_string !coq_formulas_with_numbers)) ^ ".
unfold snd.
unfold fst.\n" in
*)
  let orig_str = string_of_int orig_case in
  let str_case = string_of_int num_case in
  let nth_str = string_of_int (npos 0 n_case_string !coq_formulas_with_numbers) in
  let stuff1 = "assert (H1 := Hind F_" ^ str_case ^ "). clear Hind.
assert (HFabs0 : fst (F_" ^ str_case ^ " "
    in
(*   let exists_f = "\nexists " ^ n_case_string ^ ").\n" in *)
						  
(*     let () = buffered_output ("vars_case: " ^ (sprint_list " " (fun i -> (string_of_int i)) vars_case)) in *)
(*     let () = buffered_output ("nvars_case: " ^ (sprint_list " " (fun i -> (string_of_int i)) nvars_case)) in *)
(*     let () = buffered_output ("h_subst: " ^ (sprint_subst !h_subst)) in *)
    let exists =  sprint_list " " (fun (i, sort)  -> (
				     if i == 0 then constructor_term_res sort else 
				       let i_subst = 
					 try
					   let trm = List.assoc i !h_subst in 
					     trm#compute_string_coq_with_quantifiers [] 
					 with Not_found -> (
					   (  "u" ^ (string_of_int i)))  
				       in 
					  i_subst)) nvars_case
    in
   let fun_str = 
      match trm#content with 
	| Term (f, _, _) -> (try dico_const_string#find f with Not_found -> failwith "fn_case_totalrew: symbol not found" )
	    | Var_exist _ | Var_univ _ -> failwith "fn_case_totalrew : lhs is a variable" 
   in
let stuff12 = ")).\napply H1. trivial_in " ^ nth_str ^ ". unfold snd. unfold F_" ^ str_case ^ ". unfold F_" ^ orig_str ^ ". rewrite_model. abstract solve_rpo_mul.\nunfold fst. unfold F_" ^ orig_str ^ ". unfold F_" ^ str_case ^ ". unfold fst in HFabs0. unfold F_" ^ str_case ^ " in HFabs0. "  
    in
  let stuff2 = 
     pat_str ^ "\nsimpl " ^ fun_str ^ ". cbv beta. try unfold " ^ fun_str ^ ". try rewrite H. try rewrite H0. try unfold " ^ fun_str ^ " in HFabs0. try rewrite H in HFabs0. try rewrite H0 in HFabs0. auto.\n"
  in
(*   let less_clause = cl_case#number in *)
(*   let greater_clause = try List.assoc less_clause (List.map (fun (c1, c2) -> (c1#number, c2#number)) !coq_less_clauses) with Not_found -> failwith "less_clause not found !" in *)
(*   let less_lemma = "apply less_" ^ (string_of_int less_clause) ^ "_" ^ (string_of_int greater_clause) ^ ".\n" in *)
    
    init (*^ exists_f*) ^ stuff1 ^ exists ^ stuff12 ^ stuff2
  in
 
  let lemma_proof = List.fold_right (fun (rule, n, lvars, linst, info_rewriting) str -> 
(* 				       let () = buffered_output ("\n treating " ^ (string_of_int n) ^ " with " ^ rule) in  *)
				       let res =
					 match rule with
					   | "augmentation" -> 
					       let head = "\t(* AUGMENTATION on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let (n_case, vars_case, _) = try List.assoc n !coq_formulas_with_numbers with Not_found ->   failwith ("fun: clause " ^ (string_of_int n) ^ " used but not registered") in
					       let conv_vars = ref [] in
					       let rename_vars1 = j:= 0; List.fold_right (fun (i, _) s -> let () = j := !j + 1 in s ^ (if i == 0 then ("rename u" ^ (string_of_int !j) ^ " into d_u" ^ (string_of_int !j) ^ ". ") else let () = conv_vars := i :: !conv_vars in "rename u" ^ (string_of_int !j) ^ " into _u" ^ (string_of_int i) ^ ". ")) (List.rev vars_case) "" in  
					       let rename_vars2 = List.fold_right (fun i s -> s ^ "rename _u" ^ (string_of_int i) ^ " into u" ^ (string_of_int i) ^ ". ") !conv_vars "" in
					       let lres_c = List.hd (List.map fst (List.filter (fun (_, c) -> c#number == n) !coq_less_clauses)) in 
					       let (n_case_string, vars_case, n_ind) = try List.assoc lres_c#number !coq_formulas_with_numbers with Not_found ->  failwith ("augment: clause " ^ (string_of_int lres_c#number) ^ " used but not registered") in
					       let nth_case = (string_of_int (npos 0 n_case_string !coq_formulas_with_numbers)) in
					       let lcase = List.fold_right (fun (i, subst) str ->
							     		      let  (c_str, lvars_case) = try List.assoc i !coq_all_lemmas with Not_found -> failwith "lemma or premise not found" in
							     		      let subst_str = (sprint_list " " (fun (i, _) -> if i == 0 then "" else try let t =  List.assoc i subst in "(u" ^ (string_of_int i) ^ " := " ^ t#compute_string_coq_with_quantifiers [] ^ ")" with Not_found -> "... to complete.... ") lvars_case) in
							     			str ^ "\n" ^ "specialize true_" ^ (string_of_int i) ^ " with " ^ subst_str ^ "." ) linst (")).\napply H. trivial_in " ^ nth_case ^ ". unfold snd. unfold F_" ^ (string_of_int n) ^ ". unfold F_" ^ (string_of_int n_ind) ^ ". rewrite_model. abstract solve_rpo_mul.\n\nunfold fst. unfold F_" ^ (string_of_int n) ^ ".\n" )
					       in
					       let stuff1 = "\nassert (H := Hind F_" ^ (string_of_int n_ind) ^ "). clear Hind.\nassert (HFabs0: fst (F_" ^ (string_of_int n_ind) ^ " " in
					       let exists_str = sprint_list " " (fun (i, sort) -> (
										    if i == 0 then  constructor_term_res sort else 
										      let i_subst = 
											try
											  let trm = List.assoc i [] in 
											    trm#compute_string_coq_with_quantifiers [] 
											with Not_found -> (
											  (  "u" ^ (string_of_int i)))  
										      in 
											 i_subst) ) vars_case   in
						 head ^ rename_vars1 ^ "\n" ^ rename_vars2 ^  stuff1 ^ exists_str ^ lcase ^ " auto.\n\n\n\n\n" 
						   
					   | "total_case_rewriting" -> 
					       let head = "\t(* TOTAL CASE REWRITING on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let (_, vars_case, _) = try List.assoc n !coq_formulas_with_numbers with Not_found ->   failwith ("total case rewriting: clause " ^ (string_of_int n) ^ " used but not registered") in
					       let conv_vars = ref [] in
					       let rename_vars1 = j:= 0; List.fold_right (fun (i, _) s -> let () = j := !j + 1 in s ^ (if i == 0 then ("rename u" ^ (string_of_int !j) ^ " into d_u" ^ (string_of_int !j) ^ ". ") else let () = conv_vars := i :: !conv_vars in "rename u" ^ (string_of_int !j) ^ " into _u" ^ (string_of_int i) ^ ". ")) (List.rev vars_case) "" in  
					       let rename_vars2 = List.fold_right (fun i s -> s ^ "rename _u" ^ (string_of_int i) ^ " into u" ^ (string_of_int i) ^ ". ") !conv_vars "" in

					       let lres_c = List.map fst (List.filter (fun (_, c) -> c#number == n) !coq_less_clauses) in 
					       let llits = ref [] in
					       let lcond = List.fold_right (fun (c,_,ax_inst,_) s -> (List.fold_right (fun l s' -> 
														      (match l#content with
															| Lit_rule (l, r) -> 
															    let lstr = 
																l#compute_string_coq_with_quantifiers []
															    in 
															    let rstr = 
																r#compute_string_coq_with_quantifiers []
															    in 
															    let () = llits := (lstr, rstr) :: !llits in 
															      "(" ^ lstr ^ " = " ^ rstr ^ ")" 
															| Lit_equal (l, r) ->   let lstr = 
																l#compute_string_coq_with_quantifiers []
															    in 
															    let rstr = 
																r#compute_string_coq_with_quantifiers []
															    in 
															    let () = llits := (lstr, rstr) :: !llits in 
															      "(" ^ lstr ^ " = " ^ rstr ^ ")" 
															| Lit_diff _ -> failwith "fun: negative literals not yet treated") 
														      ^ (if compare s' "" == 0 then "" else " /\\ ") ^ s') ax_inst#negative_lits "") ^ (if compare s "" == 0 then "" else " \\/ ") ^ s) info_rewriting "" in
					       (* let sol_str1 = "destruct " in *)
					       (* let sol_str2 = "; auto.\n\ndestruct H.\n\n" in *)
					       let error_str = "\n\n(* The system is not able to automatically generate the proof for the conditions. Please fill in it manually. *)\n\n" in
					       let non_bool_terms = ref [] in
					       let strat_cond = 
						 let () = List.iter (fun (_,_,ax_inst,_) ->
									    List.iter (fun lit  -> 
											   (match lit#content with
											      | Lit_rule (l, r) -> 
												  let () = if compare l#string "true" <> 0 && compare l#string "false" <> 0 then
												    if not (list_member (fun x y -> if compare x#string y#string == 0 then true else false) l !non_bool_terms) then non_bool_terms := l :: !non_bool_terms in 															    
												  let () = if compare r#string "true" <> 0 && compare r#string "false" <> 0 then 
												    if not (list_member (fun x y -> if compare x#string y#string == 0 then true else false) r !non_bool_terms) then non_bool_terms := r :: !non_bool_terms in 
												    ()
											      | Lit_equal (l, r) -> 
												  let () = if compare l#string "true" <> 0 && compare l#string "false" <> 0 then
												    if not (list_member (fun x y -> if compare x#string y#string == 0 then true else false) l !non_bool_terms) then non_bool_terms := l :: !non_bool_terms in 															    
												  let () = if compare r#string "true" <> 0 && compare r#string "false" <> 0 then 
												    if not (list_member (fun x y -> if compare x#string y#string == 0 then true else false) r !non_bool_terms) then non_bool_terms := r :: !non_bool_terms in 
												    ()    
											      | Lit_diff _ -> failwith "fun: negative literals not yet treated") 
											   ) ax_inst#negative_lits) info_rewriting in
						 let destr_t_str = sprint_list "; " (fun t -> "destruct (" ^ t#compute_string_coq_with_quantifiers [] ^ ")") !non_bool_terms in
						 let destr_h = 
						   if List.length !non_bool_terms == 1 then "destruct H as [H|H].\n" else 
						     if List.length !non_bool_terms == 2 then "destruct H as [[H H0]|[H|[H H0]]].\n" else ""
						 in
						   if List.length !non_bool_terms > 2 then error_str else
						    "\n\n" ^ destr_t_str ^ "; auto.\n\n" ^ destr_h ^ "\n"
						 in
					       (* let strat_cond =  *)
					       (* 	 if (List.length info_rewriting == 2 (\* && List.for_all (fun (c, _, _, _) -> List.length c#negative_lits == 1) info_rewriting *\)) then *)
					       (* 	   let l1, r1 = List.hd !llits in *)
					       (* 	   let l2, r2 = List.hd (List.tl !llits) in *)
					       (* 	     if compare l1 l2 == 0 then sol_str1 ^ l1 ^ sol_str2 else *)
					       (* 	       if compare l1 r2 == 0 then sol_str1 ^ l1 ^ sol_str2 else *)
					       (* 		 if compare r1 r2 == 0 then sol_str1 ^ r1 ^ sol_str2 else error_str *)
					       (* 	 else error_str *)
					       (* in *)
					       let cond_str = "assert (H: " ^ lcond ^ "). " ^ strat_cond in
					       let c_info = try List.map2 (fun (c, _, ax_inst, s) (ax, _) -> (ax_inst#lefthand_side, s, ax, c)) info_rewriting linst with Invalid_argument _ -> failwith "Invalid argument in map2" in
					       (* let c_info = try List.map2 (fun (trm, s, ax) cres -> (trm, s, ax, cres)) ax_subst_num lres_c with Invalid_argument _ -> failwith "Again Invalid argument in map2" in *)
					       let lcase = sprint_list "\n\n" (fun (trm, s, ax, cres) -> fn_case_totalrew n cres trm s ax) c_info in
						 head ^  rename_vars1 ^ "\n" ^ rename_vars2 ^ "\n" ^ cond_str ^ lcase ^ "\n\n\n"  
					   | "rewriting" -> 
					       let head = "\t(* REWRITING on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let rew_cl, rew_los, _, rew_subst = try List.hd info_rewriting with Failure "hd" -> failwith "fn_case_rew: there should be something" in
					       let (_, vars_case, _) = try List.assoc n !coq_formulas_with_numbers with Not_found -> failwith ("fn_case_rew: clause " ^ (string_of_int n) ^ " used but not registered") in
					       let conv_vars = ref [] in
					       let rename_vars1 = j:= 0; List.fold_right (fun (i, _) s -> let () = j := !j + 1 in s ^ (if i == 0 then ("rename u" ^ (string_of_int !j) ^ " into d_u" ^ (string_of_int !j) ^ ". ") else let () = conv_vars := i :: !conv_vars in "rename u" ^ (string_of_int !j) ^ " into _u" ^ (string_of_int i) ^ ". ")) (List.rev vars_case) "" in  
					       let rename_vars2 = List.fold_right (fun i s -> s ^ "rename _u" ^ (string_of_int i) ^ " into u" ^ (string_of_int i) ^ ". ") !conv_vars "" in
					       let is_hyp = compare rew_los "C1" == 0 or compare rew_los "C2" == 0 in
					       let lcase = 
						 if not is_hyp then 
						     sprint_list "\n\n" (fun (n', _) -> fn_case_rew n n' [] (*[]*) info_rewriting) linst 
						 else
						   let (h, sub) = (rew_cl, rew_subst) in
(* 						   let (h_inst_number, _) = List.hd linst in *)
						     fn_case_rew n h#number sub (*[h_inst_number]*) info_rewriting 
					       in
						 head ^ rename_vars1 ^ "\n" ^ rename_vars2 ^ "\n" ^ lcase ^ "\n\n\n"  
					   | "generate" ->
					       let head = "\t(* GENERATE on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let (_, vars_case, _) = try List.assoc n !coq_formulas_with_numbers with Not_found ->   failwith ("generate: clause " ^ (string_of_int n) ^ " used but not registered") in
					       let () = if !maximal_output && !coqc_mode then buffered_output ("vars_case for " ^ (string_of_int n) ^ " is : " ^ (sprint_int_list (List.map fst vars_case))) in
					       let conv_vars = ref [] in
					       let rename_vars1 = j:= 0; List.fold_right (fun (i, _) s -> let () = j := !j + 1 in s ^ (if i == 0 then ("rename u" ^ (string_of_int !j) ^ " into d_u" ^ (string_of_int !j) ^ ". ") else let () = conv_vars := i :: !conv_vars in "rename u" ^ (string_of_int !j) ^ " into _u" ^ (string_of_int i) ^ ". ")) (List.rev vars_case) "" in  
					       let rename_vars2 = List.fold_right (fun i s -> s ^ "rename _u" ^ (string_of_int i) ^ " into u" ^ (string_of_int i) ^ ". ") !conv_vars "" in
					       let not_inst_vars = List.filter (fun (i, _, _) -> List.for_all (fun (_, s) -> not (List.exists (fun (j,_) -> i == j) s)) linst ) lvars in 
					       let rec fn_lvars_not_inst l =
						 match l with 
						   | [] -> []
						   | h :: t -> if List.mem h not_inst_vars then fn_lvars_not_inst t else l
					       in
					       let vars_pattern = List.map (fun (i, _, _) -> i) (fn_lvars_not_inst lvars) in
					       let f_ind_args = (sprint_list ", " (fun (i, _, _) -> "u" ^ (string_of_int i)) lvars) in
					       let f_ind_args' = (sprint_list " " (fun (i, _, _) -> "u" ^ (string_of_int i)) lvars) in
					       let f_ind_args'' = (sprint_list " " (fun i -> "_u" ^ (string_of_int i)) vars_pattern) in
					       let pattern = "\nrevert Hind.\n\npattern " ^ f_ind_args ^ ", " ^ "(f_" ^ (string_of_int n) ^ " " ^ f_ind_args' ^ "). "
 in
					       let ind_scheme = "apply f_" ^ (string_of_int n) ^ "_ind.\n\n" in
					       let lcond = List.assoc n !coq_generate_cond in
					       let linst_cond = try List.combine linst lcond with Invalid_argument("List.combine") -> failwith ( "generate: mismatch between conditions and cases : " ^ (string_of_int (List.length lcond)) ^ " and " ^  (string_of_int (List.length linst)))in
					       let write_case_eq = ref true in 
					       let lcase = List.fold_left (fun s ((n', subst), cond) -> 
										 let init = "(* case [ " ^ (string_of_int n') ^ " ] *)\n" in
										 let () = if !maximal_output && !coqc_mode then buffered_output ("gencase" ^ (string_of_int n')) in
										 let case_eq_str = if cond == [] then "" else
										   if List.length cond > 1 then "\n(* several conditions for the unifying axiom are not supported - the case should to be manually checked *)" else 
										     let lit = List.hd cond in
										     let lit_subst = lit#substitute subst in
										     let l, r = lit_subst#both_sides in 
										     let () = if !maximal_output && !coqc_mode then buffered_output ("r_string is " ^ r#string) in 
										       if compare l#string "true" == 0 or compare l#string "false" == 0 then 
											 if !write_case_eq then (write_case_eq := false; "case_eq " ^ r#compute_string_coq_with_quantifiers vars_pattern ^ "; [intro H | intro H].\n") else ""
										       else	 
											 if compare r#string "true" == 0 or compare r#string "false" == 0 then 
											   if !write_case_eq  then (write_case_eq := false; "case_eq " ^ l#compute_string_coq_with_quantifiers vars_pattern ^ "; [intro H | intro H].\n\n") else ""
											 else "\n(* several conditions for the unifying axiom are not supported - the case should to be manually checked *)"
										 in
										 let intros = "\nintros "  ^ f_ind_args'' ^ ". " in
										 let subst' = (* expand when a variable has a sort with only one constructor *)
										 
										   (* let has_only_one_constr s = *)
										   (*   let n = ref 0 in *)
										   (*   let () = dico_const_profile#iter (fun i ls ->  if  List.hd ls == s && i > 0 then n := !n + 1) in *)
										   (*     !n == 1 *)
										   (* in *)
										   (* let dummy_t s = *)
										   (*   let n = ref 0 in *)
										   (*   let () = dico_const_profile#iter (fun (i:int) ls ->  if  List.hd ls == s && i > 0 then n := i) in *)
										   (*   let max_var = list_max max (List.map (fun (i,_,_) -> i) lvars) in *)
										   (*     dummy_term !n max_var *)
										   (* in *)
										   let rez_subst = ref [] in
										   let () =  List.iter (fun (i, s, _) ->
													  try let t = List.assoc i subst in rez_subst := (i, t) :: !rez_subst
										   			  with Not_found -> () (* (if has_only_one_constr s then rez_subst := (i, dummy_t s) :: !rez_subst  ) *)) lvars in
										     !rez_subst
										 in
										   s ^ (fn_case_generate n  n' subst' vars_pattern init intros case_eq_str  !write_case_eq) ^ "\n\n"  ) "" linst_cond in
						 head ^ rename_vars1 ^ "\n" ^ rename_vars2 ^ "\n" ^ pattern ^ ind_scheme ^ lcase ^ "\n\n\n" 
					   | "positive_decomposition" -> 
					       let head = "\t(* POSITIVE DECOMPOSITION on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let (_, vars_case, _) = try List.assoc n !coq_formulas_with_numbers with Not_found ->   failwith ("posdec: clause " ^ (string_of_int n) ^ " used but not registered") in
 let conv_vars = ref [] in
					       let rename_vars1 = j:= 0; List.fold_right (fun (i, _) s -> let () = j := !j + 1 in s ^ (if i == 0 then ("rename u" ^ (string_of_int !j) ^ " into d_u" ^ (string_of_int !j) ^ ". ") else let () = conv_vars := i :: !conv_vars in "rename u" ^ (string_of_int !j) ^ " into _u" ^ (string_of_int i) ^ ". ")) (List.rev vars_case) "" in  
					       let rename_vars2 = List.fold_right (fun i s -> s ^ "rename _u" ^ (string_of_int i) ^ " into u" ^ (string_of_int i) ^ ". ") !conv_vars "" in
					       (* let preambule = if List.length info_rewriting == 1 then "" else
 *)
					       (* 	 if List.length info_rewriting > 2 then "\n\n(\* This case is not yet supported. Please fill in the proof manually *\)\n\n"
 *)
					       (* 	 else 
 *)
					       (* 	   let (c1, _, _, _) = List.hd info_rewriting in
 *)
					       (* 	   let (c2, _, _, _) = List.hd (List.tl info_rewriting) in 
 *)
					       (* 	   if c1#negative_lits <> [] or c2#negative_lits <> [] then "\n\n(\* This case is not yet supported. Please fill in the proof manually *\)\n\n"
 *)
					       (* 	   else 
 *)
					       (* 	     let c1_str = c1#compute_string_coq_with_quantifiers false in
 *)
					       (* 	     let c2_str = c2#compute_string_coq_with_quantifiers false in
 *)
					       (* 	       "\nassert((" ^ c1_str ^ " /\\ " ^ c2_str ^ ") -> False). intros. destruct H. rewrite H0 in HFabs. auto.\nassert((" ^ c1_str ^ " -> False) \\/ (" ^ c2_str ^ " -> False)). apply not_and_or. auto.\nclear HFabs. destruct H0 as [HFabs | HFabs].\n" in
 *)
 
					       let () = j := 0 in 
					       let lcase = sprint_list "\n\n" (fun (n', _) -> let () = j := !j + 1 in fn_case_posdec n n' !j) linst in
					       let rec fn_iter j str = 
						 match j with
						   | 0 -> ""
						   | _ -> str ^ (string_of_int j) ^ "|| " ^ (fn_iter (j - 1) str)
					       in 
						 head ^  rename_vars1 ^ "\n" ^ rename_vars2 ^ "\n" ^ (* preambule ^ *) lcase ^ "repeat (auto || (" ^ (fn_iter !j "rewrite HFabs" ) ^ " auto)).\n\n\n" 
					   | "negative_decomposition" -> 
					       let head = "\t(* NEGATIVE DECOMPOSITION on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let (_, vars_case, _) = try List.assoc n !coq_formulas_with_numbers with Not_found ->   failwith ("negdec: clause " ^ (string_of_int n) ^ " used but not registered") in
 let conv_vars = ref [] in
					       let rename_vars1 = j:= 0; List.fold_right (fun (i, _) s -> let () = j := !j + 1 in s ^ (if i == 0 then ("rename u" ^ (string_of_int !j) ^ " into d_u" ^ (string_of_int !j) ^ ". ") else let () = conv_vars := i :: !conv_vars in "rename u" ^ (string_of_int !j) ^ " into _u" ^ (string_of_int i) ^ ". ")) (List.rev vars_case) "" in  
					       let rename_vars2 = List.fold_right (fun i s -> s ^ "rename _u" ^ (string_of_int i) ^ " into u" ^ (string_of_int i) ^ ". ") !conv_vars "" in
					       let preambule = if List.length info_rewriting == 1 then "" else
						 if List.length info_rewriting > 2 then "\n\n(* This case is not yet supported. Please fill in the proof manually *)\n\n"
						 else 
						   let (c1, _, _, _) = List.hd info_rewriting in
						   let (c2, _, _, _) = List.hd (List.tl info_rewriting) in 
						   if c1#negative_lits <> [] or c2#negative_lits <> [] then "\n\n(* This case is not yet supported. Please fill in the proof manually *)\n\n"
						   else 
						     let c1_str = c1#compute_string_coq_with_quantifiers false in
						     let c2_str = c2#compute_string_coq_with_quantifiers false in
						       "\nassert((" ^ c1_str ^ " /\\ " ^ c2_str ^ ") -> False). intros. destruct H. rewrite H0 in HFabs. auto.\nassert((" ^ c1_str ^ " -> False) \\/ (" ^ c2_str ^ " -> False)). apply not_and_or. auto.\nclear HFabs. destruct H0 as [HFabs | HFabs].\n" in
 
					       let lcase = sprint_list "\n\n" (fun (n', _) -> fn_case_negdec n n') linst in
						 head ^  rename_vars1 ^ "\n" ^ rename_vars2 ^ "\n" ^ preambule ^ lcase ^ "\n\n\n" 
(* 					       let head = "\t(\* NEGATIVE DECOMPOSITION on [ " ^ (string_of_int n) ^ " ] *\)\n\n" in *)
(* 					       let () = if !maximal_output && !coqc_mode then buffered_output head in *)
(*  let (_, vars_case) = try List.assoc n !coq_formulas_with_numbers with Not_found ->   failwith ("generate: clause " ^ (string_of_int n) ^ " used but not registered") in *)
(* 					       let lcase = sprint_list "\n\n" (fun (n', _) -> fn_case_negdec n' vars_case) linst in *)
(* 						 head ^ lcase ^ "\n\n\n"    *)
					   | "tautology" -> 
					       let head = "\t(* TAUTOLOGY on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let lcase = "unfold fst. unfold F_" ^ (string_of_int n) ^ ".\nauto.\n" in
						 head ^ lcase ^ "\n\n\n"   
					   | "negative_clash" -> 
					       let head = "\t(* NEGATIVE CLASH on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let lcase =  "unfold fst. unfold F_" ^ (string_of_int n) ^ ". intros. try discriminate.\n" in
						 head ^ lcase ^ "\n\n\n"   
					   | "subsumption" -> 
					       let has_False s =
						 let rez = ref false in
						 let () = for i= 0 to String.length s - 6 do 
						   if compare "False" (String.sub s i 5) == 0 then rez := true
						 done 
						 in 
						   !rez
					       in
					       let head = "\t(* SUBSUMPTION on [ " ^ (string_of_int n) ^ " ] *)\n\n" in
					       let () = if !maximal_output && !coqc_mode then buffered_output head in
					       let lcase =  (if linst == [] then "auto.\n" else 
										      let (_, vars_case, _) = try List.assoc n !coq_formulas_with_numbers with Not_found ->   failwith ("fn_case: subsumed clause " ^ (string_of_int n) ^ " used but not registered") in
										      let conv_vars = ref [] in
										      let rename_vars1 = j:= 0; List.fold_right (fun (i, _) s -> let () = j := !j + 1 in s ^ (if i == 0 then ("rename u" ^ (string_of_int !j) ^ " into d_u" ^ (string_of_int !j) ^ ". ") else let () = conv_vars := i :: !conv_vars in "rename u" ^ (string_of_int !j) ^ " into _u" ^ (string_of_int i) ^ ". ")) (List.rev vars_case) "" in  
										      let rename_vars2 = List.fold_right (fun i s -> s ^ "rename _u" ^ (string_of_int i) ^ " into u" ^ (string_of_int i) ^ ". ") !conv_vars "" in
											
											
										      let (i, subst) = List.hd linst in

										      let  (c_str, lvars_case) = try List.assoc i !coq_all_lemmas with Not_found -> failwith "lemma or premise not found" in
										      let subst_str = (sprint_list " " (fun (i, _) -> if i == 0 then "" else let t = List.assoc i subst in "(u" ^ (string_of_int i) ^ " := " ^ t#compute_string_coq_with_quantifiers [] ^ ")" ) lvars_case) in
 
											rename_vars1 ^ "\n" ^ rename_vars2 ^ "\n" ^ "unfold fst. unfold F_" ^ (string_of_int n) ^ ". specialize true_" ^ (string_of_int i) ^ " with " ^ subst_str ^ "." ^ (if has_False c_str then " intro L. intros. contradict L. " else "\n") ^ "(auto || symmetry; auto).\n") 
					       in
						 head ^ lcase ^ "\n\n\n"   
					   | _ -> failwith "coq_proof : rule not yet treated"
				       in 
					 res ^ str) !coq_formulas_with_infos "" in
  let nr_args = List.fold_right (fun (_, i) n -> i + n) (List.rev !vsl) 0 in    
  let rec repeat_str str1 i str2 final sep = 
    match i with
	0 -> ""
      | n -> (repeat_str str1 (n-1) str2 final sep) ^ (if n == 1 then "" else sep) ^ str1 ^ (string_of_int n) ^ str2 ^ if n == nr_args then final else ""
  in
  let forall_str = (j:= 1; List.fold_right (fun (s, i) str -> j:= !j + i; let res = (fn_var_sort i (!j - i) "forall" s true true ", ") in str ^ (if compare str "" == 0 then "" else ", ") ^ res) (List.rev !vsl) "") in
  let main_theorem ="

(* the set of all formula instances from the proof *)
Definition S_" ^ id ^ " := fun f => exists F, In F LF_" ^ id ^ " /\\ "  ^ (repeat_str "exists e" nr_args "" "" ", ") ^ ", f = F" ^ (repeat_str " e" nr_args "" "" "") ^ ".\n\nTheorem all_true_" ^ id ^  ": forall F, In F LF_" ^  id ^ " -> " ^ forall_str ^ (if compare forall_str "" == 0 then "" else ", ") ^ "fst (F" ^ (j:= 1; List.fold_right (fun (s, i) str -> j:= !j + i; let res = (fn_var_sort i (!j - i) "" s true false " ") in str ^ res) (List.rev !vsl) "") ^ ").
Proof.
let n := constr:" ^ (string_of_int nr_args) ^ " in
let p := constr:(S(S(n))) in
intros;
let G := fresh \"G\" in
let x := fresh \"x\" in
apply wf_subset with (R:=@snd_rpo_mul Prop max_size) (S:=S_" ^ id ^ ");
[(* 1 *) apply wf_snd_rpo_mul, prec_wf
|(* 2 *) idtac
|(* 3 *) eexists; split; [ eassumption | idtac]; do_nat n ltac:(eexists); reflexivity
];

intros x G;
do_nat p ltac:(elim G; intro; clear G; intro G);
rewrite G in * |- *; clear G; clear x;
intro G;
apply main_" ^ id ^ ";
 [assumption | idtac];
intros;
apply G;
 [ idtac | assumption ];
eexists; split;
 [idtac | do_nat n ltac:(eexists); reflexivity];
assumption.
Qed.
" in
     
  let final_theorem = sprint_list "\n\n" (fun c -> 
					    let (_, vars_case, _) = try List.assoc c#number !coq_formulas_with_numbers with Not_found ->   failwith ("generate: clause " ^ (string_of_int c#number) ^ " used but not registered") in
					    let args_str = let () = j:= 0 in List.fold_right (fun (i, s) str -> "(" ^ (if i == 0 then let () = j:= !j + 1 in "_u" ^ (string_of_int !j) else ("u" ^ (string_of_int i))) ^ ": " ^ (dico_sort_string#find s) ^ ")" ^ (if compare str "" == 0 then "" else " ") ^  str) vars_case "" in
					    let args_str_orig = List.fold_right (fun (i, s) str -> (if i == 0 then "" else "(" ^ "u" ^ (string_of_int i) ^ ": " ^ (dico_sort_string#find s) ^ ")" ^ (if compare str "" == 0 then "" else " ")) ^  str) vars_case "" in
					    (* let title = "\n\nTheorem temp_" ^ (string_of_int c#number) ^ ": " ^ (if compare args_str "" == 0 then "" else "forall ") ^ args_str ^ (if compare args_str "" == 0 then "" else ", ") ^ c#compute_string_coq_with_quantifiers false ^ ".\n" in
 *)
					    let title = "\n\nTheorem true_" ^ (string_of_int c#number) ^ ": " ^ (if compare args_str "" == 0 then "" else "forall ") ^ args_str_orig ^ (if compare args_str "" == 0 then "" else ", ") ^ c#compute_string_coq_with_quantifiers false ^ ".\n" in

					    (*let assert_str = "assert (H: " ^  (if compare args_str "" == 0 then "" else "forall ") ^ args_str ^ (if compare args_str "" == 0 then "" else ", ") ^ c#compute_string_coq_with_quantifiers false ^ ").\n" in	*)    
					    let (c_case_string, vcase, _) = List.assoc c#number !coq_formulas_with_numbers in
					    let () = coq_all_lemmas := (c#number, (c_case_string, vcase)) :: !coq_all_lemmas in
					    let intro_str =  List.fold_right (fun (i, _) str -> (if i == 0 then "" else "intro. ") ^  str) vars_case "" in

						let n = (string_of_int (List.length (List.filter (fun (i,_) -> i <> 0) vars_case))) in title ^ 
"Proof.
do " ^ n ^ " intro.
apply (all_true_" ^ id ^ " F_" ^ (string_of_int c#number) ^");
 (trivial_in " ^ (string_of_int (npos 0 c_case_string !coq_formulas_with_numbers)) ^ ") ||
 (repeat constructor).
Qed.
"
					 ) !initial_conjectures in
  let print_str str =  
    let () = if !maximal_output then buffered_output str in 
    buffered_output_coq f str 
  in
  let () = flush f; print_str set_F in
(*   let () = flush f; print_str comparison_lemmas in  *)
  let () = print_str !coq_induction_schemas in
  let () = print_str lemmas in
  let () = print_str main_lemma in
  let () = print_str (lemma_proof ^ "Qed.\n\n") in
  let () = print_str main_theorem in
  let () = print_str final_theorem in
    ()
 ;;

