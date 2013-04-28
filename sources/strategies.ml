
(*
  * Project: Spike ver 0.1
   * File: strategies.ml
   * Content: Strategies
*)

open Values
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Order
open Literals
open Dummies
open Clauses
open Contextual_rewriting
open Case_rewriting
open Induction
open Generate_eq
open Induction_obs
open Decomposition_set
open Delete_set
open Eliminate_set
open Auto_simplification
open Complement
open Test_sets
open Normalize

let print_goals print_history =

  let pg = !pgoals_counter in
  let () = incr pgoals_counter in
  let () = buffered_output (!indent_string ^ "\nCurrent goals E" ^ (string_of_int pg) ^
                            " (" ^ (string_of_int conjectures_system#length) ^ "):") in
  let () = conjectures_system#print !indent_string in


  let () = buffered_output "" in
  
  let () = if print_history then
    conjectures_system#iter print_history_instance in

(*   let () =  *)
    if hypotheses_system#content <> [] then
      let () = buffered_output (!indent_string ^ "Current premises H" ^ (string_of_int pg) ^
                            " (" ^ (string_of_int hypotheses_system#length) ^ "):") in
      let () = hypotheses_system#print !indent_string in
      buffered_output ""
	
    else () 
(*   in *)
(*   let () = buffered_output "" in *)
(*   if lemmas_system#content <> [] then  *)
(*     let () = buffered_output (!indent_string ^ "\nCurrent lemmas L" ^ (string_of_int pg) ^ *)
(*     " (" ^ (string_of_int lemmas_system#length) ^ "):") in *)
(*     let () = lemmas_system#print !indent_string in *)
(*     buffered_output "" *)
(*   else () *)
    

type reasoning_module = 
    Contextual_rewriting of strategy * list_of_systems_argument * position_argument
  | Equational_rewriting of position_argument
  | Congruence_closure
  | Rewriting of bool * list_of_systems_argument * position_argument
  | Partial_case_rewriting of list_of_systems_argument * position_argument
  | Total_case_rewriting of strategy * list_of_systems_argument * position_argument
  | Generate of bool * induction_position_specification list
  | Generate_eq of bool * induction_position_specification list
  | Generate_obs of bool * induction_position_specification list
  | Positive_decomposition
  | Negative_decomposition
  | Positive_clash
  | Tautology
  | Subsumption of list_of_systems_argument
  | Augmentation of list_of_systems_argument
  | Negative_clash
  | Eliminate_redundant_literal
  | Eliminate_trivial_literal
  | Auto_simplification
  | Complement
  | Id
    
(* The rules *)
let rm_to_string = function 
    (Contextual_rewriting (st, los, pos)) ->
      "contextual_rewriting (" ^ st#string ^ ", "
      ^ (sprint_which_system_list_arg los) ^ ", "
      ^ sprint_position_argument pos ^ ")"
  |  (Equational_rewriting pos) ->
       "equational_rewriting (" ^ sprint_position_argument pos ^ ")"
  |  (Rewriting (b, sl, p)) ->
       "rewriting (" ^ (if b then "normalize" else "rewrite") ^ ", "  ^ (sprint_which_rw_system_list_arg sl) ^ ", " ^ (sprint_position_argument p) ^ ")"
  |  (Partial_case_rewriting (los, pos)) ->
       "partial_case_rewriting (" ^ (sprint_which_rw_system_list_arg los) ^ ", " ^ sprint_position_argument pos ^ ")"
  |  (Total_case_rewriting (st, los, pos)) ->
       "total_case_rewriting (" ^ st#string ^ ", "
       ^ (sprint_which_rw_system_list_arg los) ^ ", "
       ^ sprint_position_argument pos ^ ")"
  |  (Generate (b, lpos)) ->
       "generate" ^
       (match b, lpos with
	   true, [] -> ""
         | true, _ -> " (" ^ (sprint_list " ; " sprint_induction_position_specification lpos) ^ ")"
         | false, [] -> " (?)"
         | false, _ -> " (?, " ^ (sprint_list " ; " sprint_induction_position_specification lpos) ^ ")")
  |  (Generate_eq (b, lpos)) ->
       "generate_eq" ^
       (match b, lpos with
	   true, [] -> ""
         | true, _ -> " (" ^ (sprint_list " ; " sprint_induction_position_specification lpos) ^ ")"
         | false, [] -> " (?)"
         | false, _ -> " (?, " ^ (sprint_list " ; " sprint_induction_position_specification lpos) ^ ")")
  | (Generate_obs (b, lpos)) ->
      "generate_obs" ^
      (match b, lpos with
          true, [] -> ""
        | true, _ -> " (" ^ (sprint_list " ; " sprint_induction_position_specification lpos) ^ ")"
        | false, [] -> " (?)"
        | false, _ -> " (?, " ^ (sprint_list " ; " sprint_induction_position_specification lpos) ^ ")")

  | Congruence_closure -> "congruence_closure"
  |  Positive_decomposition ->
       "positive_decomposition"
  |  Negative_decomposition ->
       "negative_decomposition"
  |  Positive_clash ->
       "positive_clash"
  |  Tautology ->
       "tautology"
  |  Subsumption (los) ->
       "subsumption (" ^ (sprint_which_rw_system_list_arg los) ^ ")"
  |  Augmentation (los) ->
       "augmentation (" ^ (sprint_which_rw_system_list_arg los) ^ ")"
  |  Negative_clash ->
       "negative_clash"
  |  Eliminate_redundant_literal ->
       "eliminate_redundant_literal"
  |  Eliminate_trivial_literal ->
       "eliminate_trivial_literal"
  |  Auto_simplification ->
       "auto_simplification"
  |  Complement ->
       "complement"
  | Id -> 
      "id"

(* Types for jumps within clauses *)
type goto_type = Goto_number of int | Goto_smallest | Goto_greatest;;

(* The concrete representation of a strategy *)
type concrete_strategy =
  | Inference_rule of inference_rule
  | Series of strategy list
  | Try_ of strategy list
  | Repeat of strategy
  | Repeat_plus of strategy
  | Saturate of strategy list
  | Named_strategy of string
  | Query
  | Print_goals of bool * bool
and inference_rule =
    AddPremise of reasoning_module * strategy
  | Simplify of reasoning_module * strategy
  | Delete of reasoning_module * strategy
  | Goto of goto_type
  | Id_st of reasoning_module

let strategy_to_string st_content = 
      let fn rm = rm_to_string rm in 
      let fn1 st = st#string in
      match st_content with
	  Inference_rule (AddPremise (rm, st)) -> 
	    "add_premise(" ^ (fn rm) ^ ",[" ^ (fn1  st) ^ "])"
	| Inference_rule (Simplify (rm, st)) -> 
	    "simplify(" ^ (fn rm) ^ ",[" ^ (fn1  st) ^ "])"
	| Inference_rule (Delete (rm, st)) -> 
	    "delete(" ^ (fn rm) ^ ",[" ^ (fn1  st) ^ "])"
	| Inference_rule (Goto g) ->
            begin
              match g with
		  Goto_number n -> "goto (" ^ (string_of_int n) ^ ")"
		| Goto_smallest -> "goto (smallest)"
		| Goto_greatest -> "goto (greatest)"
            end
	| Inference_rule (Id_st rm) -> fn rm 
	| Series l ->
            "(" ^ (sprint_list ", " (fun x -> x#string) l) ^ ")"
	| Try_ l ->
            "try (" ^ (sprint_list ", " (fun x -> x#string) l) ^ ")"
	| Repeat st ->
            "repeat " ^ st#string
	| Repeat_plus st ->
            "repeat_plus " ^ st#string
	| Saturate l ->
            "saturate (" ^ (sprint_list ", " (fun x -> x#string) l) ^ ")"
	| Named_strategy s -> s
	| Query -> "?"
	| Print_goals (_, false) -> "print_goals"
	| Print_goals (_, true) -> "print_goals_history"

let apply_rm rm cxt1 cxt2 c st is_strict pp level verbose = 

  let empty_cxt = ([],[]) in 
  match rm with 
      Contextual_rewriting (st, los, pos) ->
	if cxt2 = empty_cxt then 
	  (let np = match pp with 
	      Pos_dumb -> pos 
	    | Pos_defined _ | Pos_litdefined _ | Pos_all| Pos_query -> pp 
	  in
	  try 
	    contextual_rewriting verbose st los np cxt1 c is_strict level
	  with (Failure "contextual_rewriting") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the Contextual_rewriting rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Congruence_closure ->
	if cxt2 = empty_cxt then 
	  (try
	    congruence_closure verbose c level
	  with (Failure "congruence_closure") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the Congruence_closure rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Equational_rewriting pos ->
	if cxt2 = empty_cxt then 
	  (let np = match pp with 
	      Pos_dumb -> pos 
	    | Pos_defined _ | Pos_litdefined _ | Pos_all| Pos_query -> pp 
	  in
	  try 
	    equational_rewriting verbose np cxt1 c is_strict level
	  with (Failure "equational_rewriting") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the Equational_rewriting rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Rewriting (b, sl, pos) ->
	if cxt2 = empty_cxt then 
	  (let np = match pp with 
	      Pos_dumb -> pos 
	    | Pos_defined _ | Pos_litdefined _ | Pos_all| Pos_query -> pp 
	  in
	  try 
	    rewriting verbose b sl np cxt1 c is_strict level
	  with (Failure "rewriting") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the rewriting rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Partial_case_rewriting (los, pos) ->
	if cxt2 = empty_cxt then 
	  (let np = match pp with 
	      Pos_dumb -> pos 
	    | Pos_defined _ | Pos_litdefined _ | Pos_all| Pos_query -> pp 
	  in
	  try 
	    partial_case_rewriting verbose los np cxt1 c is_strict level
	  with (Failure "partial_case_rewriting") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the Partial_case_rewriting rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Total_case_rewriting (st, los, pos) ->
(* 	if cxt2 = empty_cxt then  *)
			      (let np = match pp with 
				  Pos_dumb -> pos 
				| Pos_defined _ | Pos_litdefined _ | Pos_all| Pos_query -> pp 
			      in
			      try 
				total_case_rewriting verbose st los np cxt1 c is_strict level
			      with (Failure "total_case_rewriting") -> failwith "apply_rm")
(* 	else  *)
(* 	  failwith "apply_at_pos: the Total_case_rewriting rule is used as a first arg. of a AddPremise/Simplify/Delete rule" *)
    | Generate (_, _) ->
	if cxt2 <> empty_cxt then 
	  (try
	    generate verbose cxt1 cxt2 c is_strict 
	  with (Failure "generate") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the Generate rule cannot exist in a list of reasoning modules"
    | Generate_eq (_, _) ->
	if cxt2 <> empty_cxt then 
	  (try
	    generate_eq verbose cxt1 cxt2 c is_strict 
	  with (Failure "generate_eq") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the Generate rule cannot exist in a list of reasoning modules"
    | Generate_obs (b, lpos) ->
	if cxt2 <> empty_cxt then 
	  (try
	    generate_obs verbose b lpos c#number c  
	  with (Failure "generate_obs") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the Generate_obs rule cannot exist in a list of reasoning modules"
    | Positive_decomposition ->
	if cxt2 = empty_cxt then 
	  (try
	    positive_decomposition verbose c level
	  with (Failure "positive_decomposition") -> failwith "apply_rm")
	else 
	  failwith "apply_at_pos: the Positive_decomposition rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Negative_decomposition ->
	if cxt2 = empty_cxt then 
	  (try
	    negative_decomposition verbose c level
	  with (Failure "negative_decomposition") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Negative_decomposition rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Positive_clash ->
	if cxt2 = empty_cxt then 
	  (try
	    positive_clash verbose c level
	  with (Failure "positive_clash") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Positive_clash rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Auto_simplification ->
	if cxt2 = empty_cxt then 
	  (try
	    auto_simplification verbose c is_strict level
	  with (Failure "auto_simplification") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Auto_simplification rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Complement ->
	if cxt2 = empty_cxt then 
	  (try
	    complement verbose c is_strict level
	  with (Failure "complement") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Complement rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Tautology ->
	if cxt2 = empty_cxt then 
	  (try
	    tautology verbose c level
	  with (Failure "tautology") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Tautology rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Subsumption (los) ->
	if cxt2 = empty_cxt then 
			      (try
				subsumption verbose c los  cxt1 level
			      with (Failure "subsumption") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Subsumption rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Augmentation (los) ->
	if cxt2 = empty_cxt then 
			      (try
				augmentation verbose c los  cxt1 level
			      with (Failure "augmentation") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Augmentation rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Negative_clash ->
	if cxt2 = empty_cxt then 
			      (try 
				negative_clash verbose c level
			      with (Failure "negative_clash") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Negative_clash rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Eliminate_redundant_literal ->
	if cxt2 = empty_cxt then 
	  (try
				eliminate_redundant_literal verbose c level
	  with (Failure "eliminate_redundant_literal") -> failwith "apply_rm")
	else
	  failwith "apply_at_pos: the Eliminate_redundant_literal rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Eliminate_trivial_literal ->
	if cxt2 = empty_cxt then 
	  (try
	    eliminate_trivial_literal verbose c level
	  with (Failure "eliminate_trivial_literal") -> failwith "apply_rm")
	else
			      failwith "apply_at_pos: the Eliminate_trivial_literal rule is used as a first arg. of a AddPremise/Simplify/Delete rule"
    | Id -> 
	let e, h = (conjectures_system#content, hypotheses_system#content) in (* save *)
	if cxt2 <> empty_cxt then 
	  let brez = st#apply_new_goal verbose c cxt2 is_strict in
	  let new_goals = conjectures_system#content in 
	  let () = conjectures_system#init (List.flatten (List.map preprocess_conjecture e)) in (* restore *)
	  let () = hypotheses_system#init h in
	  if brez then new_goals else failwith "apply_rm"
	else
	  failwith "apply_at_pos: the Id cannot exist in a list of reasoning modules"

(* A wrapper class around concrete_strategy. *)

class strategy (cs: concrete_strategy) =

  object (self: 'a)

    inherit printable_object

    val content = cs

  (* pretty print function *)
    method pprint f = Format.fprintf f "@[@ Strategy: %s@]" self#string

    (* Apply a strategy. *)
    method apply verbose cxt is_strict   = self#apply_at_pos verbose Pos_dumb 0 cxt is_strict  

    (* Apply a strategy using positions *)
    method apply_at_pos verbose pp level cxt is_strict =

(*       let () = if !maximal_output then print_indent_string ((indent_blank level) ^ "Applying strategy: " ^ self#string ^ (if pp <> Pos_dumb then " at position " ^ *)
(* 	(sprint_position_argument pp) else "")) *)
(*       in *)
      
(*       let () = if !maximal_output then (print_string ("\n The current conjecture system is : \n" );  List.iter (fun x -> buffered_output x#string) conjectures_system#content) in *)
(*       let () = print_string "\n Apply_at_poss called " in *)

  (* start the computation  *)
      let res = match conjectures_system#content with
          [] -> raise Proof
	| _ ->
	    (* 	      let _ = buffered_output ("\n" ^ (indent_blank level) ^ "We will try the strategy: " ^ strategy_to_string content) in *)
	    let () =  if !interaction_mode then 
	      let () = !main_interact () in 
	      let () = interaction_mode := false in 
	      ()
	    in
            match content with
		Inference_rule r ->
		  let result phi_number phi =
		    let e_crt = new system (conjectures_system#all_but phi_number) in
		    let h_crt = hypotheses_system in
                    match r with
			AddPremise (rm, st) -> 
			  let cxt1 = (h_crt#content, e_crt#content) in
			  let cxt2 = (h_crt#content, e_crt#content @ [phi]) in
			  (
			    try 
			      (* 				let () = write_pos_clause phi in  *)
			      let l_new_conj = apply_rm rm cxt1 cxt2 phi st true  pp level verbose in
			      let _ = List.iter (fun cl -> if cl#number = !stop_clause then let () = print_detailed_position_clause cl in
			      let () = print_detailed_clause cl in
			      let () = print_history normalize cl true in  raise (MyExit "stop on clause ")) l_new_conj in
			      (* success *)
			      (* 				let () = List.iter (fun c -> write_pos_clause c) l_new_conj in  *)
			      (* 				let () = List.iter (fun c -> print_detailed_clause c) l_new_conj in  *)
			      let () = conjectures_system#replace_w_list phi_number (List.flatten (List.map preprocess_conjecture l_new_conj)) in
			      (* 				let () = if !broken_order then () else hypotheses_system#append [phi] in *)
			      true
			    with (Failure "apply_rm") -> 
			      (* 				let () = write_pos_clause phi in  *)
			      false
			  )
		      | Simplify (rm, st) ->
			  let cxt1 = ((h_crt#content @ e_crt#content), []) in
			  let cxt2 = ((h_crt#content @ e_crt#content), [phi]) in
			  (			    
			    try 
			      (* 				let () = write_pos_clause phi in  *)
			      (* 				let () = print_detailed_position_clause phi in  *)
			      let l_new_conj = apply_rm rm cxt1 cxt2 phi st false pp level verbose 
			      in (* success *)
			      let _ = List.iter (fun cl -> if cl#number = !stop_clause then let () = print_detailed_position_clause cl
			      in let () = print_detailed_clause cl in 
			      let () = print_history normalize cl true in  raise (MyExit "stop on clause ")) l_new_conj in
			      (* 				let () = List.iter (fun c -> write_pos_clause c) l_new_conj in  *)
			      (* 				let () = List.iter (fun c -> print_detailed_clause c) l_new_conj in  *)
			      (* 				let () = List.iter (fun c -> print_detailed_position_clause c) l_new_conj in  *)
			      let () = conjectures_system#replace_w_list phi_number (List.flatten (List.map preprocess_conjecture l_new_conj)) in
			      true
			    with (Failure "apply_rm") -> 	
			      (* 				let () = write_pos_clause phi in  *)
			      false
			  )
		      | Delete (rm, st) ->
			  let cxt1 = ((h_crt#content @ e_crt#content), []) in
			  let cxt2 = ((h_crt#content @ e_crt#content), [phi]) in
			  (			    
			    try 
			      (* 				let () = write_pos_clause phi in  *)
			      (* 				let () = print_detailed_position_clause phi in  *)
			      let l_new_conj = apply_rm rm cxt1 cxt2 phi st false  pp level verbose 
			      in (* success *)
			      if l_new_conj != [] then 
				  failwith ("Delete failure on " ^ (rm_to_string rm) ^ " with " ^ phi#string)
			      else
				let () = conjectures_system#replace_w_list phi_number [] in
				true
			    with (Failure "apply_rm") -> 
			      (* 				let () = write_pos_clause phi in  *)
			      false
			  )
		      | Id_st rm -> 
			  let empty_cxt = ([],[]) in 
			  let dummy_st = (new strategy (Try_ [])) in 
			  let _ = false in
			  (
			    try 
			      (* 				let () = write_pos_clause phi in  *)
			      let l_new_conj = apply_rm rm cxt empty_cxt phi dummy_st is_strict  pp level verbose
			      in (* success *)
			      (* 				let () = List.iter (fun c -> if !maximal_output then write_pos_clause c) l_new_conj in  *)
			      let () = conjectures_system#replace_w_list phi_number (List.flatten (List.map preprocess_conjecture l_new_conj)) in
			      true
			    with (Failure "apply_rm") -> 
			      (* 				let () = write_pos_clause phi in  *)
			      false
			  )
		      | Goto g ->
			  let () = assert (conjectures_system#content <> []) in 
			  match g with
			      Goto_smallest ->
				let i = list_position_smallest_el (fun y x -> clause_greater false false x y) conjectures_system#content in
				let l, l' = list_split_at_n i conjectures_system#content in
				let () = conjectures_system#init (List.flatten (List.map preprocess_conjecture (l' @ l))) in
				true
			    | Goto_greatest ->
				let i = list_position_smallest_el (clause_greater false false) conjectures_system#content in
				let l, l' = list_split_at_n i conjectures_system#content in
				let () = conjectures_system#init (List.flatten (List.map preprocess_conjecture (l' @ l))) in
				true
			    | Goto_number i ->
				try
				  let l, l' = list_split_at_n i conjectures_system#content in
				  let () = conjectures_system#init (List.flatten (List.map preprocess_conjecture (l' @ l))) in
				  true
				with (Failure "list_split_at_n") -> false 
		  in
	    	  let succes = list_exists_w_number result conjectures_system#content in
		  let () =  
		    if succes && !pgoals
		    then print_goals false
   		    else () 
		  in
	    	  succes
	      | Series l ->
                  begin
                    match l with
			[] -> true
		      | h::t ->
			  if h#apply_at_pos verbose pp (level + 1) cxt is_strict
			  then
                            let rec fn = function
				[] -> true
			      | h::t ->
				  if h#apply_at_pos verbose pp (level + 1) cxt is_strict
				  then fn t
				  else true in
                            fn t
			  else false
                  end
	      | Try_ l -> List.exists (fun x -> x#apply_at_pos verbose pp (level + 1) cxt is_strict) l 
	      | Repeat s ->
                  let rec fn () =
                    if s#apply_at_pos verbose pp (level + 1) cxt is_strict
                    then fn ()
                    else true in
                  fn ()
	      | Repeat_plus s ->
                  let rec fn () =
                    if s#apply_at_pos verbose pp (level + 1) cxt is_strict
                    then fn ()
                    else true in
                  if s#apply_at_pos verbose pp (level + 1) cxt is_strict
                  then fn ()
                  else false
	      | Saturate l ->
                  let rec fn b = function
		      [] -> b
                    | h::t ->
			let b' = h#apply_at_pos verbose pp (level + 1) cxt is_strict in
			fn (b or b') t in
                  fn false l
	      | Named_strategy s ->
                  let st =
                    try
		      dico_st#find s
                    with Not_found ->
		      let () = buffered_output ("Strategy \"" ^ s ^ "\" is not defined") in
		      raise (MyExit "strategies3")
		  in
                  st#apply_at_pos verbose pp (level + 1) cxt is_strict
	      | Query -> (!spike_parse_strategy (try dico_st#find name_strat_query with Not_found -> failwith "raising Not_found in apply_at_pos") ())#apply_at_pos verbose pp (level + 1) cxt is_strict
	      | Print_goals (_, hist) ->
                  if verbose && not !pgoals
                  then
		    let () = print_goals hist in
                    false
                    else false
      in
(*       let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "Strategy \"" ^ (strategy_to_string cs) ^ "\" is finished")  in *)
      try 
	res
      with Sys.Break -> 
	raise (MyExit "strategies4")

    (* For contextual rewriting and total case rewriting *)
    method apply_to_subgoals verbose (_: (peano_context) clause) (hyps: (peano_context) clause list) (goals: (peano_context) clause list) (is_strict: bool) =

      let e, h, l = (conjectures_system#content, hypotheses_system#content, lemmas_system#content) in
      let () = hypotheses_system#init hyps in 
      let () = conjectures_system#init (List.flatten (List.map preprocess_conjecture goals)) in
      let () = buffer_next_level () in
      let boolval =
        try self#apply verbose ([],[]) is_strict && proof_found () with
            Proof -> true
          | Refutation -> false in
      let fn c = 
	let n, p = c#content in 
	let n' = List.map (fun x -> x#update_pos) n in
	let p' = List.map (fun x -> x#update_pos) p in
	c#build n' p'
      in
      let e' = List.map fn e in
      let () = buffer_collapse_level ()
      and () = conjectures_system#init (List.flatten (List.map preprocess_conjecture e'))
      and () = lemmas_system#init l
      and () = hypotheses_system#init h in
      boolval

    (* For generate *)
    method apply_new_goal verbose (c: (peano_context) clause) cxt is_strict =
      let () = real_conjectures_system := conjectures_system#content in
      let () = conjectures_system#init [c] in (* (List.flatten (List.map preprocess_conjecture [c])) in *)
      try
        self#apply verbose cxt is_strict
      with Proof -> true
	| Refutation -> raise Refutation

    (* For generate *)
    method apply_new_goal_at_pos verbose p (c: (peano_context) clause) level cxt (is_strict: bool) =
      let () = conjectures_system#init (List.flatten (List.map preprocess_conjecture [c])) in
      try
        self#apply_at_pos verbose p (level + 1) cxt is_strict 
      with Proof -> true
	| Refutation -> false

    method compute_string = strategy_to_string content

    method fullstring =
      match content with
          Named_strategy s -> (try dico_st#find s with Not_found -> failwith "raising Not_found in fullstring")#string
	| Inference_rule _ | Series _ | Try_ _| Repeat _ | Repeat_plus _ | Saturate _ | Query  | Print_goals _ -> self#string

    method is_query =
      match content with
          Query -> true
	| Named_strategy _ | Inference_rule _ | Series _ | Try_ _| Repeat _ | Repeat_plus _ | Saturate _  | Print_goals _  -> false

  end

  (* Some predefined strategies names.
     name_strat_query, name_strat_induction_reduce are already defined *)

let name_strat_delete = "delete"
let name_strat_clean = "clean"
let name_strat_decompose = "decompose"
let name_strat_simplify = "simplify"
let name_strat_rewrite = "rewrite"
let name_strat_recursive = "recursive"
let name_strat_builtin = "builtin"
let name_strat_normalize = "normalize"

let global_strat = ref (new strategy (Named_strategy "builtin"))
let augmentation_strat = ref (new strategy (Named_strategy "builtin"))

(* The actual strategies *)
let dico_st_refill () =

  (* Query *)
  let _ = dico_st#replace name_strat_query
      (new strategy Query)

  and _ = dico_st#replace name_strat_delete
      (new strategy (Saturate [ new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st Tautology))))) ;
                                new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st (Subsumption
				  (LOS_defined [R; L]))))))) ;
                                new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st Negative_clash))))) ]))

  and _ = dico_st#replace name_strat_clean
      (new strategy (Saturate [ new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Eliminate_redundant_literal))))) ;
                                new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Eliminate_trivial_literal))))) ;
                                new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Positive_clash))))) ]))

  and _ = dico_st#replace name_strat_decompose
      (new strategy (Saturate [ new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Positive_decomposition))))) ;
                                new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Negative_decomposition))))) ]))

  and _ = dico_st#replace name_strat_simplify
      (new strategy (Saturate [ new strategy (Named_strategy "delete") ;
                                new strategy (Named_strategy "clean") ;
                                new strategy (Named_strategy "decompose") ;
                                new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Auto_simplification))))) ]))

  and _ = dico_st#replace name_strat_rewrite
      (new strategy (Try_ [ new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st (Rewriting (true, LOS_defined [R], Pos_all))))))) ;
                            new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st (Equational_rewriting Pos_all)))))) ;
                            new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st (Contextual_rewriting (new strategy (Named_strategy "recursive"),
                                                                                LOS_defined [R;C;L],
                                                                                Pos_all))))))) ;
                            new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st (Partial_case_rewriting (LOS_defined [R;L], Pos_all)))))))]))

  and _ = dico_st#replace name_strat_recursive
      (new strategy (Try_ [ new strategy (Named_strategy "delete") ;
                            new strategy (Named_strategy "rewrite") ;
                            new strategy (Inference_rule (AddPremise (Id, new strategy (Inference_rule (Id_st (Generate (true, []))))))) ]))   (*  to be modified *)

(*   and _ = dico_st#replace name_strat_builtin *)
(*       (new strategy (Repeat (new strategy (Try_ [ new strategy (Named_strategy "simplify") ; *)
(*                                                   new strategy (Named_strategy "rewrite") ; *)
(*                                                   new strategy (Print_goals false) ; *)
(*                                                   new strategy (Inference_rule (AddPremise (Id, [ (Generate (true, []))]))) ])))) *)

  and () = dico_st#replace name_strat_generate_reduce
      (new strategy (Try_ [ new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st Tautology))))) ;
                            new strategy (Named_strategy "rewrite") ])) 

  and _ = dico_st#replace name_strat_delete
      (new strategy (Saturate [ new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st Tautology))))) ;
                                new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st (Subsumption
				  (LOS_defined [R; L]))))))) ;
                                new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st Negative_clash))))) ]))

  and _ = dico_st#replace name_strat_normalize
    (new strategy (Repeat (new strategy (Try_ [   
      new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st Negative_clash))))) ;
      new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Eliminate_redundant_literal))))) ;
      new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Eliminate_trivial_literal))))) ;
      new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Positive_clash))))) ;
      new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Congruence_closure))))) ;
      new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Negative_decomposition))))) ;
      new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st Auto_simplification)))));
      new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st (Rewriting (true, LOS_defined [L;R], Pos_all))))))) ;
      new strategy (Inference_rule (Delete (Id, new strategy (Inference_rule (Id_st (Subsumption (LOS_defined [L; C]))))))) ;
      new strategy (Inference_rule (Simplify (Id, new strategy (Inference_rule (Id_st (Total_case_rewriting ( !global_strat, LOS_defined [R], Pos_all)))))))]
 ))))
  in
  ()

(* Finally, a type for tokens of the parser *)
type problem_token =
    Strat_token of (string * strategy) list
  | Conjectures_token of (peano_context) clause list
  | Hypotheses_token of (peano_context) clause list
  | Lemmas_token of (peano_context) clause list
  | Startpoint_token of strategy
  | Augmentation_token of strategy
  | Norm_token of term list
  | Cterm_token of term list
  | Rpo_token of (term * term)
  | Compare_token of (peano_context clause * peano_context clause)
  | Compare_max_token of (peano_context clause * peano_context clause)
  | Match_token of (term * term)
  | Message_token of string
  | Ac_token of (term list * term list)

let yy_queue = (Queue.create (): problem_token Queue.t)

(* Temporary *)
let yy_axioms = ref ([]: ((string * in_channel) * int * (peano_context) clause) list)
