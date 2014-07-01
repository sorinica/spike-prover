 (*
 * Project: Spike ver 0.1
 * File: spike.ml
 * Content: symbol definitions
 *)
  
open Values
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Terms_parser
open Order
open Literals
open Dummies
open Clauses
open Test_sets
open Strategies
open Parser
open Shell
open Delete_set
open Normalize
open Smt
open Coq

let all_lemmas = ref [];;

let sprint_useful_values () =
  let f (s, c, cs) = (s ^": " ^ (string_of_int (!cs - 1)) ^ " of " ^ (string_of_int (!c - 1)) ^ " tries.") in
  let s = List.map f
      [ 
        "- tautology               " , tautology_counter, tautology_counter_suc ;
        "- rewriting               " , rewriting_counter, rewriting_counter_suc ;
        "- augmentation            " , augmentation_counter, augmentation_counter_suc ;
        "- subsumption             " , subsumption_counter, subsumption_counter_suc ;
        "- total_case_rewriting    " , total_case_rewriting_counter, total_case_rewriting_counter_suc ;
        "- generate                " , generate_counter, generate_counter_suc 
] in
  ("\n--- Global statistics of the main successful operations ---\n\n" ^ sprint_string_list "\n" s) ^ ("\n\n-----------\n  Total clauses: " ^ (string_of_int (!clause_counter - 1)) ^ "\n\n-----------\n  Total lemmas: " ^ (string_of_int ((List.length !all_lemmas) - 1)) ^ "\n\n" ^ "  Max depth    : " ^ (string_of_int !maxdepth_counter))

  (* some useful parsers  *)
let string_to_term s = 
  in_a_file := false;
  reset_yy_values ();    
  flush stdout ;
  let lexbuf = Lexing.from_string s in
  Parser.get_term Lexer.token lexbuf
;;
  
let string_to_clause s = 
    in_a_file := false;
    reset_yy_values ();    
    flush stdout ;
    let lexbuf = Lexing.from_string s in
    Parser.specif_clause2 Lexer.token lexbuf
;;

  (* CAPTURING THE Ctrl-Z  *)

(* function to be executed when Ctrl-Z happens  *)
let  interact _ = interaction_mode := true

let () =  main_interact  := fun () ->
  let str = "\n\nPlease type\n <1> --- printing the environment\n <2> --- reentering the automatic mode \n <3> --- exit\n <4> --- printing a clause \n <5> --- normalizing a term" in
  let welcome = "\n\nCtrl-Z is pressed !!! You are in the INTERACTIVE mode" in
  let error = "\nTry again !!!" in
  let rec my_read_int () = 
    try 
      read_int ()
    with 
	Failure "int_of_string" |End_of_file -> 
	  let () = buffered_output error in
	  my_read_int ()
	    
  in
  (* let () = prerr_endline welcome in *)
	
	(* disable CTRL-Z  *)
  let () = Sys.set_signal Sys.sigtstp (Sys.Signal_ignore) in
  let c = ref 0 in
	
  let () = buffered_output welcome in
  (* read and treat the char  *)
  let () = buffered_output str in
  let () = c := my_read_int () in  
  
  let () =
    while !c <> 2 do
      (match !c with
	  1 ->   let () = print_goals false in  buffered_output (sprint_useful_values ()) 
	    (* 	  | 2 -> () *)
	| 3 -> raise Sys.Break
	| 4 -> 
	    let () = buffered_output ("\nClause:") in
	    let s = read_line () in
	    (try
	      let cl =  string_to_clause s in
	      buffered_output ("\n You have provided " ^ cl#string) 
	    with Parsing.Parse_error ->
	      (match !error_message with
		  "" -> buffered_output "parse error"
		| _ -> buffered_output !error_message 
	      ))    
	| 5 -> 
	    let () = buffered_output ("\nTerm:") in
	    let s = read_line () in
	    (try
	      let t =  string_to_term s in
	      let () = buffered_output ("") in
	      let id_proc = Unix.fork () in
	      if id_proc = 0 then (* the child process does the job *)
		let () = normalize_flag := true in
		let () = interaction_mode := false in
		let lit = new literal (Lit_equal (t, t)) in
		let cl = new clause ([], [lit]) [] ("",0,([],[])) in
		(* build current state *)
		let () = conjectures_system#init ([cl#update_pos]) (fun c -> print_smt c all_conjectures_system#content rewrite_system#content) in
		let normal_strat = new Strategies.strategy (Named_strategy "normalize") in
		(* proof  *)
		let _ = 
		  try
		    let _ =  normal_strat#apply false ([],[]) false in
		    (
		      try 
			if List.length conjectures_system#content <> 1 then let _ = Unix.system ("/usr/X11R6/bin/xmessage " ^ (sprint_goals())) in ()
			else
			  let cl = List.hd conjectures_system#content in
			  let t_norm = cl#subterm_at_position (true, 0, [1]) in
			  let _ = Unix.system  ("xmessage Resulted normal form: " ^ t_norm#string)  in
			  ()
		      with Failure "subterm_at_position" -> let () = buffered_output (sprint_goals()) in ()
		    )
		  with 
		    | Refutation -> 
			try 
			  if List.length conjectures_system#content <> 1 then let _ = Unix.system ("/usr/X11R6/bin/xmessage " ^ (sprint_goals())) in ()
			  else
			    let cl = List.hd conjectures_system#content in
			    let t_norm = cl#subterm_at_position (true, 0, [1]) in
			    let _ = Unix.system  ("xmessage Resulted normal form: " ^ t_norm#string) in
			    ()
			with Failure "subterm_at_position" -> let _ = Unix.system ("/usr/X11R6/bin/xmessage " ^ (sprint_goals())) in ()
			  | _ -> let _ = Unix.system ("/usr/X11R6/bin/xmessage " ^ (sprint_goals())) in ()
		in  
		let () = interaction_mode := true in
		()
	      else
		let () = buffered_output "\nwaiting for the child" in 
		let _ = Unix.wait () in (* wait for the child to die *)
		()
	    with Parsing.Parse_error ->
	      (match !error_message with
		  "" -> buffered_output "parse error"
		| _ -> buffered_output !error_message 
	      ))
	    (* 		if !res_string <> "" then buffered_output ("\nResulted normal form: " ^ !res_string) else failwith "Normalize parent : error" *)
	    
	(* other integers  *)
	| _ -> buffered_output error   
      );
      buffered_output str;
      c := my_read_int ()
    done
  in
  let () = Sys.set_signal Sys.sigtstp (Sys.Signal_handle interact) in
  ()


(* now is time to enable CTRL-Z in the program *)
let () = Sys.set_signal Sys.sigtstp (Sys.Signal_handle interact);;

(* FINISHING CAPTURING ctrl-Z  *)


let return_code = 0

let go_parsing s =
  let infile =
    try openin s
    with Sys_error _ -> 
      raise (MyExit "spike")
  in
  try
    parsed_gfile := infile ;
    let lexbuf = Lexing.from_channel (snd infile) in
    let q = specif Lexer.token lexbuf in
    let () = if !debug_mode then (* print_dicos ()  *) () else ()  in
    q
  with Parsing.Parse_error ->
    (let () =
      match Stack.length Lexer.lexbuf_stack with
          0 -> closein infile
	| _ -> Stack.iter (fun (f, _, _) -> closein f) Lexer.lexbuf_stack in
    begin
      match !error_message with
          "" -> buffered_output ((file_n_line ()) ^ "parse error")
	| _ -> buffered_output ((file_n_line ()) ^ !error_message)
    end ;
    if !debug_mode
    then (* print_dicos () *) () 
    else () ;
    flush stdout ; exit (-1))

let reset_all () =
  let () = buffered_output "Resetting all values"

  (* Reset variables *)
  and () = sort_counter := 1 (* because we have bool *)
  and () = constructor_counter := 2 (* because we have true and false *)
  and () = function_counter := -1
  and () = greatest_var := 0
  and () = free_constructors := true
  and () = clause_counter := 0
  and () = nat_specif_defined := false
  and () = int_specif_defined := false
  and () = specif_LA_defined := false
  and () = pick_pos_codes := true
  and () = in_a_file := true
  and () = parsed_gfile := ("", stdin)
  and () = linenumber := 1
  and () = error_message := ""
  and () = spec_file := ""
  and () = proof_file := ""
  and () = indent_string := ""
  and () = system_is_sufficiently_complete := false
  and () = system_is_strongly_sufficiently_complete := false
  and () = system_is_ground_convergent := false
  and () = observational_proof := false
  and () = boolean_specification := false
  and () = ac_symbols_category := 0
  and () = ac_symbols_ordered := []
 
  and () = rpos_greater := rpo_greater

  and () = yy_axioms := []
  and () = Queue.clear yy_queue

  and () = contextual_rewriting_counter := 1
  and () = equational_rewriting_counter := 1
  and () = rewriting_counter := 1
  and () = partial_case_rewriting_counter := 1
  and () = total_case_rewriting_counter := 1
  and () = generate_counter := 1
  and () = subsumption_counter := 1
  and () = augmentation_counter := 1
  and () = tautology_counter := 1
  and () = contextual_rewriting_counter_suc := 1
  and () = equational_rewriting_counter_suc := 1
  and () = rewriting_counter_suc := 1
  and () = partial_case_rewriting_counter_suc := 1
  and () = total_case_rewriting_counter_suc := 1
  and () = generate_counter_suc := 1
  and () = tautology_counter_suc := 1
  and () = pgoals_counter := 1

  and () = step_counter := 0

  and () = depth_counter := 1
  and () = maxdepth_counter := 1

  (* Reset dicos *)
  and () = dico_order#clear
  and () = dico_equivalence#clear
  and () = dico_sort_string#clear
  and () = dico_const_string#clear
  and () = dico_const_profile#clear
  and () = dico_const_sort#clear
  and () = dico_properties#clear
  and () = dico_arities#clear
  and () = dico_sort_nullarity#clear
  and () = dico_free_constructors#clear
  and () = dico_id_status#clear
  and () = dico_ind_positions_v0#clear
  and () = dico_ind_positions_v1#clear
  and () = dico_st#clear

  and () = conjectures_system#clear
  and () = hypotheses_system#clear

  and () = reset_yy_values ()

  and () = Stack.clear buffers_stack
  and () = current_buffer := ""
  and () = sub_buffer := ""

  (* refill dicos *)
  and () = dico_st_refill ()
(*   and () = add_bool_specif () *)

  and () = enable_arithmetic := false in
  ()




(* the name of the specification to be tested  *)

let out = ref stdout;;
let out_proof = ref stdout;;

let process_problem_token = function
    Strat_token l ->
      let () = List.iter (fun (x, y) -> dico_st#replace x y) l in
      let () = print_dico_st () in
      true
  | Lemmas_token l ->
      let () = all_lemmas := generic_list_object_remove_doubles (!all_lemmas @ l) in
      let () = coq_spec_lemmas := l @ !coq_spec_lemmas in
      true
  | Startpoint_token s ->
      let () = global_strat := s in
      let () = buffered_output ("Start point is now " ^ s#string) in
      true
  | Augmentation_token s ->
      let () = augmentation_strat := s in
      let () = buffered_output ("The strategy for augmentation is " ^ s#string) in
      true
  | Hypotheses_token l ->
      let () = hypotheses_system#init l (fun c -> ()) in
      true
  | Conjectures_token l ->
      let fn c = 
	let n, p = c#content in 
	let _ = List.map (fun x -> x#update_pos) n in
	let _ = List.map (fun x -> x#update_pos) p in
	let res = c#build n p in
(* 	let () = print_dico_ind_positions_v0 () in *)
(* 	let () = print_dico_rules () in *)
	let () = if !maximal_output then print_detailed_clause res in
	res
      in
      (* let () = all_conjectures_system#append l in *)
      let () = initial_conjectures := conjectures_system#content in
      let () = lemmas_system#init !all_lemmas (fun c -> ()) in
      (* all_lemmas is updated with the proved conjectures from l *)
      let () = buffered_output   "\n************************  Proving  *************************" in
      let () = List.iter (fun x -> buffered_output x#string) (* conjectures_system#content *) l  in
      let () = buffered_output "++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++" in
      let () = 
	if !all_lemmas <> [] then 
	  let () = buffered_output "\n\nusing lemmas\n" in
	  List.iter (fun x -> buffered_output x#string) lemmas_system#content
	else () 
      in
      let () = 
	if complete_lemmas_system#content <> [] then 
	  let () = buffered_output "\n\nusing complete lemmas\n" in
	  List.iter (fun x -> buffered_output x#string) complete_lemmas_system#content
	else () 
      in
      let () = 
	if hypotheses_system#content <> [] then
	  let () = buffered_output "\n\nusing hypotheses\n " in
	  List.iter (fun x -> buffered_output x#string) hypotheses_system#content 
	else ()
      in
(*       let () = if !global_strat#string = "normalize" then normalize_flag := true else normalize_flag := false in  (* to change this line  *) *)
      let () = buffered_output "\n\nusing strategy \n"in
      let () = buffered_output (!global_strat#string  ^ (if !dracula_mode then " mixed with DRaCuLa" else ""))in
      let () = buffered_output "************************************************************" in
      let l' = List.map fn l in
      let () = conjectures_system#init (List.flatten (List.map preprocess_conjecture l')) (fun c -> print_smt c all_conjectures_system#content rewrite_system#content) in
      let b =
        try
          if !global_strat#apply true ([],[]) false && proof_found ()
          then
            let () = buffered_output "\n\nThe following initial conjectures are inductive consequences of R"
	    and () = List.iter (fun x -> buffered_output x#string) (* !initial_conjectures *) l in 
            let () = exit_code := 0 in

(* 	    let () = if !coqc_mode then *)
(* 	      let () = if !maximal_output then buffered_output  ("\n\n(\* Generating the COQ proof for the conjectures:\n\n  " ^ (sprint_list "\n  " (fun x -> x#compute_string_coq_with_quantifiers true) !initial_conjectures) ^ "\n\n*\)\n" ) in *)
(* 	      let () =  output_string !out  ("\n\n(\* Generating the COQ proof for the conjectures:\n\n  " ^ (sprint_list "\n  " (fun x -> x#compute_string_coq_with_quantifiers true) !initial_conjectures) ^ "\n\n*\)\n" ) in *)
(* 	      let () = print_coq_proof !out in *)
(* 	      (\* Initialize coq proof *\) *)
(* 	      let () = coq_formulas_with_infos := [] in *)
(* 	      let () = coq_less_clauses := [] in *)
(* 	      let () = coq_main_lemma := "" in *)
(* 	      let () = main_lemma_proof := "" in *)
(* 	      let () = coq_induction_schemas := "" in *)
(* 		()  *)
(* 	    in *)
            true
          else
            let () = buffered_output "\n\nWe failed on the initial conjectures" 
	    and () = List.iter (fun x -> buffered_output x#string; if !maximal_output then write_pos_clause x) !initial_conjectures
	    in
            let () = exit_code := 3 in
            false
        with 
	    Proof ->
              let () = buffered_output "\n\nThe following initial conjectures are inductive consequences of R"
	      and () = List.iter (fun x -> buffered_output ("\n" ^ x#string)) (* !initial_conjectures *) l in
	      let () = all_lemmas := (* list_remove_doubles (fun x y -> x#syntactic_equal y) *) (!all_lemmas @ (* !initial_conjectures *) l) in
              let () = exit_code := 0 in
	      (* Initialize coq proof *)
	    let () = if !coqc_mode then
	      let () = if !maximal_output then buffered_output  ("\n\n(* Generating the COQ proof of the conjectures:\n\n  " ^ (sprint_list "\n  " (fun x -> x#compute_string_coq_with_quantifiers true) !initial_conjectures) ^ "\n\n*)\n" ) in
	      let () = output_string !out  ("\n\n(* Generating the COQ proof of the conjectures:\n\n  " ^ (sprint_list "\n  " (fun x -> x#compute_string_coq_with_quantifiers true) !initial_conjectures) ^ "\n\n*)\n" ) in
	      let () = print_coq_proof !out_proof in
	      (* Initialize coq proof *)
	      let () = coq_formulas := [] in
	      let () = coq_formulas_with_infos := [] in
	      let () = coq_less_clauses := [] in
	      let () = coq_main_lemma := "" in
	      let () = main_lemma_proof := "" in
	      let () = coq_replacing_clauses := [] in
	      let () = coq_induction_schemas := "" in
		() 
	    in
              true
          | Refutation ->
              if !system_is_strongly_sufficiently_complete && !system_is_ground_convergent && !free_constructors
              then
                let () = buffered_output "\n\nWe have a refutation of the initial conjectures" in
		let () = List.iter (fun x -> buffered_output x#string) !initial_conjectures in
                let () = exit_code := 1 in
                false
              else
                let () = buffered_output "\n\nWe are clueless while proving the initial conjectures" 
	      	and () = List.iter (fun x -> buffered_output x#string) !initial_conjectures in
                let () = exit_code := 2 in
                false
          | Sys.Break -> 
              let () = buffered_output "\n\nUser interruption by Sys.Break" in
              let () = buffered_output "\n\n while proving the following initial conjectures"
	      and () = List.iter (fun x -> buffered_output x#string) !initial_conjectures in
	      let () = exit_code := 4 in
	      false
	  | MyExit s ->
	      let () = flush stdout in
	      let () = buffered_output ("\n\nUser interruption by MyExit with " ^ s)in
              let () = buffered_output "\n\n while proving the following initial conjectures"
	      and () = List.iter (fun x -> buffered_output x#string) !initial_conjectures in
              let () = exit_code := 4 in
              false
          | ex  ->
              let () = buffered_output ("\n\nUncaught exception: " ^ (Printexc.to_string ex)) in
              let () = buffered_output "\n\n while proving the following initial conjectures"
	      and () = List.iter (fun x -> buffered_output x#string) !initial_conjectures in
              let () = exit_code := (-1) in
              false 
      in
      let () = hypotheses_system#init [] (fun c -> ()) in
      let () = buffered_output ("Elapsed time: " ^ (string_of_float (Sys.time ())) ^ " s") in
      let () = buffered_output (sprint_useful_values ()) in
      b
  | Cterm_token l ->
      let rec fn  = function 
	  [] -> []
	| trm :: tl -> 
(* 	    let () = buffered_output ("\ntreating trm = " ^ trm#string) in *)
	    let res_tl = fn tl in
	    let res_trm = List.fold_left (fun lst c -> 
(* 	      let () = buffered_output ("\ntreating c = " ^ c#string) in *)
	      let res = 
		try 
		  let lhs = c#lefthand_side in
		  let _ =  lhs#matching (fun s -> s) trm in
		  (try
		    let c' = c#orient in
		    [c']
		  with (Failure "orient") ->
		    match (List.hd c#positive_lits)#content with
			Lit_equal _ 
		      | Lit_rule _ -> 
      			  let c' = c#force_orientation in
			  let () = buffered_output ("\t" ^ c'#string) in
			  (* let () = broken_order := true in  *)
			  let () = buffered_output ("\nWARNING: the lemma [" ^ (string_of_int c#number) ^ "] is not orientable in a rewrite rule using the current order") in
			  [c']
		      | Lit_diff _ -> parse_failwith ("The lemma [" ^ (string_of_int c#number) ^ "] is not orientable") 
		  )
		with Not_Horn | (Failure "matching") -> []
	      in
	      res @ lst
	    ) [] !all_lemmas
	    in 
	    res_trm @ res_tl
      in
      let old_content = complete_lemmas_system#content in
      let () = complete_lemmas_system#init (old_content @ (fn l)) (fun c -> ()) in 
      true
  | Norm_token l ->
      let f t =
        let () = buffered_output ("\nNormalizing ONLY with unconditional rules: " ^ t#string) in
	let c_dummy = List.hd rewrite_system#content in
        let _, str, t', _ = normalize_plus [R;L] t c_dummy "" ([],[]) 0 in
        buffered_output ("\n" ^  t'#string ^ " is the normal form of " ^ t#string ^ (if str = "" then "" else " obtained by the following operations :" ^ str)) in
      let () = List.iter f l in 
      true
  | Rpo_token (t, t') ->
      let () = buffered_output "Comparing \n" in
      let () = buffered_output ("t  = " ^ t#string)
      and () = buffered_output ("t' = " ^ t'#string) in
      let s =
	if rpo_equivalent t t' then "t ~ t'"
	else 
	  if rpo_greater false t t' then "t > t'"
	  else if rpo_greater false t' t then "t < t'"
	  else "t and t' are not comparable" in
      let () = buffered_output s in
	true
  | Compare_token (c, c') ->
      let () = buffered_output ("c  = " ^ c#string)
      and () = buffered_output ("c' = " ^ c'#string) in
      let s =
	if clause_equiv false false c c' then "c ~ c'"
	else if clause_greater false false c c' then "c > c'"
	else if clause_greater false false c' c then "c < c'"
	else "c and c' are not comparable" in
      let () = buffered_output s in
      true 
  | Compare_max_token (c, c') ->
      let () = buffered_output ("c  = " ^ c#string)
      and () = buffered_output ("c' = " ^ c'#string) in
      let s =
	if clause_equiv true false c c' then "c ~ c'"
	else if clause_greater true false c c' then "c > c'"
	else if clause_greater true false c' c then "c < c'"
	else "c and c' are not comparable" in
      let () = buffered_output s in
      true 
  | Match_token (t, t') ->
      let () = buffered_output ("t  = " ^ t#string)
      and () = buffered_output ("t' = " ^ t'#string) in
      let () = 
	try 
	  let pos, subst = 
	    t#subterm_matching (fun _ s -> s) t' in
	  buffered_output 
	    ("the substitution " ^  sprint_subst subst ^ " applied to (" ^ t#string ^ ") " ^ " gives (" ^
	    t'#string ^ ") at the position " ^ (sprint_position pos) ) 
      with Failure "matching" -> 
	buffered_output ("no matching")
     in
      let () = buffered_output ("################################################################################") in
      true
  | Message_token s ->
      let () = buffered_output s
      in true
  | Ac_token (_, _) ->
(*       let () = buffered_output ("l  = " ^ (sprint_list " ; " (fun x -> x#string) l)) *)
(*       and () = buffered_output ("l' = " ^ (sprint_list " ; " (fun x -> x#string) l')) in *)
(*       let sigma = subsumes (fun s -> s) (fun proceed_fun s y z -> y#matching_core proceed_fun s [ (z, y) ]) [] l l' *)
(*       in let _ = print_endline ("subsumption sigma = " ^ (sprint_subst sigma)) *)
(*       in *) 
      true
	   
let specif_counter = ref 0
  
  
(* ;  *)
(*   !print_dico_test_set ()   *) 

let mainloop s =

 let () = reset_all () in
 let () = incr specif_counter in
 let () = global_strat := new Strategies.strategy (Named_strategy "builtin") in
 let q = go_parsing s in
 let () = print_context := true in
 let () = rewrite_system#compute_induction_positions_v0 in
 let () = if !debug_mode then print_dico_ind_positions_v0 () in
 let () = update_dico_rules () in
 let () = if !dracula_mode then 
   let () = if !coqc_spec_mode then let () = buffered_output "\n\n *** -coqc_spec option is incompatible with the Dracula strategy ***\n" in coqc_spec_mode := false in
   let () = if !coqc_mode then  let () = buffered_output "\n\n *** -coqc option is incompatible with the Dracula strategy ***\n" in coqc_mode := false in
()
 in
 if  not !Sys.interactive then
   let () =
     if !actually_process
     then
       let () = if !coqc_mode then
	 let () =  out_proof := open_out (!spec_name ^ ".v")  in
	 let () = output_string !out_proof ("\nRequire Import " ^ !spec_name ^ "_spec.\n\n") in
	   ()
       in 
   let () = if !coqc_spec_mode then
     let () = out := open_out (!spec_name ^ "_spec.v") in 
     let () = buffered_output ("\n\n(* Generating the COQ specification in " ^ !spec_name ^ ".v file *)\n") in
     let () = print_coq_specification !out in
     let () = if !maximal_output && !coqc_mode then buffered_output "********* Output of Coq (using Coccinelle) proof **********" in
     ()
   in
       let () = buffered_output (
         "\n\n************************************************************\n" ^
           "******************* Starting computation *******************\n" ^
           "************************************************************\n\n") in
         if queue_forall process_problem_token q
         then buffered_output ("\n\nAll sets of conjectures were successfully processed\n\n")
         else buffered_output ("\n\nWe failed\n\n")
     else ()
   in
   (* let () = if !smt_mode then print_smt s else () in *)
   let () = if !coqc_mode then close_out !out in
     ()
 else ()


let usage_string = "Usage: " ^ Sys.argv.(0) ^ " [options] spec_file [[options] spec_file...]\nOptions may be:"
  
let rec speclist =
  [
    ("-augment", Arg.Set augmentation_mode, ": use augmentation with LA and CC") ;
    ("-coqc_spec", Arg.Set coqc_spec_mode, ": generates the CoQ specification using Coccinelle") ;
    ("-coqc", Arg.Set coqc_mode, ": output a one-to-one CoQ proof using Coccinelle") ;
    ("-dracula", Arg.Set dracula_mode, ": D-proof mode") ;
    ("-debug", Arg.Set debug_mode, ": debug mode") ;
    ("-exclude_nullary", Arg.Set exclude_nullary_mode, ": don't add nullary variables to induction variables") ;
    ("-smt", Arg.String (fun s -> let _ =  smt_mode:= true in z3_path := s), ": requires the path for the Z3 SMT solver for specifications including `use'. The specification format for z3 is smt2.") ;
    ("-help", Arg.Unit (fun () -> let () = Arg.usage speclist usage_string in incr specif_counter), ": print this message") ;
    ("-include_nullary", Arg.Clear exclude_nullary_mode, ": add nullary variables to induction variables (default)") ;
    ("-k", Arg.Set continue_mode, ": continue even if a proof fails") ;
    ("-max_lemmas", Arg.Set max_lemmas, ": use some elements of E U H in subgoal proofs") ;
    ("-maximal", Arg.Set maximal_output, ": print a lot of annoying information") ;
    ("-min_lemmas", Arg.Clear max_lemmas, ": use no element of E U H in subgoal proofs (default)") ;
    ("-n", Arg.Clear actually_process, ": read specification without processing conjectures") ;
    ("-noinduction", Arg.Clear induction_mode, ": does not perform implicit induction") ;
    ("-noorder", Arg.Clear use_order, ": don't order lemmas") ;
    ("-nopgoals", Arg.Clear pgoals, ": print goals only using strategies") ;
    ("-order", Arg.Set use_order, ": order axioms (default)") ;
    ("-param", Arg.Set specif_parameterized, ": use it whenever the specification is parameterized") ;
    ("-pgoals", Arg.Set pgoals, ": print goals after each successful application of a rule") ;
    ("-resolution", Arg.Set resolution_mode, ": use resolution") ;
    ("-Rmaxs0", Arg.Set specif_Rmaxs0_defined, ": use the decision procedure Rmaxs0 for naturals. Works with `use: nats'") ;
    ("-Rmins0", Arg.Set specif_Rmins0_defined, ": use the decision procedure Rmins0 for naturals. Works with `use: nats'") ;
    ("-Rmps0", Arg.Set specif_Rmps0_defined, ": use the decision procedure Rmps0 for naturals. Works with `use: nats'") ;
    ("-Rzmm", Arg.Set specif_Rzmm_defined, ": use the decision procedure Rzmm for naturals. Works with `use: nats'") ;
    ("-Rnatlist", Arg.Set specif_Rnatlist_defined, ": use the decision procedure Rnatlist for naturals. Works with `use: nats'") ;
    ("-silent", Arg.Clear output_verbosity, ": select minimal output") ;
    ("-status", Arg.String change_default_status, ": default status for functions (LR | RL | MS)") ;
    ("-verbose", Arg.Set output_verbosity, ": select verbose output (default)") ;
    ("-version", Arg.Unit (fun () -> let () = print_endline spike_version in incr specif_counter), ": display version of this software")
  ]
  
let main () =
  Arg.parse speclist mainloop usage_string
      
let _ = main ()
  
let () =
  if !specif_counter = 0
  then Arg.usage speclist usage_string
  else ()
    

let _ = if not !Sys.interactive then exit !exit_code
  

