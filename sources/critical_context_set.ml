(*
  * Project: Spike ver 0.1
  * File: critical_context.ml
  * 
  * Content: critical context sets
*)



open Diverse
open Io
open Dicos
open Symbols
open Terms
open Context
open Clauses
open Test_sets

(* critical_context_set by sort of the head *)
let critical_context_set = (new Dicos.dictionary 101 : (sort, context list) dictionary) 

(* critical_context_set by sort of the contextual var *)
let critical_context_set_by_var = (new Dicos.assoc_dictionary 101 : (sort, context) assoc_dictionary)

(* print critical_context_set *)
let print_critical_context_set () =
  
  let rec f s l = try buffered_output ((dico_sort_string#find s) ^ " [" ^ (sprint_sort s) ^ "]\n" ^
                                   (sprint_list "\n" (fun x -> "\t" ^ x#string) l)) with Not_found -> failwith "raising Not_found
in print_critical_context_set" in
  let () = buffered_output "critical_context_set =" in
  critical_context_set#iter f

(* generate all terms to depth d of sort s *) 
let generate_all_terms_CC0 d s = 
  let rec fn i s =
    if i = d
    then
      if is_nullary_sort s
      then 
        let l = try List.filter is_constructor (dico_const_profile#find_keys [s]) with Not_found -> [] in
        match l with
          [] -> [ new term (Var_univ (newvar (), s)) ]
        | _ -> List.map (fun x -> new term (Term (x, [], s))) l
      else 
            [ new term (Var_univ (newvar (), s)) ]   
    else (* i <> d *)
      
      let l = try (dico_const_sort#find_keys s) with Not_found -> [] in
      [ new term (Var_univ (newvar (), s)) ] @  List.flatten (List.map (fn2 i s) l)
  and fn2 i s f =
    let profile = try (dico_const_profile#find f) with Not_found -> failwith "generate_all_terms_CC0" in
    let p = List.tl profile in
         
        let args = List.map (fn (i + 1)) p in
        let sets_of_args = megamix args in
        List.map (fun l -> new term (Term (f, l, s))) sets_of_args in
   if d = 0
  then []
  else fn 1 s

(* generate all terms to depth d of sort s having all variables at depth d *) 
let generate_all_terms_T0 d s =
let rec fn i s =
    if i = d
    then
      if is_nullary_sort s then
      
        let l = try List.filter is_constructor (dico_const_profile#find_keys [s]) with Not_found -> [] in
        match l with
          [] -> [ new term (Var_univ (newvar (), s)) ]
        | _ -> List.map (fun x -> new term (Term (x, [], s))) l
      else  
            [ new term (Var_univ (newvar (), s)) ]   
    else (* i <> d *)
      let l = try (dico_const_sort#find_keys s) with Not_found -> [] in
      List.flatten (List.map (fn2 i s) l)
  and fn2 i s f =
    let p = List.tl (try dico_const_profile#find f with Not_found -> failwith "raising Not_found in generate_all_terms_T0") in
        let args = List.map (fn (i + 1)) p in
        let sets_of_args = megamix args in
        List.map (fun l -> new term (Term (f, l, s))) sets_of_args in
   if d = 0
  then []
  else fn 1 s

(* generate all contexts to depth d of sort s *)
let generate_all_contexts_CC0 d s = 
 let generate_contexts_from_term t = List.map (fun (v,_,_) -> new context t#content v) t#variables in
 List.flatten (List.map generate_contexts_from_term (generate_all_terms_CC0 d s ))

(* generate all contexts to depth d of sort s having all variables at depth d *) 
let generate_all_contexts_T0 d s = 
 let generate_contexts_from_term t = List.map (fun (v,_,_) -> new context t#content v) t#variables in
 List.flatten (List.map generate_contexts_from_term (generate_all_terms_T0 d s ))

(* all instances of a context by terms of test set, the contextual var is not instanciated *)
let instance (c : context) = 
  let sort_list = List.map (fun (_,x,_) -> x) ((c#vars_but_context_var)) in
  let term_list_list = List.map (fun s -> try dico_test_set_v0#find s with Not_found -> failwith "instance") sort_list in
  let term_list = megamix term_list_list in
  let subs_list = List.map (fun tl -> List.combine (List.map (fun (x,_,_) -> x) c#vars_but_context_var) tl ) term_list in
  let context_one_var = if sort_list = [] then [c] else []  in 
  context_one_var @  List.map (fun sub -> c#substitute sub) subs_list



(* quasi ground reducibility test *)
let is_not_ground_reducible (c : context) = 

      if List.length(c#variables) = 1 then (*true*) 
      (List.for_all (fun lhs -> if lhs#variables = [] then true 
         else let sigma = ref [] in 
               let () = try 
               sigma := (c#matching (fun x -> x) lhs ) 
               with _-> () in
               (!sigma = [])
                ) rewrite_system#lefthand_sides)
      else
        let all_instance = instance c in
        let all_instance_and_sub = List.flatten(List.map (fun i -> i#subterms ) all_instance) in
        let sigmas = ref [] in
        let () = (List.iter (fun inst -> (List.iter(fun lhs -> try sigmas := !sigmas @ (inst#matching (fun x-> x) lhs ) with _-> () )  rewrite_system#lefthand_sides)         ) all_instance_and_sub )in
        !sigmas = []

let flag_crit_context = ref false

let set_flag_crit_context () = (flag_crit_context := true)

let cc0 = ref []
let t0 = ref [] 
let stop = ref false 

(* compute all critical contexts *) 
let compute_critical_context_set () =
  

if not !flag_crit_context then
begin
  let () = buffered_output "Computing critical contexts" in
(* initializing cc0 *)
  let fn _ n = 
    let s1 = try dico_sort_string#find_key n with Failure _ -> failwith "compute_critical context0" in
    let all_CC0 = generate_all_contexts_CC0 (Clauses.rewrite_system#depth - 1)  s1   in
    let all_CC0_wo_obs_subcont = List.filter (fun c -> c#has_no_obs_strict_subcontext) all_CC0 in
    cc0 := (!cc0) @  (List.filter (fun c -> is_not_ground_reducible c)  all_CC0_wo_obs_subcont) 
  in
  let () = dico_obs_sort#iter fn in
  let () = buffered_output "CC0 =" in
  List.iter (fun x -> buffered_output (x#string) )  (!cc0);

(* initializing t0 *)
    let fn1 s n =
      try let _ = dico_obs_sort#find  s in () 
      with Not_found ->
	let s1 = try dico_sort_string#find_key n with Failure _ -> failwith "compute_critical context1" in
	let all_T0 = generate_all_contexts_T0 (Clauses.rewrite_system#depth - 1) s1  in 
	let all_T0_wo_obs_subcont = List.filter (fun c -> c#has_no_obs_strict_subcontext ) all_T0 in 
	t0 := !t0 @ (List.filter (fun c -> is_not_ground_reducible c ) (all_T0_wo_obs_subcont)) 
    in
    let () = dico_sort_string#iter fn1 in
    let () = buffered_output "T0 =" in
    let () = List.iter (fun x -> buffered_output (x#string) )  (!t0) in
  
   
(* main loop *)   
   while not(!stop) do
        let set_to_add_remove = ref ([],[]) in
        let _ = ref [] in
        let _ = ref [] in
       
        let verify cont = 
            let exists = ref false in
            let () = List.iter (fun cobs -> 
            if (cobs#sort_var_cont = cont#sort) then
               let newcont = (new context ((cobs#substitute [(cobs#contextual_var,cont)])#content) (cont#contextual_var)) in
               if (is_not_ground_reducible newcont )
               then let () = buffered_output (" " ^  newcont#string ^ " is not quasi ground reducible") in exists:= true) (!cc0) in (!exists) in
          
        set_to_add_remove := List.partition (fun c -> verify c) (!t0);
        cc0 := (!cc0) @ (fst(!set_to_add_remove));
        t0  := snd(!set_to_add_remove); 
        stop := (List.length(fst(!set_to_add_remove)) = 0)
   done;
    let fn2 x = 
      let () = critical_context_set_by_var#add (x#sort_var_cont) x in
      let cxt_x =  
	let old = ref [] in 
	let () = try 
	  old := critical_context_set#find x#sort 
	with Not_found -> () 
	in !old 
      in
      critical_context_set#replace x#sort (cxt_x @ [x])
    in
    let () =  List.iter fn2 (!cc0) in
    print_critical_context_set ()
end








