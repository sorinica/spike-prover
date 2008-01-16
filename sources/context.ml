(*
   * Project: Spike ver 1
   * File: terms.ml
   * Content: contexts definitions
*)



open Diverse
open Io
open Dicos
open Symbols
open Terms

let obs_sort_counter = ref 0;

class context c_t   (varcont : int)  =
  object (self)
    inherit Terms.term (c_t) as base_term

    val mutable var_cont = varcont
    
 
    method contextual_var = var_cont

    method sort_var_cont = 
     let lv = base_term#variables in
     let (_,s,_) = try List.find (fun (i,_,_) -> i = self#contextual_var) lv with Not_found -> failwith "context" in
(*      match s with  *)
(* 	 Def_sort i -> i  *)
(*        | _ -> failwith "sort_var_cont" *)
     s
      
    method string = (* "[" ^ *) base_term#compute_string(*  ^ ",x" ^ string_of_int var_cont ^ "]"  *)
    
    method has_no_obs_strict_subcontext = 
      true
(*       let list_of_subterms = List.tl (self#subterms) in *)
(*       let subcontexts = List.filter (fun s -> List.mem_assoc self#contextual_var s#variables ) list_of_subterms in  *)
(*       let obs_subcontexts = List.filter (fun s -> is_obs_sort s#sort) subcontexts in *)
(*       obs_subcontexts = [] *)
    
    method vars_but_context_var = try remove_el (=) (self#contextual_var, self#sort_var_cont, true) self#variables with Failure
	"remove_el" -> failwith "vars_but_context_var"
                                                               
    method is_not_ground_reducible = true                                
  end


