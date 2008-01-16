(*
   * Project: Spike ver 0.1
   * File: values.ml
   * Content: global values for the software
*)

let interaction_mode = ref false;;

let max_counter_augmentation = ref 1;;

let spike_version = "0.1";;

let in_a_file = ref true;;  (* Are we parsing a file (or a string) *)

let parsed_gfile = ref ("", stdin);;  (* Current parsed file *)

let linenumber = ref 1;;  (* Current line in parsed file *)

let broken_order = ref false ;; 

(* String for locating errors. Emacs's next-error compatible in caml mode *)
let file_n_line () =
  let (s, fd) = !parsed_gfile in
  match s with
    "" -> ""
  | _ -> "File \"" ^ s ^ "\", line " ^ string_of_int !linenumber ^ ": "
;;

let stop_clause = ref 0;; (* The clause to stop the proof when encountered *)

let error_message = ref "";;  (* The error message *)

let spec_file = ref "";;  (* Current specification file *)

let proof_file = ref "";;  (* Current proof file *)

let gen_proof_filename () =
  let s = Filename.basename !spec_file in
  if Filename.check_suffix s ".spike" then
    Filename.chop_suffix s ".spike" ^ ".proof"
  else s ^ ".proof"
;;

let change_proof_file_name s = proof_file := s;;

let output_verbosity = ref true;;  (* Level of output verbosity *)

let maximal_output = ref false;;
    
let indent_string = ref "";;

let incr_indent s = s := "  " ^ !s;;

let decr_indent s = s := String.sub !s 2 (String.length !s - 2);;

let rec indent_blank n = if n = 0 then "" else indent_blank (n-1) ^ " ";;

let debug_mode = ref false;;

let harvey_mode = ref false;;

let coq_mode = ref false;;

let induction_mode = ref true;;

let specif_parameterized = ref false;;

let augmentation_mode = ref false;;

let resolution_mode = ref false;;

let continue_mode = ref false;;  (* continue even if a proof fails *)

let exclude_nullary_mode = ref false;;  (* add nullary variables to induction va
riables if it is false  *)
    
let system_is_sufficiently_complete = ref false;;  (* Do we do the sufficient co
mpleteness test *)

let system_is_strongly_sufficiently_complete = ref false;;  (* Do we do the stro
ng sufficient completeness test *)

let system_is_ground_convergent = ref false;;  (* Is the system ground convergen
t ? *)

let free_constructors = ref true;;  (* Is the specification based on free constr
uctors ? *)

let boolean_specification = ref false;;  (* Do we have pure boolean specificatio
n *)

let observational_proof = ref false;;  (* Do we have pure boolean specificatio
n *)


(* Category into which we fall concerning AC symbols (Delor & Puel, RTA-93):
   - 0: no AC symbols or no other category
   - 1: all AC symbols are totally ordered
   - 2: there exists f_0 in F_AC > all other AC symbols
   - 3: g < u1 < ... < un < f, ui are unary symbols
   - 4: u < g < f, u unary
   - 5: u < l1 < l2 < ... < l(n-1) < u1 < u2 ... < ln
*)
let ac_symbols_category = ref 0;;

let dico_infs_flag = ref false;;
let list_ind_priorities = ref ([]: int list);;

(* This list contains the AC symbols in a particular order, depending on the cat
egory above:
   - 0: [] (*unused*)
   - 1: [ greatest to smallest ]
   - 2: [greatest el ; all others ]
*)
let ac_symbols_ordered = ref ([] : int list)
and unary_symbols_ordered = ref ([] : int list);;

(* We need these to speed up cases 3, 4, 5.
   Handle with care ! *)
let ac_symbol_1 = ref 0
and ac_symbol_2 = ref 0
and unary_symbol_1 = ref 0;; (* The smallest unary symbol (unused in 3) *)

(* Counters for counting application of rules *)
let contextual_rewriting_counter = ref 1;;
let equational_rewriting_counter = ref 1;;
let conditional_rewriting_counter = ref 1;;
let partial_case_rewriting_counter = ref 1;;
let total_case_rewriting_counter = ref 1;;
let generate_counter = ref 1;;
let generate_eq_counter = ref 1;;
let subsumption_counter = ref 1;;
let augmentation_counter = ref 1;;
let tautology_counter = ref 1;;
let augmentation_counter_suc = ref 1;;
let contextual_rewriting_counter_suc = ref 1;;
let equational_rewriting_counter_suc = ref 1;;
let conditional_rewriting_counter_suc = ref 1;;
let partial_case_rewriting_counter_suc = ref 1;;
let total_case_rewriting_counter_suc = ref 1;;
let generate_counter_suc = ref 1;;
let generate_eq_counter_suc = ref 1;;
let subsumption_counter_suc = ref 1;;
let tautology_counter_suc = ref 1;;

let pgoals_counter = ref 1;; (* counter to print the goals from E H L  *)

(* not yet used  *)
(* let pi_contextual_rewriting_counter = ref 1 *)
    
let depth_counter = ref 1;; (* depth of the current proof *)
let maxdepth_counter = ref 1;; (* depth of the total proof *)

(* not yet used *)
(* let subproofs_outputs = ref ([]: string list) (* ou une filo *) *)

let step_counter = ref 0;;  (* defined but not used  *)
    
let exit_code = ref 0;;

let max_lemmas = ref false;;  (* use some elements of E U H in subgoal proofs if
 true  *)


let use_order = ref true;; (* order axioms  *)


let actually_process = ref true;; (* read specification without processing conjectures if false    *)

let enable_arithmetic = ref false;; (* defined but not used  *)


let pgoals = ref false;;  (* print goals after each successful application of a 
rule if true, otherwise print goals only using strategies  *)

let print_context = ref false;; (* defined but not used  *)

let param_sort_counter = ref 0;; (* give fresh parameterized sorts to the profiles of the defined symbols *)

let normalize_flag = ref false;; (* true if we want to normalize a term *)

let ctrlc_allowed = ref true ;; (* true if CTRL-C can be captured *)
