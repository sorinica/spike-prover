val interaction_mode : bool ref
val max_counter_augmentation : int ref
val spike_version : string
val stop_clause : int ref
val broken_order : bool ref
val in_a_file : bool ref
val parsed_gfile : (string * in_channel) ref
val linenumber : int ref
val file_n_line : unit -> string
val error_message : string ref
val spec_file : string ref
val proof_file : string ref
val gen_proof_filename : unit -> string
val change_proof_file_name : string -> unit
val output_verbosity : bool ref
val maximal_output : bool ref
val indent_blank : int -> string
val indent_string : string ref
val incr_indent : string ref -> unit
val decr_indent : string ref -> unit
val specif_parameterized : bool ref
val debug_mode : bool ref
val harvey_mode : bool ref
val coq_mode : bool ref
val induction_mode : bool ref
val augmentation_mode : bool ref
val resolution_mode : bool ref
val continue_mode : bool ref
val exclude_nullary_mode : bool ref
val system_is_sufficiently_complete : bool ref
val system_is_strongly_sufficiently_complete : bool ref
val system_is_ground_convergent : bool ref
val free_constructors : bool ref
val boolean_specification : bool ref
val observational_proof : bool ref
val ac_symbols_category : int ref
val ac_symbols_ordered : int list ref
val unary_symbols_ordered : int list ref
val ac_symbol_1 : int ref
val ac_symbol_2 : int ref
val unary_symbol_1 : int ref
val contextual_rewriting_counter : int ref
val equational_rewriting_counter : int ref
val conditional_rewriting_counter : int ref
val partial_case_rewriting_counter : int ref
val total_case_rewriting_counter : int ref
val generate_counter : int ref
val generate_eq_counter : int ref
val subsumption_counter : int ref
val augmentation_counter : int ref
val tautology_counter : int ref
val augmentation_counter_suc : int ref
val contextual_rewriting_counter_suc : int ref
val equational_rewriting_counter_suc : int ref
val conditional_rewriting_counter_suc : int ref
val partial_case_rewriting_counter_suc : int ref
val total_case_rewriting_counter_suc : int ref
val generate_counter_suc : int ref
val generate_eq_counter_suc : int ref
val subsumption_counter_suc : int ref
val tautology_counter_suc : int ref
val pgoals_counter : int ref
(* val pi_contextual_rewriting_counter : int ref *)
val depth_counter : int ref
val maxdepth_counter : int ref
(* val subproofs_outputs : string list ref *)
val step_counter : int ref
val exit_code : int ref
val max_lemmas : bool ref
val use_order : bool ref
val actually_process : bool ref
val enable_arithmetic : bool ref
val pgoals : bool ref
val print_context : bool ref
val param_sort_counter : int ref 
val dico_infs_flag: bool ref
val list_ind_priorities: (int list) ref 
val normalize_flag : bool ref
val ctrlc_allowed : bool ref
