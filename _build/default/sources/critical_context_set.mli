val critical_context_set :
  (Symbols.sort, Context.context list) Dicos.dictionary
val critical_context_set_by_var :
  (Symbols.sort, Context.context) Dicos.assoc_dictionary
val print_critical_context_set : unit -> unit
val generate_all_terms_CC0 : int -> Symbols.sort -> Terms.term list
val generate_all_terms_T0 : int -> Symbols.sort -> Terms.term list
val generate_all_contexts_CC0 : int -> Symbols.sort -> Context.context list
val generate_all_contexts_T0 : int -> Symbols.sort -> Context.context list
val instance : Context.context -> Context.context list
val is_not_ground_reducible : Context.context -> bool
val flag_crit_context : bool ref
val set_flag_crit_context : unit -> unit
val cc0 : Context.context list ref
val t0 : Context.context list ref
val stop : bool ref
val compute_critical_context_set : unit -> unit
