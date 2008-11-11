val obs_sort_counter : int ref
  class context :
    ('a Terms.concrete_term as 'b) ->
    Symbols.var ->
    object ('a)
      method all_positions : int list list
      method all_positions_w_sort : (int list * Symbols.sort) list
      method bijective_renaming :
        (Symbols.var * Symbols.var) list ->
        'a -> (Symbols.var * Symbols.var) list
      method bijective_renaming_core :
        (Symbols.var * Symbols.var) list ->
        'a -> (Symbols.var * Symbols.var) list
      method check_property : ('a -> bool) -> bool
      method private compute_basic_string : string
      method compute_string : string
      method content : 'b
      method contextual_var : Symbols.var
      method copy : 'a
      method core_ind_positions_v1 :
        (Symbols.var * Symbols.sort * bool) list ->
        ((Symbols.const * int) list * (int * Symbols.sort)) list
      method core_ind_positions_v2 :
        (Symbols.var * Symbols.sort * bool) list ->
        ((Symbols.const * int) list * 'a) list
      method defined_positions : int list list
      method def_symbols : string list
      method delpos_conditional_rewriting : int list -> unit
      method delpos_contextual_rewriting : int list -> unit
      method delpos_equational_rewriting : int list -> unit
      method delpos_partial_case_rewriting : int list -> unit
      method delpos_total_case_rewriting : int list -> unit
      method depth : int
      method depth_per_sort : (Symbols.sort * int) list
      method equal : 'a -> bool
      method equal_mod_var : 'a -> bool
      method expand_sorts : 'a
      method flatten : 'a
      method fprint : out_channel -> unit
      method get_ac_f_args : Symbols.const -> 'a list
      method has_constructor_arguments : bool
      method has_no_obs_strict_subcontext : bool
      method head : Symbols.const
      method head_n_sons : Symbols.const * 'a list
      method ind_positions_v1 :
        ((Symbols.const * int) list * (int * Symbols.sort)) list
      method ind_positions_v2 : ((Symbols.const * int) list * 'a) list
      method is_a_natural : bool
      method is_constructor_term : bool
      method is_int : bool
      method is_linear : bool
      method is_nat : bool
      method is_not_ground_reducible : bool
      method is_term : bool
      method leq : 'a -> bool
      method linear_positions : int list list
      method linear_values : (Symbols.var * Symbols.sort * bool) list
      method linear_variables :
        ((Symbols.var * Symbols.sort * bool) * int list list) list
      method matching :
        ((Symbols.var * 'a) list -> (Symbols.var * 'a) list) ->
        'a -> (Symbols.var * 'a) list
      method matching_core :
        ((Symbols.var * 'a) list -> (Symbols.var * 'a) list) ->
        (Symbols.var * 'a) list -> ('a * 'a) list -> (Symbols.var * 'a) list
      method non_linear_positions : int list list
      method non_linear_values : (Symbols.var * Symbols.sort * bool) list
      method non_linear_variables :
        ((Symbols.var * Symbols.sort * bool) * int list list) list
      method occur : Symbols.var -> bool
      method pos_conditional_rewriting : int list list
      method pos_contextual_rewriting : int list list
      method pos_equational_rewriting : int list list
      method pos_partial_case_rewriting : int list list
      method pos_total_case_rewriting : int list list
      method pprint : Format.formatter -> unit
      method rename : 'a
      method rename_core : (Symbols.var * Symbols.var) list -> 'a
      method replace_sort : Symbols.sort -> 'a
      method replace_subterm_at_pos : int list -> 'a -> 'a
      method replace_subterms : int ref -> 'a -> 'a -> 'a
      method resetpos_conditional_rewriting : unit
      method resetpos_contextual_rewriting : unit
      method resetpos_equational_rewriting : unit
      method resetpos_partial_case_rewriting : unit
      method resetpos_total_case_rewriting : unit
      method sons : 'a list
      method sort : Symbols.sort
      method sort_var_cont : Symbols.sort
      method sprint : string
      method strict_depth : int
      method strict_depth_core : int Diverse.pointer
      method strict_depth_per_sort : (Symbols.sort * int) list
      method strict_positions : int list list
      method strict_positions_w_sort : (int list * Symbols.sort) list
      method string : string
      method substitute : (Symbols.var * 'a) list -> 'a
      method subterm : 'a -> int list
      method subterm_at_position : int list -> 'a
      method subterm_matching :
        (int list -> (Symbols.var * 'a) list -> (Symbols.var * 'a) list) ->
        'a -> int list * (Symbols.var * 'a) list
      method subterm_matching_at_pos :
        ((Symbols.var * 'a) list -> (Symbols.var * 'a) list) ->
        int list -> 'a -> (Symbols.var * 'a) list
      method subterms : 'a list
      method syntactic_equal : 'a -> bool
      method term_congruence : 'a -> bool
      method treesize : int
      method update_pos : 'a
      method var_content : Symbols.var
      method variable_paths :
        ((Symbols.var * Symbols.sort * bool) * (Symbols.const * int) list)
        list
      method variable_positions : int list list
      method variable_positions_w_sort : (int list * Symbols.sort) list
      method variables : (Symbols.var * Symbols.sort * bool) list
      method vars_but_context_var : (Symbols.var * Symbols.sort * bool) list
      method vars_n_pos :
        ((Symbols.var * Symbols.sort * bool) * int list list) list
      val content : 'b
      val depth : int
      val mutable pos_conditional_rewriting : int list list
      val mutable pos_contextual_rewriting : int list list
      val mutable pos_equational_rewriting : int list list
      val mutable pos_partial_case_rewriting : int list list
      val mutable pos_total_case_rewriting : int list list
      val mutable string : string Diverse.pointer
      val mutable var_cont : Symbols.var
      val variables : (Symbols.var * Symbols.sort * bool) list
    end
