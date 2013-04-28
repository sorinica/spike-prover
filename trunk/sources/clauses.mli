val fn_for_capital_d : ('a * int) list -> ('a * int) list -> ('a * int) list
exception Proof
exception Refutation
exception MyExit of string
val sprint_lemmas : unit -> string
val sprint_axioms : unit -> string
val sprint_goals : unit -> string
val sprint_hypotheses : unit -> string
exception Not_Horn
type concrete_peano_literal =
  | Peano_equal of Terms.ground_term * Terms.ground_term
  | Peano_diff of Terms.ground_term * Terms.ground_term
  | Peano_less of Terms.ground_term * Terms.ground_term
  | Peano_leq of Terms.ground_term * Terms.ground_term
val peano_members :
  concrete_peano_literal -> Terms.ground_term * Terms.ground_term
val is_peano_equal : concrete_peano_literal -> bool
val is_peano_diff : concrete_peano_literal -> bool
val is_peano_less : concrete_peano_literal -> bool
val is_peano_leq : concrete_peano_literal -> bool
  class peano_literal :
    concrete_peano_literal ->
    object
      val content : concrete_peano_literal
      val mutable is_pi : bool Diverse.pointer
      val mutable string : string Diverse.pointer
      val variables : (Symbols.var * Symbols.sort * bool) list
      method both_sides : Terms.ground_term * Terms.ground_term
      method compute_pi : bool
      method compute_string : string
      method content : concrete_peano_literal
      method fprint : out_channel -> unit
      method is_pi : bool
      method is_subterm : Terms.term -> bool
      method members : Terms.ground_term * Terms.ground_term
      method pprint : Format.formatter -> unit
      method sprint : string
      method string : string
      method syntactic_equal : peano_literal -> bool
    end
val linearize : peano_literal -> Polynoms.polynom list list
val literalize : Polynoms.polynom -> peano_literal
val peano_literal_tautology : peano_literal
val normal_form : peano_literal list -> Terms.ground_term -> Terms.ground_term
val critical_pairs :
  peano_literal list ->
  Terms.ground_term ->
  Terms.ground_term -> (Terms.ground_term * Terms.ground_term) list
val invert_literal : Literals.literal -> peano_literal
val convert_literal : Literals.literal -> peano_literal
val inconsistent : peano_literal list -> peano_literal list -> bool
val reduces : Terms.ground_term -> Terms.ground_term -> bool
val implicit_equations : Polynoms.polynom list -> peano_literal list
val apply_la :
  Polynoms.polynom list ->
      Polynoms.polynom list * peano_literal list
val normalize_cx_l :
  Polynoms.polynom list list * 'a -> peano_literal list -> Polynoms.polynom list list * 'a
val apply_cc : peano_literal list -> peano_literal list ->
  peano_literal list
val normalize_lit :
  peano_literal list ->
  < content : concrete_peano_literal; .. > -> peano_literal 
type rule = Augment_L | Augment_G | A2L | A2G | L2G | G2CR
  class peano_context :
    Literals.literal list ->
    Literals.literal list ->
    peano_literal list ->
    peano_literal list ->
    Polynoms.polynom list list * peano_literal list ->
    object
      val mutable cx_a : peano_literal list
      val mutable cx_cr : peano_literal list
      val mutable cx_g : peano_literal list
      val mutable cx_l : Polynoms.polynom list list * peano_literal list
      val mutable string : string Diverse.pointer
      method a_2_g : rule list
      method a_2_l : rule list
      method apply_la :
        Polynoms.polynom list -> Polynoms.polynom list * peano_literal list
      method augment_g : rule list
      method augment_l :
        int -> Literals.literal list * Literals.literal list -> rule list
      method check_inconsistencies :
        int -> Literals.literal list * Literals.literal list -> unit
      method compute_string : string
      method cx_a : peano_literal list
      method cx_cr : peano_literal list
      method cx_g : peano_literal list
      method cx_ie : peano_literal list
      method cx_l : Polynoms.polynom list list * peano_literal list
      method cx_p : Polynoms.polynom list list
      method fprint : out_channel -> unit
      method g_2_cr : rule list
      method l_2_g : rule list
      method pprint : Format.formatter -> unit
      method sprint : string
      method string : string
    end
  class ['a] clause :
    Literals.literal list * Literals.literal list ->
    (((Symbols.var * Terms.term) list * 'b as 'd) list as 'c) ->
				      string * int * (Literals.literal list * Literals.literal list ) ->
    object ('b)
      constraint 'a = peano_context
      val mutable augmentation_failure : int list
      val mutable augmentation_literals : Literals.literal list
      val card : int
      val content : Literals.literal list * Literals.literal list
      val mutable history : 'c
      val mutable standby: bool
      val mutable delete_standby: bool
      val mutable sb_string: string
      val mutable sb_newconjs: 'b list
      val mutable sb_IHs: ('b *  (Symbols.var * Terms.term) list) list
      val mutable broken_info: string * int * (Literals.literal list * Literals.literal list)
      val mutable inference_bitstream : int
      val is_horn : bool
      val mutable maximal_terms : Terms.ground_term list Diverse.pointer
      val neg_card : int
      val number : int
      val mutable oriented : bool Diverse.pointer
      val mutable peano_context : 'a Diverse.pointer
      val pos_card : int
      val mutable string : string Diverse.pointer
      val mutable subsumption_failure : int list
      val variables : (Symbols.var * Symbols.sort * bool) list
      method add_augmentation : Literals.literal -> unit
      method add_failed_augmentation : int -> unit
      method add_failed_subsumption : int -> unit
      method get_broken_info: string * int * (Literals.literal list * Literals.literal list )
      method set_broken_info: string * int * (Literals.literal list * Literals.literal list ) -> unit
      method add_history : 'd -> unit
      method all_maximal_terms : bool -> Terms.ground_term list
      method all_neg_terms : Terms.term list
      method all_pos_terms : Terms.term list
      method all_terms : Terms.term list
      method apply_to_clause : (Literals.literal -> Literals.literal) -> 'b
      method augmentation_has_failed : int -> bool
      method augmentation_literals : Literals.literal list
      method bijective_renaming :
        (Symbols.var * Symbols.var) list ->
        'b -> (Symbols.var * Symbols.var) list
      method both_sides : Terms.term * Terms.term
      method build : Literals.literal list -> Literals.literal list -> 'b
      method build_best_context : bool -> int -> Literals.literal list
      method cachedstring : string
      method cardinal : int
      method compute_peano_context : 'a
      method compute_string : string
      method compute_string_coq_with_quantifiers : bool -> string
      method compute_string_coq_for_order : bool -> string
      method conditions : Literals.literal list
      method content : Literals.literal list * Literals.literal list
      method copy : 'b
      method depth : int
      method def_symbols : string list
      method equal : 'b -> bool
      method expand : 'b
      method expand_sorts : 'b
      method fill_peano_context : unit
      method flatten : 'b
      method force_orientation : 'b
      method fprint : out_channel -> unit
      method greatest_varcode : int
      method has_bit : int -> bool
      method history : 'c
      method delete_standby: bool
      method standby: bool
      method sb_string: string 
      method sb_newconjs: 'b list
      method sb_IHs: ('b *  (Symbols.var * Terms.term) list) list
      method is_boolean : bool
      method is_empty : bool
      method is_horn : bool
      method is_left_linear : bool
      method is_non_empty : bool
      method is_subterm : Terms.term -> bool * int * int list
      method is_unit : bool
      method l_2_r : Literals.literal
      method lefthand_side : Terms.term
      method head : Literals.literal
      method lit_at_position : bool * int -> Literals.literal
      method negative_cardinal : int
      method negative_lits : Literals.literal list
      method number : int
      method orient : 'b
      method orientable : bool
      method oriented : bool
      method peano_context : 'a
      method positive_cardinal : int
      method positive_lits : Literals.literal list
      method pprint : Format.formatter -> unit
      method rename : 'b
      method rename_from_zero : 'b
      method replace_subterm_at_pos :
        bool * int * int list -> Terms.term -> 'b
      method righthand_side : Terms.term
      method set_bit : int -> unit
      method set_history : 'c -> unit
      method set_standby: bool -> unit
      method set_delete_standby: bool -> unit
      method set_sb_string: string -> unit
      method set_sb_newconjs: 'b list -> unit
      method set_sb_IHs: ('b *  (Symbols.var * Terms.term) list) list -> unit
      method sprint : string
      method string : string
      method substitute : (Symbols.var * Terms.term) list -> 'b
      method substitute_and_rename :
        (Symbols.var * Terms.term) list -> int -> 'b *  (Symbols.var * Terms.term) list
      method subsumption_has_failed : int -> bool
      method subterm_at_position : bool * int * int list -> Terms.term
      method subterm_matching :
        (bool * int * int list ->
         (Symbols.var * Terms.term) list ->
         bool -> (Symbols.var * Terms.term) list) ->
        Literals.literal ->
        (bool * int * int list) * (Symbols.var * Terms.term) list * bool
      method subterm_matching_at_pos :
        ((Symbols.var * Terms.term) list ->
         bool -> (Symbols.var * Terms.term) list) ->
        bool * int * int list ->
        Literals.literal -> (Symbols.var * Terms.term) list * bool
      method swap_rule : 'b
      method syntactic_equal : 'b -> bool
      method try_on_boolean_horn_variants : ('b -> bool) -> bool
      method try_to_orient : 'b
      method update_pos : 'b
      method variables : (Symbols.var * Symbols.sort * bool) list
    end
val preprocess_conjecture : 'a clause -> 'a clause list
  class ['a] system :
    'a list ->
    object ('b)
      method all_but : int -> 'a list
      method append : 'a list -> unit
      method clear : unit
      method content : 'a list
      method copy : 'b
      method current_el : 'a
      method exists : ('a -> bool) -> bool
      method init : 'a list -> unit
      method is_empty : bool
      method iter : ('a -> unit) -> unit
      method ith : int -> 'a
      method length : int
      method print : string -> unit
      method replace : int -> 'a -> unit
      method replace_w_list : int -> 'a list -> unit
      method sprint_numbers : string
      val mutable content : 'a list
      constraint 'a =
        < build : (< both_sides : (< syntactic_equal : 'd -> bool; .. > as 'd) *
                                  'd;
                     is_diff : bool; syntactic_equal : 'c -> bool; .. > as 'c)
                  list ->
                  (< syntactic_equal : 'e -> bool; .. > as 'e) list -> 'a;
          content : 'c list * 'e list; equal : 'a -> bool;
          fill_peano_context : unit; number : int; string : string;
          syntactic_equal : 'a -> bool; .. >
    end
  class ['a] l_system :
    'a list ->
    object ('b)
      method all_but : int -> 'a list
      method append : 'a list -> unit
      method clear : unit
      method content : 'a list
      method copy : 'b
      method current_el : 'a
      method exists : ('a -> bool) -> bool
      method init : 'a list -> unit
      method is_empty : bool
      method iter : ('a -> unit) -> unit
      method ith : int -> 'a
      method length : int
      method print : string -> unit
      method replace : int -> 'a -> unit
      method replace_w_list : int -> 'a list -> unit
      method sprint_numbers : string
      val mutable content : 'a list
      constraint 'a =
        < build : (< both_sides : (< syntactic_equal : 'd -> bool; .. > as 'd) *
                                  'd;
                     is_diff : bool; syntactic_equal : 'c -> bool; .. > as 'c)
                  list ->
                  (< syntactic_equal : 'e -> bool; .. > as 'e) list -> 'a;
          content : 'c list * 'e list; equal : 'a -> bool;
          fill_peano_context : unit; number : int; rename_from_zero : 'a;
          string : string; syntactic_equal : 'a -> bool; try_to_orient : 'a;
          .. >
    end
class ['a] rw_system :
  'a list ->
  object
    constraint 'a =
      < is_left_linear : bool; lefthand_side : Terms.term; string : string;
        .. >
    val mutable content : 'a list
    method capital_d : int
    method capital_d_per_sort : (Symbols.sort * int) list
    method compute_induction_positions_v0 : unit
    method compute_induction_positions_v1 : unit
    method content : 'a list
    method depth : int
    method depth_per_sort : (Symbols.sort * int) list
    method exists : ('a -> bool) -> bool
    method init : 'a list -> unit
    method is_left_linear : bool
    method iter : ('a -> unit) -> unit
    method ith : int -> 'a
    method lefthand_sides : Terms.term list
    method minus : int -> 'a rw_system
    method strict_depth : int
    method strict_depth_per_sort : (Symbols.sort * int) list
    method string : string
  end
val orient_clause : < orient : 'a; .. > -> 'a
val try_to_orient_clause : peano_context clause -> peano_context clause
val print_clause_list : < string : string; .. > list -> unit
type which_system = C | R | L
val sprint_which_system_list : which_system list -> string
val sprint_which_rw_system_list : which_system list -> string
val proof_found : unit -> bool
val check_sufficient_completeness :
  < iter : (< lefthand_side : < has_constructor_arguments : bool; .. >; .. > ->
            unit) ->
           'a;
    .. > ->
  'a
type list_of_systems_argument =
  | LOS_defined of which_system list
  | LOS_query
val sprint_which_system_list_arg : list_of_systems_argument -> string
val sprint_which_rw_system_list_arg : list_of_systems_argument -> string
val update_dico_free_constructors : unit -> unit
val is_free_constructor : Symbols.const -> bool
val sufficient_completeness_test : unit -> unit
val strongly_sufficient_completeness_test : unit -> unit
val ground_convergence_test : unit -> unit
val oracle_a :  (
    int -> Polynoms.polynom -> Polynoms.polynom list ->  Literals.literal
	list * Literals.literal list -> peano_literal list ->  
    peano_literal list ->  Polynoms.polynom list list * peano_literal list -> peano_literal list) ref
val oracle_g : (peano_context clause -> peano_literal list -> peano_literal) ref

val all_nonvariable_symbols :
  < content : (< content : Literals.concrete_literal; .. > as 'a) list *
              'a list;
    .. > ->
  Symbols.const list
val recursive_new_hyps :
    < all_maximal_terms : bool -> Terms.term list;
      all_terms : Terms.term list; .. > ->
    < all_maximal_terms : bool -> Terms.term list; all_terms : Terms.term list; .. > list -> 'a list * 'a list -> 'a list
(* val cl1 : peano_context clause ref *)
(* val cl2 : peano_context clause ref *)
val print_detailed_clause : peano_context clause -> unit
val print_detailed_position_clause : peano_context clause -> unit

  val all_defined_positions :
    < content : Literals.concrete_literal; .. > list *
    < content : Literals.concrete_literal; .. > list ->
    ((bool * int * int list) * int list list) list

val sprint_clausal_position : bool * int * int list -> string

val write_pos_clause : peano_context clause -> unit


  val list_exists_w_number :
    (int ->
     (< content : < both_sides : < pos_rewriting : int list list;
                                   pos_partial_case_rewriting : int list list;
                                   pos_total_case_rewriting : int list list;
                                   .. > *
                                 < pos_rewriting : int list list;
                                   pos_partial_case_rewriting : int list list;
                                   pos_total_case_rewriting : int list list;
                                   .. >;
                    .. >
                  list *
                  < both_sides : < pos_rewriting : int list list;
                                   pos_partial_case_rewriting : int list list;
                                   pos_total_case_rewriting : int list list;
                                   .. > *
                                 < pos_rewriting : int list list;
                                   pos_partial_case_rewriting : int list list;
                                   pos_total_case_rewriting : int list list;
                                   .. >;
                    .. >
                  list;
        number : int; string : string; .. > as 'a) ->
     bool) ->
    'a list -> bool

val expand_nullary :
  Terms.term list -> (Terms.term * (Symbols.var * Terms.term) list) list
val write_pos_term_clause : peano_context clause -> unit
val print_history : (which_system list ->
    Terms.term ->
    peano_context clause ->
    string ->
       ((peano_context clause) list) *
      ((peano_context clause) list) -> int -> (string * int * (Literals.literal list * Literals.literal list)) list * string * Terms.term * (peano_context clause * (Symbols.var * Terms.term) list) list) -> peano_context clause -> bool -> unit
val print_history_instance : peano_context clause -> unit

val initial_conjectures : (peano_context clause) list ref

 val concrete_system_list : 
     which_system list -> 
     (((peano_context clause) 
     list) * ((peano_context clause) list)) -> (string * (peano_context clause)) list 
 val complete_lemmas_system : (peano_context clause) l_system 
 val lemmas_system : (peano_context clause) l_system 
 val hypotheses_system : (peano_context clause) system 
 val conjectures_system : (peano_context clause) system 
 val all_conjectures_system : (peano_context clause) system 
 val rewrite_system : (peano_context clause) rw_system 

val compute_string_clause_caml: peano_context clause -> string
val real_conjectures_system: (peano_context clause) list ref
val coq_formulas : (peano_context clause) list ref
val coq_all_lemmas : (int * (string * ((Symbols.var * Symbols.sort) list))) list ref
val coq_spec_lemmas : (peano_context clause) list ref
val coq_generate_cond  : (int * Literals.literal list list) list ref
val coq_formulas_with_infos :(string * int * (Symbols.var * Symbols.sort * bool) list * (int * (Symbols.var * Terms.term) list) list * ((peano_context clause) * string * (peano_context clause)  *  (Symbols.var * Terms.term) list ) list) list ref
val coq_less_clauses : ((peano_context clause) * (peano_context clause)) list ref
val coq_main_lemma : string ref
val main_lemma_proof : string ref
val coq_induction_schemas : string ref
val rewriting_clauses : ((peano_context clause) * string * (peano_context clause) *  (Symbols.var * Terms.term) list ) list ref
val coq_replacing_clauses : (int * (peano_context clause * (Symbols.var * Terms.term) list * int)) list ref 
