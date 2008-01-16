val print_goals : bool -> unit
  type reasoning_module =
      Contextual_rewriting of Dummies.strategy *
        Clauses.list_of_systems_argument * Dummies.position_argument
    | Equational_rewriting of Dummies.position_argument
    | Congruence_closure
    | Conditional_rewriting of bool * Clauses.list_of_systems_argument *
        Dummies.position_argument
    | Partial_case_rewriting of Clauses.list_of_systems_argument *
        Dummies.position_argument
    | Total_case_rewriting of Dummies.strategy *
        Clauses.list_of_systems_argument * Dummies.position_argument
    | Generate of bool * Test_sets.induction_position_specification list
    | Generate_eq of bool * Test_sets.induction_position_specification list
    | Generate_obs of bool * Test_sets.induction_position_specification list
    | Positive_decomposition
    | Negative_decomposition
    | Positive_clash
    | Tautology
    | Subsumption of Clauses.list_of_systems_argument
    | Augmentation of Clauses.list_of_systems_argument
    | Negative_clash
    | Eliminate_redundant_literal
    | Eliminate_trivial_literal
    | Auto_simplification
    | Complement
    | Id

type goto_type = | Goto_number of int | Goto_smallest | Goto_greatest

type inference_rule =
    AddPremise of reasoning_module * Dummies.strategy
  | Simplify of reasoning_module * Dummies.strategy
  | Delete of reasoning_module * Dummies.strategy
  | Goto of goto_type
  | Id_st of reasoning_module	
and concrete_strategy =
  | Inference_rule of inference_rule
  | Series of Dummies.strategy list
  | Try_ of Dummies.strategy list
  | Repeat of Dummies.strategy
  | Repeat_plus of Dummies.strategy
  | Saturate of Dummies.strategy list
  | Named_strategy of string
  | Query
  | Print_goals of bool * bool

val rm_to_string : reasoning_module -> string 
val strategy_to_string : concrete_strategy -> string

  class strategy :
    concrete_strategy ->
    object
      val content : concrete_strategy
      val mutable string : string Diverse.pointer
      method apply :
        bool ->
        Clauses.peano_context Clauses.clause list *
        Clauses.peano_context Clauses.clause list -> bool -> bool
      method apply_at_pos :
        bool ->
        Dummies.position_argument ->
        int ->
        Clauses.peano_context Clauses.clause list *
        Clauses.peano_context Clauses.clause list -> bool -> bool
      method apply_new_goal :
        bool ->
        Clauses.peano_context Clauses.clause ->
        Clauses.peano_context Clauses.clause list *
        Clauses.peano_context Clauses.clause list -> bool -> bool
      method apply_new_goal_at_pos :
        bool ->
        Dummies.position_argument ->
        Clauses.peano_context Clauses.clause ->
        int ->
        Clauses.peano_context Clauses.clause list *
        Clauses.peano_context Clauses.clause list -> bool -> bool
      method apply_to_subgoals :
        bool ->
        Clauses.peano_context Clauses.clause ->
        Clauses.peano_context Clauses.clause list ->
        Clauses.peano_context Clauses.clause list -> bool -> bool
      method compute_string : string
      method fprint : out_channel -> unit
      method fullstring : string
      method is_query : bool
      method pprint : Format.formatter -> unit
      method sprint : string
      method string : string
    end
val name_strat_delete : string
val name_strat_clean : string
val name_strat_decompose : string
val name_strat_simplify : string
val name_strat_rewrite : string
val name_strat_recursive : string
val name_strat_builtin : string
val global_strat : strategy ref
val augmentation_strat : strategy ref
val dico_st_refill : unit -> unit
type problem_token =
  | Strat_token of (string * strategy) list
  | Conjectures_token of Clauses.peano_context Clauses.clause list
  | Hypotheses_token of Clauses.peano_context Clauses.clause list
  | Lemmas_token of Clauses.peano_context Clauses.clause list
  | Startpoint_token of strategy
  | Augmentation_token of strategy
  | Norm_token of Terms.term list
  | Cterm_token of Terms.term list
  | Rpo_token of (Terms.term * Terms.term)
  | Compare_token of (Clauses.peano_context Clauses.clause * Clauses.peano_context Clauses.clause)
  | Match_token of (Terms.term * Terms.term)
  | Message_token of string
  | Ac_token of (Terms.term list * Terms.term list)
val yy_queue : problem_token Queue.t
val yy_axioms :
  ((string * in_channel) * int * Clauses.peano_context Clauses.clause) list
  ref
