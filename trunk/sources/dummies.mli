type literal_position = bool * int
and clausal_position = bool * int * Symbols.position
type position_argument =
  | Pos_defined of clausal_position
  | Pos_litdefined of (bool * int)
  | Pos_all
  | Pos_query
  | Pos_dumb
val sprint_position_argument : position_argument -> string
  class strategy :
    object
      method apply :
        bool ->
        Clauses.peano_context Clauses.clause list *
        Clauses.peano_context Clauses.clause list -> bool -> bool
      method apply_at_pos :
        bool ->
        position_argument ->
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
        position_argument ->
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
val dico_st : (string, strategy) Dicos.dictionary
val print_dico_st : unit -> unit
val sprint_dico_st : unit -> string
val name_strat_query : string
val name_strat_generate_reduce : string
val spike_parse_strategy : (strategy -> unit -> strategy) ref
val spike_parse_list_of_systems : (unit -> Clauses.which_system list) ref
val spike_parse_clausal_lhs_position :
  (Clauses.peano_context Clauses.clause -> unit -> position_argument) ref
val spike_parse_literal_position_in_clause :
  (Clauses.peano_context Clauses.clause -> unit -> position_argument) ref
val spike_parse_substitution : (unit -> (Symbols.var * Terms.term) list) ref
val spike_parse_positive_int :
  (Clauses.peano_context Clauses.clause -> unit -> int) ref
type shell_commands =
  | Command_strategy of strategy
  | Command_next
  | Command_run
  | Command_previous
  | Command_display
  | Command_exit
  | Command_error
val spike_parse_shell_command : (unit -> shell_commands) ref

val dico_patterns :
  (int, Clauses.peano_context Clauses.clause list list) Dicos.dictionary

val dico_rules :
  (int, Clauses.peano_context Clauses.clause list) Dicos.dictionary

val print_dico_rules : unit -> unit

val main_interact : (unit-> unit) ref
