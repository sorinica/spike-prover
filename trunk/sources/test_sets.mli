val generate_constructor_terms :
  int -> Symbols.sort -> bool -> Terms.term list 
val cs_terms : unit -> unit 
type induction_position_specification =
    Ind_pos_void
  | Ind_pos_position of (Symbols.const * (Symbols.const * int) list) list
  | Ind_pos_path of Symbols.path list
val sprint_induction_position_specification :
  induction_position_specification -> string 
val merge_induction_positions :
  induction_position_specification ->
  induction_position_specification -> induction_position_specification 
val induction_symbols_priorities : induction_position_specification list ref 
val print_induction_symbols_priorities : unit -> unit 
val fill_default_induction_positions_v0 :
  induction_position_specification list -> unit 
val fill_default_induction_positions :
  (induction_position_specification list -> unit) ref 
val sprint_fun_path : Symbols.const * int list -> string 
val compute_induction_posvar :
  Terms.term ->
  (Terms.term * int list) list 
val update_dico_rules : unit -> unit 

val test_set_version : int ref
val dico_test_set_v0 : (Symbols.sort, Terms.term list) Dicos.dictionary
val dico_test_set_v1 : (int * Symbols.sort, Terms.term list) Dicos.dictionary
val dico_test_set_v2 : (Symbols.path, Terms.term list) Dicos.dictionary
val print_dico_test_set_v0 : unit -> unit
val print_dico_test_set_v1 : unit -> unit
val print_dico_test_set_v2 : unit -> unit
val print_dico_test_set : (unit -> unit) ref
val sprint_induction_position_specification :
  induction_position_specification -> string
val merge_induction_positions :
  induction_position_specification ->
  induction_position_specification -> induction_position_specification
val induction_symbols_priorities : induction_position_specification list ref
val print_induction_symbols_priorities : unit -> unit
val fill_default_induction_positions_v0 :
  induction_position_specification list -> unit
val fill_default_induction_positions_v1 :
  induction_position_specification list -> unit
val fill_default_induction_positions_v2 :
  induction_position_specification list -> unit
val fill_default_induction_positions :
  (induction_position_specification list -> unit) ref
val sprint_fun_path : Symbols.const * int list -> string
  val induction_variables_v0 :
    (Symbols.const * (int * int) list) list ->
    Terms.term -> (Symbols.var * Symbols.sort * bool) list
  val induction_variables_v1 :
    Symbols.path list ->
    Terms.term -> (Symbols.var * (int * Symbols.sort)) list
  val induction_variables_v2 :
    Terms.term -> (Symbols.var * Symbols.path list) list
val compute_test_set_v0 :
  < capital_d_per_sort : (Symbols.sort * int) list;
    compute_induction_positions_v0 : 'a; .. > ->
  unit
val compute_test_set_v1 : < compute_induction_positions_v1 : 'a; .. > -> unit
val compute_test_set_v2 :
  < iter : (< lefthand_side : < ind_positions_v2 : (Symbols.path *
                                                    < rename : Terms.term;
                                                      .. >)
                                                   list;
                                .. >;
              string : string; .. > ->
            unit) ->
           unit;
    .. > ->
  unit
val compute_test_set : (unit -> unit) ref
val has_induction_variables_v0 : Terms.term -> bool
  val has_induction_variables_v1 : Terms.term -> bool
  val has_induction_variables_v2 : Terms.term -> bool
val has_induction_variables : (Terms.term -> bool) ref
val have_same_induction_variables_v0 : Terms.term -> Terms.term -> bool
  val have_same_induction_variables_v1 : Terms.term -> Terms.term -> bool
  val have_same_induction_variables_v2 : Terms.term -> Terms.term -> bool
val have_same_induction_variables : (Terms.term -> Terms.term -> bool) ref
  val generate_test_substitutions_core_v0 :
    ('a * Symbols.sort * 'b) list -> ('a * Terms.term) list list
val generate_test_substitutions_v0 :
  induction_position_specification ->
  Terms.term -> (Symbols.var * Terms.term) list list
val generate_test_substitutions_for_clause_v0 :
  induction_position_specification ->
  < all_terms : Terms.term list; .. > -> (Symbols.var * Terms.term) list list
val generate_test_substitutions_core_v1 :
  ('a * (int * Symbols.sort)) list -> ('a * Terms.term) list list
  val generate_test_substitutions_v1 :
    induction_position_specification ->
    Terms.term -> (Symbols.var * Terms.term) list list
  val generate_test_substitutions_for_clause_v1 :
    induction_position_specification ->
    < all_terms : Terms.term list; .. > ->
    (Symbols.var * Terms.term) list list
  val induction_sets :
    Symbols.path list ->
    Terms.term -> (Symbols.var * Terms.term list list) list
val generate_test_substitutions_core_v2 :
  ('a * (< equal : 'b -> bool; rename : 'c; .. > as 'b) list list) list ->
  ('a * 'c) list list
  val generate_test_substitutions_v2 :
    induction_position_specification ->
    Terms.term -> (Symbols.var * Terms.term) list list
val generate_test_substitutions_for_clause_v2 :
  induction_position_specification ->
  Clauses.peano_context Clauses.clause ->
  (Symbols.var * Terms.term) list list
val generate_test_substitutions :
  (induction_position_specification ->
   Terms.term -> (Symbols.var * Terms.term) list list)
  ref
val generate_test_substitutions_for_clause :
  (induction_position_specification ->
   Clauses.peano_context Clauses.clause ->
   (Symbols.var * Terms.term) list list)
  ref
val update_test_set_version : int -> unit
