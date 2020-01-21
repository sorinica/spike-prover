val case_rw_condition_1 : Terms.term -> Terms.term -> bool
  val case_rw_condition_2_with_p_given :
    (Terms.term ->
     bool ->
     int ->
     int list ->
     (Clauses.peano_context Clauses.clause *
      (Symbols.var * Terms.term) list * string)
     list -> bool) ->
    Clauses.peano_context Clauses.clause ->
    bool -> int -> int list -> Clauses.which_system list -> 'a -> 'b -> bool
  
  val generate_cond_and_eq :
    Terms.term ->
    Clauses.peano_context Clauses.clause ->
    bool ->
    int ->
    int list ->
    (Clauses.peano_context Clauses.clause * (Symbols.var * Terms.term) list * string)
    list ->
    bool ->
    Clauses.peano_context Clauses.clause list *
    Clauses.peano_context Clauses.clause list
val partial_case_rewriting :
  bool ->
    Clauses.list_of_systems_argument ->
      Dummies.position_argument ->
   	(Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list) ->
	  Clauses.peano_context Clauses.clause -> bool -> int ->
	    Clauses.peano_context Clauses.clause list
val total_case_rewriting :
  bool ->
    Dummies.strategy ->
      Clauses.list_of_systems_argument ->
	Dummies.position_argument ->
  	  (Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list) ->
	    Clauses.peano_context Clauses.clause -> bool -> int -> 
	      Clauses.peano_context Clauses.clause list
