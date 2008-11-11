val contextual_rewriting :
  bool ->
    Dummies.strategy ->
      Clauses.list_of_systems_argument ->
	Dummies.position_argument ->
	  (Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list) -> 
	    Clauses.peano_context Clauses.clause -> bool -> int -> 
	      Clauses.peano_context Clauses.clause list
val equational_rewriting :
  bool ->
    Dummies.position_argument ->
      (Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list)  -> 
	Clauses.peano_context Clauses.clause -> bool -> int -> 
	  Clauses.peano_context Clauses.clause list
  val reduce_clause :
    ( Clauses.which_system list ->
    Terms.term ->
    Clauses.peano_context Clauses.clause ->
    string ->
    Clauses.peano_context Clauses.clause list *
    Clauses.peano_context Clauses.clause list -> int -> string list * string * Terms.term)
      ->
      Clauses.which_system list -> bool ->  Clauses.peano_context Clauses.clause -> 
	(Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list) -> 
	 string list * string *  Clauses.peano_context Clauses.clause
val conditional_rewriting :
  bool ->
    bool ->
      Clauses.list_of_systems_argument ->
	Dummies.position_argument ->
	  (Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list) ->
	    Clauses.peano_context Clauses.clause -> bool -> int -> 
	      Clauses.peano_context Clauses.clause list
		

