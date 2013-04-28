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
 
val rewriting :
  bool ->
    bool ->
      Clauses.list_of_systems_argument ->
	Dummies.position_argument ->
	  (Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list) ->
	    Clauses.peano_context Clauses.clause -> bool -> int -> 
	      Clauses.peano_context Clauses.clause list
		

