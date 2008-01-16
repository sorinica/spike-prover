val eliminate_redundant_literal : 
  bool -> 
    Clauses.peano_context Clauses.clause -> int ->
      Clauses.peano_context Clauses.clause list

val eliminate_trivial_literal :   
  bool -> 
    Clauses.peano_context Clauses.clause -> int -> 
      Clauses.peano_context Clauses.clause list

