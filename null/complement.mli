val compress : bool -> unit
val complement : 
  bool -> 
    Clauses.peano_context Clauses.clause -> bool -> int ->
      Clauses.peano_context Clauses.clause list

