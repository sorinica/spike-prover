val decompose :
  int ref ->
  Literals.literal ->
  Literals.literal list

val positive_decomposition : bool -> Clauses.peano_context Clauses.clause -> int -> Clauses.peano_context Clauses.clause list 
val negative_decomposition : bool -> Clauses.peano_context Clauses.clause -> int -> Clauses.peano_context Clauses.clause list 
val positive_clash : bool -> Clauses.peano_context Clauses.clause -> int -> Clauses.peano_context Clauses.clause list 

val congruence_closure : 
  bool -> 
    Clauses.peano_context Clauses.clause -> int ->
      Clauses.peano_context Clauses.clause list
