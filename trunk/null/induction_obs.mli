val generate_obs :
  bool ->
  bool ->
  Test_sets.induction_position_specification list ->
  int -> Clauses.peano_context Clauses.clause -> (Clauses.peano_context Clauses.clause) list
