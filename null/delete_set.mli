val tautology : bool -> Clauses.peano_context Clauses.clause -> int -> Clauses.peano_context Clauses.clause list 
val subsumption_init_array :
  < negative_lits : (< is_diff : bool; .. > as 'a) list;
    positive_lits : 'a list; .. > ->
  (bool * 'a) array
val subsumption_retrieve_equivalence_classes :
  < iter : ('a -> 'b -> unit) -> unit; .. > -> 'b list
val subsumption_retrieve_greatest_simple_clause :
  'a array ->
  (int * 'b list) list list -> 'a list * (int * 'b list) list list
val subsumption_select_l_top :
  'a array -> (int * 'b) list -> 'a * (int * 'b) list
val subsumption_lit_matching_core :
  ((Symbols.var * Terms.term) list -> (Symbols.var * Terms.term) list) ->
    (Symbols.var * Terms.term) list ->
      bool * Literals.literal ->
	bool * Literals.literal -> (Symbols.var * Terms.term) list
val subsumption_subsumes :
  bool ->
  string ->
  Clauses.peano_context Clauses.clause ->
  Clauses.peano_context Clauses.clause ->
  Clauses.peano_context Clauses.clause -> int -> (bool * (Symbols.var * Terms.term) list) 

val subsumption : 
  bool -> 	   
    Clauses.peano_context Clauses.clause ->
      Clauses.list_of_systems_argument ->
	(Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list) -> int ->
	  Clauses.peano_context Clauses.clause list
	
val negative_clash : 
  bool -> 
    Clauses.peano_context Clauses.clause -> int -> 
      Clauses.peano_context Clauses.clause list
	
val augmentation : 
  bool -> 	   
    Clauses.peano_context Clauses.clause ->
      Clauses.list_of_systems_argument ->
	(Clauses.peano_context Clauses.clause list * Clauses.peano_context Clauses.clause list) -> int ->
	  Clauses.peano_context Clauses.clause list
	
