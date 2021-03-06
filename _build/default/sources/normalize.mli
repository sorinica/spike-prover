val norm_string : string ref
  
  val rewrite :
    Clauses.which_system list ->
    Terms.term ->
    Clauses.peano_context Clauses.clause ->
    string ->
    Clauses.peano_context Clauses.clause list *
    Clauses.peano_context Clauses.clause list -> int -> (string *  int * (Literals.literal list * Literals.literal list )) list * string * Terms.term * (Clauses.peano_context Clauses.clause * (Symbols.var * Terms.term) list) list
  val normalize :
    Clauses.which_system list ->
    Terms.term ->
    Clauses.peano_context Clauses.clause ->
    string ->
    Clauses.peano_context Clauses.clause list *
    Clauses.peano_context Clauses.clause list -> int -> (string *  int * (Literals.literal list * Literals.literal list )) list * string * Terms.term * (Clauses.peano_context Clauses.clause * (Symbols.var * Terms.term) list) list
  val normalize_plus :
    Clauses.which_system list ->
    Terms.term ->
    Clauses.peano_context Clauses.clause ->
    string ->
    Clauses.peano_context Clauses.clause list *
    Clauses.peano_context Clauses.clause list -> int -> (string *  int * (Literals.literal list * Literals.literal list )) list * string * Terms.term * (Clauses.peano_context Clauses.clause * (Symbols.var * Terms.term) list) list
