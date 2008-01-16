exception Inconsistent
val preprocess_ac : Terms.term -> Terms.term
val well_founded :int -> (int * < sort : Symbols.sort; string : string; .. >) list -> bool
val count_s : (< content : 'a Terms.concrete_term; .. > as 'a) -> int * 'a
val count_p : (< content : 'a Terms.concrete_term; .. > as 'a) -> int * 'a
val order_two : ('a -> 'a -> bool) -> 'a -> 'a -> 'a * 'a
val elim_null_monoms : (int * 'a) list -> (int * 'a) list
val multiply_term :
  Terms.term -> ('a * Terms.term) list -> ('a * Terms.term) list
val multiply_const : int * (int * 'a) list -> (int * 'a) list
val multiply_monoms :
 int * (int * Terms.term) list ->
    int * (int * Terms.term) list -> int * (int * Terms.term) list
val normalize_monom_list :
  (int * Terms.term) list -> int * (int * Terms.term) list
val process_monom : int * Terms.term -> int * (int * Terms.term) list
  class polynom :
    int ->
    (int * Terms.ground_term) list ->
    ('a list as 'b) ->
    object ('a)
      val constant : int
      val content : (int * Terms.term) list
      val history : 'b
      val length : int
      val mutable string : string Diverse.pointer
      method add : 'a -> 'a
      method coefficients : int list
      method combination : 'a -> int * int
      method compute_string : string
      method constant : int
      method content : (int * Terms.term) list
      method cross_multiply_add : 'a -> int * int -> 'a
      method equal : 'a -> bool
      method fprint : out_channel -> unit
      method history : 'b
      method impossible : bool
      method independent : bool
      method length : int
      method maximal_monomial : int * Terms.term
      method maximal_multiplicand : Terms.term
      method multiplicands : Terms.term list
      method pprint : Format.formatter -> unit
      method sprint : string
      method string : string
      method syntactic_equal : 'a -> bool
      method vacuous : bool
    end
val new_polynom : int -> (int * Terms.ground_term) list -> (polynom list) 
  -> polynom
val poly_0_leq_0 : polynom
val add_nat_variables :
  < content : ('a * Terms.ground_term) list; .. > list ->
  polynom list
