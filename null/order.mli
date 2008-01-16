val consecutive_elements : Symbols.const list -> Symbols.const list
val unary_symbols : unit -> Symbols.const list
val constant_symbols : unit -> Symbols.const list
val lex_greater :
  'a ->
  ('b -> 'c -> bool) ->
  ('a -> 'b -> 'c -> bool) -> 'b list -> 'c list -> bool
val remove_common_elements :
  ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list * 'b list
val multiset_greater :
  'a ->
  ('b -> 'c -> bool) ->
  ('a -> 'b -> 'c -> bool) -> 'b list -> 'c list -> bool
val multiset_geq :
  'a ->
  'b ->
  ('a -> (< syntactic_equal : 'd -> bool; .. > as 'c) -> 'd -> bool) ->
  'c list -> 'd list -> bool
val extended_greater :
  'a ->
  ('b -> 'c -> bool) ->
  ('a -> 'b -> 'c -> bool) -> Symbols.status -> 'b list -> 'c list -> bool 
val rpo_greater : bool -> Terms.term -> Terms.term  -> bool
val rpo_incomparable : bool -> Terms.term -> Terms.term  -> bool
val rpo_equivalent : Terms.term -> Terms.term -> bool
val rpo_geq : bool -> Terms.term -> Terms.term -> bool
val ground_greater : Terms.ground_term -> Terms.ground_term -> bool
val rpos_greater : (bool -> Terms.ground_term -> Terms.ground_term -> bool) ref
val rpos_geq : (bool -> Terms.term -> Terms.term -> bool) ref
val heavier : Terms.term -> Terms.term -> bool
val clause_greater :
  bool ->
  < all_maximal_terms : bool -> Terms.ground_term list; .. > ->
  < all_maximal_terms : bool -> Terms.ground_term list; .. > -> bool
val clause_equiv :
    'a ->
    < all_maximal_terms : 'a ->
                          (< term_congruence : 'b -> bool; .. > as 'b) list;
      .. > ->
    < all_maximal_terms : 'a -> 'b list; .. > -> bool
val clause_geq :
  bool ->
  < all_maximal_terms : bool -> Terms.ground_term list;
    all_terms : (< term_congruence : 'a -> bool; .. > as 'a) list; .. > ->
  < all_maximal_terms : bool -> Terms.ground_term list; all_terms : 'a list;
    .. > ->
  bool
val ac_distribute_ac_ac :
  Symbols.const -> Symbols.const -> Terms.term -> Terms.term
val ac_distribute_un_un :
  Symbols.const -> Terms.term -> Symbols.const -> Terms.term
val ac_distribute_un : Terms.term -> Symbols.const -> Terms.term
val ac_distribute_ac_un :
  Symbols.const -> Symbols.const -> Terms.term -> Terms.term
val ac_normalize_1 : Terms.term -> Terms.term
val ac_normalize_2 : Terms.term -> Terms.term
val ac_normalize_3 : 'a -> 'a
val determine_ac_category : unit -> unit
val orient : Terms.ground_term -> Terms.ground_term -> Terms.ground_term * Terms.ground_term
