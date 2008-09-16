val consecutive_elements : Symbols.const list -> Symbols.const list
val unary_symbols : unit -> Symbols.const list
val constant_symbols : unit -> Symbols.const list
val mul :
  ('a * 'a -> Symbols.order) ->
  ('a list * 'a list) -> Symbols.order
val multiset_greater :
  ('a * 'a -> Symbols.order) ->
  'a list -> 'a list -> bool
val multiset_equivalent :
  ('a * 'a -> Symbols.order) ->
  'a list -> 'a list -> bool
val multiset_geq :
  ('a * 'a -> Symbols.order) ->
  'a list -> 'a list -> bool
val rpo_greater : bool -> Terms.term -> Terms.term  -> bool
val rpo_incomparable : bool -> Terms.term -> Terms.term  -> bool
val rpo_equivalent : Terms.term -> Terms.term -> bool
val rpo_geq : bool -> Terms.term -> Terms.term -> bool
val ground_greater : Terms.ground_term -> Terms.ground_term -> bool
val rpos_greater : (bool -> Terms.ground_term -> Terms.ground_term -> bool) ref
val rpos_geq : (bool -> Terms.term -> Terms.term -> bool) ref
val rpos : (bool -> Terms.term * Terms.term -> Symbols.order) ref
val heavier : Terms.term -> Terms.term -> bool
val clause_max_greater :
  bool ->
  < all_maximal_terms : bool -> Terms.ground_term list; .. > ->
  < all_maximal_terms : bool -> Terms.ground_term list; .. > -> bool
val clause_max_geq:
bool ->
    < all_maximal_terms : bool -> Terms.term list; .. > ->
    < all_maximal_terms : bool -> Terms.term list; .. > -> bool
val clause_greater :
  bool ->
  < all_terms :  Terms.ground_term list; .. > ->
  < all_terms :  Terms.ground_term list; .. > -> bool
val clause_equiv :
     bool ->
    < all_terms : Terms.term list; .. > ->
    < all_terms : Terms.term list; .. > -> bool
val clause_geq :
 bool ->
    < all_terms : Terms.term list; .. > ->
    < all_terms : Terms.term list; .. > -> bool
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
