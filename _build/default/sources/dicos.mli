class ['a, 'b] dictionary :
  int ->
  object
    val value : ('a, 'b) Hashtbl.t
    method add : 'a -> 'b -> unit
    method apply_f : ('b -> 'b -> 'b) -> 'a -> 'b -> unit
    method clear : unit
    method empty : bool
    method find : 'a -> 'b
    method iter : ('a -> 'b -> unit) -> unit
    method remove : 'a -> unit
    method replace : 'a -> 'b -> unit
    method size : int
  end
val htbl_update : ('a, 'b list) Hashtbl.t -> 'a -> 'b -> unit
val htbl_update_list : ('a, 'b list) Hashtbl.t -> 'a -> 'b list -> unit
class ['a, 'b] reversible_dictionary :
  int ->
  object
    val revert_value : ('b, 'a list) Hashtbl.t
    val value : ('a, 'b) Hashtbl.t
    method add : 'a -> 'b -> unit
    method apply_f : ('b -> 'b -> 'b) -> 'a -> 'b -> unit
    method clear : unit
    method empty : bool
    method find : 'a -> 'b
    method find_keys : 'b -> 'a list
    method iter : ('a -> 'b -> unit) -> unit
    method remove : 'a -> unit
    method replace : 'a -> 'b -> unit
    method size : int
  end
class ['a, 'b] bijective_dictionary :
  int ->
  object
    val revert_value : ('b, 'a) Hashtbl.t
    val value : ('a, 'b) Hashtbl.t
    method add : 'a -> 'b -> unit
    method apply_f : ('b -> 'b -> 'b) -> 'a -> 'b -> unit
    method clear : unit
    method empty : bool
    method find : 'a -> 'b
    method find_key : 'b -> 'a
    method iter : ('a -> 'b -> unit) -> unit
    method remove : 'a -> unit
    method replace : 'a -> 'b -> unit
    method size : int
  end
class ['a, 'b] assoc_dictionary :
  int ->
  object
    val revert_value : ('b, 'a list) Hashtbl.t
    val value : ('a, 'b list) Hashtbl.t
    method add : 'a -> 'b -> unit
    method clear : unit
    method empty : bool
    method exists : 'a -> bool
    method find : 'a -> 'b list
    method find_keys : 'b -> 'a list
    method iter : ('a -> 'b list -> unit) -> unit
    method merge : 'a -> 'b list -> unit
    method size : int
  end
class virtual ['a] relation_dictionary :
  int ->
  object ('b)
    val value : ('a, 'a list) Hashtbl.t
    method add : 'a -> 'a list -> unit
    method add_couple : 'a -> 'a -> unit
    method apply_f : ('a list -> 'a list -> 'a list) -> 'a -> 'a list -> unit
    method clear : unit
    method dub : ('a, 'a list) Hashtbl.t -> 'b
    method empty : bool
    method find : 'a -> 'a list
    method iter : ('a -> 'a list -> unit) -> unit
    method virtual rehash : unit
    method related : 'a -> 'a -> bool
    method remove : 'a -> unit
    method replace : 'a -> 'a list -> unit
    method size : int
  end
  class ['a] equivalence_dictionary :
    int ->
    object
      val content : ('a, 'a list) Hashtbl.t
      val roots : ('a, 'a) Hashtbl.t
      method add_couple : 'a -> 'a -> unit
      method clear : unit
      method empty : bool
      method fill : ('a -> 'a -> bool) -> 'a list -> unit
      method find : 'a -> 'a list
      method init : 'a list -> unit
      method iter : ('a -> 'a list -> unit) -> unit
      method print : ('a -> string) -> unit
      method remove : 'a -> unit
      method size : int
    end
val dico_equivalence : int equivalence_dictionary
class ['a] order_dictionary :
  int ->
  object
    constraint 'a = int
    val content : ('a, 'a list) Hashtbl.t
    method add_couple : 'a -> 'a -> unit
    method add_equiv : 'a -> 'a -> unit
    method clear : unit
    method empty : bool
    method related : 'a -> 'a list
    method find : 'a -> 'a list
    method init : 'a list -> unit
    method iter : ('a -> 'a list -> unit) -> unit
    method keys : 'a list
    method merge_equivalence_relation : 'a equivalence_dictionary -> unit
    method size : int
  end
