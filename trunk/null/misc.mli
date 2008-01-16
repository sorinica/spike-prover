val dummybreak : unit -> unit
val list_insert : ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
val list_union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
val generic_list_union : 'a list -> 'a list -> 'a list
val ord_assoc :
  ('a -> 'b -> bool) -> ('b -> 'a -> bool) -> 'b -> ('a * 'c) list -> 'c
val insert_sorted :
  ('a -> 'a -> bool) -> ('a -> 'a -> bool) -> 'a -> 'a list -> 'a list
val merge_sorted_lists :
  ('b -> 'b -> bool) -> 'b list -> 'b list -> 'b list
val multiset_merge_sorted_lists :
  ('a -> 'a -> bool) ->
  ('a -> 'a -> bool) -> (int * 'a) list -> (int * 'a) list -> (int * 'a) list
val assoc_merge_sorted_lists :
  ('a -> 'a -> bool) ->
  ('a * 'b list) list -> ('a * 'b list) list -> ('a * 'b list) list 
val assoc_insert_sorted :
  ('a -> 'a -> bool) ->
  ('a -> 'a -> bool) -> 'a * 'b -> ('a * 'b list) list -> ('a * 'b list) list
val assoc_insert :
  ('a -> 'a -> bool) ->
  'b * 'a list -> ('b * 'a list) list -> ('b * 'a list) list
val remove_sorted :
  ('a -> 'b -> bool) -> ('a -> 'b -> bool) -> 'a -> 'b list -> 'b list
val remove_sorted_lists :
  ('a -> 'b -> bool) -> ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list
val setminus :
  ('a -> 'b -> bool) -> ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list
val remove_el : ('a -> 'b -> bool) -> 'a -> 'b list -> 'b list
val unsorted_setminus : ('a -> 'b -> bool) -> 'b list -> 'a list -> 'b list
val unsorted_sloppy_setminus :
  ('a -> 'b -> bool) -> 'b list -> 'a list -> 'b list
val remove_all_el : ('a -> 'b -> bool) -> 'a -> 'b list -> 'b list
val intersection_sorted_lists :
  ('a -> 'b -> bool) -> ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list
val difference : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list
val intersection_and_rest_sorted_lists :
  ('a -> 'a -> bool) ->
  ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list * 'a list
val is_subset : ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val list_max : ('a -> 'a -> 'a) -> 'a list -> 'a
val list_member : ('a -> 'b -> bool) -> 'b -> 'a list -> bool
val list_remove_doubles : ('a -> 'a -> bool) -> 'a list -> 'a list
val generic_ord_assoc : 'a -> ('a * 'b) list -> 'b
val generic_insert_sorted : 'a -> 'a list -> 'a list
val generic_merge_sorted_lists : 'a list -> 'a list -> 'a list
val subst_compose : ('a * 'b) list -> ('a * 'b) list -> ('a * 'b) list
val generic_multiset_merge_sorted_lists : 'a list -> 'a list -> 'a list
val generic_assoc_merge_sorted_lists :
  ('a * 'b list) list -> ('a * 'b list) list -> ('a * 'b list) list
val generic_assoc_insert_sorted :
  'a * 'b -> ('a * 'b list) list -> ('a * 'b list) list
val generic_remove_sorted : 'a -> 'a list -> 'a list
val generic_remove_sorted_lists : 'a list -> 'a list -> 'a list
val generic_setminus : 'a list -> 'a list -> 'a list
val generic_remove_el : 'a -> 'a list -> 'a list
val generic_intersection_sorted_lists : 'a list -> 'a list -> 'a list
val generic_intersection_and_rest_sorted_lists :
  'a list -> 'a list -> 'a list * 'a list
val generic_is_subset : 'a list -> 'a list -> bool
val generic_list_max : 'a list -> 'a
val generic_merge_set_of_lists : 'a list list -> 'a list
val generic_list_object_member :
  'a -> < equal : 'a -> bool; .. > list -> bool
val generic_list_object_remove_doubles :
  (< equal : 'a -> bool; .. > as 'a) list -> 'a list
val generic_list_sorted_mem : 'a -> 'a list -> bool
val sprint_list : string -> ('a -> string) -> 'a list -> string
val print_list : string -> ('a -> unit) -> 'a list -> unit
val print_tab_list : string list -> unit
val sprint_string_list : string -> string list -> string
val sprint_int_list : int list -> string
val list_group : ('a -> 'a -> bool) -> 'a list -> 'a list list
val lists_sync :
  ('a list -> 'b list -> bool) ->
  ('a list -> 'b list -> bool) ->
  'a list list -> 'b list list -> 'a list list * 'b list list
val check_on_permutations : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool
val ac_eq : ('a -> 'b -> 'c -> 'a) -> exn -> 'a -> 'b list -> 'c list -> 'a
val check_on_subsets : 'a -> int list -> 'b
val check_on_variants : ('a list -> 'b) -> 'a list list -> 'b
val list_special_exists : ('a -> 'b) -> exn -> 'a list -> 'b 
val subsumes :
  ('a -> 'a) ->
  (('a -> 'a) -> 'a -> 'b -> 'c -> 'a) -> 'a -> 'b list -> 'c list -> 'a
val subsumes_w_rest :
  ('a -> 'b -> 'c -> 'a) -> exn -> 'a -> 'b list -> 'c list -> 'a * 'c list
val apply_f_to_element_n : ('a -> 'a) -> int -> 'a list -> 'a list
val is_included :
  ('a -> 'b -> bool) -> ('a -> 'b -> bool) -> 'a list -> 'b list -> bool
val extract : 'a list -> ('a * 'a list) list
val all_couples_from_list : 'a list -> ('a * 'a) list
val all_combinations_from_list : 'a list -> ('a * 'a) list 
val last_el : 'a list -> 'a
val list_all_but_last_el : 'a list -> 'a list
val list_all_but : int -> 'a list -> 'a list
val list_truncate : 'a list -> int -> 'a list
val uncouple_list : ('a * 'a) list -> 'a list
val max_assoc : 'a -> 'b -> ('a * 'b) list -> ('a * 'b) list
val max_assoc_merge : ('a * 'b) list -> ('a * 'b) list -> ('a * 'b) list
val megamix : 'a list list -> 'a list list
val process_underscores : string -> string * int * int
type ginput = string * in_channel
val openin : string -> string * in_channel
val closein : string * in_channel -> unit
type 'a pointer = | Undefined | Defined of 'a
val pointer_is_defined : 'a pointer -> bool
val pointer_is_undefined : 'a pointer -> bool
val defined_content : 'a pointer -> 'a
val pointer_max : 'a pointer -> 'a pointer -> 'a pointer
val pointer_incr : int pointer -> int pointer
val list_init : int -> 'a -> 'a list
val pop_n_times : int -> 'a Stack.t -> 'a list
val list_split_at_n : int -> 'a list -> 'a list * 'a list
val array_exists : ('a -> bool) -> 'a array -> bool
val list_is_suffix : 'a list -> 'a list -> bool
val list_2_2_map :
  ('a -> 'b -> 'c * 'd) -> ('a * 'b) list -> 'c list * 'd list
val list_replace_element : int -> 'a -> 'a list -> 'a list
val list_replace_element_w_list : int -> 'a list -> 'a list -> 'a list
val list_insert_at_position : int -> 'a -> 'a list -> 'a list
val list_2_list_of_couples : 'a list -> ('a * 'a) list
val list_select_maximal_elements :
  ('a -> 'a -> bool) -> 'a list -> 'a list * 'a list
val list_create : int -> int list
val list_singleton : 'a list -> bool
val get_leading_el : ('a -> 'b -> bool) -> 'b -> 'a list -> 'a list * 'a list
val list_exists_and_proceed : ('a -> 'a) -> exn -> 'a list -> bool * 'a list
val list_exists_and_proceed_2 :
  ('a -> 'a list) -> exn -> 'a list -> bool * 'a list
val list_remove_true : ('a -> bool) -> 'a list -> bool * 'a list
val list_number_els : 'a list -> (int * 'a) list
val list_position_smallest_el : ('a -> 'a -> bool) -> 'a list -> int
type goto_type = | Goto_number of int | Goto_smallest | Goto_greatest
val list_exists_w_number : (int -> 'a -> bool) -> 'a list -> bool
val mstring : < string : 'a; .. > -> 'a
val print_bitstream : int -> unit
val power : int -> int -> int
val get_bitstream : int list -> int
val list_head_to_tail : 'a list -> 'a list
val print_list_tbox : string list -> unit
val generic_assoc2 : ('a -> 'b -> bool) -> 'a -> ('c * 'b) list -> 'c 
val list_assoc_2 : 'a -> ('b * 'a) list -> 'b
val repeat : ('a -> 'a) -> exn -> 'a -> 'a
val queue_forall : ('a -> bool) -> 'a Queue.t -> bool
class virtual generic : object ('a) method virtual equal : 'a -> bool end
class virtual printable_object :
  object
    val mutable string : string pointer
    method private virtual compute_string : string
    method string : string
  end
val subset : < syntactic_equal : 'a -> bool; .. > list -> 'a list -> bool
val do_nothing : string -> unit
val n_spaces : int -> string
val syntactic_equal : < syntactic_equal : 'a; .. > -> 'a
val matrix_exists : ('a -> bool) -> 'a list list -> bool
val matrix_map : ('a -> 'b) -> 'a list list -> 'b list list
val list_special_map :
  ((< string : string; .. > as 'a) -> 'b) -> exn -> 'a list -> 'b list
val cat_nonempty_strings : string list -> string
val gcd : int -> int -> int
val lcm : int -> int -> int 
val substring : string -> string -> bool
val print_indent_string :string -> unit
