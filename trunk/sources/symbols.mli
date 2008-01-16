type var = int
and const = int
and sort = Def_sort of int | Abstr_sort0 of string | Abstr_sort1 of int * sort | Abstr_sort2 of int * sort * sort
and position = int list
and path = (const * int) list
and arity = int * int
type parameterized_sort =
    Actual_sort of sort
  | Variable_sort of var
val yy_tmp_param_sorts : (string * sort) list ref
val sort_main_string : sort -> string
val sprint_param_sort : parameterized_sort -> string 
val sprint_sort : sort -> string 
val occurs_str : string -> sort -> bool
val insert_shorten :
  string * sort ->
      (string * sort) list -> (string * sort) list
val unify_sorts : parameterized_sort -> sort -> sort 
val equal_sorts : sort -> sort -> bool
val expand_sorts : sort -> sort 
val def_sort_id : sort -> int
val var_equal : 'a -> 'a -> bool
val var_inf : 'a -> 'a -> bool
val const_equal : 'a -> 'a -> bool
val const_inf : 'a -> 'a -> bool
val sort_equal : 'a -> 'a -> bool
val sort_inf : 'a -> 'a -> bool
val sprint_var : int -> sort -> bool -> string
val sprint_subst :
  (int * < sort : sort; string : string; .. >) list -> string
val is_abstract : sort -> bool
val sprint_position : int list -> string
val is_constructor : int -> bool
val is_defined : int -> bool
val greatest_var : int ref
val newvar : unit -> int
val update_greatest_var : < greatest_varcode : int; .. > -> unit
val sort_counter : int ref
val new_sort : unit -> sort
val obs_sort_counter : int ref
val constructor_counter : const ref
val new_constructor : unit -> const
val function_counter : const ref
val new_function : unit -> const
val all_defined_functions : const list ref
val all_constructors : const list ref
val all_induction_positions : (const * (const * int) list) list ref
val all_induction_paths : path list ref
val clause_counter : int ref
val new_clause_number : unit -> int
val dico_sort_string : (sort, string) Dicos.bijective_dictionary
val dico_obs_sort : (sort, string) Dicos.bijective_dictionary
val is_obs_sort : sort -> bool
 val subsumes :
    ((int * (< string : string; .. > as 'a)) list -> (int * 'a) list) ->
    (((int * 'a) list -> (int * 'a) list) ->
     (int * 'a) list ->
     bool * 'b -> bool * (< string : string; .. > as 'c) -> (int * 'a) list) ->
    (int * 'a) list ->
    (bool * 'b) list -> (bool * 'c) list -> ('c -> bool) -> (int * 'a) list
val subsumes_w_rest :
  ('a -> 'b -> 'c -> 'a) -> exn -> 'a -> 'b list -> 'c list -> 'a * 'c list
val print_dico_obs_sort : unit -> unit
val print_dico_sort_string : unit -> unit
val dico_const_string : (const, string) Dicos.bijective_dictionary
val print_dico_const_string : unit -> unit
val dico_const_profile : (const, sort list) Dicos.reversible_dictionary
val sprint_profile : sort list -> string
val print_dico_const_profile : unit -> unit
val dico_const_sort : (const, sort) Dicos.reversible_dictionary
val print_dico_const_sort : unit -> unit
type symbol_prop = | Prop_ac | Prop_assoc | Prop_peano
val string_of_prop : symbol_prop -> string
val dico_properties : (const, symbol_prop) Dicos.assoc_dictionary
val print_dico_properties : unit -> unit
val symbol_is_ac : const -> bool
val symbol_is_assoc : const -> bool
val symbol_is_peano : const -> bool
class dictionary_arities :
  int ->
  object
    val value : (const, int * int) Hashtbl.t
    method add : const -> int * int -> unit
    method apply_f :
      (int * int -> int * int -> int * int) -> const -> int * int -> unit
    method clear : unit
    method empty : bool
    method find : const -> int * int
    method iter : (const -> int * int -> unit) -> unit
    method left_ar : const -> int
    method remove : const -> unit
    method replace : const -> int * int -> unit
    method right_ar : const -> int
    method size : int
    method total_ar : const -> int
  end
val dico_arities : dictionary_arities
val print_dico_arities : unit -> unit
val dico_sort_nullarity : (sort, bool) Dicos.dictionary
val print_dico_sort_nullarity : unit -> unit
val is_nullary : 'a * sort * 'b -> bool
val is_nullary_sort : sort -> bool
val compute_sort_nullarity : (sort * sort list list) list -> sort -> bool
val update_dico_sort_nullarity : unit -> unit
val dico_free_constructors : (const, bool) Dicos.dictionary
val print_dico_sort_nullarity : unit -> unit
val print_dico_free_constructors : unit -> unit
val dico_order : const Dicos.order_dictionary
val dico_infs : (const, const) Dicos.assoc_dictionary
val dico_order_cc : const Dicos.order_dictionary
val print_dico_order : unit -> unit
val print_dico_equivalence : unit -> unit
val print_dico_eq :
  ('a -> string) -> < iter : ('a -> 'a list -> unit) -> 'b; .. > -> 'b
type status = | Left | Right | Multiset
val sprint_status : status -> string
val change_default_status : string -> unit
val dico_id_status : (const, status) Dicos.dictionary
val print_dico_id_status : unit -> unit
val complete_status_dico : unit -> unit
val get_status : const -> status
val greater : bool -> const -> const -> bool
val inf_sym : const -> const -> bool
val equivalent : const -> const -> bool
val minimal : const list -> const -> bool
val check_status_equivalent_symbols : unit -> unit
val sprint_path : (const * int) list -> string
val dico_ind_positions_v0 : (const, (const * int) list list) Dicos.assoc_dictionary
val dico_ind_positions_v1 : (path, int * sort) Dicos.dictionary
val print_dico_ind_positions_v0 : unit -> unit
val print_dico_ind_positions_v1 : unit -> unit
val default_fill_order_dico_cc : unit -> unit
val update_profile : sort list -> sort list
val all_specifs : string list ref
val add_specif :
  string ->
  (sort * string) list ->
  (const * string * sort list * int * int * symbol_prop list) list -> unit
val predefined_specif_table : (string, unit -> unit) Hashtbl.t
val add_predefined_specif : string -> unit
val id_sort_bool : sort
val id_sort_nat : sort
val id_sort_int : sort
val id_symbol_true : const
val id_symbol_false : const
val add_bool_specif : unit -> unit
val specif_LA_defined : bool ref
val nat_specif_defined : bool ref
val int_specif_defined : bool ref
val id_symbol_zero : const
val id_symbol_s : const
val id_symbol_p : const
val add_int_specif : unit -> unit
val add_lists_specif : unit -> unit
val id_symbol_less : const
val id_symbol_leq : const
val id_symbol_greater : const
val id_symbol_geq : const
val id_symbol_plus : const
val id_symbol_times : const
val id_symbol_minus : const
val id_symbol_minus_nat : const
val add_nat_specif : unit -> unit
val sprint_term_list : < string : string; .. > list -> string
