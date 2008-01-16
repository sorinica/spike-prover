type concrete_literal =
  | Lit_rule of Terms.term * Terms.term
  | Lit_equal of Terms.term * Terms.term
  | Lit_diff of Terms.term * Terms.term
  class literal :
    concrete_literal ->
    object ('a)
      method apply_to_lit : (Terms.term -> Terms.term) -> 'a
      method bijective_renaming :
        (Symbols.var * Symbols.var) list ->
        'a -> (Symbols.var * Symbols.var) list
      method both_sides : Terms.term * Terms.term
      method both_sides_w_or : bool -> Terms.term * Terms.term
      method compute_pi : bool
      method compute_string : string
      method content : concrete_literal
      method copy : 'a
      method depth : int
      method equal : 'a -> bool
      method expand_sorts : 'a
      method flatten : 'a
      method fprint : out_channel -> unit
      method is_boolean : bool
      method is_diff : bool
      method is_oriented : bool
      method is_pi : bool
      method is_subterm : Terms.term -> int list
      method left_apply_to_lit : (Terms.term -> Terms.term) -> 'a
      method lefthand_side : Terms.term
      method matching_core :
        ((Symbols.var * Terms.term) list -> (Symbols.var * Terms.term) list) ->
        (Symbols.var * Terms.term) list ->
        literal -> (Symbols.var * Terms.term) list
      method pos_eliminate_trivial_literal : bool
      method pos_negative_clash : bool
      method pos_negative_decomposition : bool
      method pos_positive_clash : bool
      method pos_positive_decomposition : bool
      method pprint : Format.formatter -> unit
      method rename : 'a
      method rename_core : (Symbols.var * Symbols.var) list -> 'a
      method replace_subterm_at_pos : int list -> Terms.term -> 'a
      method replace_subterms : int ref -> Terms.term -> Terms.term -> 'a
      method revert_boolean : 'a
      method right_apply_to_lit : (Terms.term -> Terms.term) -> 'a
      method righthand_side : Terms.term
      method rpos_greater : 'a -> bool
      method sprint : string
      method string : string
      method substitute : (Symbols.var * Terms.term) list -> 'a
      method subterm_at_position : int list -> Terms.term
      method subterm_matching :
        (int list ->
         (Symbols.var * Terms.term) list ->
         bool -> (Symbols.var * Terms.term) list) ->
        literal -> int list * (Symbols.var * Terms.term) list * bool
      method subterm_matching_at_pos :
        ((Symbols.var * Terms.term) list ->
         bool -> (Symbols.var * Terms.term) list) ->
        int list -> literal -> (Symbols.var * Terms.term) list * bool
      method swap : 'a
      method syntactic_equal : literal -> bool
      method treesize : int
      method update_pos : 'a
      method variables : (Symbols.var * Symbols.sort * bool) list
      val content : concrete_literal
      val mutable is_pi : bool Diverse.pointer
      val mutable pos_eliminate_trivial_literal : bool ref
      val mutable pos_negative_clash : bool ref
      val mutable pos_negative_decomposition : bool ref
      val mutable pos_positive_clash : bool ref
      val mutable pos_positive_decomposition : bool ref
      val mutable string : string Diverse.pointer
      val variables : (Symbols.var * Symbols.sort * bool) list
    end

val test_well_founded_lit : concrete_literal -> bool

val compute_string_literal_caml : literal -> string
