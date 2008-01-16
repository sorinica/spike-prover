type incomplete_tree =
  | Ivar of Symbols.var
  | Iterm of Symbols.const * incomplete_tree Diverse.pointer list
val sprint_incomplete_tree_pointer : incomplete_tree Diverse.pointer -> string
val sprint_incomplete_tree : incomplete_tree -> string
type term_token = | TT_ident of string | TT_tree of incomplete_tree
val print_term_token : term_token -> unit
val yy_incomplete_tree : incomplete_tree Diverse.pointer ref
val yy_terms_stack : incomplete_tree Diverse.pointer Stack.t
val yy_tmp_vars : (string * Symbols.var) list ref
val yy_tmp_sorts : (Symbols.var * Symbols.sort) list ref
val yy_tmp_vars2 : (string * Symbols.var) list ref
val yy_tmp_sorts2 : (Symbols.var * Symbols.sort) list ref
val yy_tmp_equiv_dico : int Dicos.equivalence_dictionary
val reset_yy_values : unit -> unit
val fill_yy_values : (Symbols.var * Symbols.sort * bool) list -> unit
val pick_pos_codes : bool ref
val code_of_var : string -> Symbols.var
val incomplete_tree_is_complete : incomplete_tree Diverse.pointer -> bool
val parse_failwith : string -> 'a

val nth : int -> 'a list -> 'a 
type asl_type =
    Unknown
  | Number
  | TypeVar of vartype
  | Arrow of asl_type * asl_type
and vartype = VT of  int * asl_type
type asl_type_scheme = Forall of int list * asl_type
type asl =
    Const_asl of int
  | Var_asl of int
  | Cond of asl * asl * asl
  | App of asl * asl
  | Abs of string * asl
type top_asl = Decl of string * asl
exception TypingBug of string

val counter : int ref 
val new_vartype : unit -> vartype 
val reset_vartypes : unit -> unit 
val shorten : asl_type -> asl_type 
exception TypeClash of asl_type * asl_type
val occurs : vartype -> asl_type -> bool 
val unify : asl_type * asl_type -> asl_type * asl_type
val init_env : string list 
val init_typing_env : asl_type_scheme list 
val global_typing_env : asl_type_scheme list ref 
val vars_of_type : asl_type -> int list 
val flat : 'a list list -> 'a list 
val subtract : 'a list -> 'a list -> 'a list 
val make_set : 'a list -> 'a list 
val unknowns_of_type : int list * asl_type -> int list 
val unknowns_of_type_env : asl_type_scheme list -> int list 
val generalise_type : asl_type_scheme list * asl_type -> asl_type_scheme
val gen_instance : asl_type_scheme -> asl_type 
val asl_typing_expr : asl_type_scheme list -> asl -> asl_type 
val tvar_name : int -> string 
val print_type_scheme : asl_type_scheme -> unit 
val typing : top_asl -> asl_type_scheme 
