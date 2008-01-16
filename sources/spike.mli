val return_code : int
val go_parsing : string -> Strategies.problem_token Queue.t
val reset_all : unit -> unit
val sprint_useful_values : unit -> string
val all_lemmas : Clauses.peano_context Clauses.clause list ref
val process_problem_token : Strategies.problem_token -> bool
val specif_counter : int ref
val name_specif : string ref
val mainloop : string -> unit
val usage_string : string
val speclist : (string * Arg.spec * string) list
val main : unit -> unit
val string_to_clause : string -> Clauses.peano_context Clauses.clause
val string_to_term : string -> Terms.term 

