val print_coq: string -> unit
val induction: string list -> unit
val rewrite_nonum: int -> string -> unit
val rewrite: int -> string -> unit
val rewrite_last_induction : unit -> unit
val next_proof: unit -> unit
val delete_set: int -> unit
val todo: string -> unit
val renumber_clauses : unit -> unit
val prepare_rewrite : string -> unit
val prepare_rewrite_last_induction : unit -> unit
val contextual_rewriting : int -> unit
val inconsistency: int -> unit;;
