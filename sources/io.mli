val buffers_stack : string Stack.t
val current_buffer : string ref
val sub_buffer : string ref
val buffered_output : string -> unit
val buffer_next_level : unit -> unit
val buffer_collapse_level : unit -> unit
