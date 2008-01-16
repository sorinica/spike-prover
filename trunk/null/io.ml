(*
   * Project: Spike ver 0.1
   * File: io.ml
   * Content: input / output
*)

open Values;;
  
   (* Output buffers *)
let buffers_stack = Stack.create ();;
let current_buffer = ref "";;
let sub_buffer = ref "";;  (* it contains the proof in the next level  *)

  (* buffered display *)
let buffered_output s =
  if !depth_counter > 1 then current_buffer := !current_buffer ^ s ^ "\n"
  else let () = print_endline s in flush stdout
;;

  (* Create buffer for subproof *)
let buffer_next_level () =
  let () = incr depth_counter
  and () = maxdepth_counter := max !depth_counter !maxdepth_counter
  and () = incr_indent indent_string in
  Stack.push !current_buffer buffers_stack
;;

  (* Collapse next level *)
let buffer_collapse_level () =
  let () = decr depth_counter
  and () = sub_buffer := !current_buffer
  and () = decr_indent indent_string in
  current_buffer := Stack.pop buffers_stack
;;

