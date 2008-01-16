
(*
   * Project: Spike ver 0.1
   * File: pi.ml
   * Content: declaration of the virtual class pi_object
*)

open Diverse
  
class virtual pi_object =
  
  object (self: 'a)

    val mutable is_pi = (Undefined: bool pointer)

    method is_pi =
      match is_pi with
        Undefined ->
          let b = self#compute_pi in
          let () = is_pi <- Defined b in
          b
      | Defined b -> b

  end

let name_strat_pi = "pi_strat"
