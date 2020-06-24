
(*
   * Project: Spike ver 0.1
   * File: complement.ml
   * Content: complement inference rule
*)

open Values
open Diverse
open Io
open Order
open Symbols
open Terms
open Clauses

  (* defined but not used  *)
let compress verbose =
  let l = List.filter (fun x -> x#is_unit && x#is_boolean) conjectures_system#content in
  let ll = List.map (fun x -> List.hd (snd x#content)) l in
  let ll' = List.map (fun x -> x#revert_boolean) ll in
  if List.exists (fun x -> List.exists x#syntactic_equal ll) ll'
  then
    let () =
      if verbose
      then
        buffered_output ("Compression produced a refutation")
      else () in
    raise Refutation
  else ()

(* This rules makes a positive clause out of a boolean clause *)
let complement verbose clause is_strict level =
  let comp_count = ref 0 in
  let fn c =
    let () = incr comp_count in
    let n, p = c#content in
    let n1, n2 = List.partition (fun x -> (x#is_boolean || x#is_diff)) n
    and p1, p2 = List.partition (fun x -> x#is_boolean) p in
    let n'1 = List.map (fun x -> x#revert_boolean) n1 in
    let suf_f = 
      (fun x y ->
        let lhs, rhs = x#both_sides
        and lhs', rhs' = y#both_sides in
	let order_on_terms = !rpos in
        multiset_greater (order_on_terms false)  [lhs ; rhs] [lhs' ; rhs'])
    in
    let (m, o) = list_select_maximal_elements suf_f (n'1 @ p1) in
    let c' = c#build (n2 @ List.map (fun x -> x#revert_boolean) o) (p2 @ m) in
    let () = c'#set_bit complement_bit in
    let () = 
      if ((is_strict && clause_greater false false c c') || ((not is_strict) && clause_geq false false c c')) then
        if verbose
        then
          let () = buffered_output (!indent_string ^ "Complement: simplify\n" ^
          !indent_string ^ "\171 " ^ c#string ^ "\n" ^
          !indent_string ^ "\187 " ^ c'#string) in
          buffered_output ""
        else () 
      else failwith "fn"
      in
    c' 
  in
  if clause#has_bit complement_bit
  then failwith "complement"  (* échec *)
  else (* réussite *)
    let _ = if !maximal_output then buffered_output ("\n" ^ (indent_blank level) ^ "We will try the rule Complement " ) in
(*     let _ = if !maximal_output then buffered_output ((indent_blank level) ^ "on " ^ clause#string); flush stdout  in *)
    let new_c = try fn clause with (Failure _) -> failwith "complement" in
    [new_c]
