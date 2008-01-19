
(*
   * Project: Spike ver 0.1
   * File: dummies.ml
   * Content: This file presents a class having strictly the same profile than the strategy class.
   * It is never used as such, but allows in turn to defined a dictionary and a parsing function (reference)
   * that will be necessary to the following.
   * It avoids cross-dependancy troubles between modules associated to the rules and the strategy module.
*)

open Diverse
open Io
open Dicos
open Symbols
open Terms
open Literals
open Polynoms
open Clauses

type literal_position = bool * int
type clausal_position = bool * int * position


(* Positions: can be
   - completely specified
   - only literal is specified
   - try first possible
   - ask *)
type position_argument =
    Pos_defined of clausal_position
  | Pos_litdefined of (bool * int)
  | Pos_all
  | Pos_query
  | Pos_dumb

let sprint_position_argument = function
    Pos_defined p -> sprint_clausal_position p
  | Pos_litdefined (b, n) -> (string_of_bool b) ^ "/" ^ (string_of_int n) ^ "/*"
  | Pos_all -> "*"
  | Pos_query -> "?"
  | Pos_dumb -> failwith "position in sprint_position_argument"

class strategy =

object ((self : 'a))
  
    method apply (_: bool) (_: (peano_context) clause list * (peano_context) clause list) (_: bool) = true
    method apply_at_pos (_: bool) (_: position_argument) (_: int) (_: (peano_context) clause list * (peano_context) clause list) (_: bool) = true
    method apply_new_goal (_: bool) (_: (peano_context) clause) (_: (peano_context) clause list * (peano_context) clause list) (_: bool) = true
    method apply_new_goal_at_pos (_: bool) (_: position_argument) (_: (peano_context) clause) (_:int) (_: (peano_context) clause list * (peano_context) clause list) (_: bool) = true
    method apply_to_subgoals (_: bool) (_: (peano_context) clause) (_: (peano_context) clause list) (_: (peano_context) clause
      list) (_: bool) = true
    method compute_string = ""
    method fullstring = ""
    method is_query = true
    method string = ""
    method pprint f = Format.fprintf f "@[@ %s@]" self#string
      
    method fprint o = fprint o self
    method sprint   = sprint   self

  end


(* The dictionary and its default entries *)
let dico_st = (new dictionary 101: (string, strategy) dictionary)

let print_dico_st () =
  buffered_output "dico_st:" ;
  let fn s st = buffered_output (s ^ " = " ^ st#string) in
  dico_st#iter fn

let sprint_dico_st () =
  let str = ref "" in
  let fn s st = str := !str ^ "\n" ^ s ^ " = " ^ st#string in
  let () = dico_st#iter fn
  in !str

let name_strat_query = "query"

let name_strat_generate_reduce = "generate_reduce"

(* Dummy function to parse a strategy. Updated in the lexer *)
let spike_parse_strategy = ref (fun (st: strategy) () -> st)

(* Dummy function to parse a list of systems. Updated in the lexer *)
let spike_parse_list_of_systems = ref (fun () -> ([]: which_system list))

(* Dummy function to parse a clausal position. Updated in the lexer *)
let spike_parse_clausal_lhs_position = ref (fun (_: (peano_context) clause) () -> Pos_all)

(* Dummy function to parse a literal clausal position. Updated in the lexer *)
let spike_parse_literal_position_in_clause = ref (fun (_: (peano_context) clause) () -> Pos_all)

(* Dummy function to parse a substitution. Updated in the lexer *)
let spike_parse_substitution = ref (fun () -> ([]: (var * term) list))

(* Dummy function to parse an integer. Updated in the lexer *)
let spike_parse_positive_int = ref (fun (_: (peano_context) clause) () -> 0)

(* Dummy function to parse an integer. Updated in the lexer *)
let main_interact = ref (fun  () -> let () = print_string "\n I am in dummies.ml !" in ())



(* Type of shell commands *)
type shell_commands =
    Command_strategy of strategy
  | Command_next
  | Command_run
  | Command_previous
  | Command_display
  | Command_exit
  | Command_error

(* Parse command line *)
let spike_parse_shell_command = ref (fun () -> Command_error)

(*let pi_strat = ref (new strategy)*)
  
let dico_patterns = (new dictionary 101: (int, (Clauses.peano_context Clauses.clause list list)) dictionary)

let dico_rules = (new dictionary 101: (int, (Clauses.peano_context Clauses.clause list)) dictionary)

let print_dico_rules () =
  buffered_output "dico_rules:";
  dico_rules#iter
    (fun k lr ->
       try buffered_output (dico_const_string#find k) with Not_found -> failwith "raising Not_found in print_dico_rules";
       buffered_output " --> ";
       buffered_output (sprint_list "\n" (fun r -> r#string)
	 (* (fun x -> string_of_int x) *) lr))
;;

