
(*
   * Project: Spike ver 0.1
   * File: shell.ml
   * Content: Spike shell
*)

open Values
open Io
open Dummies
open Clauses
open Dicos
open Symbols
open Terms
open Test_sets

let print_dicos () =


  print_dico_sort_string () ;
  print_dico_sort_nullarity () ;
  print_dico_const_string () ;
  print_dico_properties () ;
  print_dico_const_profile () ;
  print_dico_const_sort () ;
  print_dico_arities () ;
  print_dico_id_status () ;
  print_dico_order () ;
  print_dico_equivalence () ;
  print_dico_rules ();
  print_dico_st () ;
  flush stdout

