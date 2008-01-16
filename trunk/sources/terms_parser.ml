
(*
   * Project: Spike ver 0.1
   * File: terms_parser.ml
   * Content: We don't rely on the parser to build the terms. Instead, we use a tree structure that
   allows to discard use of parenthesis except for priorities definitons *)

open Values
open Diverse
open Dicos
open Symbols
open Terms
open Str
open Io

type incomplete_tree =
    Ivar of var
  | Iterm of const * incomplete_tree pointer list

let  sprint_incomplete_tree_pointer t = 
  let rec fn =
    function
	Undefined -> "***"
      | Defined (Iterm (s, l)) ->
	  let v = try dico_const_string#find s with Not_found -> failwith "raising Not_found in sprint_incomplete_tree_pointer" in
	  (v ^ (" (" ^ 
	  (sprint_list ", " fn l)
	  ^ ") "))
      | Defined (Ivar x) -> if x < 0 then ("E" ^ (string_of_int x)) else  ("U" ^ (string_of_int x))
  in
 (fn t)

let rec sprint_incomplete_tree t = 
  let rec fn = 
    function
	Iterm (s, l) ->
	  (string_of_int s) ^  " (" ^ 
	  (sprint_list ", " sprint_incomplete_tree_pointer l) ^
	  ") "
      | Ivar x -> if x < 0 then ("E" ^ (string_of_int x)) else  ("U" ^ (string_of_int x))
  in
 (fn t)
        (* This type is needed to allow precedence as defined by parenthesis *)
type term_token =
    TT_ident of string
  | TT_tree of incomplete_tree

let print_term_token = function
    TT_ident s -> buffered_output ("TT_ident (" ^ s ^ ") ")
  | TT_tree t -> buffered_output ("TT_tree (" ^  (sprint_incomplete_tree t) ^  ") ")

(*
   * Useful values for parsing:
   * - the current incomplete tree
   * - a stack of incomplete trees (that will be used to fill prefixed symbols arguments)
   * - a local variables counter
*)
let yy_incomplete_tree = ref (Undefined: incomplete_tree pointer)
let yy_terms_stack = (Stack.create (): incomplete_tree pointer Stack.t)
let yy_tmp_vars = ref ([]: (string * var) list) (* id <-> string assoc for variables *)
let yy_tmp_sorts = ref ([]: (var * sort) list) (* id <-> sort assoc for variables *)
let yy_tmp_vars2 = ref ([]: (string * var) list) (* id <-> string assoc for variables *)
let yy_tmp_sorts2 = ref ([]: (var * sort) list) (* id <-> sort assoc for variables *)
let yy_tmp_equiv_dico = (new equivalence_dictionary 101: int equivalence_dictionary) (* for typewise mutually dependent variables *)

(* Reset these values *)
let reset_yy_values () =
  yy_tmp_vars := [] ;
  yy_tmp_sorts := [] ;
  yy_tmp_param_sorts := [] ;
  yy_tmp_equiv_dico#clear ;
  yy_incomplete_tree := Undefined ;
  Stack.clear yy_terms_stack

(* Fill the variables array with given values *)
let rec fill_yy_values = function
    [] -> ()
  | (v, s, b)::t ->
      yy_tmp_vars := generic_insert_sorted (sprint_var v s b, v) !yy_tmp_vars ;
      yy_tmp_sorts := generic_insert_sorted (v, s) !yy_tmp_sorts ;
      fill_yy_values t

(* All existential variables contained in axioms and lemmas are automatically generated.
   In other cases, they are deduced syntactically according to a specific pattern *)

let pick_pos_codes = ref true

(* Find the code of a variable in the yy_tmp_vars list, generate a new one otherwise *)
let code_of_var x =
  try
    List.assoc x !yy_tmp_vars
  with Not_found ->
    let len = List.length !yy_tmp_vars + 1 in
    if !pick_pos_codes 
    then (yy_tmp_vars := (x, len) :: !yy_tmp_vars ; len)
    else 
          let pattern = regexp "e[1-9][0-9]*" in
	  let is_existential x = string_match pattern x 0 in
	  if is_existential x  then (yy_tmp_vars := (x, - len)::!yy_tmp_vars ; - len)
	  else (yy_tmp_vars := (x, len) :: !yy_tmp_vars ; len)

(* Checks whether no Undefined node exists in an incomplete tree *)
let incomplete_tree_is_complete t =
  let rec fn = function
      [] -> true
    | Undefined::t -> let () = if !debug_mode then print_string "\nTree is incomplete" in false
    | (Defined h)::t ->
        match h with
          Ivar _ -> fn t
        | Iterm (_, l) -> fn l && fn t in
  fn [t]

(* Prints error message and raise Parsing.Parse_error *)
let parse_failwith s =
  error_message := s ;
  raise Parsing.Parse_error


(* ********************************************************************** *)
(* ********************************************************************** *)
(* ****** Code inspired from the typing check of the ASL language ******* *)
(* ********************************************************************** *)
(* ********************************************************************** *)

let rec nth n = function
  | []  -> raise (Failure "nth")
  | x :: l -> if n = 1 then x else nth (n - 1) l;;

type asl_type =
   | Unknown
   | Number
   | TypeVar of vartype
   | Arrow of asl_type * asl_type

and vartype = VT of int * asl_type
and asl_type_scheme = Forall of int list * asl_type
;;

type asl =
   | Const_asl of int
   | Var_asl of int
   | Cond of asl * asl * asl
   | App of asl * asl
   | Abs of string * asl

and top_asl = Decl of string * asl;;

exception TypingBug of string;;

let counter = ref 0

  (* Generating and resetting unknowns *)

let new_vartype () =
  counter := !counter+1; VT (!counter, Unknown)

let reset_vartypes () = counter := 0

let rec shorten t =
    match t with
    | TypeVar (VT(_,Unknown)) -> t
    | TypeVar (VT(_, TypeVar (VT(x, Unknown)))) -> TypeVar (VT(x, Unknown))
    | TypeVar (VT(x, TypeVar (VT(y, Number)))) -> shorten (TypeVar (VT(x, Number)))
    | TypeVar (VT(x, TypeVar (VT(y, Arrow (a, b))))) -> shorten (TypeVar (VT(x, Arrow (a,b))))
    | TypeVar (VT(x, TypeVar (VT(y, TypeVar a)))) -> shorten (TypeVar (VT(x, TypeVar a)))
    | TypeVar (VT (_, Arrow (x, y))) -> Arrow (x, y)
    | TypeVar (VT (_, Number)) -> Number
    | Unknown -> raise (TypingBug "shorten")
    | Arrow (x,y) -> Arrow (x, y)
    | Number -> Number

exception TypeClash of asl_type * asl_type

let occurs (VT (n, _)) =
  let rec occrec = function
    | TypeVar (VT(m,  Unknown)) -> (n = m)
    | TypeVar (VT(m,  TypeVar x)) -> (n = m) || (occrec (TypeVar x))
    | TypeVar (VT(m,  Number)) -> (n = m) || (occrec Number)
    | TypeVar (VT(m,  Arrow (x,y))) -> (n = m) || (occrec (Arrow (x, y)))
    | Number -> false
    | Arrow (t1, t2) -> (occrec t1) || (occrec t2)
    | Unknown -> raise (TypingBug "occurs") in
 occrec


let rec unify (tau1, tau2) =
  let tau1' = shorten tau1 
  and tau2' = shorten tau2 in
  match tau1', tau2' with
    | (* type variable n and type variable m *)
	(TypeVar (VT(n, Unknown))), (TypeVar (VT (m, Unknown))) ->
	if n = m then (tau1', tau2') else (TypeVar (VT(n,(TypeVar (VT (m, Unknown))))), TypeVar (VT (m, Unknown)))
    | (* type t1 and type variable *)
	Number, ((TypeVar (VT (x, Unknown))) as t2) ->
	if not(occurs (VT (x, Unknown)) Number) then Number, (TypeVar (VT (x, Number))) 
	else raise (TypeClash (Number, t2))
    |	(Arrow (a,b)), ((TypeVar (VT (x, Unknown))) as t2) ->
	if not(occurs (VT (x, Unknown)) (Arrow (a,b))) then (Arrow (a,b)), (TypeVar (VT (x, (Arrow (a,b))))) 
	else raise (TypeClash ((Arrow (a, b)), t2))
    |	Unknown, ((TypeVar (VT (x, Unknown))) as t2) ->
	if not(occurs (VT (x, Unknown)) Unknown) then Unknown, (TypeVar (VT (x, Unknown))) 
	else raise (TypeClash (Unknown, t2))

    | (* type variable and type t2 *)
	((TypeVar (VT (x, Unknown)) as tv) as t1), Number ->
	if not(occurs (VT (x, Unknown)) Number) then (TypeVar (VT (x, Number))), Number
	else raise (TypeClash (t1, Number))
    |	((TypeVar (VT (x, Unknown)) as tv) as t1), (Arrow (a, b)) ->
	if not(occurs (VT (x, Unknown)) (Arrow (a, b))) then (TypeVar (VT (x, (Arrow (a, b))))), (Arrow (a, b))
	else raise (TypeClash (t1, (Arrow (a, b))))
    |	((TypeVar (VT (x, Unknown)) as tv) as t1), Unknown ->
	if not(occurs (VT (x, Unknown)) Unknown) then (TypeVar (VT (x, Unknown))), Unknown
	else raise (TypeClash (t1, Unknown))
    | Number, Number -> (Number, Number)
    | Arrow (t1, t2), (Arrow (t'1, t'2) as t) -> 
	let t1new, t'1new = unify(t1, t'1) in
	let t2new, t'2new = unify(t2, t'2) in
	t1new, t2new
    | ((Number as t1), (Unknown as t2)) -> raise (TypeClash (t1, t2))
    | ((Unknown as t1), (Number as t2)) -> raise  (TypeClash (t1, t2)) 
    | (((Arrow (a, b)) as t1), (Unknown as t2)) -> raise  (TypeClash (t1, t2)) 
    | ((Unknown as t1), ((Arrow (a, b)) as t2)) -> raise  (TypeClash (t1, t2)) 
    | (((Arrow (a, b)) as t1), (Number as t2)) -> raise  (TypeClash (t1, t2)) 
    | ((Number as t1), ((TypeVar (VT (_, (Arrow (_, _))))) as t2)) -> raise (TypeClash (t1, t2)) 
    | ((Number as t1), ((TypeVar (VT (_, Number))) as t2)) -> raise  (TypeClash (t1, t2)) 
    | ((Number as t1), ((TypeVar (VT (_, (TypeVar _)))) as t2)) -> raise  (TypeClash (t1, t2)) 
    | ((Number as t1), ((Arrow (_, _)) as t2)) -> raise  (TypeClash (t1, t2)) 
    | (((Arrow(x, y)) as t1), ((TypeVar (VT (_, (Arrow (_, _))))) as t2)) -> raise (TypeClash (t1, t2)) 
    | (((Arrow(x, y)) as t1), ((TypeVar (VT (_, Number))) as t2)) -> raise  (TypeClash (t1, t2)) 
    | (((Arrow(x, y)) as t1), ((TypeVar (VT (_, (TypeVar _)))) as t2)) -> raise  (TypeClash (t1, t2)) 
    | ((Unknown as t1), (Unknown as t2)) -> raise (TypeClash (t1, t2))
    | ((Unknown as t1), ((TypeVar (VT (_, (Arrow (_, _))))) as t2)) -> raise (TypeClash (t1, t2)) 
    | ((Unknown as t1), ((TypeVar (VT (_, Number))) as t2)) -> raise  (TypeClash (t1, t2)) 
    | ((Unknown as t1), ((TypeVar (VT (_, (TypeVar _)))) as t2)) -> raise  (TypeClash (t1, t2)) 
    | (((TypeVar (VT (_, (Arrow (_, _))))) as t1, t2)) -> raise (TypeClash (t1, t2)) 
    | (((TypeVar (VT (_, Number))) as t1, t2)) -> raise  (TypeClash (t1, t2)) 
    | (((TypeVar (VT (_, (TypeVar _)))) as t1, t2)) -> raise  (TypeClash (t1, t2)) 
    | ((TypeVar (VT (_, Unknown))) as t1), ((TypeVar (VT (_, (Arrow (_, _))))) as t2) -> raise  (TypeClash (t1, t2)) 
    | ((TypeVar (VT (_, Unknown))) as t1), ((TypeVar (VT (_, Number))) as t2) -> raise  (TypeClash (t1, t2)) 
    | ((TypeVar (VT (_, Unknown))) as t1), ((TypeVar (VT (_, TypeVar _))) as t2) ->  raise  (TypeClash (t1, t2)) 

let init_env =  ["+"; "-"; "*"; "/"; "="]            

let global_env = ref init_env 

let init_typing_env =
    List.map
     (function s ->
       Forall([], Arrow(Number, Arrow(Number, Number))))
     init_env 

let global_typing_env = ref init_typing_env

let vars_of_type tau =
 let rec vars vs = function
   | Number -> vs
   | TypeVar (VT ( n, Unknown)) ->
       if List.mem n vs then vs else n :: vs
   | TypeVar (VT ( _, Number)) -> vars vs Number
   | TypeVar (VT ( _, Arrow (x,y))) -> vars vs (Arrow (x,y))
   | TypeVar (VT ( _, TypeVar x)) -> vars vs (TypeVar x)
   | Arrow(t1, t2) -> vars (vars vs t1) t2
   | Unknown -> raise (TypingBug "vars_of_type") in
 vars [] tau

let flat l = List.fold_left ( @) [] l

let subtract f l =
 match f, l with
 | f, [] -> f
 | f, e ->
    let rec subtract_e = function
      | [] -> []
      | elem :: l ->
         if List.mem elem e then subtract_e l else elem :: subtract_e l in
 subtract_e f


let rec make_set = function
  | []  -> []
  | x :: l -> if List.mem x l then make_set l else x :: make_set l



let unknowns_of_type (bv, t) = subtract (vars_of_type t) bv

let unknowns_of_type_env env =
    flat (List.map (function Forall(gv, t) -> unknowns_of_type (gv, t)) env)


let generalise_type (gamma, tau) =
  let genvars =
    make_set (subtract (vars_of_type tau) (unknowns_of_type_env gamma))
  in Forall(genvars, tau)


let gen_instance (Forall(gv, tau)) = 
  (* We associate a new unknown to each generic variable *)
  let unknowns =
      List.map (function n -> n, TypeVar(new_vartype())) gv in
  let rec ginstance = function
    | TypeVar (VT ( n, Unknown)) as t ->
        (try List.assoc n unknowns
        with Not_found -> t)
      | TypeVar (VT (_, Number)) -> ginstance Number
      | TypeVar (VT (_, (Arrow (x, y)))) -> ginstance (Arrow (x, y))
	| TypeVar (VT (_, TypeVar x)) -> ginstance (TypeVar x)
      | Number -> Number
      | Arrow (t1, t2) -> Arrow(ginstance t1, ginstance t2)
      | Unknown -> raise (TypingBug "gen_instance")
      in ginstance tau


let rec asl_typing_expr gamma =
  let rec type_rec = function
  | Const_asl _ -> Number
  | Var_asl n ->
      let sigma =
        try nth n gamma
        with Failure _ -> raise (TypingBug "Unbound")
      in gen_instance sigma
  | Cond (e1, e2, e3) -> 
      let _ = unify(Number, type_rec e1)
      and t2 = type_rec e2 and t3 = type_rec e3 in 
      let _ = unify(t2, t3) in t3
  | App((Abs(x, e2) as f), e1) -> (* LET case *)
      let t1 = type_rec e1 in
      let sigma = generalise_type (gamma, t1)
      in asl_typing_expr (sigma :: gamma) e2
   | App((Const_asl x) as e1, e2) ->
      let u = TypeVar(new_vartype()) in
      let _ = unify(type_rec e1, Arrow(type_rec e2, u)) in u
   | App((Var_asl x) as e1, e2) ->
      let u = TypeVar(new_vartype()) in
      let _ = unify(type_rec e1, Arrow(type_rec e2, u)) in u
   | App((Cond (x, y, z)) as e1, e2) ->
      let u = TypeVar(new_vartype()) in
      let _ = unify(type_rec e1, Arrow(type_rec e2, u)) in u
   | App((App (x, y)) as e1, e2) ->
      let u = TypeVar(new_vartype()) in
      let _ = unify(type_rec e1, Arrow(type_rec e2, u)) in u
  | Abs(x, e) ->
      let u = TypeVar(new_vartype()) in
      let s = Forall([], u)
      in Arrow(u, asl_typing_expr (s :: gamma) e) 
  in
  type_rec


let tvar_name n =
 (* Computes a name "'a", ... for type variables, *)
 (* given an integer n representing the position  *)
 (* of the type variable in the list of generic   *)
 (* type variables                                *)
 let rec name_of n =
    let q, r = (n / 26), (n mod 26) in
    let s = String.make 1 (char_of_int (96 + r)) in
    if q = 0 then s else name_of q ^ s
 in "'" ^ name_of n


let print_type_scheme (Forall(gv, t)) =
 (* Prints a type scheme.               *)
 (* Fails when it encounters an unknown *)
 let names =
   let rec names_of = function
   | (n, []) -> []
   | (n, (v1 :: lv)) -> tvar_name n :: names_of (n + 1, lv) in
   names_of (1, gv) in
 let tvar_names = List.combine (List.rev gv) names in
 let rec print_rec = function
   | TypeVar (VT ( n, Unknown)) ->
        let name =
            try List.assoc n tvar_names
            with Not_found ->
              raise (TypingBug "Non generic variable")
        in print_string name
   | TypeVar (VT ( _, Number)) -> print_rec Number
   | TypeVar (VT ( _, TypeVar x)) -> print_rec (TypeVar x)
   | TypeVar (VT ( _, Arrow (x, y))) -> print_rec (Arrow (x, y))
   | Number -> print_string "Number"
   | Arrow(t1, t2) ->
          print_string "("; print_rec t1;
          print_string " -> "; print_rec t2;
          print_string ")"
   | Unknown -> raise (TypingBug "print_type_scheme") in
  print_rec t


let typing (Decl(s, e)) =
  reset_vartypes();
  let tau =
    try asl_typing_expr !global_typing_env e
    with TypeClash(t1, t2) ->
      let vars = vars_of_type(t1) @ vars_of_type(t2) in
      print_string "*** ASL Type clash between ";
      print_type_scheme (Forall(vars, t1));
      print_string " and ";
      print_type_scheme (Forall(vars, t2));
      reset_vartypes();
      raise (Failure "ASL typing")
  in                    
  generalise_type ([], tau)
;;

global_env:=init_env

(* typing (parse_top "x=1;");; *)
(* typing (parse_top "y = + 2 ((\\x.x) 3);");; *)
(* typing (parse_top "z = C (+ 0 1) 1 0;");; *)
(* typing (parse_top "i = \\x.x;");; *)
(* typing (parse_top "t = + (i 1) (i i 2);");; *)
(* typing (parse_top "f = (\\x.x x) (\\x.x);");; *)
(* typing (parse_top "a = + (\\x.x) 1;");; *)
(* typing (parse_top "z = \\f.((\\x.f(\\z.(x x)z)) (\\x.f(\\z.(x x)z)));");; *)
(* global_env := `z`::init_env; *)
(* global_typing_env:= *)
(*     (Forall([1], *)
(*      Arrow(Arrow(TypeVar{index=1;value=Unknown}, *)
(*                    TypeVar{index=1;value=Unknown}), *)
(*             TypeVar{index=1;value=Unknown}))) *)
(*    ::init_typing_env; *)
(* ();; *)
(* typing (parse_top "f = z(\\f.(\\n. C (= n 0) 1 ( * n (f (- n 1)))));");; *)
(* typing (parse_top "x = f 8;");; *)
(* typing (parse_top *)
(*   "b = z(\\b.(\\n. C (= n 1) 1 (C (= n 2) 1 (+ (b(- n 1)) (b(- n 2))))));");; *)
(* typing (parse_top "x = b 9;");; *)

