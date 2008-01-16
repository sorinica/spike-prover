
(*
   * Project: Spike ver 0.1
   * File: terms.ml
   * Content: classes for dictionaries
*)

open Diverse
open Io

(* Normal dictionary. No reverse association *)
class ['a, 'b] dictionary ini_size =
  object (self)
    val value = (Hashtbl.create ini_size : ('a, 'b) Hashtbl.t)
    method add k v = Hashtbl.add value k v
    method remove k = Hashtbl.remove value k
    method find k = Hashtbl.find value k
    method iter f = Hashtbl.iter f value
    method replace k v =
      let () = Hashtbl.remove value k in Hashtbl.add value k v
    method size =
      let l = ref 0 in let fn x y = incr l in Hashtbl.iter fn value; !l
    method empty = self#size = 0
    method clear = Hashtbl.clear value
    method apply_f f k v =
      try
        let v' = self#find k in let w = f v v' in self#remove k; self#add k w
      with
        Not_found -> self#add k v
  end;;

(* k is the key, v should be inserted in the list associated to k  *)
let htbl_update htbl k v =
  try
    let l = Hashtbl.find htbl k in
    let l' = generic_insert_sorted v l in
    Hashtbl.remove htbl k; Hashtbl.add htbl k l'
  with
    Not_found -> Hashtbl.add htbl k [v]
;;

  (* the list vl is merged to the list associated to k  *)
let htbl_update_list htbl k vl =
  try
    let l = Hashtbl.find htbl k in
    let l' = generic_merge_sorted_lists vl l in
    Hashtbl.remove htbl k; Hashtbl.add htbl k l'
  with
    Not_found -> Hashtbl.add htbl k vl
;;

(* Dictionary holding extra information on value -> key bindings *)
class ['a, 'b] reversible_dictionary ini_size =
  object (self)
    inherit ['a, 'b] dictionary ini_size as super
    val revert_value = (Hashtbl.create ini_size : ('b, 'a list) Hashtbl.t)
    method add k v =
      try 
	Hashtbl.remove value k;
	Hashtbl.add value k v;
	htbl_update revert_value v k
      with Not_found -> failwith "raising Not_found in add" 

    method remove k =
      try
        let v = Hashtbl.find value k in
        Hashtbl.remove value k;
        let l = Hashtbl.find revert_value v in
        let l' = generic_remove_sorted k l in
        Hashtbl.remove revert_value v; Hashtbl.add revert_value v l'
      with
        Not_found -> failwith "raising Not_found in remove (1)"
    method find_keys v = Hashtbl.find revert_value v
    method clear = super#clear; Hashtbl.clear revert_value
  end;;

(* The same for for bijective associations *)
class ['a, 'b] bijective_dictionary ini_size =
  object (self)
    inherit ['a, 'b] dictionary ini_size as super
    val revert_value = (Hashtbl.create ini_size : ('b, 'a) Hashtbl.t)
    method add k v = super#add k v; Hashtbl.add revert_value v k
    method remove k =
      try
        let v = self#find k in super#remove k; Hashtbl.remove revert_value v
      with
        Not_found -> failwith "raising Not_found in remove (2)"
    method find_key v = try Hashtbl.find revert_value v with
       Not_found -> failwith "find_key"
    method clear = super#clear; Hashtbl.clear revert_value
  end;;

(* these dictionaries hold associations in both key -> values and value -> keys directions.
   It means that in both directions, we have lists of values.
   We don't use the internal hidding feature of hash tables, but rather sorted lists.
   Some checks still remain to be done upon adding and removal. *)
class ['a, 'b] assoc_dictionary ini_size =
  object (self)
    val value = (Hashtbl.create ini_size : ('a, 'b list) Hashtbl.t)
    val revert_value = (Hashtbl.create ini_size : ('b, 'a list) Hashtbl.t)
    method size =
      let l = ref 0 in let fn x y = incr l in Hashtbl.iter fn value; !l
    method empty = self#size = 0
    method add k v = htbl_update value k v; htbl_update revert_value v k
    method merge k l =
      htbl_update_list value k l;
      List.iter (fun x -> htbl_update revert_value x k) l
    method exists k =
      try let _ = Hashtbl.find value k in true with
        Not_found -> false
    method find k = Hashtbl.find value k
    method find_keys v = Hashtbl.find revert_value v
    method clear = Hashtbl.clear value; Hashtbl.clear revert_value
    method iter f = Hashtbl.iter f value
  end;;

(* A virtual class for dictionaries holding information about a relation.
   The rehash method will have to be overloaded to define the
   completion function 
Defined, but not used *)

class virtual ['a] relation_dictionary ini_size =
  object (self)
    inherit ['a, 'a list] dictionary ini_size
    method add_couple k v =
      htbl_update value k v;
      try let _ = self#find v in () with
        Not_found -> self#add v []
    method related k v =
      try let l = self#find k in List.mem v l with
        Not_found -> false
    method dub v = {< value = v >}
    method virtual rehash : unit
  end;;

class ['a] equivalence_dictionary ini_size =
  object (self)
    val content = (Hashtbl.create ini_size : ('a, 'a list) Hashtbl.t)

    val roots = (Hashtbl.create ini_size : ('a, 'a) Hashtbl.t)

    method init l =
      List.iter (fun x -> Hashtbl.add content x [x]; Hashtbl.add roots x x) l

    method add_couple x x' =
      try
        let r = Hashtbl.find roots x in
        try
          let r' = Hashtbl.find roots x' in
          if r = r' then ()
          else
            let l = Hashtbl.find content r
            and l' = Hashtbl.find content r' in
            let () = Hashtbl.remove content r
            and () = Hashtbl.remove content r' in
            let () = Hashtbl.add content r (generic_merge_sorted_lists l l')
            and () =
              List.iter
                (fun v ->
                   let () = Hashtbl.remove roots v in Hashtbl.add roots v r)
                l'
            in
            ()
        with Not_found -> (* r found, r' not found *)
          let l = Hashtbl.find content r in
          let () = Hashtbl.remove content r in
          let () = Hashtbl.add content r (generic_insert_sorted x' l) in
          let () = Hashtbl.add roots x' r in
          ()
      with Not_found -> (* r not found *)
        try
          let r' = Hashtbl.find roots x' in
          let l = Hashtbl.find content r' in
          let () = Hashtbl.remove content r' in
          let () = Hashtbl.add content r' (generic_insert_sorted x l) in
          let () = Hashtbl.add roots x r' in
          ()
        with Not_found -> (* None found *)
          let () = Hashtbl.add content x (generic_merge_sorted_lists [x] [x']) in
          let () = Hashtbl.add roots x x
          and () = Hashtbl.add roots x' x in
          ()

    method print f =
      let fn k v = buffered_output (f k ^ " --> " ^ sprint_list ", " f v) in
      Hashtbl.iter fn content
    method fill f =
      let rec fn el =
        function
          [] -> ()
        | h :: t -> let () = if f el h then self#add_couple el h in fn el t
      in
      function
        [] -> ()
      | h :: t -> let () = fn h t in self#fill f t
    method iter f = Hashtbl.iter f content
    method find k = let r = Hashtbl.find roots k in Hashtbl.find content r
    method clear = let () = Hashtbl.clear content in Hashtbl.clear roots

    method remove k =
      let r = Hashtbl.find roots k in
      let l = Hashtbl.find content r in
      let () = List.iter (Hashtbl.remove roots) l in Hashtbl.remove content r
    method size =
      let l = ref 0 in let fn x y = incr l in Hashtbl.iter fn content; !l
    method empty = self#size = 0

  end;;

let dico_equivalence = new equivalence_dictionary 101;;



(* Specialization of the previous for an order relation *)
class ['a] order_dictionary ini_size =
  object (self)
    val content = (Hashtbl.create ini_size : ('a, 'a list) Hashtbl.t)

    method init l = List.iter (fun x -> Hashtbl.add content x []) l


    method related x = 
      let res = ref ([]:'a list) in 
      let () = self#iter (fun u l -> if List.mem x l then res:= (generic_insert_sorted u !res))
      in !res

    method add_couple x x' =
      let lequiv_x =  
	try dico_equivalence#find x with 
	    Not_found -> [x] 
      in
      if List.mem x' lequiv_x then ()
      else
	let lequiv_x' = 
	  try dico_equivalence#find x' with
	      Not_found -> [x']
	in
	if List.mem x lequiv_x' then ()
	else 
	  let l =
            try Hashtbl.find content x with
		Not_found -> []
	  and l' =
            try Hashtbl.find content x' with
		Not_found -> []
	  in
	  let new_l' = 
	    if List.mem x l' then 
	      let () = dico_equivalence#fill (fun x' y' -> true) [x; x'] in
	      let l'' = remove_all_el ( = ) x l' in
	      let () = Hashtbl.remove content x' in
	      let () = Hashtbl.add content x' l'' in
	      l''
	    else
	      generic_insert_sorted x' l'
	  in
	  
	  
	  let v = generic_merge_sorted_lists l new_l' in
	  let () = Hashtbl.remove content x in
	  let () = Hashtbl.add content x v in
	  (* update the related values w.r.t x *)
	  let rel_x = self#related x in
	  let fn v1 = 
	    let lv =
              try Hashtbl.find content v1 with
		  Not_found -> failwith "add_couple"
 	    in 
	    let new_lv = generic_merge_sorted_lists v lv in
	    let () = Hashtbl.remove content v1 in
	    Hashtbl.add content v1 new_lv 
	  in
	  List.iter fn rel_x
	    
	

    method find k = Hashtbl.find content k

    method add_equiv x x' =
      if x = x' then ()
      else
        let l =
          try Hashtbl.find content x with
            Not_found -> []
        and l' =
          try Hashtbl.find content x' with
            Not_found -> []
        in
        let () =
          if List.mem x l' or List.mem x' l then failwith "add_equiv"
        in
        let fn k v =
          if List.mem x v then
            let () = Hashtbl.remove content k in
            Hashtbl.add content k
              (generic_insert_sorted x' (generic_merge_sorted_lists v l'))
          else if List.mem x' v then
            let () = Hashtbl.remove content k in
            Hashtbl.add content k
              (generic_insert_sorted x (generic_merge_sorted_lists v l))
        in
        let () = Hashtbl.iter fn content in
        let v = generic_merge_sorted_lists l l'
        and () = Hashtbl.remove content x
        and () = Hashtbl.remove content x' in
        let () = Hashtbl.add content x v in Hashtbl.add content x' v

    method iter f = Hashtbl.iter f content

    method size =
      let l = ref 0 in let fn x y = incr l in Hashtbl.iter fn content; !l

    method empty = self#size = 0

    method clear = Hashtbl.clear content

    method keys =
      let ks = ref [] in
      let fn k _ = ks := k :: !ks in let () = self#iter fn in !ks

    method merge_equivalence_relation (ed : 'a equivalence_dictionary) =
      let fn k =
        let () = if k = 0 then buffered_output "processing 0" in
        let equivs = try generic_remove_sorted k (ed#find k) with Not_found -> failwith "raising Not_found in merge_equivalence_relation" in
        List.iter (fun x -> self#add_equiv k x) equivs
      in
      List.iter fn self#keys

  end;;

