(*
   * Project: Spike ver 0.1
   * File: literals.ml
   * Content: literals definitions
*)

open Diverse
open Symbols
open Terms
open Order
open Pi
open Values
open Io

type concrete_literal =
    Lit_rule of term * term
  | Lit_equal of term * term
  | Lit_diff of term * term


let print_both_terms c_l =
  let str =
    match c_l with 
	Lit_rule (_,_)  -> " -> " |  Lit_equal (_,_)  -> " = " | Lit_diff (_,_) -> " <> " 
  in
  match c_l with 
      Lit_rule (lhs,rhs) |  Lit_equal (lhs,rhs) | Lit_diff (lhs,rhs) -> lhs#string ^ str ^ rhs#string
	
let test_well_founded_lit c_l = 
  match c_l with 
      Lit_rule (lhs,rhs) |  Lit_equal (lhs,rhs) | Lit_diff (lhs,rhs) -> 
	if equal_sorts lhs#sort rhs#sort then true else
	  let () = if !maximal_output then buffered_output ("literal: incompatible types on " ^ (print_both_terms c_l) ^ "\nunify_sorts:  the list yy_tmp_param_sorts is : " ^
	  (List.fold_right (fun (x, s) y -> (x ^ " has associated the sort " ^ (sprint_sort s) ^ ", " ^ y)) !yy_tmp_param_sorts ""))  in
	  
	  let () = if !maximal_output then buffered_output ("\nthe term lhs = " ^ lhs#string ^ ": " ^ (sprint_sort lhs#sort) ^ "; rhs = " ^ rhs#string ^
	  ": " ^ (sprint_sort rhs#sort))
	  in false
	       
;;

let constr_heads cl = 
  match cl with
          Lit_equal (lhs, rhs)
        | Lit_diff (lhs, rhs) 
        | Lit_rule (lhs, rhs) -> (lhs#is_term && is_constructor lhs#head) && (rhs#is_term && is_constructor rhs#head)


class literal c_l =
  let () = if not (test_well_founded_lit c_l) then 
    failwith ("literal")
  in
   object (self: 'a)

    inherit generic
    inherit printable_object
    inherit pi_object

    val content = c_l

    val variables =
      let lhs, rhs =
        match c_l with
          Lit_equal (lhs, rhs) -> lhs, rhs
        | Lit_diff (lhs, rhs) -> lhs, rhs 
        | Lit_rule (lhs, rhs) -> lhs, rhs in
      generic_merge_sorted_lists lhs#variables rhs#variables

    val mutable pos_positive_decomposition  = ref (constr_heads c_l)
    val mutable pos_negative_decomposition   = ref (constr_heads c_l)
    val mutable pos_positive_clash = ref (constr_heads c_l)
    val mutable pos_negative_clash   = ref (constr_heads c_l)
    val mutable pos_eliminate_trivial_literal   = ref (constr_heads c_l)

    method pos_positive_decomposition  = !pos_positive_decomposition
    method pos_negative_decomposition  = !pos_negative_decomposition
    method pos_positive_clash  = !pos_positive_clash
    method pos_negative_clash  = !pos_negative_clash
    method pos_eliminate_trivial_literal  = !pos_eliminate_trivial_literal

    method content = content

    method variables = variables

  (* pretty print function *)
    method pprint f = Format.fprintf f "@[@ Literal: %s@]" self#string


    method update_pos = 
      match content with
	  Lit_rule (t1, t2) -> {< content = Lit_rule (t1#update_pos, t2#update_pos) ; >}
	| Lit_equal (t1, t2) -> {< content = Lit_equal (t1#update_pos, t2#update_pos);>}
	| Lit_diff (t1, t2) -> {< content = Lit_diff (t1#update_pos, t2#update_pos); >}

    method  expand_sorts = 
      match content with
	  Lit_rule (t1, t2) -> {< content = Lit_rule (t1#expand_sorts, t2#expand_sorts) ; string = Undefined>}
	| Lit_equal (t1, t2) -> {< content = Lit_equal (t1#expand_sorts, t2#expand_sorts); string = Undefined >}
	| Lit_diff (t1, t2) -> {< content = Lit_diff (t1#expand_sorts, t2#expand_sorts); string = Undefined >}
	    
    method compute_string =
      match content with
        Lit_rule (t, t') -> t#string ^ " -> " ^ t'#string
      | Lit_equal (t, t') -> t#string ^ " = " ^ t'#string
      | Lit_diff (t, t') -> t#string ^ " <> " ^ t'#string

   
    (* Apply function term -> term to members of a literal *)
    method apply_to_lit f =
      match content with
        Lit_rule (t, t') ->
          let u = f t
          and u' = f t' in
          {< content = Lit_rule (u, u') ;
            variables = generic_merge_sorted_lists u#variables u'#variables ;
            string = Undefined >}
      | Lit_equal (t, t') ->
          let u = f t
          and u' = f t' in
          {< content = Lit_equal (u, u') ;
            variables = generic_merge_sorted_lists u#variables u'#variables ;
            string = Undefined >}
      | Lit_diff (t, t') ->
          let u = f t
          and u' = f t' in
          {< content = Lit_diff (u, u') ;
            variables = generic_merge_sorted_lists u#variables u'#variables ;
            string = Undefined >}

    (* Apply function term -> term to left member of a literal *)
    method left_apply_to_lit f =
      match content with
        Lit_rule (t, t') ->
          let u = f t in
          {< content = Lit_rule (u, t') ;
            variables = generic_merge_sorted_lists u#variables t'#variables ;
            string = Undefined >}
      | Lit_equal (t, t') ->
          let u = f t in
          {< content = Lit_equal (u, t') ;
            variables = generic_merge_sorted_lists u#variables t'#variables ;
            string = Undefined >}
      | Lit_diff (t, t') ->
          let u = f t in
          {< content = Lit_diff (u, t') ;
            variables = generic_merge_sorted_lists u#variables t'#variables ;
            string = Undefined >}

    (* Apply function term -> term to right member of a literal *)
    method right_apply_to_lit f =
      match content with
        Lit_rule (t, t') ->
          let u' = f t' in
          {< content = Lit_rule (t, u') ;
            variables = generic_merge_sorted_lists t#variables u'#variables ;
            string = Undefined >}
      | Lit_equal (t, t') ->
          let u' = f t' in
          {< content = Lit_equal (t, u') ;
            variables = generic_merge_sorted_lists t#variables u'#variables ;
            string = Undefined >}
      | Lit_diff (t, t') ->
          let u' = f t' in
          {< content = Lit_diff (t, u') ;
            variables = generic_merge_sorted_lists t#variables u'#variables ;
            string = Undefined >}

    (* swap arguments *)
    method swap =
      match content with
        Lit_rule _ -> failwith "swap"
      | Lit_equal (t, t') -> {< content = Lit_equal (t', t) ;
                               string = Undefined >}
      | Lit_diff (t, t') -> {< content = Lit_diff (t', t) ;
                               string = Undefined >}

    method substitute s =
      let subst_s t = t#substitute s in
      self#apply_to_lit subst_s

    (* Bijective renaming modulo AC properties of some constructors *)
    method bijective_renaming ren lit =
      let double_eq s s' t t' =
        let ren' = s#bijective_renaming ren s' in
        t#bijective_renaming ren' t' in
      match content, lit#content with
        Lit_rule (s, s'), Lit_rule (t, t') -> double_eq s t s' t'
      | Lit_equal (s, s'), Lit_equal (t, t') ->
          begin (* Discards PM on exceptions *)
            try
              double_eq s t s' t'
            with (Failure "bijective_renaming") ->
              double_eq s t' s' t
          end
      | Lit_diff (s, s'), Lit_diff (t, t') ->
          begin (* Discards PM on exceptions *)
            try
              double_eq s t s' t'
            with (Failure "bijective_renaming") ->
              double_eq s t' s' t
          end
      | Lit_rule _, Lit_equal _ | Lit_equal _, Lit_rule _| Lit_rule _, Lit_diff _| Lit_diff _, Lit_rule _ | Lit_equal _, Lit_diff _| Lit_diff _, Lit_equal _ -> failwith "bijective_renaming"

    (* Equality modulo renaming and AC properties *)

    method copy = 
      match content with
          Lit_equal (t, t') -> 
	    {< content = Lit_equal (t#copy, t'#copy) >}
	| Lit_rule (t, t') ->  
	    {< content = Lit_rule (t#copy, t'#copy) >}
	| Lit_diff (t, t') ->  
	    {< content = Lit_diff (t#copy, t'#copy) >}
	    
    method equal lit =
      try
        let _ = self#bijective_renaming [] lit in
        true
      with (Failure "bijective_renaming") ->
        false

    method syntactic_equal (l: literal) =
      let lhs, rhs = self#both_sides
      and lhs', rhs' = l#both_sides in
      if (self#is_diff && l#is_diff) or ((not self#is_diff) && (not l#is_diff)) then
	    (lhs#syntactic_equal lhs' && rhs#syntactic_equal rhs') or
	(lhs#syntactic_equal rhs' && rhs#syntactic_equal lhs')
      else false 
    (* Is this literal oriented ? *)
    method is_oriented =
      match content with
        Lit_rule _ -> true
      | Lit_equal _ | Lit_diff _ -> false

    method lefthand_side =
      match content with
        Lit_rule (t, _) -> t
      | Lit_equal (t, _) -> t
      | Lit_diff (t, _) -> t

    method righthand_side =
      match content with
        Lit_rule (_, t') -> t'
      | Lit_equal (_, t') -> t'
      | Lit_diff (_, t') -> t'

    method both_sides =
      match content with
        Lit_rule (t, t') -> t, t'
      | Lit_equal (t, t') -> t, t'
      | Lit_diff (t, t') -> t, t'

    (* Subterm at position *)
    method subterm_at_position p =
      match p with
        0::t -> (try (self#lefthand_side)#subterm_at_position t with (Failure "subterm_at_position") -> failwith ("subterm_at_position in literals.ml for literal " ^
	  self#string ^ " in subterm_at_position for p = " ^ (sprint_position p)))
      | 1::t -> (try (self#righthand_side)#subterm_at_position t with (Failure "subterm_at_position") -> failwith ("subterm_at_position in literals.ml for literal " ^
	  self#string ^ " for subterm_at_position for p = " ^ (sprint_position p)))
      | _ -> failwith "subterm"

    (* Replace subterm at position p by st
       proceed_fun: substitution -> bool -> bool *)
    method replace_subterm_at_pos p st =
      let replace pos x = x#replace_subterm_at_pos pos st in
      match p with
        0::p' -> self#left_apply_to_lit (replace p')
      | 1::p' -> self#right_apply_to_lit (replace p')
      | _ -> invalid_arg "replace_subterm_at_pos"

    (* We replace s by t and count the number of times we have done so *)
    method replace_subterms counter s t =
      let res = self#apply_to_lit (fun x -> x#replace_subterms counter s t) in
      let new_l', new_r' = res#both_sides in
      match content with
        Lit_equal (_, _) -> 
	  {< content = Lit_equal (new_l', new_r') ;
	  variables = generic_merge_sorted_lists new_l'#variables new_r'#variables ;
          string = Undefined >}
      | Lit_rule (_, _) ->  
	  {< content = Lit_rule (new_l', new_r') ;
	  variables = generic_merge_sorted_lists new_l'#variables new_r'#variables ;
	  string = Undefined >}
      | Lit_diff (_, _) ->  
	  {< content = Lit_diff (new_l', new_r') ;
	  variables = generic_merge_sorted_lists new_l'#variables new_r'#variables ;
          string = Undefined >}
	  
    (* Attempt subterm matching with the lhs of another literal.
       If the literal is oriented, this lhs is uniquely determined, otherwise, we check both sides
       The last element returned is true if we kept orientation of the literal, false if we swaped elements
       proceed_fun: position -> substitution -> bool -> bool *)
    method subterm_matching proceed_fun (lit: literal) =
      let lhs, rhs = self#both_sides in
      let fn t t' = 
        begin
          try
            let p, s = lhs#subterm_matching (fun p s -> proceed_fun (0::p) s true) t in
            0::p, s, true
          with (Failure "matching") ->
            try
              let p, s = rhs#subterm_matching (fun p s -> proceed_fun (1::p) s true) t in
              1::p, s, true
            with (Failure "matching") ->
              try
                let p, s = lhs#subterm_matching (fun p s -> proceed_fun (0::p) s false) t' in
                0::p, s, false
              with (Failure "matching") ->
                let p, s = rhs#subterm_matching (fun p s -> proceed_fun (1::p) s false) t' in
                1::p, s, false
        end
      in
      match lit#content with
          Lit_equal (t, t') -> fn t t'
	| Lit_diff (t, t') -> fn t t'
      	| Lit_rule (t, _) ->
            try
              let p, s = lhs#subterm_matching (fun p s -> proceed_fun (0::p) s true) t in
              0::p, s, true
            with (Failure "matching") ->
              let p, s = rhs#subterm_matching (fun p s -> proceed_fun (1::p) s true) t in
              1::p, s, true
		
    (* Checks if the subterm of self at position p matches t (i.e. exists sigma, t.sigma = s[p]).
       Once more, we provide information on whether we have swaped arguments *)
    method subterm_matching_at_pos proceed_fun p (lit: literal) =
      let s = self#subterm_at_position p in
      let fn t t' = 
        begin
          try
            let sigma = s#matching (fun s -> proceed_fun s true) t in
            sigma, true
          with (Failure "matching") ->
            let sigma = s#matching (fun s -> proceed_fun s false(*true*)) t' in
            sigma, false
        end
      in
      match lit#content with
          Lit_equal (t, t') -> fn t t'
        | Lit_diff (t, t') -> fn t t'
	| Lit_rule (t, _) ->
            let sigma = s#matching (fun s -> proceed_fun s true) t in
            sigma, true
	      
    (* Matching
       proceed_fun: substitution -> bool *)
    method matching_core proceed_fun sigma (lit: literal) =
      match content, lit#content with
        Lit_rule (t0, t0'), Lit_rule (t1, t1') ->
          t0#matching_core proceed_fun sigma [ (t0, t1) ; (t0', t1') ]
	| Lit_diff _, Lit_diff _| Lit_equal _, Lit_equal _  | Lit_rule _, Lit_equal _ | Lit_equal _, Lit_rule _| Lit_rule _, Lit_diff _| Lit_diff _, Lit_rule _ | Lit_equal _, Lit_diff _| Lit_diff _, Lit_equal _ ->
          let t0, t0' = self#both_sides
          and t1, t1' = lit#both_sides in
          try
            t0#matching_core proceed_fun sigma [ (t0, t1) ; (t0', t1') ]
          with (Failure "matching") ->
            t0#matching_core proceed_fun sigma [ (t0, t1') ; (t0', t1) ]

    method treesize =
      let lhs, rhs = self#both_sides in
      1 + lhs#treesize + rhs#treesize

  (* useless  *)
    method flatten =
      match content with
        Lit_equal (t, t') -> {< content = Lit_equal (t#flatten, t'#flatten) ;
                               string = Undefined >}
      | Lit_rule (t, t') -> {< content = Lit_rule (t#flatten, t'#flatten) ;
                              string = Undefined >}
      | Lit_diff (t, t') -> {< content = Lit_diff (t#flatten, t'#flatten) ;
                              string = Undefined >}

    (* Return both sides. They are swaped if the argument is negative *)
    method both_sides_w_or kept_or =
      let lhs, rhs = self#both_sides in
      match kept_or with
        true -> lhs, rhs
      | false -> rhs, lhs


    method is_boolean =
      let lhs, rhs = self#both_sides
      and f = term_true#syntactic_equal
      and g = term_false#syntactic_equal in
      f rhs or g rhs or f lhs or g lhs

  (* if the literal is of the form t1=true it returns t1 = false and
     viceversa. Any Lit_diff is transformed in Lit_equal  *)
    method revert_boolean =
      match content with
          Lit_equal (s, s') ->
            let new_lit =
              if term_is_true s'
              then Lit_equal (s, term_false)
              else if term_is_false s'
              then Lit_equal (s, term_true)
              else if term_is_true s
              then Lit_equal (s', term_false)
              else if term_is_false s
              then Lit_equal (s', term_true)
              else Lit_diff (s, s') in
            {< content = new_lit ;
            string = Undefined >}
	| Lit_diff (s, s') -> 
            {< content = Lit_equal (s, s') ;
            string = Undefined >}

      	| Lit_rule (s, s') ->
            let (t, t') =
              if term_is_true s'
              then (s, term_false)
              else if term_is_false s'
              then (s, term_true)
              else if term_is_true s
              then (term_false, s')
              else if term_is_false s
              then (term_true, s')
              else failwith "revert_boolean" in
            {< content = Lit_rule (t, t') ;
            string = Undefined >}
        
    method is_diff = match content with
	Lit_diff (_,_) -> true
      | Lit_equal _| Lit_rule _ -> false

    method rename_core v =
      self#apply_to_lit (fun x -> x#rename_core v)
        
    method rename =
      let v = List.map (fun (x, _, _) -> x, newvar ()) variables in
      self#apply_to_lit (fun x -> x#rename_core v)

    method depth =
      let lhs, rhs = self#both_sides in
      1 + (max lhs#depth rhs#depth)

    method rpos_greater (lit: 'a) =
      let lhs, rhs = lit#both_sides in
      let fn t t' = 
          (!rpos_greater false t t' && !rpos_greater false t lhs &&
	  !rpos_greater false t rhs)
            or
          (!rpos_greater false t' t && !rpos_greater false t' lhs &&
	  !rpos_greater false t' rhs) 
      in
      match content with
          Lit_equal (t, t') -> fn t t'
      	| Lit_diff (t, t') -> fn t t'
      	| Lit_rule (t, _) ->
            !rpos_greater false t lhs && !rpos_greater false t rhs

    method compute_pi =
      let peano_sort = if !nat_specif_defined then id_sort_nat else
	id_sort_int in
      match content with
        Lit_equal (t, _) -> t#sort = peano_sort
      | Lit_rule (t, _) -> t#sort = peano_sort
      | Lit_diff (t, _) -> t#sort = peano_sort

    method is_subterm (t : term) =
      let lhs, rhs = self#both_sides in
      try
	let p = t#subterm lhs
	in 0::p
      with (Failure "subterm") ->
	let p = t#subterm rhs
	in 1::p
      
  end
      
let compute_string_literal_caml l =
      match l#content with
        Lit_rule (t, t') -> (compute_string_caml t) ^ " -> " ^ (compute_string_caml t')
      | Lit_equal (t, t') -> (compute_string_caml t) ^ " = " ^ (compute_string_caml t')
      | Lit_diff (t, t') -> (compute_string_caml t) ^ " <> " ^ (compute_string_caml t')

