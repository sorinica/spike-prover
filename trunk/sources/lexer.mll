
(*
   * Project: Spike v0.1
   * File: lexer.mll

   * Content: lexing tokens
*)

  {

open Parser
open Values
open Diverse
open Io
open Dicos
open Symbols
open Terms
open Terms_parser
open Dummies
open Clauses

let gprint (s: string) = if !debug_mode then buffered_output s else ()    
let lexbuf_stack = (Stack.create (): (ginput * int * Lexing.lexbuf) Stack.t)

let keyword_table = Hashtbl.create 53
let () = List.iter (fun (kwd, tok) -> Hashtbl.add keyword_table kwd tok)
    [ ("add_premise",                   TOK_ADDPREMISE) ;
      ("ac",                            TOK_AC) ;
      ("ac_subsumes",                   TOK_AC_SUBSUMES) ;
      ("assoc",                         TOK_ASSOC) ;
      ("augmentation",                  TOK_AUGMENTATION) ;
      ("augmentation_strategy",         TOK_AUGMENTATION_STRATEGY) ;
      ("auto_simplification",           TOK_AUTO_SIMPLIFICATION) ;
      ("axioms",                        TOK_AXIOMS) ;
      ("bool",                          TOK_IDENT "bool") ;
      ("complement",                    TOK_COMPLEMENT) ;
      ("conditional_rewriting",         TOK_CONDITIONAL_REWRITING) ;
      ("congruence_closure",            TOK_CONGRUENCE_CLOSURE) ;
      ("complete_terms",                TOK_COMPLETE_TERMS) ;
      ("conjectures",                   TOK_CONJECTURES) ;
      ("constructors",                  TOK_CONSTRUCTORS) ;
      ("contextual_rewriting",          TOK_CONTEXTUAL_REWRITING) ;
      ("critical_context_sets",         TOK_CRITICAL_CONTEXT_SETS) ;
      ("delete",                        TOK_DELETE) ;
      ("defined",                       TOK_FUNCTIONS) ;
      ("eliminate_redundant_literal",   TOK_ELIMINATE_REDUNDANT_LITERAL) ;
      ("eliminate_trivial_literal",     TOK_ELIMINATE_TRIVIAL_LITERAL) ;
      ("equational_rewriting",          TOK_EQUATIONAL_REWRITING) ;
      ("goals",                         TOK_CONJECTURES) ;
      ("equiv",                         TOK_EQUIV) ;
      ("function_props",                TOK_FUNCTION_PROPS) ;
      ("functions",                     TOK_FUNCTIONS) ;
      ("s_goto",                        TOK_GOTO) ;
      ("hypotheses",                    TOK_HYPOTHESES) ;
      ("id",                            TOK_ID) ;
      ("generate",                      TOK_GENERATE) ;
      ("generate_eq",                   TOK_GENERATE_EQ) ;
      ("generate_obs",                  TOK_GENERATE_OBS) ;
      ("lemmas",                        TOK_LEMMAS) ;
      ("greater",                       TOK_GREATER) ;
      ("lr",                            TOK_LEFTRIGHT) ;
      ("match",                         TOK_MATCH) ;
      ("ms",                            TOK_MULTISET) ;
      ("negative_clash",                TOK_NEGATIVE_CLASH) ;
      ("negative_decomposition",        TOK_NEGATIVE_DECOMPOSITION) ;
      ("norm",                          TOK_NORM) ;
      ("obs_sorts",			TOK_OBS_SORTS) ;
      ("partial_case_rewriting",        TOK_PARTIAL_CASE_REWRITING) ;
      ("positive_clash",                TOK_POSITIVE_CLASH) ;
      ("positive_decomposition",        TOK_POSITIVE_DECOMPOSITION) ;
      ("print_goals",                   TOK_PRINT_GOALS) ;
      ("print_clause_caml",                   TOK_PRINT_CAML) ;
      ("print_goals_with_history",      TOK_PRINT_GOALS_HISTORY) ;
      ("priorities",                    TOK_PRIORITIES) ;
      ("ind_priorities",                TOK_IND_PRIORITIES) ;
      ("properties",                    TOK_PROPERTIES) ;
      ("repeat",                        TOK_REPEAT) ;
      ("repeat_plus",                   TOK_REPEAT_PLUS) ;
      ("rl",                            TOK_RIGHTLEFT) ;
      ("rpocompare",                    TOK_RPOCOMPARE) ;
      ("s_compare",                     TOK_COMPARE) ;
      ("s_max_compare",                 TOK_MAX_COMPARE) ;
      ("extract",                       TOK_EXTRACT) ;
      ("simplify",                      TOK_SIMPLIFY) ;
      ("saturate",                      TOK_SATURATE) ;
      ("sorts",                         TOK_SORTS) ;
      ("specification",                 TOK_SPECIF) ;
      ("start_with",                    TOK_START_WITH) ;
      ("status",                        TOK_STATUS) ;
      ("stop_on_clause",                TOK_STOP_ON_CLAUSE) ;
      ("strategy",                      TOK_STRATEGIES) ;
      ("subsumption",                   TOK_SUBSUMPTION) ;
      ("tautology",                     TOK_TAUTOLOGY) ;
      ("test_sets",                     TOK_TEST_SETS) ;
      ("nullary_sorts",                 TOK_NULLARY_SORTS) ;
      ("total_case_rewriting",          TOK_TOTAL_CASE_REWRITING) ;
      ("try",                           TOK_TRY) ;
      ("use",                           TOK_USE) 
    ]
}

let whitespace = [ ' ' '\013' '\009' ]
let newline = [ '\010' ]
let integer = [ '1'-'9' ] [ '0'-'9' ] *
let special_ident = [ '<' '>' '+' '-' '*' '/' '.' ] + '=' ? [ '<' '>' '+' '-' '*' '/' '.' ] *
let ident_core = [ 'A'-'Z' 'a'-'z' '_' '0'-'9' '''] + | special_ident
let ident = '_' * ident_core '_' *
let filename_ident = [ 'A'-'Z' 'a'-'z' '_' '0'-'9' '=' '+' '-' '/' '.' ]
let comment = "%"[ ^'\010' ]*
let string =  '[' integer ']' [ ^'\010' ]*

rule token = parse
  whitespace                            { token lexbuf }
| newline                               { let () = incr linenumber in token lexbuf }
| comment                               { token lexbuf }
| ":"                                   { let () = gprint "TOK_COLUMN" in TOK_COLUMN }
| ","                                   { let () = gprint "TOK_COMA" in TOK_COMA }
| ";"                                   { let () = gprint "TOK_SEMICOLUMN" in TOK_SEMICOLUMN }
| "->"                                  { let () = gprint "TOK_ARROW" in TOK_ARROW }
| "("                                   { let () = gprint "TOK_LPAR" in TOK_LPAR }
| ")"                                   { let () = gprint "TOK_RPAR" in TOK_RPAR }
| "["                                   { let () = gprint "TOK_LBRACKET" in TOK_LBRACKET }
| "]"                                   { let () = gprint "TOK_RBRACKET" in TOK_RBRACKET }
| "=>"                                  { let () = gprint "TOK_IMPLIES" in TOK_IMPLIES }
| "="                                   { let () = gprint "TOK_EQUAL" in TOK_EQUAL }
| "<>"                                  { let () = gprint "TOK_DIFF" in TOK_DIFF }
| "&"                                   { let () = gprint "TOK_AND" in TOK_AND }
| "|"                                   { let () = gprint "TOK_OR" in TOK_OR }
| "?"                                   { let () = gprint "TOK_QUESTION_MARK" in TOK_QUESTION_MARK }
| "@"                                   { let () = gprint "TOK_AROBAT" in TOK_AROBAT }
| "<!"                                   { let () = gprint "TOK_OPEN_SUBSTITUTION" in TOK_OPEN_SUBSTITUTION}
| "!>"                                   { let () = gprint "TOK_CLOSE_SUBSTITUTION" in TOK_CLOSE_SUBSTITUTION}
| "on"                                   { let () = gprint "TOK_ON" in TOK_ON}
| "include"                             { inclusions lexbuf } 
| "end" | eof                           { if (not !in_a_file)
                                          then let () = gprint "TOK_EOF" in TOK_EOF
                                          else
                                            let () = closein !parsed_gfile in
                                            try
                                              let (f, l, lb) = Stack.pop lexbuf_stack
                                              in let () = parsed_gfile := f
                                              and () = linenumber := l
                                              in token lb
                                            with Stack.Empty -> let () = gprint "TOK_EOF" in TOK_EOF }
| integer                               { let s = Lexing.lexeme lexbuf in
                                          let char_s =
					    try
					      let _ = dico_const_string#find_key "s"
					      in "s"
					    with Not_found -> 
					      try
						let _ = dico_const_string#find_key  "S"
						in "S"
					      with Not_found -> ""
					  in
					  if  char_s <> "" then TOK_IDENT s
(*                                             let rec fn = function  *)
(*                                                  0 -> [ "0" ] *)
(*                                               | i -> char_s ::fn (i - 1) *)
(*                                             in let () = gprint "TOK_IDENT_LIST" in TOK_IDENT_LIST (fn (int_of_string s)) *)
                                          else
                                            try
                                              let x = Hashtbl.find keyword_table (String.lowercase s) in
                                              let () = gprint ("TOK_KWD_" ^ s)
                                              in x
                                            with Not_found ->
                                              let () = gprint ("TOK_IDENT (" ^ s ^ ")") 
					      in TOK_IDENT s 
                                         }
| ident                                 { let s = Lexing.lexeme lexbuf
                                          in try
                                            let x = Hashtbl.find keyword_table (String.lowercase s) in
                                            let () = gprint ("TOK_KWD_" ^ s)
                                            in x
                                          with Not_found ->
                                            let () = gprint ("TOK_IDENT (" ^ s ^ ")") in TOK_IDENT s }
| string                                {let s = Lexing.lexeme lexbuf in
                                        if true then 
                                             TOK_STRING s
                                        else parse_failwith ("unknown string" ^ s)}
| _                                     { parse_failwith "unknown symbol" }

and inclusions = parse
  whitespace +                          { inclusions lexbuf }
| newline                               { incr linenumber ; inclusions lexbuf }
| comment                               { inclusions lexbuf }
| filename_ident +                      { let infile =
                                            try openin (Lexing.lexeme lexbuf)
                                            with Sys_error _ ->
					      raise (MyExit "lexer1")
                                          in let () = Stack.push (!parsed_gfile, !linenumber, lexbuf) lexbuf_stack
                                          in let () = parsed_gfile := infile 
                                          and () = linenumber := 1
                                          in let lexbuf = Lexing.from_channel (snd infile)
                                          in token lexbuf }

{

(* The readline primitive.
   It reads a line, and parses it according to the given argument parse_fn.
   If parse_fn fails, it asks again, otherwise, it provides the concrete value of the string.
   If the string is void, provides the default argument *)
let spike_readline s def parse_fn =
  let rec fn2 () =
    let v = read_line ()
    in let len = String.length v
    in if len = 0 then v
    else if String.get v (len - 1) = '\\'
    then (String.sub v 0 (len - 1)) ^ fn2 ()
    else v
  and fn () =
    print_string s ;
    flush stdout ;
    let v = fn2 () in
    match v with
      "" -> def
    | _ ->
        let lexbuf = Lexing.from_string v in
        try parse_fn token lexbuf
        with Parsing.Parse_error ->
          let () =
            match !error_message with
              "" -> buffered_output "parse error"
            | _ -> buffered_output !error_message in
          fn ()
  in fn ()

(* The function to actually parse strategies within inference rules.
   It produces actual strategies (while the prototype would produce dummies) *)
let _ =
  spike_parse_strategy := fun def_st () ->
    let rec fn () =
      let s = spike_readline
          "Enter strategy: "
          def_st
          strategy_term
      in if s#is_query
      then fn ()
      else s
    in fn ()

(* Parse a list of systems *)
let _ =
  spike_parse_list_of_systems := fun () -> spike_readline
      "Enter list of systems [C->L->R]: "
      [C ; L ; R]
      list_of_systems

(* Parse a clausal position, and repeat until it is valid *)
let _ =
  spike_parse_clausal_lhs_position := fun c () ->
    let rec fn () =
      let p = spike_readline
          "Enter a clausal position [*]: "
          Pos_all
        Parser.specif_clausal_position
      in match p with
        Pos_all -> p
      | Pos_defined (neg_pos, n, p') ->
          begin (* Discards second level PM *)
            match p' with
              0::t ->
                begin (* Discards PM on exceptions *)
                  try let _ = c#subterm_at_position (neg_pos, n, p') in Pos_defined (neg_pos, n, t)
                  with (Failure "subterm_at_position") ->
                    print_string "Invalid position" ;
                    print_newline () ;
                    fn ()
                end
            | _ ->
                print_string "Invalid position (must be in lefthand side)" ;
                print_newline () ;
                fn ()
          end
      | Pos_litdefined p' ->
          begin
            try let _ = c#lit_at_position p' in p
            with (Failure "lit_at_position") ->
              print_string "Invalid position" ;
              print_newline () ;
              fn ()
          end
      | Pos_query -> fn ()
      | Pos_dumb -> failwith "positions in lexer"
    in fn ()

(* Same for the position of a literal in a clause *)
let _ =
  spike_parse_literal_position_in_clause := fun c () ->
    let rec fn () =
      let p = spike_readline
          "Enter a literal position in clause [*]: "
          Pos_all
        Parser.specif_literal_position_in_clause
      in match p with
        Pos_all -> p
      | Pos_defined (b, n, p') ->
          begin
            try let _ = c#subterm_at_position (b, n, p') in p
            with (Failure "subterm_at_position") ->
              print_string "Invalid position" ;
              print_newline () ;
              fn ()
          end
      | Pos_litdefined (b, n) ->
          begin (* Discards second level PM *)
            try let _ = c#lit_at_position (b, n) in p
            with (Failure "lit_at_position") ->
              print_string "Invalid position" ;
              print_newline () ;
              fn ()
          end
      | Pos_query -> fn ()
      | Pos_dumb -> failwith "positions in lexer"
    in fn ()

let _ =
  spike_parse_substitution := fun () ->
    spike_readline
      "Enter a substitution:"
      []
    Parser.specif_substitution

let _ =
  spike_parse_positive_int := fun c () ->
    let rec fn () =
      let p = spike_readline
          "Enter a literal number:"
          0
        Parser.specif_positive_int
      in try

        let _ = c#lit_at_position (true, p)
        in p
      with (Failure "lit_at_position") -> fn ()
    in fn ()

let spike_parse_term () =
  spike_readline
    "Enter a term: "
    (new term (Var_univ (0, Def_sort 0)))
  Parser.get_term

let _ =
  spike_parse_shell_command := fun () ->
    let rec fn () =
      try
        let c = spike_readline
            "spike> "
            Command_error
          Parser.specif_shell_command
        in match c with
          Command_error ->
            let () = print_endline "Bad command or file name"
            in fn ()
        | Command_strategy _
	| Command_next
	| Command_run
	| Command_previous
	| Command_display
	| Command_exit -> c
	with End_of_file -> Command_exit
    in fn ()

  (* to be used interactively  *)
let spike_readline2 s parse_fn =
  let rec fn2 () =
    let v = read_line ()
    in let len = String.length v
    in if len = 0 then v
    else if String.get v (len - 1) = '\\'
    then (String.sub v 0 (len - 1)) ^ fn2 ()
    else v
  and fn () =
    reset_yy_values () ;
    print_string s ;
    flush stdout ;
    let v = fn2 ()
    in match v with
      "" ->       
	begin
	  print_indent_string ("\n Raising MyExit exception from lexer.mll, line341"); flush stdout; raise (MyExit "lexer2")
	end
    | _ ->
        let lexbuf = Lexing.from_string v
        in try parse_fn token lexbuf
        with Parsing.Parse_error ->
          begin
            print_endline !error_message ;
            fn ()
          end
  in fn ()

}
