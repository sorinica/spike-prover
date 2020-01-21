type token =
  | TOK_EOF
  | TOK_COLUMN
  | TOK_COMA
  | TOK_ARROW
  | TOK_SEMICOLUMN
  | TOK_LPAR
  | TOK_RPAR
  | TOK_IMPLIES
  | TOK_EQUAL
  | TOK_DIFF
  | TOK_AND
  | TOK_OR
  | TOK_QUESTION_MARK
  | TOK_AROBAT
  | TOK_LBRACKET
  | TOK_RBRACKET
  | TOK_SPECIF
  | TOK_SORTS
  | TOK_CONSTRUCTORS
  | TOK_FUNCTIONS
  | TOK_FUNCTION_PROPS
  | TOK_EQUIV
  | TOK_STATUS
  | TOK_AXIOMS
  | TOK_OBS_SORTS
  | TOK_CONJECTURES
  | TOK_COMPLETE_TERMS
  | TOK_LEMMAS
  | TOK_STRATEGIES
  | TOK_USE
  | TOK_PROPERTIES
  | TOK_PRIORITIES
  | TOK_IND_PRIORITIES
  | TOK_TEST_SETS
  | TOK_NULLARY_SORTS
  | TOK_NORM
  | TOK_RPOCOMPARE
  | TOK_COMPARE
  | TOK_MAX_COMPARE
  | TOK_STOP_ON_CLAUSE
  | TOK_EXTRACT
  | TOK_MATCH
  | TOK_AC_SUBSUMES
  | TOK_CRITICAL_CONTEXT_SETS
  | TOK_CRITIC
  | TOK_HYPOTHESES
  | TOK_LEFTRIGHT
  | TOK_MULTISET
  | TOK_RIGHTLEFT
  | TOK_AC
  | TOK_ASSOC
  | TOK_TRY
  | TOK_SATURATE
  | TOK_ON
  | TOK_REDUCTION
  | TOK_REPEAT
  | TOK_REPEAT_PLUS
  | TOK_TAUTOLOGY
  | TOK_GENERATE
  | TOK_GENERATE_EQ
  | TOK_GENERATE_OBS
  | TOK_PARTIAL_CASE_REWRITING
  | TOK_TOTAL_CASE_REWRITING
  | TOK_CONTEXTUAL_REWRITING
  | TOK_CONGRUENCE_CLOSURE
  | TOK_EQUATIONAL_REWRITING
  | TOK_REWRITING
  | TOK_NEGATIVE_DECOMPOSITION
  | TOK_POSITIVE_DECOMPOSITION
  | TOK_POSITIVE_CLASH
  | TOK_ELIMINATE_TRIVIAL_LITERAL
  | TOK_ELIMINATE_REDUNDANT_LITERAL
  | TOK_AUTO_SIMPLIFICATION
  | TOK_COMPLEMENT
  | TOK_SUBSUMPTION
  | TOK_AUGMENTATION
  | TOK_NEGATIVE_CLASH
  | TOK_START_WITH
  | TOK_AUGMENTATION_STRATEGY
  | TOK_GOTO
  | TOK_ADDPREMISE
  | TOK_SIMPLIFY
  | TOK_GREATER
  | TOK_DELETE
  | TOK_ID
  | TOK_PRINT_GOALS
  | TOK_PRINT_CAML
  | TOK_PRINT_GOALS_HISTORY
  | TOK_OPEN_SUBSTITUTION
  | TOK_CLOSE_SUBSTITUTION
  | TOK_IDENT of (string)
  | TOK_STRING of (string)

val specif :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Strategies.problem_token Queue.t 
val strategy_term :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Strategies.strategy 
val reasoning_module :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Strategies.reasoning_module 
val list_of_systems :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Clauses.which_system list 
val specif_clausal_position :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Dummies.position_argument 
val specif_literal_position_in_clause :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Dummies.position_argument 
val specif_substitution :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  (Symbols.var * Terms.term) list 
val specif_positive_int :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  int 
val get_term :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Terms.term 
val specif_term :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Terms_parser.term_token list 
val specif_clause2 :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Clauses.peano_context Clauses.clause 
val specif_shell_command :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf ->  Dummies.shell_commands 
