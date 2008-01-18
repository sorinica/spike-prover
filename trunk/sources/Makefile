#
#   * Project: Spike ver 0.1
#   * File: Makefile
#   * Creation-date: <00/01/19 09:34:07 sorin>
#   * Content: the makefile
#

# read the infos from /home/sorin/ocaml/ocaml_make/README to know hwo to work with OcamlMakefile

OCAMLBCFLAGS 	= -custom -w A -dtypes
CC		= gcc
INCFLAGS	= -i
LIBS		= unix str
OCAMLMAKEFILE 	= OcamlMakefile

SOURCES_MLI	= auto_simplification.mli   delete_set.mli     diverse.mli       strategies.mli \
                  dicos.mli        \
		  normalize.mli  harvey.mli coq.mli \
		 symbols.mli \
		  case_rewriting.mli        dummies.mli        order.mli      terms.mli context.mli \
		  clauses.mli               eliminate_set.mli  parser.mli     terms_parser.mli \
                 induction.mli induction_obs.mli generate_eq.mli    pi.mli         test_sets.mli critical_context_set.mli \
		  complement.mli            io.mli             polynoms.mli   values.mli \
		  contextual_rewriting.mli  augment.mli lexer.mli          shell.mli \
		  decomposition_set.mli     literals.mli       extract.mli spike.mli 

SOURCES_C	= # myclock.c 

SOURCES_ML	= values.ml io.ml diverse.ml dicos.ml pi.ml \
		  symbols.ml terms.ml context.ml order.ml polynoms.ml terms_parser.ml literals.ml \
		  clauses.ml coq.ml dummies.ml normalize.ml test_sets.ml critical_context_set.ml shell.ml \
		  contextual_rewriting.ml case_rewriting.ml induction.ml induction_obs.ml generate_eq.ml \
		  decomposition_set.ml delete_set.ml eliminate_set.ml auto_simplification.ml complement.ml harvey.ml \
		  strategies.ml augment.ml extract.ml

SOURCES_MLL	= lexer.mll

SOURCES_MLY	= parser.mly

TARGET		= spike.ml

SOURCES		= $(SOURCES_MLI) $(SOURCES_C) $(SOURCES_ML) $(SOURCES_MLY) $(SOURCES_MLL) $(TARGET)

RESULT		= spike
BCSUFFIX	= _bc
NCSUFFIX	= _nc
TOPSUFFIX	= _top

EXPDIR		= $(HOME)/spike/experimentations
PROOFDIR	= $(HOME)/spike/proofs

all: bc # top byte-code native-code

# include the MAGIC file 

-include $(OCAMLMAKEFILE)

# generates a customized top-level 
top:			$(AUTO_TARGETS)
			@$(MAKE) -r -f $(OCAMLMAKEFILE) $(TOPRESULT) \
				REAL_RESULT="$(TOPRESULT)" OCAMLC="$(OCAMLC)" REAL_OCAMLC_LINK="$(OCAMLMKTOP)" make_deps=yes

# generates the tags for each .ml file
taguri:
#	ocamltags $(SOURCES_ML) parser.ml lexer.ml $(TARGET)
	otags -v $(SOURCES_ML) parser.mly lexer.mll $(TARGET)
#	cattags *.etags > TAGS

all_tags: # builds tags in directories recursively. Needs script.sh

	find . -type d exec ./script.sh '{}' ';'

sorted: nc
	$(RESULT)$(NCSUFFIX) -debug ${EXPDIR}/sorted.spike | tee $(PROOFDIR)/sorted.proof

test3: nc
	$(RESULT)$(NCSUFFIX) -debug ${EXPDIR}/test3.spike | tee $(PROOFDIR)/test3.proof

exc: top
	$(foreach FILE_ML,$(SOURCES_ML) spike.ml,/home/sorin/ocamlexc/i586/bin/ocamlexcc -I /home/sorin/ocamlexc/i586/stdlib $(FILE_ML);)

dot: 

	ocamldep $(SOURCES_ML) lexer.ml parser.ml $(TARGET)> .depend
	$(HOME)/ocaml/ocamldot/ocamldot .depend > dep.dot
	dot -Tps -o dot.ps dep.dot
