#
#   * Project: Spike ver 0.1
#   * File: Makefile
#   * Creation-date: <00/01/19 09:34:07 sorin>
#   * Content: the makefile
#

NAME = spike
OCAMLBUILD = ocamlbuild -use-ocamlfind 

SOURCES_ML	= values.ml io.ml diverse.ml dicos.ml pi.ml \
		  symbols.ml terms.ml context.ml order.ml npolynoms.ml max.ml min.ml zmaxmin.ml natlist.ml polynoms.ml terms_parser.ml literals.ml \
		  clauses.ml coq.ml dummies.ml normalize.ml test_sets.ml critical_context_set.ml shell.ml \
		  contextual_rewriting.ml case_rewriting.ml induction.ml induction_obs.ml generate_eq.ml \
		  decomposition_set.ml delete_set.ml eliminate_set.ml auto_simplification.ml complement.ml harvey.ml \
		  strategies.ml augment.ml extract.ml

TARGET		= spike.ml


default: dev

dev:
	make build
	make tags

build:
	$(OCAMLBUILD) -libs unix -libs str spike.d.byte
	mv spike.d.byte spike_bc

nc:
	$(OCAMLBUILD) -libs unix -libs str spike.native
	mv spike.native spike_nc


tags:
	otags -v $(SOURCES_ML)  $(TARGET)


all:
	make build
	make doc

doc:
	$(OCAMLBUILD) spike.docdir/index.html

clean:
	$(OCAMLBUILD) -clean


.PHONY: build default install tags dev 
