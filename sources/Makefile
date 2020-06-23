#
#   * Project: Spike ver 0.1
#   * File: Makefile
#   * Creation-date: <00/01/19 09:34:07 sorin>
#   * Content: the makefile
#

NAME = spike
OCAMLBUILD = ocamlbuild -use-ocamlfind

SOURCES_ML	= augment.ml	eliminate_set.ml pi.ml auto_simplification.ml	extract.ml polynoms.ml case_rewriting.ml generate_eq.ml shell.ml clauses.ml induction.ml	smt.ml complement.ml induction_obs.ml spike.ml context.ml io.ml strategies.ml contextual_rewriting.ml literals.ml symbols.ml coq.ml max.ml terms.ml critical_context_set.ml min.ml terms_parser.ml decomposition_set.ml misc.ml test_sets.ml delete_set.ml natlist.ml values.ml dicos.ml normalize.ml zmaxmin.ml diverse.ml npolynoms.ml dummies.ml order.ml

TARGET		= spike.ml


default: dev

dev:
	make build
#	make tags

build:
	$(OCAMLBUILD) -libs unix -libs str spike.d.byte
	mv spike.d.byte spike_bc

nc:
	$(OCAMLBUILD) -libs unix -libs str spike.native
	mv spike.native spike_nc


tags:
	$(OCAMLBUILD) -tags annot $(SOURCES_ML)  $(TARGET)


all:
	make build
	make doc

doc:
	$(OCAMLBUILD) spike.docdir/index.html

clean:
	$(OCAMLBUILD) -clean


.PHONY: build default install tags dev 
