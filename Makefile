OCAMLBUILD=ocamlbuild
OPTIONS=-use-ocamlfind
PACKAGES=ocaml-sat-solvers
SRC=src
MAIN=dimo
INCLUDES=$(SRC)
LIBS=unix
PARAMS=-I $(INCLUDES) -lib $(LIBS) -pkgs $(PACKAGES)
SED=sed

PDFLATEX=/usr/local/texlive/2018/bin/x86_64-darwin/pdflatex

all: byte native

byte: version
	$(OCAMLBUILD) $(PARAMS) $(SRC)/$(MAIN).byte

native: version
	$(OCAMLBUILD) $(PARAMS) $(SRC)/$(MAIN).native

clean:
	$(OCAMLBUILD) -clean

archive: version
	zip dimo.zip src/alschemes.ml src/basics.ml src/dimo.ml src/engine.ml src/enumerators.ml \
	src/lexer.mll src/parser.mly src/propFormula.ml src/version.ml \
	examples/exactlyMofN.dm examples/nQueens.dm Makefile _tags README

doc: version
	make -C doc

version:
	$(SED) "s/[0-9,\.]*/let version=\"&\"/" Version.txt > src/version.ml
	$(SED) "s/[0-9,\.]*/\\\newcommand\{\\\DiMoVersion\}\{&\}/" Version.txt > doc/version.tex

