EXENAME=explanator2
MODULENAME=main
NAME=src/$(MODULENAME)
OCAMLBUILD=ocamlbuild -use-ocamlfind -use-menhir -no-plugin -package safa -package str -yaccflags --explain
OCAMLFIND=ocamlfind
OBJS=$(wildcard _build/*.cm* _build/*.a _build/*.o)
# OBJS=$(wildcard _build/*.{cmi,cmo,cma,cmx,cmxa,a,o})

SOURCEFOLDER=src

standalone:
	$(OCAMLBUILD) $(NAME).native
	mv -f $(MODULENAME).native $(EXENAME).native

install: standalone
	cp ./$(EXENAME).native $(PREFIX)/bin/$(EXENAME)

uninstall:
	rm -f ${PREFIX}/bin/$(EXENAME)

clean:
	$(OCAMLBUILD) -clean
