default:
	ocamlbuild -tag thread -use-ocamlfind -use-menhir -package batteries Parse.native

clean:
	rm -f *.cmx
	rm -f *.cmi
	rm -f *.o
	rm -f *.cmo
	rm -f *.automaton
	rm -Rf _build
	rm Parse.native
