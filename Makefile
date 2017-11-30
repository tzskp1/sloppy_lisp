all : sloppy_lisp

eval.cmx: eval.ml
	ocamlopt -c eval.ml

parse.cmx: parse.ml eval.cmx
	ocamlopt -c parse.ml

main.cmx: main.ml eval.cmx parse.cmx
	ocamlopt -c main.ml

sloppy_lisp: main.cmx eval.cmx parse.cmx
	ocamlopt -o sloppy_lisp eval.cmx parse.cmx main.cmx
