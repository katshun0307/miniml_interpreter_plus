
PROG = miniml

default: main.exe 

%.exe: main.ml lexer.ml parser.ml
	dune build $@ --profile release
	mv ./_build/default/main.exe miniml

lexer.ml: lexer.mll
	ocamllex lexer.mll

parser.ml: parser.mly
	menhir parser.mly

clean: 
	rm lexer.cmi lexer.cmx lexer.ml lexer.o
	rm parser.ml parser.mli parser.o parser.conflicts parser.automaton
	dune clean
