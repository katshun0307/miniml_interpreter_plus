# MiniML Interpreter

## prerequisites

+ menhir
+ ocamllex
+ core

## Building and invoking MiniML interpreter

Software written in OCaml 
- Type `make` to build.
- Type `./miniml` to invoke the interpreter.

## Files

This directory contains the following files.

- `main.ml`: The entry point of the entire interpreter.
- `syntax.ml`: Definition of the type for MiniML abstract syntax trees.
- `eval.ml`: The functions that evaluate MiniML expressions/declarations.
- `parser.mly`: The definition of the MiniML parser.
- `lexer.mll`: The definition of the MiniML lexer.
- `environment.mli`: The interface of the ADT (abstract data type) for
  an environment -- an important data structure often used in
  interpreters and compilers.
- `environment.ml`: The implementation of the ADT for an environment.
- `mySet.mli`: The interface of the ADT for a set.
- `mySet.ml`: The implementation of the ADT for a set.
- `typing.ml`: The implementation of MiniML type inference (to be
  implemented by students.)
- `test.ml`: Test file. Run test with `./miniml -test`.
- `Makefile`: Makefile interpreted by `make`.

After typing `make`, the OCaml compiler generates many intermediate
files.  Important files among them are following.
- `parser.automaton`: Description of the LR(1) automaton generated
  from `parser.mly`.  If you encounter a conflict(s) after customizing
  the parser, read this file carefully (and think how you should
  correct your parser).
