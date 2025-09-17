# rocq-session-types-tutorial
This is the code for the paper:

_Mechanizing the Meta-Theory of Session Types in Rocq: a Tutorial._

by Marco Carbone and Alberto Momigliano

There are **2** versions of the implementation and accordingly of the paper describing it:

1. The `main` branch with the current, maintained and simpler code
2. The branch `tutorial-with-autosubsts2`, where the syntax was generated via Autosubst2 

## Instructions

It can be run either with Rocq 9.0.0 or with Coq Classic 8.20.1

- `rocq makefile -f _CoqProject *.v -o Makefile; mv Makefile* theories; make`

- `coq_makefile -f _CoqProject *.v -o Makefile; mv Makefile* theories; make`


Whatever the version, you need to install the following Coq library:
- all_ssreflect
