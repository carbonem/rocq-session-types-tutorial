# rocq-session-types-tutorial
A tutorial on how to mechanize session types in Rocq with Linearity Predicates. In this branch we rely on the output of _Autosubst2_.

## Compatibility

It can be run either with Rocq 9.0.0 or with Coq Classic 8.20.1. 

- `rocq makefile -f _CoqProject *.v -o Makefile; mv Makefile* theories; make`

- `coq_makefile -f _CoqProject *.v -o Makefile; mv Makefile* theories; make`

In both cases, you need to install the following Coq libraries:
- all_ssreflect
