# DiMo
A Tool for Discrete Modelling Using Propositional Logic


Installation
============

1. Install and initialize opam, see https://opam.ocaml.org/

2. Issue the following commands in order to obtain all necessary packages and the right OCaml compiler.

```
opam switch 4.07.0
eval `opam config env` 
opam install ocamlbuild ocamlfind ocaml-sat-solvers
```

3. To build a byte-code version of the discrete modelling tool, issue

```
make
```

Optionally, use

```
make native
```

to build a native version.



Running
=======

Issue

> dimo.byte -h

respectively

> dimo.native -h

to see info on the use via the command line.
