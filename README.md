Table of Contents
=================

  * [Introduction](#introduction)
  * [Installation](#installation)

# Introduction

This is a supplementary repository for a one-term course on formal semantics. The project consists of the following files:

- `Id.v` --- definition of identifiers (partially inherited from Benjamin Pierce's Software Foundations);
- `State.v` --- definition of states and some operations for states;
- `Expr.v` --- pure strict expressions with big-step evaluation definition and equivalences;
- `Stmt.v` --- a While-like language with big-step/small-step/CPS semantics, equivalences and properties.
- Some other things in progress.

# Installation

The use of [opam](https://opam.ocaml.org) is highly advised. The current version works
with `ocaml>=4.07.1` and `coq>=8.8.2`. From the command line:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq
opam install coq-bignums
opam install coq-hahn
```
This will install coq + bignums + hahn library. You can then make the project
```bash
make
```
to make sure everything is in sync.
