# A shallow embedding of µRust

This directory contains the parser-independent shallow semantics for µRust (or
"Micro Rust") in Isabelle/HOL, including the expression and continuation types,
core operations, iterator and value semantics, parser target, lemmas, evaluation,
pullback, SSA, and roll-up theories.

The theories use direct HOL expressions and HOL monadic notation.
`Micro_Rust_Parser_Impl` depends on this session; parser-backed clients import
the production parser separately where needed.

To perform a batch build:

```shell
λ> $ISABELLE_HOME/bin/isabelle build -d .. Shallow_Micro_Rust
```

To open this session for interactive editing (from within the directory):

```shell
λ> $ISABELLE_HOME/bin/isabelle jedit -d .. -l Shallow_Micro_Rust *.thy &
```
