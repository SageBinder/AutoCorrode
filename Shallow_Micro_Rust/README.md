# A shallow embedding of µRust

This directory contains material related to the shallow embedding of µRust (or
"Micro Rust") in Isabelle/HOL.

The theories use direct HOL expressions and HOL monadic notation rather than
the legacy parser frontend. `Legacy_Parser_Isolation_Tests.thy` checks that the
old embedding bracket is unavailable in the completed session context.

To perform a batch build:

```shell
λ> $ISABELLE_HOME/bin/isabelle build -d .. Shallow_Micro_Rust
```

To open this session for interactive editing (from within the directory):

```shell
λ> $ISABELLE_HOME/bin/isabelle jedit -d .. -l Shallow_Micro_Rust *.thy &
```
