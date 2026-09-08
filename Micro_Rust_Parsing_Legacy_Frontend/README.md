# Legacy Micro Rust parsing frontend

This directory contains the legacy inner-syntax parser for Micro Rust
expressions. It remains available as the conformance oracle for the production
parser. To perform a batch build of all theories and generate PDF
documentation, invoke:

```shell
λ> $ISABELLE_HOME/bin/isabelle build -D .
```

To edit interactively, use:

```shell
λ> $ISABELLE_HOME/bin/isabelle jedit *.thy &
```
