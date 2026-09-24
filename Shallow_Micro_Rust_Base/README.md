# Shallow µRust base

This directory contains the parser-independent shallow semantics for µRust. The session defines
the expression and continuation types, core operations, iterator and value semantics, and the
syntax-neutral notation registry and parser target.

`Micro_Rust_Parser_Impl` depends on this session. Parser-backed lemmas, evaluation, pullback, SSA,
and the integrated roll-up theories live in the downstream `Shallow_Micro_Rust` session.

From the repository root, build the session with:

```shell
$ISABELLE_HOME/bin/isabelle build -d . Shallow_Micro_Rust_Base
```

To open its theories for interactive editing:

```shell
$ISABELLE_HOME/bin/isabelle jedit -d . -l Shallow_Micro_Rust_Base \
  Shallow_Micro_Rust_Base/*.thy &
```
