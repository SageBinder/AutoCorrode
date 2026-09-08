# A shallow-embedding of Separation Logic

This directory contains generic material related to the development of
Separation Logic. To perform a batch build of all theories, and generate PDF
documentation, invoke:

```shell
λ> $ISABELLE_HOME/bin/isabelle build -d ../Misc -d ../Micro_Rust_Parsing_Legacy_Frontend -d ../Shallow_Micro_Rust_Base -d ../Micro_Rust_Parser_Impl -d ../Shallow_Micro_Rust -D .
```

To edit interactively, use:

```shell
λ> $ISABELLE_HOME/bin/isabelle jedit -d ../Misc -d ../Micro_Rust_Parsing_Legacy_Frontend -d ../Shallow_Micro_Rust_Base -d ../Micro_Rust_Parser_Impl -d ../Shallow_Micro_Rust *.thy &
```
