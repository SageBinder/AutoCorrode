# A shallow-embedding of Separation Logic

This directory contains generic material related to the development of
Separation Logic. To perform a batch build of all theories, and generate PDF
documentation, invoke:

```shell
λ> $ISABELLE_HOME/bin/isabelle build -d .. Shallow_Separation_Logic
```

To edit interactively, use:

```shell
λ> $ISABELLE_HOME/bin/isabelle jedit -d .. -l Shallow_Separation_Logic *.thy &
```
