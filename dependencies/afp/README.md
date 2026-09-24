# AFP dependencies

AutoCorrode depends on the following AFP entries. Download and unpack them here.
If they are located in a different directory, set the `AFP_COMPONENT_BASE` environment variable accordingly.

- [Word_Lib](https://www.isa-afp.org/entries/Word_Lib.html) — word-level operations and bit manipulation
- [Isabelle_C](https://www.isa-afp.org/entries/Isabelle_C.html) — C11 parser front-end (required only
  for the isolated Micro C adapter session)

CI pins `isabelle-prover/mirror-afp-2025-2` at
`42452c8a5661996af380ce4ee01c253a3ec8fa52`. For the C baseline, point `AFP_SOURCE_BASE` at that
checkout's `thys` directory and run `make prepare-isabelle-c`. The preparation script validates the
pin, copies Isabelle/C here, and applies the exact multi-specifier-parameter compatibility patch.
