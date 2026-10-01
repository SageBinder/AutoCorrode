# AutoCorrode Tutorial

A Beamer slide deck generated from formally-checked Isabelle/HOL theories.
Every slide is a live theory: definitions, types, lemmas, and proofs shown
in the PDF were type-checked at build time, so the deck cannot compile if a
referenced fact stops being true.

The deck is intended both as a guided walkthrough of AutoCorrode and as an
experimentation ground -- open the sources in jEdit, change a definition or
a contract, and watch which proofs still go through.

## Layout

- `ROOT` -- Isabelle session `AutoCorrodeTutorial`, inheriting the
  `AutoCorrode` parent session.
- `Slides.thy` -- outer-syntax commands (`slide`, `end_slide`,
  `interlude`, ...) that emit Beamer frame markup from `.thy` files.
- `Tutorial_*.thy` -- one theory per topic (preamble, monads, Hoare logic,
  separation logic, etc.). Loaded in order from `document/root.tex`.
- `document/root.tex` -- Beamer document skeleton; chooses which
  `Tutorial_*.tex` are included and in what order.
- `Makefile` -- thin wrapper around `isabelle build`.
- `output/` -- Isabelle's session output directory; `output/document.pdf`
  is copied to `autocorrode_tutorial.pdf`.

## Build

Set `AFP_COMPONENT_BASE` to the installed AFP snapshot's `thys` directory, then run:

```sh
make AFP_COMPONENT_BASE=/path/to/afp/thys heaps
make AFP_COMPONENT_BASE=/path/to/afp/thys build
```

The same target is available from the repository root as
`make AFP_COMPONENT_BASE=/path/to/afp/thys tutorial`.
