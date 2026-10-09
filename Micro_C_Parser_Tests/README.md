# AutoCorrode/C regression suite

`Micro_C_Parser_Tests` is the executable specification for C parsing, translation,
commands, diagnostics, and generated program behavior. It complements the
separation-logic proofs in `Micro_C_Examples`. CI runs both, plus the language
isolation tests.

Run the whole C suite from the repository root:

```sh
make ISABELLE_HOME=/path/to/Isabelle2025-2/bin \
  AFP_COMPONENT_BASE=/path/to/afp/thys \
  ISABELLE_FLAGS="-b -j 1 -o threads=2" c-tests
```

For a focused run, use `build-micro-c-parser-tests`. `c-test-audit` checks that
all test theories are registered, fixtures are used, the coverage manifest points
to real tests, and no proof bypass appears in the test or example corpus. This
audit is structural; passing Isabelle builds establish the proofs and assertions.
Expected errors are caught inside immutable theory values and do not require
failing sessions or disabled proofs.

## Coverage parallel to the µRust suite

| Layer | C theories | Corresponding µRust coverage |
| --- | --- | --- |
| Expressions | `C_Parser_Expression_Tests`, `C_Parser_Semantics_Tests` | expression tests and checked lowering |
| Grammar | `C_Parser_Syntax_Tests` | precedence, grouping, comments, separators |
| Functions and control | `C_Parser_Function_Tests`, `C_Parser_Control_Flow_Tests` | function tests, branches, iteration, matching |
| Declarations and types | `C_Parser_Type_Tests` | datatype and declaration tests |
| Resolution | `C_Parser_Name_Resolution_Tests` | lexical shadowing and namespace collisions |
| Memory | `C_Parser_Memory_Tests`, `C_Parser_Runtime_Tests` | references, mutation, aggregates |
| Commands | `C_Parser_Command_Tests`, `Parser_Denotation_Tests` | options, artifacts, local targets |
| Rejection and recovery | `C_Parser_Rejection_Tests`, `Parser_Expected_Failures` | rejection tests and subsequent recovery |
| Positions | `C_Parser_Position_Tests`, `Parser_Adapter_Tests` | source ranges and semantic navigation boundaries |
| Target profiles | `C_Parser_Profile_Tests` | C-specific ABI/compiler configuration |

Language-specific surfaces differ: C consumes translation units through
Isabelle/C and has no public expression command, notation-registration layer,
or source pretty-printer. It therefore tests the actual `c_source`/`c_file`
surface, raw AST ranges, C declarations, and switch behavior rather than
introducing substitutes for the µRust-only commands or grammar.

## What is asserted

- New positive functions are checked for well-typed generated definitions,
  escaped lexical variables, and unsupported stubs. Selected cases additionally
  assert signatures and the exact arithmetic, control, memory, and abort backends.
- Precedence tests compare untyped term structure against explicit grouping:
  generated schematic type-variable names are irrelevant to grouping. Separate
  signature and semantic checks retain type coverage, and alternative groupings
  must remain different.
- Memory-bearing signatures may contain generated phantom `TYPE` parameters;
  control-flow tests distinguish those from C parameters and explicit loop fuel.
- Semantic rows prove evaluations of freshly generated C functions, including
  wrapping, signed extrema, truncating signed division/remainder, division by
  zero, shifts at the width boundary, casts, comparison results, and unevaluated
  `sizeof`, generic associations, and short-circuit branches. Pointer identities
  and null-terminated string returns guard inference-driven return representations.
- The scalar-store fixture executes assignments, increments/decrements, scope
  shadowing, loops with explicit insufficient and sufficient fuel, break,
  continue, nested-loop and switch/loop interactions, early returns, switch
  fall-through and returns, forward/backward goto, reads, writes, and swap.
  It tests observable values and store changes. It is not a byte-memory or
  lifetime model; the examples verify those separate abstract memory contracts.
- All five ABI profiles are crossed with all six compiler profiles. Each of the
  30 combinations checks metadata, actual parameter types, shift/narrowing
  backends, evaluated `sizeof(long)`/`sizeof(void *)`, and actual signed shifts
  and narrowing at their profile-dependent boundaries.
- Inline and file translation, manifest comments/list markers, selection,
  empty filters, two-pass extraction, namespace extension, locale invocation,
  generated-name collisions, and duplicate options are exercised.
- Negative tests require the expected diagnostic fragment and source identity;
  interrupts propagate. Recovery reuses the failed namespace with a different
  ABI/compiler configuration and checks the new metadata.

The pinned Isabelle/C parser rejects multi-character constants during parsing,
before the translator's dedicated diagnostic is reachable. The rejection row
records this parser boundary. Other upstream declaration-specifier limitations
remain documented in `Micro_C_Parsing_Frontend/README.md`.
Raw AST positions do not necessarily retain filenames. Position tests check
exact recovered source and lines; frontend diagnostics separately check the
original source identity.

## Existing boundary and concurrency tests

`Parser_Elaboration_Tests` and `Parser_Denotation_Tests` exercise the neutral
diagnostic, checked-term, declaration-plan, and transaction helpers.
`Parser_Expected_Failures` checks malformed options/manifests, configuration
mismatches, collisions, unsupported variadic functions, and late translation
failures followed by recovery.

`Parser_Concurrent_A` and `Parser_Concurrent_B` are sibling-theory parses.
`Parser_Parallel_Adapter_Tests` runs 36 parses through Isabelle futures and checks
raw declarations, source identities, and recovered ranges.
`Parser_Parallel_Translation_Tests` translates four independently configured
units concurrently and checks metadata and namespace isolation.

The parser and C example sessions inherit the production frontend heap so focused
rebuilds do not replay its dependencies. Every `.thy` in this directory is registered in `ROOT`.
The layer inventory is recorded in `design-documents/c-parity-manifest.json`.
