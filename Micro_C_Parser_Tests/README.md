# Micro C adapter, frontend, and command-transaction tests

This session is the executable specification for the direct Isabelle/C boundary and the
language-neutral `Frontend_Common` support library. It checks that parsing preserves the raw
translation-unit AST, positions can be mapped back to source text, frontend declaration
preflight remains failure-atomic, and failed C commands do not mutate their input theory.

## Test theories

- `Parser_Adapter_Tests.thy` checks raw AST preservation, source ranges, source extraction, and
  parser-error propagation.
- `Parser_Elaboration_Tests.thy` checks positioned diagnostics and checked HOL term builders.
- `Parser_Denotation_Tests.thy` checks immutable declaration plans, namespace collision
  preflight, checked-term obligations, and transactional rollback.
- `Parser_Concurrent_A.thy` and `Parser_Concurrent_B.thy` retain independent sibling-theory
  adapter parses, exercising the session scheduler's theory-level concurrency.
- `Parser_Parallel_Adapter_Tests.thy` runs 36 direct-AST adapter parses through Isabelle
  futures, checking raw declaration counts, source ranges, source identities, and exact source
  recovery.
- `Parser_Parallel_Translation_Tests.thy` translates four independent units concurrently under
  distinct ABI/compiler profiles and checks generated pointer width, `long` width, plain-char
  signedness, endianness, and declaration isolation.
- `Parser_Expected_Failures.thy` executes actual `c_source` and `c_file` outer-syntax
  transactions in isolated theory values. It catches configuration mismatches, existing-name
  collisions, inline-selection/manifest conflicts, positioned unsupported variadic functions,
  and late undeclared-call failures. It checks declaration rollback and successful recovery
  after each stateful failure.

Every tracked `.thy` file in this directory is registered in `ROOT`.
