# Micro C parser and translation tests

This session is the executable specification for the Isabelle/C-backed prototype frontend. It
keeps parser-adapter normalization, source-position checks, pure elaboration, neutral lowering,
definition installation, evaluation, rejection, failure-atomicity, and re-entrancy coverage
separate from the implementation sessions.

## Test theories

- `Parser_Adapter_Tests.thy` checks complete-function normalization, source ranges, expression
  association, and positional rejection of unsupported AST categories.
- `Parser_Elaboration_Tests.thy` exercises type, prototype, parameter, scope, and integer-literal
  validation without parsing or installation, and exercises lowering without declaration.
- `Parser_Denotation_Tests.thy` checks generated definitions, successful evaluation, signed
  overflow, named-theorem registration, and failure-atomic installation.
- `Parser_Concurrent_A.thy` and `Parser_Concurrent_B.thy` translate independently from the same
  parent theory, exercising re-entrant command state.

Every tracked `.thy` file in this directory is registered in `ROOT`.
