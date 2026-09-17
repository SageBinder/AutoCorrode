# Parser test-to-notes traceability

This file records links between parser test coverage and the corresponding planning or design items.
The theories intentionally describe the behavior without these item identifiers.

| Item | Test coverage and relationship |
|---|---|
| D-1 | `Parser_Expr_Conformance_Tests.thy`, “Resolved: direct if binary operands”, keeps the shared parenthesized conformance fixture; direct parser-only operand rows are in `Parser_Syntax_Tests.thy`. |
| D-2 | `Parser_Expr_Conformance_Tests.thy`, “Resolved: no-semicolon sequencing of block-like expressions”, covers block, `if`, and `if`/`else` sequencing. |
| D-3 | `Parser_Expr_Conformance_Tests.thy`, “Resolved: HOL-constant-named binders are captured in antiquotations”, covers constant and notation-name shadowing. |
| D-5 | `Parser_Expr_Conformance_Tests.thy`, “Resolved: embedded HOL callees”, covers expression-antiquotation callees and arity-indexed function literals; `Parser_Rejection_Tests.thy` covers their restricted generic grammar. |
| D-7 | `Parser_Expr_Conformance_Tests.thy`, “Rich case-pattern lowering” and “Resolved: advanced patterns and consumer-specific gates”, covers nested/or patterns and the consumer-specific acceptance boundaries. |
| D-13 | `Parser_Rejection_Tests.thy` and `Parser_Struct_Ambiguity_{Left,Right}_Fixtures.thy` cover rejection and diagnostics for ambiguous unqualified struct heads. |
| D-14 | `Parser_Rejection_Tests.thy` covers the ordinary datatype selector named `more` that the legacy frontend mistakes for record-extension metadata. |
| D-15 | `Parser_Rejection_Tests.thy`, “Fueled loops”, covers rejection of unparenthesized fueled-`while` conditions; parenthesized positive rows are in `Parser_Expr_Conformance_Tests.thy`. |
| D-20 | `Parser_Expr_Conformance_Tests.thy`, “Semantic turbofish”, covers the supported restricted payload grammar; `Parser_Rejection_Tests.thy`, “Restricted turbofish grammar”, covers unsupported arbitrary HOL payloads. |
| D-21 | Struct-expression positive coverage is in `Parser_Expr_Conformance_Tests.thy`; negative coverage is in `Parser_Rejection_Tests.thy`; legacy frontend goldens are in `Parser_Conformance_Corpus.thy`. |
| D-22 | `Parser_Expr_Conformance_Tests.thy`, “Yield and primitive logging”, covers positive placement and lowering; malformed logging-data coverage is in `Parser_Rejection_Tests.thy`. |
| D-23 | `Parser_Rejection_Tests.thy`, “Unparenthesized struct expressions in control heads”, covers the restricted control-head surface; delimiter-restored positive coverage is in `Parser_Expr_Conformance_Tests.thy` and `Parser_Syntax_Tests.thy`. |
| D-24 | `Parser_Improvements_Tests.thy`, “Function parameter precedence”, checks that typed lexical parameters shadow registered literal, call, and field notation and compares this with explicit legacy spellings. |
| T-29 | `Parser_Rejection_Tests.thy` records the current explicit rejection boundary for HOL record patterns pending selector-based lowering. |
| T-39 | The struct-expression matrices in `Parser_Expr_Conformance_Tests.thy`, `Parser_Rejection_Tests.thy`, and `Parser_Conformance_Corpus.thy` preserve frontend-compatible syntax-only labels while metadata-correct semantics remain future work. |
