# µRust parser implementation

## Automatic-read ownership

`Parser_Impl_Auto_Deref.thy` is the sole owner of parser-internal automatic-read eligibility,
lowered-result metadata, marker encoding, type-directed resolution, one-cycle deferral, unresolved
marker rejection, and term-check phase registration.

The public interface is intentionally limited to:

- `plain`;
- `eligible`;
- `transparent`;
- `project_field`;
- `project_index`;
- `raw_term`; and
- `value_term`.

The result policy is fail-closed:

| Expression result | Policy |
|---|---|
| `UE_Path` | Conditional candidate after resolution classifies an allocated mutable local |
| `UE_Field`, `UE_Index` | Projected candidate |
| `UE_Group`, `UE_Block` | Transparent carrier |
| Every other constructor | Never a candidate |

`Parser_Impl_Translate.thy` owns AST traversal and may only consume lowered results through
`raw_term` or `value_term`. Field/index receivers, borrow operands, explicit-dereference operands,
and assignment places use the raw form. Declaration roots and ordinary value-consuming children use
the value form.

`Parser_Impl_Shallow_Terms.thy` retains the marker declaration for qualified-name compatibility and
the exact low-level shallow term that performs a core-reference read. It does not expose marker
construction or checking policy. `URust_Shallow_Terms.automatic_dereference` has one production
caller: `URust_Auto_Deref`.

## Composed places and notation dispatch

An eligible projection carries a private place recipe: its base term, its base source position, and
an ordered sequence of field or index segments. A field segment stores the witness already resolved
by `URust_Resolution`; an index segment stores the lowered index term once. Both retain their
operator source positions for semantic navigation.

Projection recipes are resolved inside-out. Ordinary-value receivers use value projection and do
not acquire an automatic read. Core-reference receivers use reference-preserving projection.
Crossing a nested core-reference boundary inserts one intermediate read before continuing with the
remaining segment. The final read is decided only after the complete place and its expected type
are known.

`Micro_Rust_Dispatch` exposes notation candidates, each candidate's instantiated type, and
single-candidate selection. `URust_Auto_Deref` checks the receiver and argument recipes against
candidate parameter types before selection. A uniquely compatible reference-consuming backend
receives the raw place; a uniquely compatible value-consuming backend receives its value form.
Multiple compatible backends retain the existing ambiguity diagnostic, and no compatible backend
retains the existing no-match diagnostic. Dispatch rejection runs before unresolved automatic-read
or projection markers are rejected.

This support is deliberately narrow. It does not recursively retry checking, implicitly borrow,
auto-dereference arbitrary wrappers, auto-dereference call results, or make call-result expressions
eligible places.

## Regression oracle and checkpoints

`Parser_Automatic_Read_Hardening_Tests.thy` is the focused public acceptance oracle. Its neutral
fixtures cover composed projections, nested core references, single evaluation of dynamic indices,
expected-type propagation, reference/value notation dispatch, ambiguity and recovery, raw-place
boundaries, ordinary receivers, negative eligibility boundaries, internal-marker rejection, and
mutation-guard sensitivity.

The work is based on `52abf4e6e47f47ef17bcc3d10cae3a6ce1fec0f4`. The completed Phase 1 checkpoint
is `080b8f25c49caf96c081f8ac60660213e52f45a4`; the Phase 2 implementation-and-regression checkpoint
before this documentation commit is `f7c442ab607babb5184d0a9ea26010f208264ab0`.
