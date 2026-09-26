# µRust parser implementation

## Automatic-read ownership

`Parser_Impl_Auto_Deref.thy` is the sole owner of parser-internal automatic-read eligibility,
lowered-result metadata, marker encoding, type-directed resolution, one-cycle deferral, unresolved
marker rejection, and term-check phase registration.

The public interface is intentionally limited to:

- `plain`;
- `eligible`;
- `transparent`;
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

The abstraction was extracted from base commit
`52abf4e6e47f47ef17bcc3d10cae3a6ce1fec0f4`. The implementation-and-policy checkpoint before this
documentation commit is `41a309d`.
