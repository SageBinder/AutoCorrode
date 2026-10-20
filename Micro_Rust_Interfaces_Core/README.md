# Micro Rust Interfaces (Core)

`References.thy` specifies typed and raw references through the `reference` locale. Allocation
requires `reference_stack F Φ`: it owns the allocator, lists the live references, and constrains
absorbed cell values with `F`. Allocation appends the new reference, stack ownership implies
distinctness, and a full cell satisfying `F` can be absorbed at any known list position.

Contracts carry the stack explicitly; an allocation capability alone does not record the resources
needed to release a cell. The concrete heap proves membership for a separately owned full cell
(`urust_heap_reference_stack_member` in `Micro_Rust_Runtime/Runtime_Heap.thy`), and its stack
assertion is invariant under reordering (`heap_stack_reordering` in
`Micro_Rust_Examples/Reference_Examples.thy`). These are backend properties rather than
assumptions of the generic locale.

`Micro_Rust_Interfaces/Transfer_References.thy` transports stack ownership by precise
separation-lens pullback. Physical memory continues to reject allocation: its stack assertion and
new-value domain are empty. See `Micro_Rust_Examples/Reference_Examples.thy` and
`Micro_Rust_Examples/Pullback_Example.thy` for concrete uses.
