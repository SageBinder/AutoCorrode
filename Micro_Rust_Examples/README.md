# Micro Rust Examples

This directory contains various examples demonstrating aspects of Micro Rust and its verification.

See [`Showcase.thy`](Showcase.thy) for a general overview of working with Micro Rust.  Then, for more detail, see:

- [`Basic_Micro_Rust.thy`](Basic_Micro_Rust.thy) for the basics of the Micro Rust language,
- [`Crush_Examples.thy`](Crush_Examples.thy) for examples of how to work with `crush`, our scalable automation tactic for weakest-precondition reasoning, and all the various tweakable knobs that it exposes,
- [`Common_Pitfalls.thy`](Common_Pitfalls.thy) for how to avoid some common issues when working with Micro Rust, especially when trying to combine it with Isabelle's code generator,
- [`Reference_Examples.thy`](Reference_Examples.thy) for examples of how to work with references in Micro Rust,
- [`Pullback_Example.thy`](Pullback_Example.thy) for pulling the heap reference implementation back along a separation lens, including precise transport of reference stack ownership,
- [`Linked_List.thy`](Linked_List.thy), [`Linked_List_Executable_Heap.thy`](Linked_List_Executable_Heap.thy), [`Linked_List_Executable_Hybrid.thy`](Linked_List_Executable_Hybrid.thy), and [`Linked_List_Exececutable_Physical_Memory.thy`](Linked_List_Executable_Physical_Memory.thy) for a series of examples of working with pointer-bearing data-structures (linked lists) in Micro Rusts with different underlying memory models.

Reference allocation contracts carry `reference_stack F Φ`, which records the live references.
Allocation contracts are verified in `Showcase.thy`, `Tutorial.thy`, `Linked_List.thy` and the
ML-KEM examples. `Reference_Examples.thy` covers distinctness, interior popping, and concrete heap
membership and reordering. The pullback example exercises transferred membership and precise
pullback of stack ownership. Physical-memory allocation remains unsupported.

