(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Micro_Rust
  imports
    Shallow_Micro_Rust_Base.Bool_Type
    Bool_Type_Lemmas
    Shallow_Micro_Rust_Base.Core_Expression
    Core_Expression_Lemmas
    Shallow_Micro_Rust_Base.Core_Syntax
    Shallow_Micro_Rust_Base.Result_Type
    Shallow_Micro_Rust_Base.Option_Type
    Shallow_Micro_Rust_Base.Range_Type
    Shallow_Micro_Rust_Base.Rust_Iterator
    Rust_Iterator_Lemmas
    Shallow_Micro_Rust_Base.Numeric_Types
    Numeric_Types_Lemmas
    Shallow_Micro_Rust_Base.Global_Store
    SSA
    Shallow_Micro_Rust_Base.Micro_Rust_Shallow_Embedding
begin
(*>*)

section\<open>Entry point for Micro Rust\<close>

text\<open>This theory's main purpose is to import all of the material related to Core Micro Rust.  It
also serves as a point where common material (for example, automation routines) can be placed.\<close>

(*<*)
end
(*>*)
