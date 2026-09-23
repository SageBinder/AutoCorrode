(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Legacy_Parser_Provider
  imports
    Micro_Rust_Shallow_Embedding
    Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

section\<open>Legacy conformance provider\<close>

ML\<open>
fun legacy_micro_rust_parse ctxt source =
  Syntax.parse_term ctxt
    ("\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>")
\<close>

setup \<open>
  Context.theory_map
    (Micro_Rust_Legacy_Parser_Provider.register legacy_micro_rust_parse)
\<close>

end
