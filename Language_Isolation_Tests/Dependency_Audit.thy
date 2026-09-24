(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Dependency_Audit
  imports Main
begin

section\<open>Language-isolation dependency auditing\<close>

ML\<open>
structure Language_Isolation_Dependency_Audit =
struct

fun is_forbidden forbidden name =
  exists (fn prefix => name = prefix orelse String.isPrefix (prefix ^ ".") name) forbidden

fun forbidden_names forbidden names =
  filter (is_forbidden forbidden) names

fun assert_names label forbidden names =
  (case forbidden_names forbidden names of
    [] => ()
  | bad =>
      error (label ^ " has forbidden dependencies:\n  " ^
        commas (sort_strings (distinct (op =) bad))))

fun ancestry thy =
  map Context.theory_long_name (Theory.nodes_of thy)

fun assert_context label forbidden ctxt =
  assert_names label forbidden (ancestry (Proof_Context.theory_of ctxt))

end
\<close>

ML_val\<open>
  local
    open Language_Isolation_Dependency_Audit

    val forbidden =
      ["Micro_Rust_Parser_Impl", "Micro_Rust_Parsing_Legacy_Frontend",
       "Micro_C_Isabelle_C_Adapter", "Isabelle_C"]

    fun assert message condition =
      if condition then () else error ("dependency-audit unit test: " ^ message)
  in
    val _ = assert_names "synthetic allowed graph" forbidden
      ["HOL.Main", "Misc.Debug_Logging", "Lenses_And_Other_Optics.Lens"]
    val _ = assert "exact forbidden theory"
      (forbidden_names forbidden ["Micro_Rust_Parser_Impl"] =
        ["Micro_Rust_Parser_Impl"])
    val _ = assert "forbidden session descendant"
      (forbidden_names forbidden ["Micro_Rust_Parser_Impl.Parser_Impl_Command"] =
        ["Micro_Rust_Parser_Impl.Parser_Impl_Command"])
    val _ = assert "similarly named neutral theory is allowed"
      (null (forbidden_names forbidden ["Neutral.Micro_Rust_Parser_Impl_Helper"]))
  end
\<close>

end
