(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Logging
  imports
    Shallow_Micro_Rust.Shallow_Micro_Rust
begin
declare [[urust_conformance_check = true]]
(*>*)

section\<open>The Rust logging facade\<close>

subsection\<open>The facade, proper\<close>

text\<open>Strictly speaking the interface (facade) of the Rust logging API is separate from its
implementations.  Here, we provide a unified interface and simple implementation, calling into the
underlying primitive logger, provided as a yield handler.  Note that strictly speaking these are
also \<^emph>\<open>macros\<close> in Rust; we use \<^verbatim>\<open>\<mu>Rust\<close> functions to model logging instead.

First, the \<^verbatim>\<open>fatal\<close> logger:\<close>
urust fn [urust_abbrev = true] fatal ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) fatal ("fatal!")

text\<open>The \<^verbatim>\<open>info\<close> logger:\<close>
urust fn [urust_abbrev = true] info ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Info\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) info ("info!")

text\<open>The \<^verbatim>\<open>error\<close> logger:\<close>
urust fn [urust_abbrev = true] error ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) error ("error!")

text\<open>The \<^verbatim>\<open>debug\<close> logger:\<close>
urust fn [urust_abbrev = true] debug ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Debug\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) debug ("debug!")

text\<open>The \<^verbatim>\<open>trace\<close> logger:\<close>
urust fn [urust_abbrev = true] trace ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) trace ("trace!")

\<comment>\<open>A bit of syntax sugar to reduce the pain of writing logging expressions:
   Write \<^verbatim>\<open>trace! ([["string0", data0, "string1", data1, ...]])\<close>\<close>
nonterminal log_entry
nonterminal log_entry_list
syntax
  "_log_entry_id" :: "id \<Rightarrow> log_entry"
    ("_" [0]1000)
  "_log_entry_string" :: "string_token \<Rightarrow> log_entry"
    ("_" [0]1000)
  "_log_entry_list_single" :: "log_entry \<Rightarrow> log_entry_list"
    ("_" [0]1000)
  "_log_entry_list_cons" :: "log_entry \<Rightarrow> log_entry_list \<Rightarrow> log_entry_list"
    ("_, _" [0, 0] 1000)
  "_log_entry_list_to_hol" :: "log_entry_list \<Rightarrow> logic"
  "_log_entry_to_hol" :: "log_entry \<Rightarrow> logic"
  "_urust_log_data" :: "log_entry_list \<Rightarrow> urust"
    ("l\<llangle>_\<rrangle>" [0] 1000)
translations
  "_log_entry_list_to_hol (_log_entry_list_single e)" \<rightharpoonup> "_log_entry_to_hol e"
  "_log_entry_list_to_hol (_log_entry_list_cons e es)" \<rightharpoonup> "CONST List.append (_log_entry_to_hol e) (_log_entry_list_to_hol es)"
  "_log_entry_to_hol (_log_entry_string s)" \<rightharpoonup> "CONST Cons (CONST LogString (_string_token_to_hol s)) (CONST Nil)"
  "_log_entry_to_hol (_log_entry_id s)" \<rightharpoonup> "CONST generate_debug s"
  "_shallow (_urust_log_data es)" \<rightharpoonup> "CONST literal (_log_entry_list_to_hol es)"

urust expr [urust_abbrev = true] StdLib_Logging_urust_site_1
  (x, y, z)
  \<open>
  fatal!(l\<llangle>"this ", x, " is ", y, " a ", z, " test "\<rrangle>)
  \<close>

term \<open>StdLib_Logging_urust_site_1 x y z\<close>

(*<*)
end
(*>*)
