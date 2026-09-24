(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory StdLib_Logging
  imports
    Micro_Rust_Parser_Impl.Parser_Impl_Command
    Shallow_Micro_Rust.Shallow_Micro_Rust
begin
(*>*)

section\<open>The Rust logging facade\<close>

subsection\<open>The facade, proper\<close>

text\<open>Strictly speaking the interface (facade) of the Rust logging API is separate from its
implementations.  Here, we provide a unified interface and simple implementation, calling into the
underlying primitive logger, provided as a yield handler.  Note that strictly speaking these are
also \<^emph>\<open>macros\<close> in Rust; we use \<^verbatim>\<open>\<mu>Rust\<close> functions to model logging instead.

First, the \<^verbatim>\<open>fatal\<close> logger:\<close>
urust_fn [abbrev] fatal ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Fatal\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) fatal ("fatal!")

text\<open>The \<^verbatim>\<open>info\<close> logger:\<close>
urust_fn [abbrev] info ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Info\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) info ("info!")

text\<open>The \<^verbatim>\<open>error\<close> logger:\<close>
urust_fn [abbrev] error ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) error ("error!")

text\<open>The \<^verbatim>\<open>debug\<close> logger:\<close>
urust_fn [abbrev] debug ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Debug\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) debug ("debug!")

text\<open>The \<^verbatim>\<open>trace\<close> logger:\<close>
urust_fn [abbrev] trace ::
  \<open>log_data \<Rightarrow> ('s, unit, 'abort, 'i prompt, 'o prompt_output) function_body\<close>
  (m)
  \<open>
     \<l>\<o>\<g> \<llangle>Trace\<rrangle> \<llangle>m\<rrangle>
  \<close>
micro_rust_notation (call) trace ("trace!")

urust_expr [abbrev] StdLib_Logging_ex1
  (x, y, z)
  \<open>
  fatal!(l\<llangle>"this ", x, " is ", y, " a ", z, " test "\<rrangle>)
  \<close>

term \<open>StdLib_Logging_ex1 x y z\<close>

(*<*)
end
(*>*)
