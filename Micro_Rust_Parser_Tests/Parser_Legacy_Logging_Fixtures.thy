(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Legacy_Logging_Fixtures
  imports
    Micro_Rust_Parsing_Legacy_Frontend.Legacy_Parser_Provider
    Micro_Rust_Std_Lib.StdLib_Logging
begin

section\<open>Legacy logging conformance fixture\<close>

text\<open>
The dedicated parser reads logging macros directly from the neutral notation
registry. Legacy conformance additionally needs the isolated adapter to replay
the logging registrations after the provider and standard-library import
branches merge. The old logging-data grammar also lives here rather than in the
production standard library.
\<close>

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
  "_log_entry_list_to_hol (_log_entry_list_cons e es)" \<rightharpoonup>
    "CONST List.append (_log_entry_to_hol e) (_log_entry_list_to_hol es)"
  "_log_entry_to_hol (_log_entry_string s)" \<rightharpoonup>
    "CONST Cons (CONST LogString (_string_token_to_hol s)) (CONST Nil)"
  "_log_entry_to_hol (_log_entry_id s)" \<rightharpoonup> "CONST generate_debug s"
  "_shallow (_urust_log_data es)" \<rightharpoonup>
    "CONST literal (_log_entry_list_to_hol es)"

local_setup \<open>Legacy_Micro_Rust_Notations.install_and_replay\<close>

end
