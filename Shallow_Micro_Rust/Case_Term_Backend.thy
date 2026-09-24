(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Case_Term_Backend
  imports Main
begin

section\<open>Unchecked HOL case-term construction\<close>

text\<open>
This theory is the language-neutral owner of the raw HOL case-combinator
trees used by parser frontends. It deliberately contains no surface syntax
or parse translations.
\<close>

ML\<open>
structure Case_Term_Backend =
struct
  fun case_constant name arguments =
    Term.list_comb (Const (name, dummyT), arguments)

  fun case_guard guard scrutinee cases =
    case_constant \<^const_name>\<open>case_guard\<close> [guard, scrutinee, cases]

  fun case_cons head tail =
    case_constant \<^const_name>\<open>case_cons\<close> [head, tail]

  val case_nil = Const (\<^const_name>\<open>case_nil\<close>, dummyT)

  fun case_element pattern body =
    case_constant \<^const_name>\<open>case_elem\<close> [pattern, body]

  fun case_abstraction abstraction =
    case_constant \<^const_name>\<open>case_abs\<close> [abstraction]

  fun make_case guard scrutinee branches =
    case_guard guard scrutinee (fold_rev case_cons branches case_nil)
end
\<close>

end
