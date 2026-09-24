theory Parser_Iterator_Fixtures
  imports
    Parser_Test_Utils
    Shallow_Micro_Rust.Eval
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

section\<open>Shared iterator fixtures\<close>

type_synonym zip_left_iterator =
  \<open>(nat list, nat, unit, unit, unit) iterator\<close>

type_synonym zip_right_iterator =
  \<open>(nat list, bool, unit, unit, unit) iterator\<close>

type_synonym zip_pair_iterator =
  \<open>(nat list, nat \<times> bool \<times> tnil, unit, unit, unit) iterator\<close>

definition zip_left_empty :: zip_left_iterator where
  \<open>zip_left_empty \<equiv> make_iterator []\<close>

definition zip_left_two :: zip_left_iterator where
  \<open>zip_left_two \<equiv> make_iterator [fun_literal 1, fun_literal 2]\<close>

definition zip_left_one :: zip_left_iterator where
  \<open>zip_left_one \<equiv> make_iterator [fun_literal 1]\<close>

definition zip_right_one :: zip_right_iterator where
  \<open>zip_right_one \<equiv> make_iterator [fun_literal True]\<close>

definition zip_right_two :: zip_right_iterator where
  \<open>zip_right_two \<equiv> make_iterator [fun_literal True, fun_literal False]\<close>

definition zip_effect_thunk ::
    \<open>nat \<Rightarrow> 'value \<Rightarrow>
     (nat list, 'value, unit, unit, unit) function_body\<close>
  where
  \<open>zip_effect_thunk marker value \<equiv> FunctionBody (
    bind (put (\<lambda>trace. trace @ [marker])) (\<lambda>_. literal value))\<close>

end
