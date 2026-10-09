(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Pullback_Profile
  imports
    Shallow_Computation.Pullback
    Eval_Profile
    Prompts_And_Responses
begin

setup \<open>Sign.root_path #> Sign.add_path "Pullback"\<close>

context
    fixes l :: \<open>('a, 'b) lens\<close>
  assumes LV: \<open>is_valid_lens l\<close>
begin

lemma canonical_pull_back_yield_handler_no_yield[simp]:
  shows \<open>canonical_pull_back_yield_handler l
      (yield_handler_no_yield ::
        ('b, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic) =
    (yield_handler_no_yield ::
      ('a, 'abort, 'i prompt, 'o prompt_output) yield_handler_nondet_basic)\<close>
  unfolding fun_eq_iff
  by (simp add: canonical_pull_back_yield_handler_def yield_handler_no_yield_def
                lift_yield_result_def LV lens_laws_update(2))

lemma canonical_pull_back_yield_handler_log_preserving:
  assumes \<open>is_log_transparent_yield_handler y\<close>
  shows \<open>is_log_transparent_yield_handler (canonical_pull_back_yield_handler l y)\<close>
proof -
  have update_view: \<open>\<And>\<sigma>. lens_update l (lens_view l \<sigma>) \<sigma> = \<sigma>\<close>
    using LV by (rule lens_laws_update(2))
  from assms show ?thesis
    by (clarsimp simp add: is_log_transparent_yield_handler_def
      canonical_pull_back_yield_handler_def lift_yield_result_def LV update_view)
qed

end

setup \<open>Sign.local_path\<close>

end
