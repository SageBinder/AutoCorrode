theory C_Arithmetic_Rules
  imports
    C_Numeric_Types
    "Shallow_Separation_Logic.Weakest_Precondition"
begin

section \<open>WP Rules for C Arithmetic Operations\<close>

context sepalg
begin

text \<open>
  We provide weakest-precondition rules for the overflow-checked C arithmetic
  operations defined in @{theory "Shallow_Micro_C.C_Numeric_Types"}.  Each
  operation has:
  \<^enum> A simp rule tagged @{text "[separation_logic_wp_simps]"} giving the equational WP.
  \<^enum> An intro rule tagged @{text "[separation_logic_wp_intros]"} that assumes
    no overflow, suitable for use by Crush.

  The intro rules follow the pattern of @{thm wp_literalI}: they do not
  require @{const ucincl} and instead reduce to @{thm wp_literalI} in the
  success case.
\<close>

subsection \<open>Overflow Condition Abbreviation\<close>

abbreviation c_signed_in_range :: \<open>int \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>c_signed_in_range v l \<equiv> -(2^(l - 1)) \<le> v \<and> v < 2^(l - 1)\<close>

subsection \<open>Addition\<close>

lemma wp_c_signed_add_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_add_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (let result_int = sint a + sint b
       in if result_int < -(2^(LENGTH('l) - 1)) \<or>
             result_int \<ge> 2^(LENGTH('l) - 1)
          then \<W>\<P> \<Gamma> (abort_handler SignedOverflow) \<psi> \<rho> \<theta>
          else \<psi> (word_of_int result_int))\<close>
using assms by (simp add: c_signed_add_with_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_add [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_add a b) \<psi> \<rho> \<theta> =
             (if c_signed_in_range (sint a + sint b) LENGTH('l) then
                \<psi> (word_of_int (sint a + sint b))
              else
                \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (auto simp add: c_signed_add_def c_signed_overflow_def c_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_addI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>c_signed_in_range (sint a + sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a + sint b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_add a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_add a b = literal (word_of_int (sint a + sint b))\<close>
    by (simp add: c_signed_add_def c_signed_overflow_def Let_def)
  from assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Subtraction\<close>

lemma wp_c_signed_sub_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_sub_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (let result_int = sint a - sint b
       in if result_int < -(2^(LENGTH('l) - 1)) \<or>
             result_int \<ge> 2^(LENGTH('l) - 1)
          then \<W>\<P> \<Gamma> (abort_handler SignedOverflow) \<psi> \<rho> \<theta>
          else \<psi> (word_of_int result_int))\<close>
using assms by (simp add: c_signed_sub_with_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_sub [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_sub a b) \<psi> \<rho> \<theta> =
            (if c_signed_in_range (sint a - sint b) LENGTH('l) then
               \<psi> (word_of_int (sint a - sint b))
             else
               \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (simp add: c_signed_sub_def c_signed_overflow_def c_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_subI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>c_signed_in_range (sint a - sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a - sint b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_sub a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_sub a b = literal (word_of_int (sint a - sint b))\<close>
    by (simp add: c_signed_sub_def c_signed_overflow_def Let_def)
  from assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Multiplication\<close>

lemma wp_c_signed_mul_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_mul_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (let result_int = sint a * sint b
       in if result_int < -(2^(LENGTH('l) - 1)) \<or>
             result_int \<ge> 2^(LENGTH('l) - 1)
          then \<W>\<P> \<Gamma> (abort_handler SignedOverflow) \<psi> \<rho> \<theta>
          else \<psi> (word_of_int result_int))\<close>
using assms by (simp add: c_signed_mul_with_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_mul [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_mul a b) \<psi> \<rho> \<theta> =
             (if c_signed_in_range (sint a * sint b) LENGTH('l) then
                \<psi> (word_of_int (sint a * sint b))
              else
                \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (simp add: c_signed_mul_def c_signed_overflow_def c_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_mulI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>c_signed_in_range (sint a * sint b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a * sint b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_mul a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_mul a b = literal (word_of_int (sint a * sint b))\<close>
    by (simp add: c_signed_mul_def c_signed_overflow_def Let_def)
  from assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Division\<close>

lemma wp_c_signed_div_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_div_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if b = 0 then
         \<W>\<P> \<Gamma> (abort_handler DivisionByZero) \<psi> \<rho> \<theta>
       else
         let result_int = c_trunc_div_int (sint a) (sint b)
         in if result_int < -(2^(LENGTH('l) - 1)) \<or>
               result_int \<ge> 2^(LENGTH('l) - 1)
            then \<W>\<P> \<Gamma> (abort_handler SignedOverflow) \<psi> \<rho> \<theta>
            else \<psi> (word_of_int result_int))\<close>
using assms by (simp add: c_signed_div_with_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_div [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_div a b) \<psi> \<rho> \<theta> =
             (if b = 0 then
                \<theta> (CustomAbort DivisionByZero)
              else if c_signed_in_range (c_trunc_div_int (sint a) (sint b)) LENGTH('l) then
                \<psi> (word_of_int (c_trunc_div_int (sint a) (sint b)))
              else
                \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (simp add: c_signed_div_def c_signed_overflow_def c_abort_def c_division_by_zero_def
  Let_def separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_divI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>b \<noteq> 0\<close>
      and \<open>c_signed_in_range (c_trunc_div_int (sint a) (sint b)) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (c_trunc_div_int (sint a) (sint b)))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_div a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_div a b = literal (word_of_int (c_trunc_div_int (sint a) (sint b)))\<close>
    by (simp add: c_signed_div_def c_signed_overflow_def c_division_by_zero_def Let_def)
  from assms this show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Modulo\<close>

lemma wp_c_signed_mod_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_mod_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if b = 0 then
         \<W>\<P> \<Gamma> (abort_handler DivisionByZero) \<psi> \<rho> \<theta>
       else
         let q_int = c_trunc_div_int (sint a) (sint b);
             result_int = c_trunc_mod_int (sint a) (sint b)
         in if q_int < -(2^(LENGTH('l) - 1)) \<or>
               q_int \<ge> 2^(LENGTH('l) - 1)
            then \<W>\<P> \<Gamma> (abort_handler SignedOverflow) \<psi> \<rho> \<theta>
            else \<psi> (word_of_int result_int))\<close>
using assms by (simp add: c_signed_mod_with_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_mod [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_mod a b) \<psi> \<rho> \<theta> =
            (if b = 0 then
               \<theta> (CustomAbort DivisionByZero)
             else if c_signed_in_range (c_trunc_div_int (sint a) (sint b)) LENGTH('l) then
               \<psi> (word_of_int (c_trunc_mod_int (sint a) (sint b)))
             else
               \<theta> (CustomAbort SignedOverflow))\<close>
using assms by (simp add: c_signed_mod_def c_signed_overflow_def c_abort_def
  c_division_by_zero_def Let_def separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_modI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>b \<noteq> 0\<close>
      and \<open>c_signed_in_range (c_trunc_div_int (sint a) (sint b)) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (c_trunc_mod_int (sint a) (sint b)))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_mod a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_mod a b = literal (word_of_int (c_trunc_mod_int (sint a) (sint b)))\<close>
    by (simp add: c_signed_mod_def c_signed_overflow_def c_division_by_zero_def Let_def)
  from this assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Comparison operations\<close>

text \<open>Comparisons never overflow --- they always succeed.\<close>

lemma wp_c_signed_less [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_less a b) \<psi> \<rho> \<theta> = \<psi> (sint a < sint b)\<close>
using assms by (simp add: c_signed_less_def separation_logic_wp_simps)

lemma wp_c_signed_lessI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (sint a < sint b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_less a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_less_def wp_literalI asepconj_simp)

lemma wp_c_signed_le [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_le a b) \<psi> \<rho> \<theta> = \<psi> (sint a \<le> sint b)\<close>
using assms by (simp add: c_signed_le_def separation_logic_wp_simps)

lemma wp_c_signed_leI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (sint a \<le> sint b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_le a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_le_def wp_literalI asepconj_simp)

lemma wp_c_signed_eq [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_eq a b) \<psi> \<rho> \<theta> = \<psi> (a = b)\<close>
using assms by (simp add: c_signed_eq_def separation_logic_wp_simps)

lemma wp_c_signed_eqI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a = b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_eq a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_eq_def wp_literalI asepconj_simp)

lemma wp_c_signed_neq [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_neq a b) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> b)\<close>
using assms by (simp add: c_signed_neq_def separation_logic_wp_simps)

lemma wp_c_signed_neqI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_neq a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_neq_def wp_literalI asepconj_simp)

subsection \<open>Unsigned addition\<close>

lemma wp_c_unsigned_add [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_add a b) \<psi> \<rho> \<theta> = \<psi> (a + b)\<close>
using assms by (simp add: c_unsigned_add_def separation_logic_wp_simps)

lemma wp_c_unsigned_addI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a + b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_add a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_add_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Subtraction\<close>

lemma wp_c_unsigned_sub [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_sub a b) \<psi> \<rho> \<theta> = \<psi> (a - b)\<close>
using assms by (simp add: c_unsigned_sub_def separation_logic_wp_simps)

lemma wp_c_unsigned_subI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a - b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_sub a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_sub_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Multiplication\<close>

lemma wp_c_unsigned_mul [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_mul a b) \<psi> \<rho> \<theta> = \<psi> (a * b)\<close>
using assms by (simp add: c_unsigned_mul_def separation_logic_wp_simps)

lemma wp_c_unsigned_mulI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a * b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_mul a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_mul_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Comparison Operations\<close>

lemma wp_c_unsigned_less [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_less a b) \<psi> \<rho> \<theta> = \<psi> (a < b)\<close>
using assms by (simp add: c_unsigned_less_def separation_logic_wp_simps)

lemma wp_c_unsigned_lessI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a < b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_less a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_less_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_le [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_le a b) \<psi> \<rho> \<theta> = \<psi> (a \<le> b)\<close>
using assms by (simp add: c_unsigned_le_def separation_logic_wp_simps)

lemma wp_c_unsigned_leI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<le> b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_le a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_le_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_eq [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_eq a b) \<psi> \<rho> \<theta> = \<psi> (a = b)\<close>
using assms by (simp add: c_unsigned_eq_def separation_logic_wp_simps)

lemma wp_c_unsigned_eqI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a = b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_eq a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_eq_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_neq [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_neq a b) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> b)\<close>
using assms by (simp add: c_unsigned_neq_def separation_logic_wp_simps)

lemma wp_c_unsigned_neqI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_neq a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_neq_def wp_literalI asepconj_simp)

subsection \<open>C Truthiness\<close>

lemma wp_c_signed_truthy [separation_logic_wp_simps]:
    fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_truthy a) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> 0)\<close>
using assms by (simp add: c_signed_truthy_def separation_logic_wp_simps)

lemma wp_c_signed_truthyI [separation_logic_wp_intros]:
    fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> 0)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_truthy a) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_truthy_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_truthy [separation_logic_wp_simps]:
    fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_truthy a) \<psi> \<rho> \<theta> = \<psi> (a \<noteq> 0)\<close>
using assms by (simp add: c_unsigned_truthy_def separation_logic_wp_simps)

lemma wp_c_unsigned_truthyI [separation_logic_wp_intros]:
    fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a \<noteq> 0)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_truthy a) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_truthy_def wp_literalI asepconj_simp)

subsection \<open>Signed bitwise operations\<close>

lemma wp_c_signed_and [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_and a b) \<psi> \<rho> \<theta> = \<psi> (a AND b)\<close>
using assms by (simp add: c_signed_and_def separation_logic_wp_simps)

lemma wp_c_signed_andI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a AND b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_and a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_and_def wp_literalI asepconj_simp)

lemma wp_c_signed_or [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_or a b) \<psi> \<rho> \<theta> = \<psi> (a OR b)\<close>
using assms by (simp add: c_signed_or_def separation_logic_wp_simps)

lemma wp_c_signed_orI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a OR b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_or a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_or_def wp_literalI asepconj_simp)

lemma wp_c_signed_xor [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_xor a b) \<psi> \<rho> \<theta> = \<psi> (a XOR b)\<close>
using assms by (simp add: c_signed_xor_def separation_logic_wp_simps)

lemma wp_c_signed_xorI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a XOR b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_xor a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_xor_def wp_literalI asepconj_simp)

lemma wp_c_signed_not [separation_logic_wp_simps]:
    fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_not a) \<psi> \<rho> \<theta> = \<psi> (NOT a)\<close>
using assms by (simp add: c_signed_not_def separation_logic_wp_simps)

lemma wp_c_signed_notI [separation_logic_wp_intros]:
    fixes a :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (NOT a)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_not a) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_signed_not_def wp_literalI asepconj_simp)

subsection \<open>Unsigned bitwise operations\<close>

lemma wp_c_unsigned_and [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_and a b) \<psi> \<rho> \<theta> = \<psi> (a AND b)\<close>
using assms by (simp add: c_unsigned_and_def separation_logic_wp_simps asepconj_simp)

lemma wp_c_unsigned_andI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a AND b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_and a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_and_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_or [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_or a b) \<psi> \<rho> \<theta> = \<psi> (a OR b)\<close>
using assms by (simp add: c_unsigned_or_def separation_logic_wp_simps)

lemma wp_c_unsigned_orI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a OR b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_or a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_or_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_xor [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_xor a b) \<psi> \<rho> \<theta> = \<psi> (a XOR b)\<close>
using assms by (simp add: c_unsigned_xor_def separation_logic_wp_simps)

lemma wp_c_unsigned_xorI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (a XOR b)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_xor a b) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_xor_def wp_literalI asepconj_simp)

lemma wp_c_unsigned_not [separation_logic_wp_simps]:
    fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_not a) \<psi> \<rho> \<theta> = \<psi> (NOT a)\<close>
using assms by (simp add: c_unsigned_not_def separation_logic_wp_simps)

lemma wp_c_unsigned_notI [separation_logic_wp_intros]:
    fixes a :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (NOT a)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_not a) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_unsigned_not_def wp_literalI asepconj_simp)

subsection \<open>Unsigned Shift Operations\<close>

lemma wp_c_unsigned_shl_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_shl_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if unat b \<ge> LENGTH('l) then
         \<W>\<P> \<Gamma> (abort_handler ShiftOutOfRange) \<psi> \<rho> \<theta>
       else \<psi> (push_bit (unat b) a))\<close>
using assms by (simp add: c_unsigned_shl_with_abort_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_unsigned_shl [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_shl a b) \<psi> \<rho> \<theta> =
            (if unat b < LENGTH('l) then
               \<psi> (push_bit (unat b) a)
             else
               \<theta> (CustomAbort ShiftOutOfRange))\<close>
using assms by (simp add: c_unsigned_shl_def c_shift_out_of_range_def c_abort_def separation_logic_wp_simps
  asepconj_simp)

lemma wp_c_unsigned_shlI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (push_bit (unat b) a)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_shl a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_unsigned_shl a b = literal (push_bit (unat b) a)\<close>
    by (simp add: c_unsigned_shl_def)
  from this assms show ?thesis
    unfolding eq using assms by (auto intro: wp_literalI simp add: asepconj_simp)
qed

lemma wp_c_unsigned_shr [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_shr a b) \<psi> \<rho> \<theta> =
             (if unat b < LENGTH('l) then
                \<psi> (drop_bit (unat b) a)
              else \<theta> (CustomAbort ShiftOutOfRange))\<close>
using assms by (simp add: c_unsigned_shr_def c_shift_out_of_range_def c_abort_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_unsigned_shr_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_shr_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if unat b \<ge> LENGTH('l) then
         \<W>\<P> \<Gamma> (abort_handler ShiftOutOfRange) \<psi> \<rho> \<theta>
       else \<psi> (drop_bit (unat b) a))\<close>
using assms by (simp add: c_unsigned_shr_with_abort_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_unsigned_shrI [separation_logic_wp_intros]:
  fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (drop_bit (unat b) a)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_unsigned_shr a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_unsigned_shr a b = literal (drop_bit (unat b) a)\<close>
    by (simp add: c_unsigned_shr_def)
  from this assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Signed shift operations\<close>

lemma wp_c_signed_shl_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_shl_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if unat b \<ge> LENGTH('l) then
         \<W>\<P> \<Gamma> (abort_handler ShiftOutOfRange) \<psi> \<rho> \<theta>
       else
         let result_int = sint a * 2 ^ unat b
         in if sint a < 0 \<or>
               result_int < -(2^(LENGTH('l) - 1)) \<or>
               result_int \<ge> 2^(LENGTH('l) - 1)
            then \<W>\<P> \<Gamma> (abort_handler SignedOverflow) \<psi> \<rho> \<theta>
            else \<psi> (word_of_int result_int))\<close>
using assms by (simp add: c_signed_shl_with_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_shl [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_shl a b) \<psi> \<rho> \<theta> =
            (if unat b \<ge> LENGTH('l) then
               \<theta> (CustomAbort ShiftOutOfRange)
             else
               let result_int = sint a * 2 ^ unat b in
                 if sint a < 0 \<or> \<not> c_signed_in_range result_int LENGTH('l) then
                   \<theta> (CustomAbort SignedOverflow)
                 else
                   \<psi> (word_of_int result_int))\<close>
using assms by (simp add: c_signed_shl_def c_shift_out_of_range_def c_signed_overflow_def
                c_abort_def Let_def separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_shlI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>sint a \<ge> 0\<close>
      and \<open>c_signed_in_range (sint a * 2 ^ unat b) LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a * 2 ^ unat b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_shl a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_shl a b = literal (word_of_int (sint a * 2 ^ unat b))\<close>
    by (simp add: c_signed_shl_def c_shift_out_of_range_def c_signed_overflow_def Let_def)
  from this assms show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

lemma wp_c_signed_shr [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_shr a b) \<psi> \<rho> \<theta> =
             (if unat b \<ge> LENGTH('l) then
                \<theta> (CustomAbort ShiftOutOfRange)
              else
                \<psi> (word_of_int (sint a div 2 ^ unat b)))\<close>
using assms by (simp add: c_signed_shr_def c_shift_out_of_range_def c_abort_def separation_logic_wp_simps
  asepconj_simp)

lemma wp_c_signed_shr_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_shr_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if unat b \<ge> LENGTH('l) then
         \<W>\<P> \<Gamma> (abort_handler ShiftOutOfRange) \<psi> \<rho> \<theta>
       else \<psi> (word_of_int (sint a div 2 ^ unat b)))\<close>
using assms by (simp add: c_signed_shr_with_abort_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_shrI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a div 2 ^ unat b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_shr a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_shr a b = literal (word_of_int (sint a div 2 ^ unat b))\<close>
    by (simp add: c_signed_shr_def c_shift_out_of_range_def)
  from assms this show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

lemma wp_c_signed_shr_conservative [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_signed_shr_conservative a b) \<psi> \<rho> \<theta> =
             (if unat b \<ge> LENGTH('l) then
                \<theta> (CustomAbort ShiftOutOfRange)
              else if sint a < 0 then
                \<theta> (CustomAbort SignedOverflow)
              else
                \<psi> (word_of_int (sint a div 2 ^ unat b)))\<close>
using assms by (simp add: c_signed_shr_conservative_def c_shift_out_of_range_def
  c_signed_overflow_def c_abort_def separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_shr_conservative_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma>
        (c_signed_shr_conservative_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if unat b \<ge> LENGTH('l) then
         \<W>\<P> \<Gamma> (abort_handler ShiftOutOfRange) \<psi> \<rho> \<theta>
       else if sint a < 0 then
         \<W>\<P> \<Gamma> (abort_handler SignedOverflow) \<psi> \<rho> \<theta>
       else \<psi> (word_of_int (sint a div 2 ^ unat b)))\<close>
using assms by (simp add: c_signed_shr_conservative_with_abort_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_signed_shr_conservativeI [separation_logic_wp_intros]:
    fixes a b :: \<open>'l::{len} sword\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>unat b < LENGTH('l)\<close>
      and \<open>sint a \<ge> 0\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint a div 2 ^ unat b))\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_signed_shr_conservative a b) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have eq: \<open>c_signed_shr_conservative a b = literal (word_of_int (sint a div 2 ^ unat b))\<close>
    by (simp add: c_signed_shr_conservative_def c_shift_out_of_range_def)
  from assms this show ?thesis
    unfolding eq by (auto intro: wp_literalI simp add: asepconj_simp)
qed

subsection \<open>Type cast operations\<close>

lemma wp_c_ucast [separation_logic_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_ucast w) \<psi> \<rho> \<theta> = \<psi> (ucast w)\<close>
using assms by (simp add: c_ucast_def separation_logic_wp_simps)

lemma wp_c_ucastI [separation_logic_wp_intros]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (ucast w)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_ucast w) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_ucast_def wp_literalI asepconj_simp)

lemma wp_c_scast [separation_logic_wp_simps]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_scast w) \<psi> \<rho> \<theta> = \<psi> (scast w)\<close>
using assms by (simp add: c_scast_def separation_logic_wp_simps)

lemma wp_c_scastI [separation_logic_wp_intros]:
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (scast w)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_scast w) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: c_scast_def wp_literalI asepconj_simp)

lemma wp_c_scast_checked [separation_logic_wp_simps]:
    fixes w :: \<open>'l::{len} word\<close>
      and \<psi> :: \<open>'b::{len} word \<Rightarrow> 's::{sepalg} set\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_scast_checked w) \<psi> \<rho> \<theta> =
             (let v = sint w
              in if v < -(2^(LENGTH('b) - 1)) \<or> v \<ge> 2^(LENGTH('b) - 1) then
                   \<theta> (CustomAbort SignedOverflow)
                 else
                   \<psi> (word_of_int v))\<close>
using assms by (simp add: c_scast_checked_def c_signed_overflow_def c_abort_def
  separation_logic_wp_simps asepconj_simp Let_def)

lemma wp_c_scast_checked_with_abort [separation_logic_wp_simps]:
    fixes w :: \<open>'l::{len} word\<close>
      and \<psi> :: \<open>'b::{len} word \<Rightarrow> 's::{sepalg} set\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_scast_checked_with_abort abort_handler w) \<psi> \<rho> \<theta> =
      (let v = sint w
       in if v < -(2^(LENGTH('b) - 1)) \<or> v \<ge> 2^(LENGTH('b) - 1)
          then \<W>\<P> \<Gamma> (abort_handler SignedOverflow) \<psi> \<rho> \<theta>
          else \<psi> (word_of_int v))\<close>
using assms by (simp add: c_scast_checked_with_abort_def Let_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_scast_checkedI [separation_logic_wp_intros]:
    fixes w :: \<open>'l::{len} word\<close>
      and \<psi> :: \<open>'b::{len} word \<Rightarrow> 's::{sepalg} set\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
      and \<open>sint w \<ge> -(2^(LENGTH('b) - 1))\<close>
      and \<open>sint w < 2^(LENGTH('b) - 1)\<close>
      and \<open>\<phi> \<longlongrightarrow> \<psi> (word_of_int (sint w) :: 'b word)\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (c_scast_checked w) \<psi> \<rho> \<theta>\<close>
using assms by (simp add: wp_c_scast_checked)

subsection \<open>Unsigned Division and Modulo\<close>

lemma wp_c_unsigned_div_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_div_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if b = 0 then
         \<W>\<P> \<Gamma> (abort_handler DivisionByZero) \<psi> \<rho> \<theta>
       else \<psi> (a div b))\<close>
using assms by (simp add: c_unsigned_div_with_abort_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_unsigned_div [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_div a b) \<psi> \<rho> \<theta> =
             (if b = 0 then
                \<theta> (CustomAbort DivisionByZero)
              else
                \<psi> (a div b))\<close>
using assms by (simp add: c_unsigned_div_def c_abort_def c_division_by_zero_def separation_logic_wp_simps
  asepconj_simp)

lemma wp_c_unsigned_mod_with_abort [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_mod_with_abort abort_handler a b) \<psi> \<rho> \<theta> =
      (if b = 0 then
         \<W>\<P> \<Gamma> (abort_handler DivisionByZero) \<psi> \<rho> \<theta>
       else \<psi> (a mod b))\<close>
using assms by (simp add: c_unsigned_mod_with_abort_def
  separation_logic_wp_simps asepconj_simp)

lemma wp_c_unsigned_mod [separation_logic_wp_simps]:
    fixes a b :: \<open>'l::{len} word\<close>
  assumes \<open>\<And>r. ucincl (\<psi> r)\<close>
      and \<open>\<And>r. ucincl (\<theta> r)\<close>
    shows \<open>\<W>\<P> \<Gamma> (c_unsigned_mod a b) \<psi> \<rho> \<theta> =
             (if b = 0 then
                \<theta> (CustomAbort DivisionByZero)
              else
                \<psi> (a mod b))\<close>
using assms by (simp add: c_unsigned_mod_def c_abort_def c_division_by_zero_def separation_logic_wp_simps
  asepconj_simp)

section \<open>C Integer Promotion Lemmas\<close>

text \<open>
  C11 integer promotion widens sub-int types before arithmetic. These
  lemmas show that the widen-operate-narrow roundtrip equals direct
  operation, and that 32-bit signed overflow cannot occur for promoted
  16-bit operands.
\<close>

subsection \<open>Signed 16 to 32 promotion roundtrip\<close>

lemma scast_scast_add_roundtrip_16_32 [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>SCAST(32 signed \<rightarrow> 16 signed) (SCAST(16 signed \<rightarrow> 32 signed) a + SCAST(16 signed \<rightarrow> 32 signed) b) = a + b\<close>
by (simp add: scast_down_add scast_up_scast_id is_up is_down)

lemma scast_scast_sub_roundtrip_16_32 [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>SCAST(32 signed \<rightarrow> 16 signed) (SCAST(16 signed \<rightarrow> 32 signed) a - SCAST(16 signed \<rightarrow> 32 signed) b) = a - b\<close>
by (simp add: scast_down_minus scast_up_scast_id is_up is_down)

subsection \<open>32-bit signed overflow bounds for promoted 16-bit signed values\<close>

lemma sint_scast_16_32_add_upper [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) + sint (SCAST(16 signed \<rightarrow> 32 signed) b) < 2147483648\<close>
proof -
  have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) b) = sint b\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint a \<ge> -32768 \<and> sint a \<le> 32767\<close>
    using sint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>sint b \<ge> -32768 \<and> sint b \<le> 32767\<close>
    using sint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

lemma sint_scast_16_32_add_lower [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>- 2147483648 \<le> sint (SCAST(16 signed \<rightarrow> 32 signed) a) + sint (SCAST(16 signed \<rightarrow> 32 signed) b)\<close>
proof -
  have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) b) = sint b\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint a \<ge> -32768\<close>
    using sint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>sint b \<ge> -32768\<close>
    using sint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

lemma sint_scast_16_32_sub_upper [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) - sint (SCAST(16 signed \<rightarrow> 32 signed) b) < 2147483648\<close>
proof -
  have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) b) = sint b\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint a \<le> 32767\<close>
    using sint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>sint b \<ge> -32768\<close>
    using sint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

lemma sint_scast_16_32_sub_lower [simp]:
  fixes a b :: \<open>16 sword\<close>
  shows \<open>- 2147483648 \<le> sint (SCAST(16 signed \<rightarrow> 32 signed) a) - sint (SCAST(16 signed \<rightarrow> 32 signed) b)\<close>
proof -
  have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) a) = sint a\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint (SCAST(16 signed \<rightarrow> 32 signed) b) = sint b\<close>
    by (simp add: sint_up_scast is_up)
  moreover have \<open>sint a \<ge> -32768\<close>
    using sint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>sint b \<le> 32767\<close>
    using sint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

subsection \<open>Unsigned 16 to signed 32 promotion roundtrip\<close>

lemma scast_ucast_roundtrip_16_32:
  fixes a :: \<open>16 word\<close>
  shows \<open>SCAST(32 signed \<rightarrow> 16) (UCAST(16 \<rightarrow> 32 signed) a) = a\<close>
by (simp add: scast_def sint_ucast_eq_uint is_down word_of_int_uint)

lemma scast_ucast_add_roundtrip_16_32 [simp]:
  fixes a b :: \<open>16 word\<close>
  shows \<open>SCAST(32 signed \<rightarrow> 16) (UCAST(16 \<rightarrow> 32 signed) a + UCAST(16 \<rightarrow> 32 signed) b) = a + b\<close>
by (simp add: scast_down_add is_down scast_ucast_roundtrip_16_32)

lemma sint_ucast_16_32_add_upper [simp]:
  fixes a b :: \<open>16 word\<close>
  shows \<open>sint (UCAST(16 \<rightarrow> 32 signed) a) + sint (UCAST(16 \<rightarrow> 32 signed) b) < 2147483648\<close>
proof -
  have \<open>sint (UCAST(16 \<rightarrow> 32 signed) a) = uint a\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  moreover have \<open>sint (UCAST(16 \<rightarrow> 32 signed) b) = uint b\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  moreover have \<open>uint a < 65536\<close>
    using uint_range_size[where w=a] by (simp add: word_size)
  moreover have \<open>uint b < 65536\<close>
    using uint_range_size[where w=b] by (simp add: word_size)
  ultimately show ?thesis
    by linarith
qed

lemma sint_ucast_16_32_add_lower [simp]:
  fixes a b :: \<open>16 word\<close>
  shows \<open>- 2147483648 \<le> sint (UCAST(16 \<rightarrow> 32 signed) a) + sint (UCAST(16 \<rightarrow> 32 signed) b)\<close>
proof -
  have \<open>sint (UCAST(16 \<rightarrow> 32 signed) a) = uint a\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  moreover have \<open>sint (UCAST(16 \<rightarrow> 32 signed) b) = uint b\<close>
    by (simp add: sint_ucast_eq_uint is_down)
  moreover have \<open>uint a \<ge> 0\<close>
    by simp
  moreover have \<open>uint b \<ge> 0\<close>
    by simp
  ultimately show ?thesis
    by linarith
qed

end

end
