(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Aligned_Blocks
  imports
    Word_Lib.Word_Lib_Sumo
    Misc.WordAdditional
begin

section\<open>Decomposing address ranges into aligned blocks\<close>

lemma word_ctz_is_aligned:
  shows \<open>is_aligned l (word_ctz l)\<close>
proof -
  have \<open>\<And>n. n < word_ctz l \<Longrightarrow> \<not> (l !! n)\<close>
    by (clarsimp simp add: word_ctz_unfold', blast)
  then show ?thesis
    using is_aligned_nth by auto
qed

lemma word_ctz_is_aligned':
  assumes \<open>is_aligned l n\<close> \<open>n \<le> size l\<close>
  shows \<open>n \<le> word_ctz l\<close>
  using assms
  unfolding is_aligned_nth word_ctz_unfold' le_def
  by (metis Min.insert Min.singleton Min_in finite_bit_word
      mem_Collect_eq min_def word_size)

lemma word_log2_pow2_le:
  assumes \<open>l > 0\<close>
  shows \<open>2 ^ word_log2 l \<le> l\<close>
proof -
  have \<open>word_log2 l = Max {n. l !! n}\<close>
    using assms word_log2_unfold[of l] by clarsimp
  moreover have \<open>l !! Max {n. l !! n}\<close>
    using assms word_exists_nth[of l]
    by (metis bit_word_log2 word_gt_0 word_log2_unfold)
  ultimately show ?thesis
    using assms bang_is_le[of l] by clarsimp
qed

definition next_aligned_block_size ::
    \<open>64 word \<Rightarrow> 64 word \<Rightarrow> nat\<close>
  where
    \<open>next_aligned_block_size addr len \<equiv>
       min (word_ctz addr) (word_log2 len)\<close>

lemma next_aligned_block_size_le:
  fixes len :: \<open>64 word\<close>
  assumes \<open>len > 0\<close>
  shows \<open>2 ^ next_aligned_block_size addr len \<le> len\<close>
proof -
  have
    \<open>next_aligned_block_size addr len \<le> word_log2 len\<close>
    by (simp add: next_aligned_block_size_def)
  then show ?thesis
    using word_log2_pow2_le[OF assms]
    unfolding next_aligned_block_size_def
    by (metis (no_types, opaque_lifting) order_trans
        two_power_increasing word_log2_max word_size)
qed

lemma next_aligned_block_size_gt0:
  fixes len :: \<open>64 word\<close>
  assumes \<open>len > 0\<close>
  shows \<open>2 ^ next_aligned_block_size addr len > (0 :: 64 word)\<close>
  using assms
  unfolding next_aligned_block_size_def
  by (metis min.strict_coboundedI2 p2_gt_0 word_log2_max wsst_TYs(3))

lemma next_aligned_block_size_shrink:
  fixes len :: \<open>64 word\<close>
  assumes \<open>len > 0\<close>
  shows
    \<open>len - 2 ^ next_aligned_block_size addr len < len\<close>
  using next_aligned_block_size_gt0 assms next_aligned_block_size_le
    word_diff_less by blast

lemma next_aligned_block_is_aligned:
  \<open>is_aligned addr (next_aligned_block_size addr len)\<close>
  unfolding next_aligned_block_size_def
  using word_ctz_is_aligned is_aligned_weaken min.cobounded1
  by blast

function range_to_aligned_blocks ::
    \<open>64 word \<Rightarrow> 64 word \<Rightarrow> (64 word \<times> nat) list\<close>
  where
    \<open>range_to_aligned_blocks addr len =
       (if len > 0 then
          let n = next_aligned_block_size addr len
          in (addr, n) #
             range_to_aligned_blocks
               (addr + 2 ^ n) (len - 2 ^ n)
        else [])\<close>
  by pat_completeness auto
termination
  apply (relation \<open>measure (unat \<circ> snd)\<close>, force)
  by (simp add: unat_mono next_aligned_block_size_shrink comp_def)

declare range_to_aligned_blocks.simps[simp del]

lemma range_to_aligned_blocks_induct:
  assumes
    \<open>\<And>addr len. len = 0 \<Longrightarrow> P addr len []\<close>
    \<open>\<And>addr len blocks.
       0 < len \<Longrightarrow>
       blocks =
         range_to_aligned_blocks
           (addr + 2 ^ next_aligned_block_size addr len)
           (len - 2 ^ next_aligned_block_size addr len) \<Longrightarrow>
       P (addr + 2 ^ next_aligned_block_size addr len)
         (len - 2 ^ next_aligned_block_size addr len)
         blocks \<Longrightarrow>
       P addr len
         ((addr, next_aligned_block_size addr len) # blocks)\<close>
  shows
    \<open>P addr len (range_to_aligned_blocks addr len)\<close>
proof (induction addr len rule: range_to_aligned_blocks.induct)
  case (1 addr len)
  then show ?case
    by (metis assms range_to_aligned_blocks.simps word_gt_0)
qed

lemma range_to_aligned_blocks_aligned:
  assumes
    \<open>(addr', n) \<in> set (range_to_aligned_blocks addr len)\<close>
  shows \<open>is_aligned addr' n\<close>
  using assms
  by (induction addr len rule: range_to_aligned_blocks_induct)
     (auto simp add: Let_def next_aligned_block_is_aligned)

end
