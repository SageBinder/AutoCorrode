(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Byte_Trie
  imports
    Aligned_Blocks
begin

section\<open>Compressed tries of bytes\<close>

text\<open>A byte leaf represents a uniform block. A branch divides a block by
the next address bit. The block height is supplied to lookup and update
operations, so uniform regions remain compact.\<close>

datatype byte_trie =
    Byte_Branch byte_trie byte_trie
  | Uniform_Byte \<open>8 word\<close>

fun byte_trie_left :: \<open>byte_trie \<Rightarrow> byte_trie\<close>
  where
    \<open>byte_trie_left (Byte_Branch left right) = left\<close>
  | \<open>byte_trie_left (Uniform_Byte byte) = Uniform_Byte byte\<close>

fun byte_trie_right :: \<open>byte_trie \<Rightarrow> byte_trie\<close>
  where
    \<open>byte_trie_right (Byte_Branch left right) = right\<close>
  | \<open>byte_trie_right (Uniform_Byte byte) = Uniform_Byte byte\<close>

fun byte_trie_height :: \<open>byte_trie \<Rightarrow> nat\<close>
  where
    \<open>byte_trie_height (Uniform_Byte _) = 0\<close>
  | \<open>byte_trie_height (Byte_Branch left right) =
       1 + max (byte_trie_height left) (byte_trie_height right)\<close>

fun lookup_byte_trie ::
    \<open>byte_trie \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 8 word\<close>
  where
    \<open>lookup_byte_trie (Uniform_Byte byte) _ _ = byte\<close>
  | \<open>lookup_byte_trie (Byte_Branch _ _) 0 _ = undefined\<close>
  | \<open>lookup_byte_trie (Byte_Branch zero one) (Suc height) addr =
       (if bit addr height
        then lookup_byte_trie one height addr
        else lookup_byte_trie zero height addr)\<close>

fun compact_byte_branch ::
    \<open>byte_trie \<Rightarrow> byte_trie \<Rightarrow> byte_trie\<close>
  where
    \<open>compact_byte_branch (Uniform_Byte left) (Uniform_Byte right) =
       (if left = right
        then Uniform_Byte left
        else Byte_Branch (Uniform_Byte left) (Uniform_Byte right))\<close>
  | \<open>compact_byte_branch left right = Byte_Branch left right\<close>

lemma lookup_compact_byte_branch:
  assumes
    \<open>height > byte_trie_height left\<close>
    \<open>height > byte_trie_height right\<close>
  shows
    \<open>lookup_byte_trie (compact_byte_branch left right) height addr =
     lookup_byte_trie (Byte_Branch left right) height addr\<close>
  using assms
proof (induction left right rule: compact_byte_branch.induct)
  case (1 left right)
  then show ?case by (cases height; simp)
qed auto

fun canonicalize_byte_trie :: \<open>byte_trie \<Rightarrow> byte_trie\<close>
  where
    \<open>canonicalize_byte_trie (Byte_Branch left right) =
       compact_byte_branch
         (canonicalize_byte_trie left)
         (canonicalize_byte_trie right)\<close>
  | \<open>canonicalize_byte_trie (Uniform_Byte byte) = Uniform_Byte byte\<close>

fun write_byte_trie ::
    \<open>byte_trie \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> 8 word \<Rightarrow>
      byte_trie\<close>
  where
    \<open>write_byte_trie _ 0 _ byte = Uniform_Byte byte\<close>
  | \<open>write_byte_trie trie (Suc height) addr byte =
       (if bit addr height
        then compact_byte_branch
               (byte_trie_left trie)
               (write_byte_trie
                 (byte_trie_right trie) height addr byte)
        else compact_byte_branch
               (write_byte_trie
                 (byte_trie_left trie) height addr byte)
               (byte_trie_right trie))\<close>

fun fill_byte_trie_block ::
    \<open>byte_trie \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow> nat \<Rightarrow>
      8 word \<Rightarrow> byte_trie\<close>
  where
    \<open>fill_byte_trie_block trie height addr block_height byte =
       (if height > block_height
        then
          if bit addr (height - 1)
          then compact_byte_branch
                 (byte_trie_left trie)
                 (fill_byte_trie_block
                   (byte_trie_right trie) (height - 1)
                   addr block_height byte)
          else compact_byte_branch
                 (fill_byte_trie_block
                   (byte_trie_left trie) (height - 1)
                   addr block_height byte)
                 (byte_trie_right trie)
        else Uniform_Byte byte)\<close>

declare fill_byte_trie_block.simps[simp del]

definition byte_trie_canonical :: \<open>byte_trie \<Rightarrow> bool\<close>
  where
    \<open>byte_trie_canonical trie \<equiv>
       canonicalize_byte_trie trie = trie\<close>

lemma compact_byte_branch_canonical:
  assumes
    \<open>byte_trie_canonical left\<close>
    \<open>byte_trie_canonical right\<close>
  shows
    \<open>byte_trie_canonical (compact_byte_branch left right)\<close>
  using assms
  unfolding byte_trie_canonical_def
  by (induction left right rule: compact_byte_branch.induct) auto

lemma compact_byte_branch_commute:
  \<open>canonicalize_byte_trie (compact_byte_branch left right) =
   compact_byte_branch
     (canonicalize_byte_trie left)
     (canonicalize_byte_trie right)\<close>
  by (induction left right rule: compact_byte_branch.induct) auto

lemma canonicalize_byte_trie_correct:
  \<open>byte_trie_canonical (canonicalize_byte_trie trie)\<close>
  using compact_byte_branch_canonical
  unfolding byte_trie_canonical_def
  by (induction trie) (auto simp add: compact_byte_branch_commute)

lemma compact_byte_branch_height_le:
  \<open>byte_trie_height (compact_byte_branch left right) \<le>
   byte_trie_height (Byte_Branch left right)\<close>
  by (induction left right rule: compact_byte_branch.induct) auto

lemma write_byte_trie_height_le:
  assumes \<open>byte_trie_height trie \<le> height\<close>
  shows \<open>byte_trie_height (write_byte_trie trie height addr byte) \<le> height\<close>
  using assms
proof (induction trie height addr byte rule: write_byte_trie.induct)
  case (1 x xa byte)
  then show ?case by simp
next
  case (2 trie height addr byte)
  then show ?case
    by (cases trie)
       (auto intro!: order.trans[OF compact_byte_branch_height_le])
qed

end
