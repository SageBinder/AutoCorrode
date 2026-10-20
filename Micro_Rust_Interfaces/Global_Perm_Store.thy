(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

(*<*)
theory Global_Perm_Store
  imports Micro_Rust_Interfaces_Core.References Shallow_Micro_Rust.Global_Store
begin
(*>*)

locale global_perm_store = store: global_store store_read_reference store_write_reference
                              store_allocate_reference
      for store_read_reference :: \<open>'s::{sepalg} \<Rightarrow> 'a \<rightharpoonup> 'b\<close>
      and store_write_reference :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 'b \<rightharpoonup> 's\<close>
      and store_allocate_reference :: \<open>'s \<rightharpoonup> ('a \<times> 's)\<close> +
    fixes store_perm_map :: \<open>'s \<Rightarrow> 'a \<Rightarrow> share\<close>
      and store_alloc_pool :: \<open>'s \<Rightarrow> 'a set\<close>
      and store_has_valid_allocator :: \<open>'s \<Rightarrow> bool\<close>
  assumes store_pool_inf: \<open>\<And>s. store_alloc_pool s = {} \<or> infinite (store_alloc_pool s)\<close>
      and store_alloc_unique: \<open>\<And>s1 s2. s1\<sharp>s2 \<Longrightarrow> store_alloc_pool s1 = {} \<or> store_alloc_pool s2 = {}\<close>
      and read_perm_succeeds: \<open>\<And>s a. store_perm_map s a > 0 \<longleftrightarrow> (\<exists>v. store_read_reference s a = Some v)\<close>
      and write_perm_succeeds: \<open>\<And>s a v. store_perm_map s a = \<top> \<longleftrightarrow> (\<exists>s'. store_write_reference s a v = Some s')\<close>
      and allocate_succeeds : \<open>\<And>s. store_alloc_pool s \<noteq> {} \<longleftrightarrow> (\<exists>a s'. store_allocate_reference s = Some (a,s'))\<close>
      and store_disjoint_perm: \<open>\<And>s1 s2. s1 \<sharp> s2 \<Longrightarrow> (\<forall>a. store_perm_map s1 a \<sharp> store_perm_map s2 a)\<close>
      and store_disjoint_pool: \<open>\<And>s1 s2. s1 \<sharp> s2 \<Longrightarrow> store_alloc_pool s1 \<sharp> store_alloc_pool s2\<close>
      and store_add_perm: \<open>\<And>s1 s2 a. s1 \<sharp> s2 \<Longrightarrow>
            store_perm_map (s1+s2) a = store_perm_map s1 a \<squnion> store_perm_map s2 a\<close>
      and store_add_pool: \<open>\<And>s1 s2. s1 \<sharp> s2 \<Longrightarrow>
            store_alloc_pool (s1 + s2) = store_alloc_pool s1 \<union> store_alloc_pool s2\<close>
      and store_add_read: \<open>\<And>s1 s2 a v. store_read_reference s1 a = Some v \<Longrightarrow> s1 \<sharp> s2 \<Longrightarrow> 
            store_read_reference (s1+s2) a = Some v\<close>
      and store_add_write: \<open>\<And>s1 s1' s2 a v. store_write_reference s1 a v = Some s1' \<Longrightarrow> s1 \<sharp> s2 \<Longrightarrow> 
            store_write_reference (s1+s2) a v = Some (s1'+s2) \<and> s1'\<sharp>s2\<close>
      and store_add_alloc: \<open>\<And>s1 s1' s2 a. s1 \<sharp> s2 \<Longrightarrow> store_allocate_reference s1 = Some (a, s1') \<Longrightarrow>
            store_allocate_reference (s1 + s2) = Some (a, s1' + s2) \<and> s1' \<sharp> s2\<close>
      and store_add_valid_allocator: \<open>\<And>s1 s2. s1\<sharp>s2 \<Longrightarrow> store_has_valid_allocator s1 \<Longrightarrow>
            store_has_valid_allocator (s1 + s2)\<close>
      and store_write_valid_allocator: \<open>\<And>s a v s'. store_has_valid_allocator s \<Longrightarrow>
            store_write_reference s a v = Some s' \<Longrightarrow> store_has_valid_allocator s'\<close>
      and store_alloc_valid_allocator: \<open>\<And>s a s'. store_has_valid_allocator s \<Longrightarrow>
            store_allocate_reference s = Some (a, s') \<Longrightarrow> store_has_valid_allocator s'\<close>
      and store_write_pool: \<open>\<And>s a v s'. store_write_reference s a v = Some s' \<Longrightarrow>
            store_alloc_pool s = store_alloc_pool s'\<close>
      and store_write_perm_map: \<open>\<And>s a v s'. store_write_reference s a v = Some s' \<Longrightarrow>
            store_perm_map s' = store_perm_map s\<close>
      and allocate_full_share: \<open>\<And>s a s'. store_allocate_reference s = Some (a, s') \<Longrightarrow>
            a \<in> store_alloc_pool s \<and> store_alloc_pool s' = store_alloc_pool s - {a} \<and>
              store_perm_map s' a = \<top>\<close>
      and store_alloc_perm_map: \<open>\<And>s a s'. store_allocate_reference s = Some (a, s') \<Longrightarrow>
            store_perm_map s' = (store_perm_map s)(a := \<top>)\<close>
      and store_split_allocator: \<open>\<And>s. store_has_valid_allocator s \<Longrightarrow> \<exists>s1 s2. s = s1 + s2 \<and>
            s1 \<sharp> s2 \<and> store_has_valid_allocator s1 \<and> store_alloc_pool s1 = store_alloc_pool s \<and>
            store_alloc_pool s2 = {} \<and> (\<forall>a. store_perm_map s1 a = \<bottom>) \<and>
              (\<forall>a. store_perm_map s2 a = store_perm_map s a)\<close>
      and store_split_perm: \<open>\<And>s p1 p2. p1 \<sharp> p2 \<Longrightarrow> store_perm_map s = p1 + p2 \<Longrightarrow>
           \<exists>s1 s2. s1 \<sharp> s2 \<and> s = s1 + s2 \<and> store_perm_map s1 = p1 \<and> store_perm_map s2 = p2\<close>
begin

definition points_to_raw' ::
    \<open>('a, 'b) gref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> 's assert\<close>
  where
  \<comment>\<open>This assertion owns no allocator and no permissions outside
  the referenced address. The requested share remains a lower bound, so the
  assertion fixes the heap support without fixing a larger actual share.\<close>
  \<open>points_to_raw' r sh b \<equiv>
    {s. 0 < sh \<and> sh \<le> store_perm_map s (address r) \<and>
      store_read_reference s (address r) = Some b \<and>
      store_alloc_pool s = {} \<and>
      (\<forall>a. a \<noteq> address r \<longrightarrow> store_perm_map s a = \<bottom>)}\<close>

definition reference_stack ::
    \<open>('b \<Rightarrow> bool) \<Rightarrow> ('a, 'b) gref list \<Rightarrow> 's assert\<close>
  where
  \<comment>\<open>The stack owns the allocator and every previously allocated
  location which is no longer live. Live and future locations are absent from
  the resource; absorbed locations are held at full share and contain an
  admissible value.\<close>
  \<open>reference_stack F \<Phi> \<equiv>
    {s. store_has_valid_allocator s \<and>
      store_alloc_pool s \<noteq> {} \<and>
      distinct (List.map address \<Phi>) \<and>
      (\<forall>r \<in> set \<Phi>. address r \<notin> store_alloc_pool s) \<and>
      (\<forall>a. a \<in> store_alloc_pool s \<or> a \<in> set (List.map address \<Phi>)
        \<longrightarrow> store_perm_map s a = \<bottom>) \<and>
      (\<forall>a. a \<notin> store_alloc_pool s \<longrightarrow>
        a \<notin> set (List.map address \<Phi>) \<longrightarrow>
        (\<exists>v. store_perm_map s a = \<top> \<and>
          store_read_reference s a = Some v \<and> F v))}\<close>

lemma reference_stack_hidden:
  assumes \<open>s \<Turnstile> reference_stack F \<Phi>\<close>
      and \<open>a \<notin> store_alloc_pool s\<close>
      and \<open>a \<notin> set (List.map address \<Phi>)\<close>
    shows \<open>\<exists>v. store_perm_map s a = \<top> \<and>
      store_read_reference s a = Some v \<and> F v\<close>
  using assms
  by (auto simp add: reference_stack_def asat_def)

notation points_to_raw' ("(_) \<mapsto> \<langle>_\<rangle> (_)" [69,0,69]70)

lemma points_to_aentails_rawI [intro]:
  assumes \<open>sh1 \<ge> sh2\<close>
      and \<open>0 < sh2\<close>
      and \<open>g1 = g2\<close>
    shows \<open>r \<mapsto> \<langle>sh1\<rangle> g1 \<longlongrightarrow> r \<mapsto>\<langle>sh2\<rangle> g2\<close>
using assms by (auto simp add: aentails_def points_to_raw'_def asat_def)

lemma points_to_raw'I [intro]:
  assumes \<open>0 < sh\<close>
      and \<open>sh \<le> store_perm_map s (address r)\<close>
      and \<open>store_read_reference s (address r) = Some b\<close>
      and \<open>store_alloc_pool s = {}\<close>
      and \<open>\<And>a. a \<noteq> address r \<Longrightarrow> store_perm_map s a = \<bottom>\<close>
    shows \<open>s \<Turnstile> r \<mapsto>\<langle>sh\<rangle> b\<close>
using assms by (auto simp add: asat_def points_to_raw'_def)

lemma points_to_raw'E [elim]:
  assumes \<open>s \<Turnstile> r \<mapsto>\<langle>sh\<rangle> b\<close>
      and \<open>0 < sh \<Longrightarrow> sh \<le> store_perm_map s (address r) \<Longrightarrow>
              store_read_reference s (address r) = Some b \<Longrightarrow> R\<close>
    shows \<open>R\<close>
using assms by (auto simp add: asat_def points_to_raw'_def)

lemma points_to_raw_write:
  assumes points_to: \<open>s \<Turnstile> points_to_raw' r \<top> g0\<close>
      and write_result: \<open>store_write_reference s (address r) g = Some s'\<close>
    shows \<open>s' \<Turnstile> points_to_raw' r \<top> g\<close>
proof -
  have perm: \<open>store_perm_map s' = store_perm_map s\<close>
    using store_write_perm_map write_result by blast
  have pool: \<open>store_alloc_pool s' = store_alloc_pool s\<close>
    using store_write_pool write_result by blast
  have read: \<open>store_read_reference s' (address r) = Some g\<close>
    using store.write_store_read_store write_result by blast
  show ?thesis
    using points_to perm pool read
    by (auto simp add: points_to_raw'_def asat_def)
qed

lemma points_to_raw_combine':
  shows \<open>r \<mapsto>\<langle>sh1\<rangle> v1 \<star> r \<mapsto>\<langle>sh2\<rangle> v2 \<longlongrightarrow> r \<mapsto>\<langle>sh1+sh2\<rangle> v1 \<star> \<langle>v1 = v2\<rangle>\<close>
proof (rule aentailsI)
  fix x
  assume \<open>x \<Turnstile> r \<mapsto> \<langle>sh1\<rangle> v1 \<star> r \<mapsto> \<langle>sh2\<rangle> v2\<close>
  moreover from this obtain y z where \<open>x = y + z\<close> and \<open>y \<sharp> z\<close> and \<open>y \<Turnstile> r \<mapsto> \<langle>sh1\<rangle> v1\<close> and \<open>z \<Turnstile> r \<mapsto> \<langle>sh2\<rangle> v2\<close>
    by (elim asepconjE)
  moreover from this have \<open>0 < sh1\<close> and \<open>sh1 \<le> store_perm_map y (address r)\<close> and
      \<open>store_read_reference y (address r) = Some v1\<close> and
      \<open>store_alloc_pool y = {}\<close> and
      \<open>\<And>a. a \<noteq> address r \<Longrightarrow> store_perm_map y a = \<bottom>\<close> and
      \<open>0 < sh2\<close> and \<open>sh2 \<le> store_perm_map z (address r)\<close> and
      \<open>store_read_reference z (address r) = Some v2\<close> and
      \<open>store_alloc_pool z = {}\<close> and
      \<open>\<And>a. a \<noteq> address r \<Longrightarrow> store_perm_map z a = \<bottom>\<close>
    by (auto simp add: points_to_raw'_def asat_def)
  moreover from calculation have \<open>0 < sh1 + sh2\<close>
    using less_supI2 plus_share_def by auto
  moreover from calculation have \<open>sh1 + sh2 \<le> store_perm_map x (address r)\<close>
    by (metis plus_share_def store_add_perm sup_mono)
  moreover from calculation have \<open>store_read_reference x (address r) = Some v1\<close>
    using store_add_read by blast
  moreover from calculation have \<open>store_alloc_pool x = {}\<close>
    by (simp add: store_add_pool)
  moreover from calculation have
      \<open>\<And>a. a \<noteq> address r \<Longrightarrow> store_perm_map x a = \<bottom>\<close>
    by (simp add: store_add_perm)
  moreover from calculation have \<open>x \<Turnstile> r \<mapsto> \<langle>sh1 + sh2\<rangle> v1\<close>
    by (auto simp add: points_to_raw'_def asat_def)
  moreover from calculation have \<open>v1 = v2\<close>
    by (metis disjoint_sym option.inject sepalg_comm store_add_read)
  ultimately show \<open>x \<Turnstile> r \<mapsto> \<langle>sh1 + sh2\<rangle> v1 \<star> \<langle>v1 = v2\<rangle>\<close>
    by (simp add: asat_apure_precise_distrib2)
qed

lemma points_to_raw_split1:
  assumes \<open>x \<Turnstile> r \<mapsto>\<langle>sh\<rangle> v\<close>
      and \<open>sh = sh1 + sh2\<close>
      and \<open>sh1 \<sharp> sh2\<close>
      and \<open>0 < sh1\<close>
      and \<open>0 < sh2\<close>
    shows \<open>x \<Turnstile> r \<mapsto>\<langle>sh1\<rangle> v \<star> r \<mapsto>\<langle>sh2\<rangle> v\<close>
proof -
  let ?shr = \<open>store_perm_map x (address r)\<close>
  let ?shr' = \<open>?shr - sh1\<close>
  let ?p1 = \<open>0( address r := sh1)\<close>
  let ?p2 = \<open>(store_perm_map x)( address r := ?shr' )\<close>
  from assms have \<open>0 < sh\<close> and \<open>sh \<le> ?shr\<close> and
      \<open>store_read_reference x (address r) = Some v\<close> and
      \<open>store_alloc_pool x = {}\<close> and
      \<open>\<And>a. a \<noteq> address r \<Longrightarrow> store_perm_map x a = \<bottom>\<close>
    by (auto simp add: points_to_raw'_def asat_def)
  moreover from this and assms have \<open>sh2 \<le> ?shr'\<close>
    by (clarsimp simp add: plus_share_def disjoint_share_def) (metis diff_eq inf_shunt
      inf_sup_aci(1) le_infI)
  moreover from assms have \<open>sh1 \<sharp> ?shr'\<close>
    by (simp add: diff_eq disjoint_share_def)
  moreover from calculation assms have \<open>?shr = sh1 \<squnion> ?shr'\<close>
    by (metis (no_types, lifting) diff_eq inf.absorb1 inf.cobounded2 le_iff_sup le_supE
      plus_share_def shunt2 sup_inf_distrib1)
  moreover from calculation have \<open>?p1 \<sharp> ?p2\<close>
    by (auto simp add: disjoint_fun_def zero_fun_def)
  moreover from calculation and assms  have \<open>store_perm_map x = ?p1 + ?p2\<close>
    by (intro ext) (auto simp add: diff_eq zero_fun_def plus_share_def plus_fun_def zero_share_def)
  moreover from calculation and assms obtain x1 x2 where \<open>x1 \<sharp> x2\<close> and \<open>x = x1 + x2\<close> and
        \<open>store_perm_map x1 = ?p1\<close> and \<open>store_perm_map x2 = ?p2\<close>
    using store_split_perm[of ?p1 ?p2 x] by fast
  moreover from assms and calculation have \<open>store_read_reference x1 (address r) = Some v\<close>
    using read_perm_succeeds store_add_read by (metis fun_upd_same)
  moreover from assms and calculation have \<open>store_read_reference x2 (address r) = Some v\<close>
    using read_perm_succeeds store_add_read by (metis disjoint_sym fun_upd_same inf.absorb_iff2
        less_supI2 sepalg_comm sup_inf_absorb)
  moreover from calculation and assms have
      \<open>store_alloc_pool x1 = {}\<close> and \<open>store_alloc_pool x2 = {}\<close>
    by (auto simp add: store_add_pool)
  moreover from calculation and assms have
      \<open>\<And>a. a \<noteq> address r \<Longrightarrow> store_perm_map x1 a = \<bottom>\<close>
    by (auto simp add: zero_fun_def zero_share_def)
  moreover from calculation and assms have
      \<open>\<And>a. a \<noteq> address r \<Longrightarrow> store_perm_map x2 a = \<bottom>\<close>
    by auto
  moreover from calculation and assms have \<open>x1 \<Turnstile> r\<mapsto>\<langle>sh1\<rangle> v\<close>
    by (intro points_to_raw'I) auto
  moreover from calculation and assms have \<open>x2 \<Turnstile> r\<mapsto>\<langle>sh2\<rangle> v\<close>
    by (intro points_to_raw'I) auto
  ultimately show \<open>x \<Turnstile> r \<mapsto>\<langle>sh1\<rangle> v \<star> r\<mapsto>\<langle>sh2\<rangle> v\<close>
    by (intro asepconjI) auto
qed

lemma points_to_raw_split'':
  assumes \<open>sh = sh1+sh2\<close>
      and \<open>sh1 \<sharp> sh2\<close>
      and \<open>0 < sh1\<close>
      and \<open>0 < sh2\<close>
    shows \<open>r \<mapsto>\<langle>sh\<rangle> v \<longlongrightarrow> r \<mapsto>\<langle>sh1\<rangle> v \<star> r \<mapsto>\<langle>sh2\<rangle> v\<close>
proof (unfold aentails_def, intro allI impI)
  fix x
  assume \<open>x \<Turnstile> r \<mapsto>\<langle>sh\<rangle> v\<close>
  moreover from assms and calculation have \<open>x \<Turnstile> r \<mapsto>\<langle>sh1\<rangle> v \<star> r \<mapsto>\<langle>sh2\<rangle> v\<close>
    by (intro points_to_raw_split1) auto
  ultimately show \<open>x \<Turnstile> r \<mapsto>\<langle>sh1\<rangle> v \<star> r \<mapsto>\<langle>sh2\<rangle> v\<close>
    by (auto intro: asepconjI)
qed

lemma reference_stack_allocates:
  assumes \<open>s \<Turnstile> reference_stack F \<Phi>\<close>
  shows \<open>\<exists>a s'. store_allocate_reference s = Some (a, s')\<close>
  using assms allocate_succeeds
  by (auto simp add: reference_stack_def asat_def)

lemma store_read_split_eq:
  assumes split: \<open>s = x + y\<close>
      and disjoint: \<open>x \<sharp> y\<close>
      and perm: \<open>store_perm_map x = store_perm_map s\<close>
    shows \<open>store_read_reference x = store_read_reference s\<close>
  using assms read_perm_succeeds store_add_read
  by (intro ext; metis option.exhaust)

lemma reference_stack_allocate:
  assumes stack: \<open>s \<Turnstile> reference_stack F \<Phi>\<close>
      and alloc: \<open>store_allocate_reference s = Some (a, s\<^sub>a)\<close>
      and write_result: \<open>store_write_reference s\<^sub>a a g = Some s'\<close>
  shows \<open>s' \<Turnstile>
    points_to_raw' (make_untyped_ref a) \<top> g \<star>
      reference_stack F (\<Phi> @ [make_untyped_ref a])\<close>
proof -
  from stack have
      valid: \<open>store_has_valid_allocator s\<close>
    and pool_nonempty: \<open>store_alloc_pool s \<noteq> {}\<close>
    and distinct: \<open>distinct (List.map address \<Phi>)\<close>
    and live_outside:
      \<open>\<And>r. r \<in> set \<Phi> \<Longrightarrow>
        address r \<notin> store_alloc_pool s\<close>
    and stack_zero:
      \<open>\<And>l. l \<in> store_alloc_pool s \<or>
          l \<in> set (List.map address \<Phi>) \<Longrightarrow>
        store_perm_map s l = \<bottom>\<close>
    and hidden:
      \<open>\<And>l. l \<notin> store_alloc_pool s \<Longrightarrow>
        l \<notin> set (List.map address \<Phi>) \<Longrightarrow>
        \<exists>v. store_perm_map s l = \<top> \<and>
          store_read_reference s l = Some v \<and> F v\<close>
    by (auto simp add: reference_stack_def asat_def)
  obtain allocator heap where
      s_split: \<open>s = allocator + heap\<close>
    and allocator_heap: \<open>allocator \<sharp> heap\<close>
    and allocator_valid: \<open>store_has_valid_allocator allocator\<close>
    and allocator_pool:
      \<open>store_alloc_pool allocator = store_alloc_pool s\<close>
    and heap_pool: \<open>store_alloc_pool heap = {}\<close>
    and allocator_zero:
      \<open>\<And>l. store_perm_map allocator l = \<bottom>\<close>
    and heap_perm:
      \<open>\<And>l. store_perm_map heap l = store_perm_map s l\<close>
    using store_split_allocator[OF valid] by blast
  have heap_perm_eq:
      \<open>store_perm_map heap = store_perm_map s\<close>
    using heap_perm by blast
  have heap_read_eq:
      \<open>store_read_reference heap = store_read_reference s\<close>
    by (rule store_read_split_eq[
          where s=s and x=heap and y=allocator])
      (use s_split allocator_heap heap_perm_eq in auto)
  obtain allocated allocator_alloc where allocator_alloc:
      \<open>store_allocate_reference allocator =
        Some (allocated, allocator_alloc)\<close>
    using allocate_succeeds allocator_pool pool_nonempty by blast
  have framed_alloc:
      \<open>store_allocate_reference s =
          Some (allocated, allocator_alloc + heap)\<close>
    and allocator_alloc_heap: \<open>allocator_alloc \<sharp> heap\<close>
    using store_add_alloc[OF allocator_heap allocator_alloc] s_split
    by auto
  have allocated: \<open>allocated = a\<close>
    and s\<^sub>a: \<open>s\<^sub>a = allocator_alloc + heap\<close>
    using alloc framed_alloc by auto
  have allocator_alloc':
      \<open>store_allocate_reference allocator =
        Some (a, allocator_alloc)\<close>
    using allocator_alloc allocated by simp
  let ?cell_perm = \<open>0(a := \<top>)\<close>
  have allocator_alloc_perm:
      \<open>store_perm_map allocator_alloc = ?cell_perm\<close>
    using store_alloc_perm_map[OF allocator_alloc'] allocator_zero
    by (intro ext) (simp add: zero_fun_def zero_share_def)
  have allocator_alloc_valid:
      \<open>store_has_valid_allocator allocator_alloc\<close>
    using allocator_valid allocator_alloc' store_alloc_valid_allocator
    by blast
  have allocator_alloc_top:
      \<open>store_perm_map allocator_alloc a = \<top>\<close>
    using allocator_alloc_perm by simp
  obtain allocator_written where allocator_write:
      \<open>store_write_reference allocator_alloc a g =
        Some allocator_written\<close>
    using allocator_alloc_top write_perm_succeeds by blast
  have framed_write:
      \<open>store_write_reference s\<^sub>a a g =
        Some (allocator_written + heap)\<close>
    and allocator_written_heap: \<open>allocator_written \<sharp> heap\<close>
    using store_add_write[OF allocator_write allocator_alloc_heap] s\<^sub>a
    by auto
  have s': \<open>s' = allocator_written + heap\<close>
    using write_result framed_write by simp
  have allocator_written_valid:
      \<open>store_has_valid_allocator allocator_written\<close>
    using allocator_alloc_valid allocator_write
      store_write_valid_allocator by blast
  have allocator_written_perm:
      \<open>store_perm_map allocator_written = ?cell_perm\<close>
    using store_write_perm_map[OF allocator_write]
      allocator_alloc_perm by simp
  obtain stack_allocator cell where
      written_split: \<open>allocator_written = stack_allocator + cell\<close>
    and stack_cell: \<open>stack_allocator \<sharp> cell\<close>
    and stack_allocator_valid:
      \<open>store_has_valid_allocator stack_allocator\<close>
    and stack_allocator_pool:
      \<open>store_alloc_pool stack_allocator =
        store_alloc_pool allocator_written\<close>
    and cell_pool: \<open>store_alloc_pool cell = {}\<close>
    and stack_allocator_zero:
      \<open>\<And>l. store_perm_map stack_allocator l = \<bottom>\<close>
    and cell_perm:
      \<open>\<And>l. store_perm_map cell l =
        store_perm_map allocator_written l\<close>
    using store_split_allocator[OF allocator_written_valid] by blast
  have triple_apart: \<open>stack_allocator + cell \<sharp> heap\<close>
    using allocator_written_heap written_split by simp
  have cell_residual:
      \<open>cell \<sharp> stack_allocator + heap\<close>
    and rotate:
      \<open>(stack_allocator + cell) + heap =
        cell + (stack_allocator + heap)\<close>
    using stack_cell triple_apart
    by (metis disjoint_sym sepalg_apart_assoc sepalg_apart_plus
          sepalg_apart_plus2 sepalg_assoc sepalg_comm)+
  have state_split:
      \<open>s' = cell + (stack_allocator + heap)\<close>
    using s' written_split rotate by simp
  have stack_allocator_heap: \<open>stack_allocator \<sharp> heap\<close>
  proof -
    have \<open>heap \<sharp> stack_allocator\<close>
      by (rule sepalg_apart_plus2[
            where x=heap and y=stack_allocator and z=cell])
        (use triple_apart stack_cell in auto)
    then show ?thesis by simp
  qed
  have cell_map: \<open>store_perm_map cell = ?cell_perm\<close>
    using cell_perm allocator_written_perm by auto
  have cell_read_eq:
      \<open>store_read_reference cell =
        store_read_reference allocator_written\<close>
    by (rule store_read_split_eq[
          where s=allocator_written and x=cell and y=stack_allocator])
      (use written_split stack_cell cell_perm in auto)
  have cell_read: \<open>store_read_reference cell a = Some g\<close>
    using cell_read_eq allocator_write store.write_store_read_store
    by simp
  have cell_points_to:
      \<open>cell \<Turnstile> points_to_raw'
        (make_untyped_ref a) \<top> g\<close>
    using cell_pool cell_map cell_read shares_nontrivial
    by (auto simp add: points_to_raw'_def asat_def
        make_untyped_ref_def zero_fun_def zero_share_def)
  have result_pool:
      \<open>store_alloc_pool s' = store_alloc_pool s - {a}\<close>
    using allocate_full_share[OF alloc] store_write_pool[OF write_result]
    by auto
  have residual_pool:
      \<open>store_alloc_pool (stack_allocator + heap) =
        store_alloc_pool s - {a}\<close>
    using stack_allocator_heap stack_allocator_pool heap_pool
      allocator_written_heap s' result_pool
    by (simp add: store_add_pool)
  have residual_perm:
      \<open>store_perm_map (stack_allocator + heap) l =
        store_perm_map s l\<close>
    for l
    using stack_allocator_heap stack_allocator_zero heap_perm
      store_add_perm by simp
  have allocated_in_pool: \<open>a \<in> store_alloc_pool s\<close>
    using allocate_full_share[OF alloc] by blast
  have residual_valid:
      \<open>store_has_valid_allocator (stack_allocator + heap)\<close>
    using stack_allocator_heap stack_allocator_valid
      store_add_valid_allocator by blast
  have residual_pool_nonempty:
      \<open>store_alloc_pool (stack_allocator + heap) \<noteq> {}\<close>
    using pool_nonempty store_pool_inf[of s] residual_pool
    by (metis finite.emptyI finite_insert infinite_remove)
  have residual_read:
      \<open>store_read_reference (stack_allocator + heap) l = Some v\<close>
    if perm: \<open>store_perm_map s l = \<top>\<close>
      and read: \<open>store_read_reference s l = Some v\<close>
    for l v
  proof -
    have heap_stack_allocator: \<open>heap \<sharp> stack_allocator\<close>
      using stack_allocator_heap by simp
    show ?thesis
      using store_add_read[
        OF _ heap_stack_allocator] heap_read_eq read stack_allocator_heap
      by simp
  qed
  have residual_stack:
      \<open>stack_allocator + heap \<Turnstile>
        reference_stack F (\<Phi> @ [make_untyped_ref a])\<close>
    using distinct live_outside stack_zero hidden allocated_in_pool
      residual_valid residual_pool_nonempty residual_pool residual_perm
      residual_read
    by (auto simp add: reference_stack_def asat_def make_untyped_ref_def;
        metis)
  show ?thesis
    by (rule asepconjI[where y=cell
          and z=\<open>stack_allocator + heap\<close>])
      (use state_split cell_residual cell_points_to residual_stack in auto)
qed

lemma reference_stack_pop:
  shows \<open>(reference_stack F (\<Phi> @ [r]) \<star>
      points_to_raw' r \<top> g) \<star> \<langle>F g\<rangle>
    \<longlongrightarrow> reference_stack F \<Phi>\<close>
proof (rule aentailsI)
  fix x
  assume sat:
    \<open>x \<Turnstile> (reference_stack F (\<Phi> @ [r]) \<star>
      points_to_raw' r \<top> g) \<star> \<langle>F g\<rangle>\<close>
  have stack_points_to:
      \<open>x \<Turnstile> reference_stack F (\<Phi> @ [r]) \<star>
        points_to_raw' r \<top> g\<close>
    and allowed: \<open>F g\<close>
    using sat by (simp_all add: asat_apure_precise_distrib2)
  from stack_points_to obtain stack cell where
      x: \<open>x = stack + cell\<close>
    and disjoint: \<open>stack \<sharp> cell\<close>
    and stack_sat: \<open>stack \<Turnstile> reference_stack F (\<Phi> @ [r])\<close>
    and cell_sat: \<open>cell \<Turnstile> points_to_raw' r \<top> g\<close>
    by (elim asepconjE)
  from stack_sat have
      valid: \<open>store_has_valid_allocator stack\<close>
    and pool_nonempty: \<open>store_alloc_pool stack \<noteq> {}\<close>
    and distinct: \<open>distinct (List.map address (\<Phi> @ [r]))\<close>
    and live_outside:
      \<open>\<And>q. q \<in> set (\<Phi> @ [r]) \<Longrightarrow>
        address q \<notin> store_alloc_pool stack\<close>
    and stack_zero:
      \<open>\<And>a. a \<in> store_alloc_pool stack \<or>
          a \<in> set (List.map address (\<Phi> @ [r])) \<Longrightarrow>
        store_perm_map stack a = \<bottom>\<close>
    and hidden:
      \<open>\<And>a. a \<notin> store_alloc_pool stack \<Longrightarrow>
        a \<notin> set (List.map address (\<Phi> @ [r])) \<Longrightarrow>
        \<exists>v. store_perm_map stack a = \<top> \<and>
          store_read_reference stack a = Some v \<and> F v\<close>
    by (auto simp add: reference_stack_def asat_def)
  from cell_sat have
      cell_pool: \<open>store_alloc_pool cell = {}\<close>
    and cell_read: \<open>store_read_reference cell (address r) = Some g\<close>
    and cell_top: \<open>store_perm_map cell (address r) = \<top>\<close>
    and cell_zero:
      \<open>\<And>a. a \<noteq> address r \<Longrightarrow>
        store_perm_map cell a = \<bottom>\<close>
    by (auto simp add: points_to_raw'_def asat_def
        top.extremum_unique)
  have pool: \<open>store_alloc_pool x = store_alloc_pool stack\<close>
    using x disjoint cell_pool store_add_pool by simp
  have valid': \<open>store_has_valid_allocator x\<close>
    using x disjoint valid store_add_valid_allocator by blast
  have distinct': \<open>distinct (List.map address \<Phi>)\<close>
    using distinct by simp
  have live_outside':
      \<open>\<And>q. q \<in> set \<Phi> \<Longrightarrow>
        address q \<notin> store_alloc_pool x\<close>
    using live_outside pool by auto
  have zero:
      \<open>\<And>a. a \<in> store_alloc_pool x \<or>
          a \<in> set (List.map address \<Phi>) \<Longrightarrow>
        store_perm_map x a = \<bottom>\<close>
  proof -
    fix a
    assume location:
      \<open>a \<in> store_alloc_pool x \<or>
        a \<in> set (List.map address \<Phi>)\<close>
    have not_r: \<open>a \<noteq> address r\<close>
      using location pool live_outside[of r] distinct by auto
    have \<open>store_perm_map stack a = \<bottom>\<close>
      using stack_zero location pool by auto
    then show \<open>store_perm_map x a = \<bottom>\<close>
      using x disjoint cell_zero[OF not_r] store_add_perm
      by simp
  qed
  have absorbed:
      \<open>\<And>a. a \<notin> store_alloc_pool x \<Longrightarrow>
        a \<notin> set (List.map address \<Phi>) \<Longrightarrow>
        \<exists>v. store_perm_map x a = \<top> \<and>
          store_read_reference x a = Some v \<and> F v\<close>
  proof -
    fix a
    assume outside_pool: \<open>a \<notin> store_alloc_pool x\<close>
      and not_live: \<open>a \<notin> set (List.map address \<Phi>)\<close>
    show \<open>\<exists>v. store_perm_map x a = \<top> \<and>
      store_read_reference x a = Some v \<and> F v\<close>
    proof (cases \<open>a = address r\<close>)
      case True
      have stack_empty: \<open>store_perm_map stack a = \<bottom>\<close>
        using stack_zero True by simp
      have cell_disjoint: \<open>cell \<sharp> stack\<close>
        using disjoint by simp
      have cell_sum: \<open>x = cell + stack\<close>
        using x disjoint by simp
      have read: \<open>store_read_reference x a = Some g\<close>
        using cell_sum cell_read True
          store_add_read[OF cell_read cell_disjoint]
        by simp
      show ?thesis
        using x disjoint stack_empty cell_top allowed read True
          store_add_perm
        by auto
    next
      case False
      obtain v where
          stack_top: \<open>store_perm_map stack a = \<top>\<close>
        and stack_read: \<open>store_read_reference stack a = Some v\<close>
        and admissible: \<open>F v\<close>
        using hidden[of a] outside_pool not_live False pool
        by auto
      have read: \<open>store_read_reference x a = Some v\<close>
        using x disjoint stack_read store_add_read by blast
      show ?thesis
        using x disjoint stack_top cell_zero[OF False] admissible read
          store_add_perm
        by auto
    qed
  qed
  show \<open>x \<Turnstile> reference_stack F \<Phi>\<close>
    using valid' pool_nonempty pool distinct' live_outside' zero absorbed
    by (auto simp add: reference_stack_def asat_def)
qed

lemma reference_stack_pop_general:
  assumes \<open>r \<in> set \<Phi>\<close>
  shows \<open>(points_to_raw' r \<top> g \<star> reference_stack F \<Phi>) \<star>
      \<langle>F g\<rangle>
    \<longlongrightarrow>
      (\<Squnion>\<Phi>\<^sub>1 \<Phi>\<^sub>2.
        reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<star>
        \<langle>\<Phi> = \<Phi>\<^sub>1 @ [r] @ \<Phi>\<^sub>2\<rangle>)\<close>
proof -
  obtain \<Phi>\<^sub>1 \<Phi>\<^sub>2 where split: \<open>\<Phi> = \<Phi>\<^sub>1 @ r # \<Phi>\<^sub>2\<close>
    using assms by (meson split_list)
  have stack_eq:
      \<open>reference_stack F \<Phi> =
        reference_stack F ((\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) @ [r])\<close>
    using split by (auto simp add: reference_stack_def)
  have pop:
      \<open>(points_to_raw' r \<top> g \<star> reference_stack F \<Phi>) \<star>
          \<langle>F g\<rangle>
        \<longlongrightarrow> reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2)\<close>
    using reference_stack_pop[
      where F=F and \<Phi>=\<open>\<Phi>\<^sub>1 @ \<Phi>\<^sub>2\<close> and r=r and g=g]
    by (simp add: stack_eq asepconj_comm)
  have package:
      \<open>reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2)
        \<longlongrightarrow>
        (\<Squnion>\<Phi>\<^sub>1 \<Phi>\<^sub>2.
          reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<star>
          \<langle>\<Phi> = \<Phi>\<^sub>1 @ [r] @ \<Phi>\<^sub>2\<rangle>)\<close>
    apply (rule aexists_entailsR[where x=\<Phi>\<^sub>1])
    apply (rule aexists_entailsR[where x=\<Phi>\<^sub>2])
    using split
    apply (simp add: asepconj_simp aentails_refl)
    done
  show ?thesis
    by (rule aentails_trans[OF pop package])
qed

lemma reference_stack_distinct:
  shows \<open>reference_stack F \<Phi>
    \<longlongrightarrow> \<langle>distinct \<Phi>\<rangle> \<star> reference_stack F \<Phi>\<close>
proof (rule aentailsI)
  fix s
  assume sat: \<open>s \<Turnstile> reference_stack F \<Phi>\<close>
  have mapped: \<open>distinct (List.map address \<Phi>)\<close>
    using sat
    by (auto simp add: reference_stack_def asat_def)
  then have distinct: \<open>distinct \<Phi>\<close>
    by (induction \<Phi>) auto
  with sat show
    \<open>s \<Turnstile> \<langle>distinct \<Phi>\<rangle> \<star> reference_stack F \<Phi>\<close>
    by (simp add: asat_apure_precise_distrib)
qed

subsection\<open>Reference allocation\<close>

lemma urust_eval_predicate_reference_raw:
  shows \<open>(\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>, store.reference_raw g\<rangle> (a, \<sigma>')) \<longleftrightarrow> (
             (store_allocate_reference \<sigma> = None \<and> AssertionFailed = a \<and> \<sigma> = \<sigma>') \<or>
             (\<exists>\<sigma>'' addr. store_allocate_reference \<sigma> = Some (addr, \<sigma>'') \<and>
                  store_write_reference \<sigma>'' addr g = None \<and>
                  a = AssertionFailed \<and> \<sigma>' = \<sigma>''))\<close> (is ?abort)
    and \<open>(\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>, store.reference_raw g\<rangle> (v,\<sigma>'')) \<longleftrightarrow> (
         \<exists>\<sigma>' addr. store_allocate_reference \<sigma> = Some (addr, \<sigma>') \<and>
                   store_write_reference \<sigma>' addr g = Some \<sigma>'' \<and>
                   make_untyped_ref addr = v)\<close> (is ?value)
    and \<open>(\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>, store.reference_raw g\<rangle> (r,\<sigma>')) \<longleftrightarrow> False\<close> (is ?return)
proof
  assume \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>, store.reference_raw g\<rangle> (a, \<sigma>')\<close>
  from this show \<open>store_allocate_reference \<sigma> = None \<and> AssertionFailed = a \<and> \<sigma> = \<sigma>' \<or>
        (\<exists>\<sigma>'' addr. store_allocate_reference \<sigma> = Some (addr, \<sigma>'') \<and>
          store_write_reference \<sigma>'' addr g = None \<and> a = AssertionFailed \<and> \<sigma>' = \<sigma>'')\<close>
    by (clarsimp simp add: urust_eval_predicate_defs deep_evaluates_nondet_basic.simps
      store.reference_raw_def evaluate_def call_def call_function_body.simps
      split!: option.splits expression.splits continuation.splits)
next
  assume \<open>store_allocate_reference \<sigma> = None \<and> AssertionFailed = a \<and> \<sigma> = \<sigma>' \<or> (\<exists>\<sigma>'' addr.
            store_allocate_reference \<sigma> = Some (addr, \<sigma>'') \<and>
            store_write_reference \<sigma>'' addr g = None \<and> a = AssertionFailed \<and> \<sigma>' = \<sigma>'')\<close>
  from this show \<open>\<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>,store.reference_raw g\<rangle> (a, \<sigma>')\<close>
    by (clarsimp simp add: urust_eval_predicate_defs deep_evaluates_nondet_basic.simps
      store.reference_raw_def evaluate_def call_def call_function_body.simps
      split!: option.splits expression.splits continuation.splits)
next
  show \<open>\<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>, store.reference_raw g\<rangle> (v,\<sigma>'') = (\<exists>\<sigma>' addr.
          store_allocate_reference \<sigma> = Some (addr, \<sigma>') \<and>
            store_write_reference \<sigma>' addr g = Some \<sigma>'' \<and> make_untyped_ref addr = v)\<close>
    by (clarsimp simp add: urust_eval_predicate_defs deep_evaluates_nondet_basic.simps make_untyped_ref_def
      store.reference_raw_def evaluate_def call_def call_function_body.simps
      split!: option.splits expression.splits continuation.splits)
next
  show \<open>\<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>,store.reference_raw g\<rangle> (r,\<sigma>') = False\<close>
    by (clarsimp simp add: urust_eval_predicate_defs deep_evaluates_nondet_basic.simps
      store.reference_raw_def evaluate_def split!: option.splits)
qed

lemma urust_eval_predicate_reference_raw_stack_local:
  shows \<open>urust_is_local \<Gamma> (store.reference_raw g)
    (reference_stack F \<Phi>)\<close>
proof (intro conjI)
  show \<open>is_local
    (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>v
      \<langle>\<Gamma>,store.reference_raw g\<rangle> (v,\<sigma>'))
    (reference_stack F \<Phi>)\<close>
  proof (clarsimp simp add: urust_eval_predicate_reference_raw
      is_local_def, safe, goal_cases)
    case (1 \<sigma>_0 \<sigma>_1 \<sigma>_0' \<sigma>' addr)
    have alloc_disjoint: \<open>\<sigma>' \<sharp> \<sigma>_1\<close>
      using 1(1,3) store_add_alloc by blast
    have write_disjoint: \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close>
      using 1(4) alloc_disjoint store_add_write by blast
    show ?case
      using write_disjoint by (simp add: disjoint_sym)
  next
    case (2 \<sigma>_0 \<sigma>_1 \<sigma>' v \<sigma>'' addr) note assms = this
    obtain \<sigma>_0' addr' where \<open>store_allocate_reference \<sigma>_0 = Some (addr', \<sigma>_0')\<close>
      using reference_stack_allocates assms by blast
    moreover from this and assms have \<open>addr' = addr\<close> and \<open>\<sigma>_0' \<sharp> \<sigma>_1\<close> and \<open>\<sigma>'' = \<sigma>_0' + \<sigma>_1\<close>
      using store_add_alloc by force+
    ultimately show ?case using assms
      by (metis option.inject store.allocate_write_succeeds store_add_write)
  next
    case (3 \<sigma>_0 \<sigma>_1 \<sigma>' v \<sigma>_0' \<sigma>'' addr)
    then show ?case using store_add_alloc store_add_write by blast
  qed
next
  show \<open>is_local
    (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>r
      \<langle>\<Gamma>,store.reference_raw g\<rangle> (v,\<sigma>'))
    (reference_stack F \<Phi>)\<close>
    by (clarsimp simp add: is_local_def asat_def urust_eval_predicate_reference_raw)
next
  show \<open>is_local
    (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>a
      \<langle>\<Gamma>,store.reference_raw g\<rangle> (v,\<sigma>'))
    (reference_stack F \<Phi>)\<close>
  proof (clarsimp simp add: urust_eval_predicate_reference_raw
      is_local_def, goal_cases)
    case (1 \<sigma>_0 \<sigma>_1)
    obtain addr sigma_alloc where
        alloc: \<open>store_allocate_reference \<sigma>_0 =
          Some (addr, sigma_alloc)\<close>
      using reference_stack_allocates 1 by blast
    obtain sigma_write where
        write_result:
          \<open>store_write_reference sigma_alloc addr g =
            Some sigma_write\<close>
      using store.allocate_write_succeeds alloc by blast
    have full_alloc:
        \<open>store_allocate_reference (\<sigma>_0 + \<sigma>_1) =
          Some (addr, sigma_alloc + \<sigma>_1)\<close>
      using store_add_alloc 1 alloc by blast
    obtain full_write where
        full_write_result:
          \<open>store_write_reference (sigma_alloc + \<sigma>_1) addr g =
            Some full_write\<close>
      using store.allocate_write_succeeds full_alloc by blast
    show ?case
      using alloc write_result full_alloc full_write_result
      by auto
  qed
qed

lemma asat_hoist_pure_precise:
  shows \<open>\<phi> \<Turnstile> \<langle>P\<rangle> \<star> \<xi> \<longleftrightarrow> (P \<and> (\<phi> \<Turnstile> \<xi>))\<close> (is ?g1)
    and \<open>\<phi> \<Turnstile> \<xi> \<star> \<langle>P\<rangle> \<longleftrightarrow> ((\<phi> \<Turnstile> \<xi>) \<and> P)\<close> (is ?g2)
proof -
  show ?g1
    by (rule asat_apure_precise_distrib)
  show ?g2
    by (rule asat_apure_precise_distrib2)
qed

lemma striple_ref_raw_stack:
  shows \<open>\<Gamma>; reference_stack F \<Phi> \<turnstile> store.reference_raw g
    \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k
      (\<lambda>r. points_to_raw' r \<top> g \<star>
        reference_stack F (\<Phi> @ [r])) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof (intro striple_localI)
  fix \<sigma> \<sigma>' r
  assume eval:
      \<open>\<sigma> \<leadsto>\<^sub>v\<langle>yh \<Gamma>, store.reference_raw g\<rangle> (r, \<sigma>')\<close>
    and stack: \<open>\<sigma> \<Turnstile> reference_stack F \<Phi>\<close>
  obtain sigma_alloc addr where
      alloc: \<open>store_allocate_reference \<sigma> =
        Some (addr, sigma_alloc)\<close>
    and write_result: \<open>store_write_reference sigma_alloc addr g =
        Some \<sigma>'\<close>
    and ref: \<open>make_untyped_ref addr = r\<close>
    using eval urust_eval_predicate_reference_raw(2) by blast
  have \<open>\<sigma>' \<Turnstile>
      points_to_raw' (make_untyped_ref addr) \<top> g \<star>
      reference_stack F (\<Phi> @ [make_untyped_ref addr])\<close>
    by (rule reference_stack_allocate[OF stack alloc write_result])
  with ref show \<open>\<sigma>' \<Turnstile> points_to_raw' r \<top> g \<star>
      reference_stack F (\<Phi> @ [r])\<close>
    by simp
next
  show \<open>\<And>\<sigma> \<sigma>' r.
    \<sigma> \<leadsto>\<^sub>r\<langle>yh \<Gamma>, store.reference_raw g\<rangle> (r, \<sigma>') \<Longrightarrow>
    \<sigma> \<Turnstile> reference_stack F \<Phi> \<Longrightarrow>
    \<sigma>' \<Turnstile> \<rho> r\<close>
    by (simp add: urust_eval_predicate_reference_raw(3))
next
  fix \<sigma> \<sigma>' a
  assume eval:
      \<open>\<sigma> \<leadsto>\<^sub>a\<langle>yh \<Gamma>, store.reference_raw g\<rangle> (a, \<sigma>')\<close>
    and stack: \<open>\<sigma> \<Turnstile> reference_stack F \<Phi>\<close>
  obtain addr sigma_alloc where
      alloc: \<open>store_allocate_reference \<sigma> =
        Some (addr, sigma_alloc)\<close>
    using reference_stack_allocates stack by blast
  obtain sigma_write where
      write_result:
        \<open>store_write_reference sigma_alloc addr g = Some sigma_write\<close>
    using store.allocate_write_succeeds alloc by blast
  with eval alloc show \<open>\<sigma>' \<Turnstile> \<theta> a\<close>
    by (auto simp add: urust_eval_predicate_reference_raw)
qed (use urust_eval_predicate_reference_raw_stack_local in fastforce)+

lemma sstriple_ref_raw_stack:
  shows \<open>\<Gamma>; reference_stack F \<Phi> \<turnstile> store.reference_raw g
    \<stileturn>
      (\<lambda>r. points_to_raw' r \<top> g \<star>
        reference_stack F (\<Phi> @ [r])) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  by (intro sstriple_from_stripleI striple_ref_raw_stack)
    (auto simp add: eval_abort_def eval_value_def eval_return_def
      urust_eval_predicate_reference_raw_stack_local)

corollary ref_raw_stack_spec':
  shows \<open>\<Gamma> ; store.reference_raw_fun g \<Turnstile>\<^sub>F
    reference_defs.reference_raw_contract
      points_to_raw' (\<lambda>_. UNIV) UNIV
        reference_stack F \<Phi> g\<close>
  unfolding store.reference_raw_fun_def satisfies_function_contract_def
  by (simp add: reference_defs.reference_raw_contract_def
      reference_defs.points_to_raw_def asepconj_simp
      sstriple_ref_raw_stack)

subsection\<open>Dereferencing\<close>

lemma urust_eval_predicate_dereference_raw:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,store.dereference_by_value_raw r\<rangle> (v,\<sigma>') \<longleftrightarrow>
          (\<sigma>' = \<sigma> \<and> store_read_reference \<sigma> (address r) = Some v)\<close> (is ?value)
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,store.dereference_by_value_raw r\<rangle> (r',\<sigma>') \<longleftrightarrow> False\<close>  (is ?return)
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,store.dereference_by_value_raw r\<rangle> (a, \<sigma>') \<longleftrightarrow>
          (a = DanglingPointer \<and> \<sigma> = \<sigma>' \<and> store_read_reference \<sigma> (address r) = None)\<close> (is ?abort)
by (cases \<open>store_read_reference \<sigma> (address r)\<close>, auto simp add: store.dereference_by_value_raw_def
  urust_eval_predicate_bind urust_eval_predicate_get urust_eval_predicate_abort
  urust_eval_predicate_literal)+

lemma urust_eval_predicate_dereference_raw_local:
  shows \<open>urust_is_local \<Gamma> (store.dereference_by_value_raw r) (r \<mapsto>\<langle>sh\<rangle> v)\<close>
by (auto simp add: is_local_def urust_eval_predicate_dereference_raw points_to_raw'_def
  asat_def store_add_read)

lemma striple_dereference_raw:
  shows \<open>\<Gamma>; r \<mapsto>\<langle>sh\<rangle> v \<turnstile> store.dereference_by_value_raw r \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>v'. r\<mapsto>\<langle>sh\<rangle> v \<star> \<langle>v = v'\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  apply (intro striple_localI)
  using urust_eval_predicate_dereference_raw_local
  apply (auto simp: urust_eval_predicate_dereference_raw asat_apure_precise_distrib2
     simp add: asepconj_simp)
  done

lemma sstriple_dereference_raw:
  notes asepconj_simp [simp]
  shows \<open>\<Gamma>; r \<mapsto>\<langle>sh\<rangle> v \<turnstile> store.dereference_by_value_raw r \<stileturn> (\<lambda>v'. r\<mapsto>\<langle>sh\<rangle> v \<star> \<langle>v = v'\<rangle>) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro sstriple_from_stripleI, intro striple_dereference_raw) (auto simp add: eval_value_def
  eval_abort_def eval_return_def urust_eval_predicate_dereference_raw_local)

lemma wp_dereference_raw:
    notes asat_simp [simp]
      and aentails_intro [intro]
    shows \<open>r\<mapsto>\<langle>sh\<rangle> g \<star> (r\<mapsto>\<langle>sh\<rangle> g \<Zsurj> \<psi> g) \<longlongrightarrow> \<W>\<P> \<Gamma> (store.dereference_by_value_raw r) \<psi> \<rho> \<theta>\<close>
proof -
  have \<open>r \<mapsto>\<langle>sh\<rangle> g \<star> (\<Sqinter>g'. (r \<mapsto>\<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) \<Zsurj> \<psi> g') \<longlongrightarrow>
                      \<W>\<P> \<Gamma> (store.dereference_by_value_raw r) \<psi> \<rho> \<theta>\<close>
    by (intro sstriple_straightline_to_wp sstriple_dereference_raw)
  moreover have \<open>r \<mapsto>\<langle>sh\<rangle> g \<star> (r \<mapsto>\<langle>sh\<rangle> g \<Zsurj> \<psi> g) \<longlongrightarrow>
      r \<mapsto>\<langle>sh\<rangle> g \<star> (\<Sqinter>g'. (r \<mapsto>\<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) \<Zsurj> \<psi> g')\<close>
  proof (intro asepconj_mono4 aentails_refl aforall_entailsR)
    fix g'
    show \<open>r \<mapsto>\<langle>sh\<rangle> g \<Zsurj> \<psi> g \<longlongrightarrow> (r \<mapsto>\<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) \<Zsurj> \<psi> g'\<close>
    proof (cases \<open>g = g'\<close>)
      \<comment>\<open>A precise-pure factor is a unit when true and an annihilator when false.\<close>
      case True
      then show ?thesis
        by (simp add: asepconj_simp aentails_refl)
    next
      case False
      then show ?thesis
        by (simp add: asepconj_simp awand_bot aentails_true)
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma wp_dereference_rawI:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> (r\<mapsto>\<langle>sh\<rangle> g \<star> (r\<mapsto>\<langle>sh\<rangle> g \<Zsurj> \<psi> g))\<close>
    shows \<open>\<phi> \<longlongrightarrow>  \<W>\<P> \<Gamma> (store.dereference_by_value_raw r) \<psi> \<rho> \<theta>\<close>
by (rule aentails_trans', rule wp_dereference_raw) (auto intro: assms)

definition dereference_by_value_raw_contract'
  :: \<open>('a, 'b) gref \<Rightarrow> share \<Rightarrow> 'b \<Rightarrow> ('s, 'b, 'abort) function_contract\<close> where
  \<open>dereference_by_value_raw_contract' r sh g \<equiv>
     let pre = r \<mapsto>\<langle>sh\<rangle> g in
     let post = \<lambda>g'. (r \<mapsto>\<langle>sh\<rangle> g \<star> \<langle>g=g'\<rangle>) in
     make_function_contract pre post\<close>

corollary dereference_by_value_raw_spec':
  shows \<open>\<Gamma> ; store.dereference_by_value_raw_fun r \<Turnstile>\<^sub>F dereference_by_value_raw_contract' r sh g\<close>
proof -
  have \<open>r \<mapsto> \<langle>sh\<rangle> g \<longlongrightarrow>
    \<W>\<P> \<Gamma> (store.dereference_by_value_raw r) (\<lambda>g'. r \<mapsto> \<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) (\<lambda>g'. r \<mapsto> \<langle>sh\<rangle> g \<star> \<langle>g = g'\<rangle>) \<bottom>\<close>
    using sstriple_dereference_raw wp_sstriple_iff by blast
  then show ?thesis
    by (simp add: store.dereference_by_value_raw_fun_def satisfies_function_contract_def dereference_by_value_raw_contract'_def
        wp_sstriple_iff)
qed

subsection\<open>Modifications behind a reference\<close>

lemma urust_eval_predicate_modify_raw:
  shows \<open>\<sigma> \<leadsto>\<^sub>v\<langle>\<Gamma>,store.modify_raw r f\<rangle> (v,\<sigma>') \<longleftrightarrow>
          (\<exists>g. store_read_reference \<sigma> (address r) = Some g \<and>
               store_write_reference \<sigma> (address r) (f g) = Some \<sigma>')\<close> (is ?value)
    and \<open>\<sigma> \<leadsto>\<^sub>r\<langle>\<Gamma>,store.modify_raw r f\<rangle> (r',\<sigma>') \<longleftrightarrow> False\<close>  (is ?return)
    and \<open>\<sigma> \<leadsto>\<^sub>a\<langle>\<Gamma>,store.modify_raw r f\<rangle> (a, \<sigma>') \<longleftrightarrow>
          (a = DanglingPointer \<and> \<sigma>' = \<sigma> \<and> (
              (store_read_reference \<sigma> (address r) = None)
            \<or> (\<exists>g. store_read_reference \<sigma> (address r) = Some g \<and>
                   store_write_reference \<sigma> (address r) (f g) = None)))\<close> (is ?abort)
by (auto simp add: store.modify_raw_def urust_eval_predicate_bind urust_eval_predicate_get
  urust_eval_predicate_abort urust_eval_predicate_literal urust_eval_predicate_put_assert split:
  option.splits)

lemma urust_eval_predicate_modify_raw_local:
  shows \<open>urust_is_local \<Gamma> (store.modify_raw r f) (r \<mapsto>\<langle>\<top>\<rangle> v)\<close>
proof (intro conjI)
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>v \<langle>\<Gamma>,store.modify_raw r f\<rangle> (v,\<sigma>')) (r \<mapsto> \<langle>\<top>\<rangle> v)\<close>
  proof -
    have \<open>\<exists>\<sigma>_0'. store_write_reference \<sigma>_0 (address r) (f v) = Some \<sigma>_0' \<and> \<sigma>' = \<sigma>_0' + \<sigma>_1\<close>
      if \<open>\<sigma>_0 \<sharp> \<sigma>_1\<close>
        and \<open>\<top> \<le> store_perm_map \<sigma>_0 (address r)\<close>
        and \<open>store_write_reference (\<sigma>_0 + \<sigma>_1) (address r) (f v) = Some \<sigma>'\<close>
      for \<sigma>_0 \<sigma>_1 \<sigma>' :: 's
      using that
      by (metis option.inject store_add_write top.extremum_uniqueI write_perm_succeeds)
    then show ?thesis
      by (auto simp add: is_local_def urust_eval_predicate_modify_raw points_to_raw'_def asat_def
          dest: store_add_read store_add_write)
  qed
next
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>r \<langle>\<Gamma>,store.modify_raw r f\<rangle> (v,\<sigma>')) (r \<mapsto> \<langle>\<top>\<rangle> v)\<close>
    by (clarsimp simp add: is_local_def urust_eval_predicate_modify_raw)
next
  show \<open>is_local (\<lambda>\<sigma> (v, \<sigma>'). \<sigma> \<leadsto>\<^sub>a \<langle>\<Gamma>,store.modify_raw r f\<rangle> (v,\<sigma>')) (r \<mapsto> \<langle>\<top>\<rangle> v)\<close>
    apply (clarsimp simp add: is_local_def urust_eval_predicate_modify_raw
      points_to_raw'_def asat_def store_add_read top.extremum_unique)
    apply (metis option.distinct(1) store_add_write write_perm_succeeds)
    done
qed

lemma striple_modify_raw:
  notes global_store_simps [simp]
  shows \<open>\<Gamma>; r \<mapsto>\<langle>\<top>\<rangle> v \<turnstile> store.modify_raw r f \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. r \<mapsto>\<langle>\<top>\<rangle> (f v)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
proof (intro striple_localI)
  fix \<sigma> \<sigma>' :: 's and va
  assume \<sigma>: \<open>\<sigma> \<leadsto>\<^sub>v \<langle>yh \<Gamma>,store.modify_raw r f\<rangle> (va,\<sigma>')\<close> \<open>\<sigma> \<Turnstile> r \<mapsto> \<langle>\<top>\<rangle> v\<close>
  have read: \<open>store_read_reference \<sigma> (address r) = Some v\<close>
    using \<sigma> by (auto simp add: points_to_raw'_def asat_def)
  show \<open>\<sigma>' \<Turnstile> r \<mapsto> \<langle>\<top>\<rangle> f v\<close>
    apply (rule points_to_raw_write[OF \<sigma>(2)])
    using \<sigma>(1) read
    by (auto simp add: urust_eval_predicate_modify_raw)
next
  fix \<sigma> \<sigma>' :: 's and ra :: 'f
  assume \<open>\<sigma> \<leadsto>\<^sub>r \<langle>yh \<Gamma>,store.modify_raw r f\<rangle> (ra,\<sigma>')\<close>
    and \<open>\<sigma> \<Turnstile> r \<mapsto> \<langle>\<top>\<rangle> v\<close>
  then show \<open>\<sigma>' \<Turnstile> \<rho> ra\<close>
    by (simp add: urust_eval_predicate_modify_raw(2))
next
  fix \<sigma> \<sigma>' :: 's and a :: \<open>'c abort\<close>
  assume \<sigma>: \<open>\<sigma> \<leadsto>\<^sub>a \<langle>yh \<Gamma>,store.modify_raw r f\<rangle> (a,\<sigma>')\<close> \<open>\<sigma> \<Turnstile> r \<mapsto> \<langle>\<top>\<rangle> v\<close>
  then have \<open>\<sigma> \<in> \<theta> DanglingPointer\<close>
    by (metis option.distinct(1) points_to_raw'E top.extremum_unique urust_eval_predicate_modify_raw(3)
        write_perm_succeeds)
  with \<sigma> show \<open>\<sigma>' \<Turnstile> \<theta> a\<close>
    by (simp add: urust_eval_predicate_modify_raw asat_hoist_pure_precise ucincl_intros points_to_raw'_def asat_def)
qed (use urust_eval_predicate_modify_raw_local in fastforce)+

lemma sstriple_modify_raw:
  shows \<open>\<Gamma>; r \<mapsto>\<langle>\<top>\<rangle> v \<turnstile> store.modify_raw r f \<stileturn> (\<lambda>_. r \<mapsto>\<langle>\<top>\<rangle> (f v)) \<bowtie> \<rho> \<bowtie> \<theta>\<close>
by (intro sstriple_from_stripleI, intro striple_modify_raw) (auto simp add: eval_value_def
  eval_return_def eval_abort_def urust_eval_predicate_modify_raw_local)

lemma wp_modify_raw:
    notes asat_simp [simp]
      and aentails_intro [intro]
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>r\<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> ()) \<longlongrightarrow> \<W>\<P> \<Gamma> (store.modify_raw r f) \<psi> \<rho> \<theta>\<close>
proof -
  from assms have \<open>r\<mapsto>\<langle>\<top>\<rangle> g \<star> (\<Sqinter>u. r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> u) \<longlongrightarrow>
                      \<W>\<P> \<Gamma> (store.modify_raw r f) \<psi> \<rho> \<theta>\<close>
    by (intro sstriple_straightline_to_wp sstriple_modify_raw)
  moreover have \<open>r\<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> ()) \<longlongrightarrow> r\<mapsto>\<langle>\<top>\<rangle> g \<star> (\<Sqinter>u. r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> u)\<close>
    by (auto elim!: asepconjE awandE intro!: asepconjI awandI simp add: asat_weaken
      aentails_def)
  ultimately show ?thesis
    by blast
qed

lemma wp_modify_rawI:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> r\<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> (f g) \<Zsurj> \<psi> ())\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (store.modify_raw r f) \<psi> \<rho> \<theta>\<close>
  by (rule aentails_trans', rule wp_modify_raw) (auto intro: assms)

definition modify_raw_contract' :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>modify_raw_contract' r g f \<equiv>
     let pre = r \<mapsto>\<langle>\<top>\<rangle> g in
     let post = \<lambda>_. (r \<mapsto>\<langle>\<top>\<rangle> (f g)) in
     make_function_contract pre post\<close>

corollary modify_raw_spec':
  shows \<open>\<Gamma> ; store.modify_raw_fun r f \<Turnstile>\<^sub>F modify_raw_contract' r g f\<close>
  unfolding store.modify_raw_fun_def satisfies_function_contract_def
  by (simp add: modify_raw_contract'_def sstriple_modify_raw)

subsection\<open>Updating a reference\<close>

lemma striple_update_raw:
  shows \<open>\<And>\<rho>. \<Gamma>; r \<mapsto>\<langle>\<top>\<rangle> g \<turnstile> store.update_raw r g' \<stileturn>\<^sub>w\<^sub>e\<^sub>a\<^sub>k (\<lambda>_. r \<mapsto>\<langle>\<top>\<rangle> g') \<bowtie> \<rho> \<bowtie> \<theta>\<close>
  using striple_modify_raw
  by (force simp add: store.update_raw_def)

lemma wp_update_raw:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
    shows \<open>r \<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> g' \<Zsurj> \<psi> ()) \<longlongrightarrow> \<W>\<P> \<Gamma> (store.update_raw r g') \<psi> \<rho> \<theta>\<close>
  unfolding store.update_raw_def
  by (rule wp_modify_raw[OF assms])

lemma wp_update_rawI:
  assumes \<open>\<And>v. ucincl (\<psi> v)\<close>
      and \<open>\<phi> \<longlongrightarrow> r\<mapsto>\<langle>\<top>\<rangle> g \<star> (r\<mapsto>\<langle>\<top>\<rangle> g' \<Zsurj> \<psi> ())\<close>
    shows \<open>\<phi> \<longlongrightarrow> \<W>\<P> \<Gamma> (store.update_raw r g') \<psi> \<rho> \<theta>\<close>
  by (rule aentails_trans', rule wp_update_raw) (auto intro: assms)

definition update_raw_contract' :: \<open>('a, 'b) gref \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> ('s, unit, 'abort) function_contract\<close> where
  \<open>update_raw_contract' r g0 g \<equiv>
     let pre = r \<mapsto>\<langle>\<top>\<rangle> g0 in
     let post = \<lambda>_. (r \<mapsto>\<langle>\<top>\<rangle> g) in
     make_function_contract pre post\<close>

corollary update_raw_spec':
  shows \<open>\<Gamma> ; store.update_raw_fun r g \<Turnstile>\<^sub>F update_raw_contract' r g0 g\<close>
  using modify_raw_spec'[where r=r and g=g0 and f=\<open>\<lambda>_. g\<close>]
  by (simp add: store.update_raw_fun_def store.update_raw_def
      store.modify_raw_fun_def modify_raw_contract'_def
      update_raw_contract'_def)

no_notation points_to_raw' ("(_) \<mapsto> \<langle>_\<rangle> (_)" [69,0,69]70)

(*<*)
end
(*>*)

\<comment>\<open>Conceptually, \<^locale>\<open>global_perm_store\<close> could be
declared as a sublocale of \<^locale>\<open>reference\<close>. However, code generation
does not seem to handle the combination of nested locales and sublocales
reliably (see the code generation tutorial). We therefore prove the logical
content of that sublocale declaration in
\<^verbatim>\<open>reference_sublocale\<close> and use the theorem explicitly when
interpreting concrete stores.\<close>

context global_perm_store
begin

lemma reference_sublocale: \<open>reference
   store.update_raw_fun store.dereference_by_value_raw_fun store.reference_raw_fun
   points_to_raw' (\<lambda>_. UNIV) UNIV reference_stack\<close>
proof
  show \<open>\<And>\<Gamma> r g g0. \<Gamma> ; store.update_raw_fun r g \<Turnstile>\<^sub>F
      reference_defs.update_raw_contract points_to_raw' (\<lambda>_. UNIV) r g0 g\<close>
    using update_raw_spec'
    by (simp add: reference_defs.update_raw_contract_def
        reference_defs.points_to_raw_def update_raw_contract'_def
        asepconj_simp)
next
  show \<open>\<And>\<Gamma> r sh g.
       \<Gamma> ; store.dereference_by_value_raw_fun
             r \<Turnstile>\<^sub>F reference_defs.dereference_raw_contract points_to_raw' r sh g\<close>
    using dereference_by_value_raw_spec'
    by (simp add: reference_defs.dereference_raw_contract_def
        reference_defs.points_to_raw_def
        dereference_by_value_raw_contract'_def)
next
  show \<open>\<And>\<Gamma> g F \<Phi>. \<Gamma> ; store.reference_raw_fun
      g \<Turnstile>\<^sub>F reference_defs.reference_raw_contract
        points_to_raw' (\<lambda>_. UNIV) UNIV reference_stack F \<Phi> g\<close>
    by (rule ref_raw_stack_spec')
next
  show \<open>\<And>F \<Phi> r g. r \<in> set \<Phi> \<Longrightarrow>
      (reference_defs.points_to_raw points_to_raw' r \<top> g \<star>
        reference_stack F \<Phi>) \<star> \<langle>F g\<rangle>
      \<longlongrightarrow>
      (\<Squnion>\<Phi>\<^sub>1 \<Phi>\<^sub>2.
        reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<star>
        \<langle>\<Phi> = \<Phi>\<^sub>1 @ [r] @ \<Phi>\<^sub>2\<rangle>)\<close>
  proof -
    fix F :: \<open>'b \<Rightarrow> bool\<close>
      and \<Phi> :: \<open>('a, 'b) gref list\<close>
      and r :: \<open>('a, 'b) gref\<close>
      and g :: 'b
    assume member: \<open>r \<in> set \<Phi>\<close>
    show \<open>(reference_defs.points_to_raw points_to_raw' r \<top> g \<star>
        reference_stack F \<Phi>) \<star> \<langle>F g\<rangle>
      \<longlongrightarrow>
      (\<Squnion>\<Phi>\<^sub>1 \<Phi>\<^sub>2.
        reference_stack F (\<Phi>\<^sub>1 @ \<Phi>\<^sub>2) \<star>
        \<langle>\<Phi> = \<Phi>\<^sub>1 @ [r] @ \<Phi>\<^sub>2\<rangle>)\<close>
      unfolding reference_defs.points_to_raw_def
      by (rule reference_stack_pop_general[OF member])
  qed
next
  show \<open>\<And>F \<Phi>. reference_stack F \<Phi>
      \<longlongrightarrow> \<langle>distinct \<Phi>\<rangle> \<star> reference_stack F \<Phi>\<close>
    by (rule reference_stack_distinct)
next
  show \<open>\<And>r sh1 sh2 v1 v2.
       reference_defs.points_to_raw points_to_raw' r sh1 v1 \<star>
       reference_defs.points_to_raw points_to_raw' r sh2 v2 \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r (sh1 + sh2) v1 \<star> \<langle>v1 = v2\<rangle>\<close>
    by (simp add: points_to_raw_combine' reference_defs.points_to_raw_def)
next
  show \<open>\<And>sh sh1 sh2 r v.
       sh = sh1 + sh2 \<Longrightarrow>
       sh1 \<sharp> sh2 \<Longrightarrow>
       0 < sh1 \<Longrightarrow>
       0 < sh2 \<Longrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh v \<longlongrightarrow>
       reference_defs.points_to_raw points_to_raw' r sh1 v \<star>
        reference_defs.points_to_raw points_to_raw' r sh2 v\<close>
    by (simp add: points_to_raw_split'' reference_defs.points_to_raw_def)
qed

end

(*<*)
end
(*>*)
