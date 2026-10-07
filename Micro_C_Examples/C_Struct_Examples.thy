theory C_Struct_Examples
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Shallow_Micro_C.C_Arithmetic_Rules"
    C_Reference_Rules
begin

c_source CStruct \<open>
  struct point {
    int x;
    int y;
  };
\<close>

thm CStruct.point.record_simps

section \<open>C struct verification\<close>

text \<open>
  This theory demonstrates verification of C code operating on structs.
  The function @{text swap_coords} swaps the x and y fields of a
  point struct via a pointer.
\<close>

locale c_struct_verification_ctx =
    c_reference reference_types _ _ _ _ _ _ _ +
    ref_c_int: c_reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism +
    ref_c_point: c_reference_allocatable reference_types _ _ _ _ _ _ _ c_point_prism
  for reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> c_abort \<Rightarrow> 'prompt \<Rightarrow>
        'output \<Rightarrow> unit\<close>
  and c_int_prism :: \<open>('gv, c_int) prism\<close>
  and c_point_prism :: \<open>('gv, CStruct.point) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_point.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

c_source CStruct [types = []] \<open>
  struct point {
    int x;
    int y;
  };

  void swap_coords(struct point *p) {
    int t = p->x;
    p->x = p->y;
    p->y = t;
  }
\<close>

thm CStruct.swap_coords_def

text \<open>
  The contract for swap\_coords: given a reference to a c\_point with value
  @{text pval}, after execution the x and y fields are swapped.
\<close>
definition c_swap_coords_contract :: \<open>('addr, 'gv, CStruct.point) State_References.ref \<Rightarrow> 'gv \<Rightarrow> CStruct.point \<Rightarrow>
      ('s, 'a, 'b) function_contract\<close> where
  \<open>c_swap_coords_contract pref pg pval \<equiv>
    let pre  = can_alloc_reference \<star>
               pref \<mapsto>\<langle>\<top>\<rangle> pg\<down>pval;
        post = \<lambda>_. can_alloc_reference \<star>
               pref \<mapsto>\<langle>\<top>\<rangle>
                 (\<lambda>_. CStruct.update_point_y (\<lambda>_. CStruct.point_x pval)
                         (CStruct.update_point_x (\<lambda>_. CStruct.point_y pval) pval)) \<sqdot> (pg\<down>pval)
     in make_function_contract pre post\<close>
ucincl_auto c_swap_coords_contract

lemma c_point_x_focus_view [simp]:
  shows \<open>focus_view (Abs_focus (make_focus_raw (\<lambda>s. Some (CStruct.point_x s)) (\<lambda>y. CStruct.update_point_x (\<lambda>_. y)))) pval = Some (CStruct.point_x pval)\<close>
proof -
  have valid_via_modify: \<open>is_valid_focus (make_focus_raw_via_view_modify (\<lambda>s. Some (CStruct.point_x s)) CStruct.update_point_x)\<close>
  proof (rule is_valid_focus_via_modifyI')
    show \<open>is_valid_view_modify (\<lambda>s. Some (CStruct.point_x s)) CStruct.update_point_x\<close>
      unfolding is_valid_view_modify_def
    proof (intro conjI allI impI)
      fix f s
      show \<open>Some (CStruct.point_x (CStruct.update_point_x f s)) = map_option f (Some (CStruct.point_x s))\<close>
        by (cases s) simp
    next
      fix f s
      assume eq: \<open>map_option f (Some (CStruct.point_x s)) = Some (CStruct.point_x s)\<close>
      then have fx: \<open>f (CStruct.point_x s) = CStruct.point_x s\<close>
        by simp
      show \<open>CStruct.update_point_x f s = s\<close>
      proof (cases s)
        case (make_point x1 x2)
        from fx make_point have \<open>f x1 = x1\<close>
          by simp
        then show ?thesis
          using make_point by (simp add: CStruct.point.record_simps CStruct.point.expand)
      qed
    next
      fix f g s
      show \<open>CStruct.update_point_x f (CStruct.update_point_x g s) = CStruct.update_point_x (\<lambda>x. f (g x)) s\<close>
        by (cases s) simp
    qed
  qed
  then have valid: \<open>is_valid_focus (make_focus_raw (\<lambda>s. Some (CStruct.point_x s)) (\<lambda>y. CStruct.update_point_x (\<lambda>_. y)))\<close>
    by (simp add: make_focus_raw_via_view_modify_def)
  then show ?thesis
    by (auto simp add: eq_onp_same_args focus_view.abs_eq Abs_focus_inverse)
qed

lemma c_point_y_focus_view [simp]:
  shows \<open>focus_view (Abs_focus (make_focus_raw (\<lambda>s. Some (CStruct.point_y s)) (\<lambda>y. CStruct.update_point_y (\<lambda>_. y)))) pval = Some (CStruct.point_y pval)\<close>
proof -
  have valid_via_modify: \<open>is_valid_focus (make_focus_raw_via_view_modify (\<lambda>s. Some (CStruct.point_y s)) CStruct.update_point_y)\<close>
  proof (rule is_valid_focus_via_modifyI')
    show \<open>is_valid_view_modify (\<lambda>s. Some (CStruct.point_y s)) CStruct.update_point_y\<close>
      unfolding is_valid_view_modify_def
    proof (intro conjI allI impI)
      fix f s
      show \<open>Some (CStruct.point_y (CStruct.update_point_y f s)) = map_option f (Some (CStruct.point_y s))\<close>
        by (cases s) simp
    next
      fix f s
      assume eq: \<open>map_option f (Some (CStruct.point_y s)) = Some (CStruct.point_y s)\<close>
      then have fy: \<open>f (CStruct.point_y s) = CStruct.point_y s\<close>
        by simp
      show \<open>CStruct.update_point_y f s = s\<close>
      proof (cases s)
        case (make_point x1 x2)
        from fy make_point have \<open>f x2 = x2\<close>
          by simp
        then show ?thesis
          using make_point by (simp add: CStruct.point.record_simps CStruct.point.expand)
      qed
    next
      fix f g s
      show \<open>CStruct.update_point_y f (CStruct.update_point_y g s) = CStruct.update_point_y (\<lambda>x. f (g x)) s\<close>
        by (cases s) simp
    qed
  qed
  then have valid: \<open>is_valid_focus (make_focus_raw (\<lambda>s. Some (CStruct.point_y s)) (\<lambda>y. CStruct.update_point_y (\<lambda>_. y)))\<close>
    by (simp add: make_focus_raw_via_view_modify_def)
  then show ?thesis
    by (auto simp add: eq_onp_same_args focus_view.abs_eq Abs_focus_inverse)
qed

lemma c_point_x_lens_focus_view [simp]:
  shows \<open>focus_view (Abs_focus (lens_to_focus_raw (make_lens_via_view_modify CStruct.point_x CStruct.update_point_x))) pval = Some (CStruct.point_x pval)\<close>
proof -
  have valid_vm: \<open>is_valid_lens_view_modify CStruct.point_x CStruct.update_point_x\<close>
    unfolding is_valid_lens_view_modify_def
  proof (intro conjI allI impI)
    fix f s
    show \<open>CStruct.point_x (CStruct.update_point_x f s) = f (CStruct.point_x s)\<close>
      by (cases s) simp
  next
    fix f s
    assume eq: \<open>f (CStruct.point_x s) = CStruct.point_x s\<close>
    show \<open>CStruct.update_point_x f s = s\<close>
    proof (cases s)
      case (make_point x1 x2)
      from eq make_point have \<open>f x1 = x1\<close>
        by simp
      then show ?thesis
        using make_point by (simp add: CStruct.point.record_simps CStruct.point.expand)
    qed
  next
    fix f g s
    show \<open>CStruct.update_point_x f (CStruct.update_point_x g s) = CStruct.update_point_x (\<lambda>x. f (g x)) s\<close>
      by (cases s) simp
  qed
  have valid: \<open>is_valid_lens (make_lens_via_view_modify CStruct.point_x CStruct.update_point_x)\<close>
    by (rule is_valid_lens_via_modifyI'[OF valid_vm])
  from lens_to_focus_raw_components'[OF valid] show ?thesis
    by (simp add: make_lens_via_view_modify_components)
qed

lemma c_point_y_lens_focus_view [simp]:
  shows \<open>focus_view (Abs_focus (lens_to_focus_raw (make_lens_via_view_modify CStruct.point_y CStruct.update_point_y))) pval = Some (CStruct.point_y pval)\<close>
proof -
  have valid_vm: \<open>is_valid_lens_view_modify CStruct.point_y CStruct.update_point_y\<close>
    unfolding is_valid_lens_view_modify_def
  proof (intro conjI allI impI)
    fix f s
    show \<open>CStruct.point_y (CStruct.update_point_y f s) = f (CStruct.point_y s)\<close>
      by (cases s) simp
  next
    fix f s
    assume eq: \<open>f (CStruct.point_y s) = CStruct.point_y s\<close>
    show \<open>CStruct.update_point_y f s = s\<close>
    proof (cases s)
      case (make_point x1 x2)
      from eq make_point have \<open>f x2 = x2\<close>
        by simp
      then show ?thesis
        using make_point by (simp add: CStruct.point.record_simps CStruct.point.expand)
    qed
  next
    fix f g s
    show \<open>CStruct.update_point_y f (CStruct.update_point_y g s) = CStruct.update_point_y (\<lambda>x. f (g x)) s\<close>
      by (cases s) simp
  qed
  have valid: \<open>is_valid_lens (make_lens_via_view_modify CStruct.point_y CStruct.update_point_y)\<close>
    by (rule is_valid_lens_via_modifyI'[OF valid_vm])
  from lens_to_focus_raw_components'[OF valid] show ?thesis
    by (simp add: make_lens_via_view_modify_components)
qed

lemma c_swap_coords_spec:
  shows \<open>\<Gamma>; CStruct.swap_coords pref \<Turnstile>\<^sub>F c_swap_coords_contract pref pg pval\<close>
by (crush_boot f: CStruct.swap_coords_def contract: c_swap_coords_contract_def)
  (crush_base simp add: CStruct.point.record_simps)

end

end
