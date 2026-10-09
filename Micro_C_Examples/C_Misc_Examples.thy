theory C_Misc_Examples
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
    "Shallow_Micro_C.C_Arithmetic_Rules"
    C_Reference_Rules
begin

section \<open>Miscellaneous C Feature Tests\<close>

text \<open>
  Smoke tests for minor C frontend features: @{text "_Static_assert"},
  range case labels, @{text "_Alignas"}, @{text "__builtin_types_compatible_p"},
  and character constants.
\<close>

locale c_misc_verification_ctx =
    c_pointer_model c_ptr_add c_ptr_shift_signed c_ptr_diff c_ptr_less c_ptr_le c_ptr_greater c_ptr_ge
      c_ptr_to_uintptr c_uintptr_to_ptr +
    c_reference reference_types _ _ _ _ _ _ _ +
    ref_c_uint: c_reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_prism +
    ref_c_uint_ptr: c_reference_allocatable reference_types _ _ _ _ _ _ _ c_uint_ptr_prism +
    ref_c_int: c_reference_allocatable reference_types _ _ _ _ _ _ _ c_int_prism
  for c_ptr_add :: \<open>('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_shift_signed :: \<open>('addr, 'gv) gref \<Rightarrow> int \<Rightarrow> nat \<Rightarrow> ('addr, 'gv) gref\<close>
  and c_ptr_diff :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> nat \<Rightarrow> int\<close>
  and c_ptr_less :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_le :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_greater :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_ge :: \<open>('addr, 'gv) gref \<Rightarrow> ('addr, 'gv) gref \<Rightarrow> bool\<close>
  and c_ptr_to_uintptr :: \<open>('addr, 'gv) gref \<Rightarrow> int\<close>
  and c_uintptr_to_ptr :: \<open>int \<Rightarrow> ('addr, 'gv) gref\<close>
  and reference_types :: \<open>'s::{sepalg} \<Rightarrow> 'addr \<Rightarrow> 'gv \<Rightarrow> c_abort \<Rightarrow>
      'prompt::nondeterministic_prompt \<Rightarrow>
      'output::nondeterministic_response \<Rightarrow> unit\<close>
  and c_uint_prism :: \<open>('gv, c_uint) prism\<close>
  and c_uint_ptr_prism :: \<open>('gv, ('addr, 'gv, c_uint) State_References.ref) prism\<close>
  and c_int_prism :: \<open>('gv, c_int) prism\<close>
begin

adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_uint_ptr.new
adhoc_overloading store_reference_const \<rightleftharpoons> ref_c_int.new
adhoc_overloading store_update_const \<rightleftharpoons> update_fun

subsection \<open>Static Assert\<close>

c_source CMisc \<open>
  _Static_assert(sizeof(int) == 4, "int must be 32 bits");

  unsigned int static_assert_test(unsigned int x) {
    _Static_assert(1, "trivially true");
    return x + 1;
  }
\<close>

definition c_static_assert_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_static_assert_test_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_static_assert_test_contract

lemma c_static_assert_test_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.static_assert_test x \<Turnstile>\<^sub>F c_static_assert_test_contract x\<close>
by (crush_boot f: CMisc.static_assert_test_def contract: c_static_assert_test_contract_def)
   (crush_base simp add: c_unsigned_add_def)

subsection \<open>Range Case Labels\<close>

c_source CMisc \<open>
  unsigned int range_case(unsigned int x) {
    unsigned int result;
    switch (x) {
      case 1 ... 5:
        result = 1;
        break;
      case 10 ... 20:
        result = 2;
        break;
      default:
        result = 0;
        break;
    }
    return result;
  }
\<close>

definition c_range_case_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_range_case_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star>
               \<langle>r = (if 1 \<le> x \<and> x \<le> 5 then 1
                     else if 10 \<le> x \<and> x \<le> 20 then 2
                     else 0)\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_range_case_contract

lemma c_range_case_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.range_case x \<Turnstile>\<^sub>F c_range_case_contract x\<close>
by (crush_boot f: CMisc.range_case_def contract: c_range_case_contract_def)
   crush_base

subsection \<open>Alignas Specifier\<close>

c_source CMisc \<open>
  unsigned int alignas_test(unsigned int x) {
    _Alignas(16) unsigned int y = x + 1;
    return y;
  }
\<close>

definition c_alignas_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_alignas_test_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = x + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_alignas_test_contract

lemma c_alignas_test_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.alignas_test x \<Turnstile>\<^sub>F c_alignas_test_contract x\<close>
by (crush_boot f: CMisc.alignas_test_def contract: c_alignas_test_contract_def)
   (crush_base simp add: c_unsigned_add_def)

subsection \<open>Builtin Types Compatible\<close>

c_source CMisc \<open>
  unsigned int types_compat_test(unsigned int x) {
    if (__builtin_types_compatible_p(unsigned int, unsigned int))
      return x;
    else
      return 0;
  }
\<close>

definition c_types_compat_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_types_compat_test_contract x \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = x\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_types_compat_test_contract

lemma c_types_compat_test_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.types_compat_test x \<Turnstile>\<^sub>F c_types_compat_test_contract x\<close>
by (crush_boot f: CMisc.types_compat_test_def contract: c_types_compat_test_contract_def)
   crush_base

subsection \<open>Character Constants\<close>

c_source CMisc \<open>
  int char_val(void) {
    return 'A';
  }
\<close>

definition c_char_val_contract :: \<open>('s::{sepalg}, c_int, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_char_val_contract \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = 65\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_char_val_contract

lemma c_char_val_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.char_val \<Turnstile>\<^sub>F c_char_val_contract\<close>
by (crush_boot f: CMisc.char_val_def contract: c_char_val_contract_def)
   crush_base

subsection \<open>Register Storage Class\<close>

c_source CMisc \<open>
  typedef unsigned int register_uint_t;
  unsigned int register_add(register register_uint_t x) {
    register unsigned int y = x + 1;
    return y;
  }
\<close>

definition c_register_add_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_register_add_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = x + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_register_add_contract

lemma c_register_add_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.register_add x \<Turnstile>\<^sub>F c_register_add_contract x\<close>
by (crush_boot f: CMisc.register_add_def contract: c_register_add_contract_def)
   (crush_base simp add: c_unsigned_add_def)

subsection \<open>Builtin Offsetof\<close>

c_source CMisc \<open>
  struct offset_test { int a; int b; };
  typedef unsigned long offset_size_t;
  offset_size_t offset_of_b(void) {
    return __builtin_offsetof(struct offset_test, b);
  }
\<close>

definition c_offset_of_b_contract :: \<open>('s::{sepalg}, c_ulong, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_offset_of_b_contract \<equiv>
    let pre  = \<langle>True\<rangle>;
        post = \<lambda>r. \<langle>r = 4\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_offset_of_b_contract

lemma c_offset_of_b_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.offset_of_b \<Turnstile>\<^sub>F c_offset_of_b_contract\<close>
by (crush_boot f: CMisc.offset_of_b_def contract: c_offset_of_b_contract_def)
   crush_base

subsection \<open>Range Designators\<close>

c_source CMisc \<open>
  static unsigned int range_arr[4] = { [0 ... 1] = 10, [2 ... 3] = 20 };
  unsigned int range_test(unsigned int i) {
    return range_arr[i];
  }
\<close>

definition c_range_test_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_range_test_contract i \<equiv>
    let pre  = \<langle>i = 0\<rangle>;
        post = \<lambda>r. \<langle>r = 10\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_range_test_contract

lemma c_range_test_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.range_test i \<Turnstile>\<^sub>F c_range_test_contract i\<close>
by (crush_boot f: CMisc.range_test_def contract: c_range_test_contract_def)
   crush_base

subsection \<open>Struct Compound Literal\<close>

c_source CMiscNat [addr = nat] \<open>
  struct compound_lit_pair { int x; int y; };
  void compound_lit_write(struct compound_lit_pair *out) {
    *out = (struct compound_lit_pair){3, 7};
  }
\<close>

thm CMiscNat.compound_lit_write_def

subsection \<open>Statement Expression\<close>

c_source CMisc \<open>
  unsigned int stmt_expr_add(unsigned int x) {
    return ({
      unsigned int r = x + 1;
      r;
    });
  }
\<close>

definition c_stmt_expr_add_contract :: \<open>c_uint \<Rightarrow> ('s::{sepalg}, c_uint, 'b) function_contract\<close> where
  [crush_contracts]: \<open>c_stmt_expr_add_contract x \<equiv>
    let pre  = can_alloc_reference;
        post = \<lambda>r. can_alloc_reference \<star> \<langle>r = x + 1\<rangle>
     in make_function_contract pre post\<close>
ucincl_auto c_stmt_expr_add_contract

lemma c_stmt_expr_add_spec [crush_specs]:
  shows \<open>\<Gamma>; CMisc.stmt_expr_add x \<Turnstile>\<^sub>F c_stmt_expr_add_contract x\<close>
by (crush_boot f: CMisc.stmt_expr_add_def contract: c_stmt_expr_add_contract_def)
   (crush_base simp add: c_unsigned_add_def)

end

end
