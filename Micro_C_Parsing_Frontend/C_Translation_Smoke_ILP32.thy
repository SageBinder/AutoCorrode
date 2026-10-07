theory C_Translation_Smoke_ILP32
  imports
    C_To_Core_Translation
begin

section \<open>ILP32 Arithmetic Conversion Smoke Tests\<close>

text \<open>
  Regression tests for C11-compliant @{text "usual_arith_conv"} under ILP32,
  where @{text "long"} is 32-bit and @{text "long long"} is 64-bit.

  \<^item> @{text "type_rank"}: @{text "CLongLong"} must rank strictly above @{text "CLong"}
    (C11 \<section>6.3.1.1p1). Without this, @{text "long + long long"} returns the
    narrower @{text "long"} type.

  \<^item> @{text "usual_arith_conv"} mixed-signedness: when the signed operand has
    higher rank but NOT strictly more bits (e.g.\ 32-bit @{text "long"} vs.\
    32-bit @{text "unsigned int"}), C11 \<section>6.3.1.8 rule 3 requires converting to
    the unsigned type, not the signed one.
\<close>

subsection \<open>Rank ordering: \<^verbatim>\<open>long\<close> vs \<^verbatim>\<open>long long\<close>\<close>

text \<open>
  Under ILP32, @{text "long"} is 32-bit and @{text "long long"} is 64-bit.
  The result of @{text "long + long long"} must be @{text "long long"} (64-bit).
  A buggy @{text "type_rank"} that gives both the same rank would return @{text "long"}
  (32-bit), silently losing precision.
\<close>

c_source ilp32 [abi = ilp32-le] \<open>
long long add_long_longlong(long a, long long b) {
  return a + b;
}
\<close>

thm ilp32.add_long_longlong_def

text \<open>Same test for unsigned variants.\<close>

c_source ilp32 [abi = ilp32-le] \<open>
/*
 * Isabelle/C 2025-2 rejects unsigned long long in a parameter declarator
 * during its environment-markup pass, before returning the AST.  This typedef
 * is type-equivalent and keeps the frontend rank/conversion check buildable.
 */
typedef unsigned long long ilp32_ulonglong_t;
ilp32_ulonglong_t add_ulong_ulonglong(unsigned long a, ilp32_ulonglong_t b) {
  return a + b;
}
\<close>

thm ilp32.add_ulong_ulonglong_def

subsection \<open>Mixed-signedness bit-width check\<close>

text \<open>
  Under ILP32, @{text "unsigned int"} (32-bit) and @{text "long"} (32-bit signed)
  have the same width. C11 \<section>6.3.1.8 rule 3: since the signed type cannot represent
  all unsigned values, convert to the unsigned counterpart (@{text "unsigned long"}).
  A buggy implementation that skips the bit-width check would return @{text "long"}
  (signed), silently changing the signedness of the result.
\<close>

c_source ilp32 [abi = ilp32-le] \<open>
unsigned long add_uint_long(unsigned int a, long b) {
  return a + b;
}
\<close>

thm ilp32.add_uint_long_def

subsection \<open>ABI sanity checks\<close>

c_source ilp32 [abi = ilp32-le] \<open>
unsigned int sizeof_long(void) { return sizeof(long); }
unsigned int sizeof_ptr(void) { return sizeof(int *); }
unsigned int sizeof_longlong(void) { return sizeof(long long); }
\<close>

thm ilp32.sizeof_long_def
thm ilp32.sizeof_ptr_def
thm ilp32.sizeof_longlong_def

lemma ilp32_abi_profile_values:
  shows "ilp32.abi_pointer_bits = 32"
    and "ilp32.abi_long_bits = 32"
    and "ilp32.abi_big_endian = False"
  by (simp_all add: ilp32.abi_pointer_bits_def ilp32.abi_long_bits_def ilp32.abi_big_endian_def)

section \<open>LLP64 (Windows) ABI Smoke Tests\<close>

text \<open>
  Under LLP64 (Windows x64), @{text "long"} is 32-bit but pointers are 64-bit.
  This distinguishes LLP64 from LP64 (where @{text "long"} is 64-bit) and from
  ILP32 (where pointers are 32-bit).
\<close>

c_source llp64 [abi = llp64-le] \<open>
long long add_long_longlong(long a, long long b) {
  return a + b;
}
\<close>

thm llp64.add_long_longlong_def

c_source llp64 [abi = llp64-le] \<open>
unsigned int sizeof_long(void) { return sizeof(long); }
unsigned int sizeof_ptr(void) { return sizeof(int *); }
unsigned int sizeof_longlong(void) { return sizeof(long long); }
\<close>

thm llp64.sizeof_long_def
thm llp64.sizeof_ptr_def
thm llp64.sizeof_longlong_def

lemma llp64_abi_profile_values:
  shows "llp64.abi_pointer_bits = 64"
    and "llp64.abi_long_bits = 32"
    and "llp64.abi_big_endian = False"
  by (simp_all add: llp64.abi_pointer_bits_def llp64.abi_long_bits_def llp64.abi_big_endian_def)

section \<open>ILP32-BE (32-bit Big-Endian) ABI Smoke Tests\<close>

c_source ilp32be [abi = ilp32-be] \<open>
unsigned int sizeof_long(void) { return sizeof(long); }
unsigned int sizeof_ptr(void) { return sizeof(int *); }
\<close>

thm ilp32be.sizeof_long_def
thm ilp32be.sizeof_ptr_def

lemma ilp32be_abi_profile_values:
  shows "ilp32be.abi_pointer_bits = 32"
    and "ilp32be.abi_long_bits = 32"
    and "ilp32be.abi_big_endian = True"
  by (simp_all add: ilp32be.abi_pointer_bits_def ilp32be.abi_long_bits_def ilp32be.abi_big_endian_def)

end
