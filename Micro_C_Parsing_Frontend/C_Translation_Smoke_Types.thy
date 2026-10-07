theory C_Translation_Smoke_Types
  imports
    C_To_Core_Translation
begin

section \<open>Type/Semantics Translation Smoke\<close>

c_source "C" \<open>
unsigned int smoke_types_u_add(unsigned int a, unsigned int b) {
  return a + b;
}
\<close>

thm C.smoke_types_u_add_def

c_source "C" \<open>
long smoke_types_l_add(long a, long b) {
  return a + b;
}
\<close>

thm C.smoke_types_l_add_def

c_source "C" \<open>
char smoke_types_identity_char(char c) {
  return c;
}
\<close>

thm C.smoke_types_identity_char_def

c_source "C" \<open>
unsigned int smoke_types_u_max(unsigned int a, unsigned int b) {
  if (a > b) return a;
  else return b;
}
\<close>

thm C.smoke_types_u_max_def

c_source "C" \<open>
unsigned char smoke_types_id_u8(unsigned char x) {
  return x;
}
\<close>

thm C.smoke_types_id_u8_def

c_source "C" \<open>
char smoke_types_char_lit(char c) {
  return 'A';
}
\<close>

thm C.smoke_types_char_lit_def

c_source "C" \<open>
_Bool smoke_types_bool(_Bool a, _Bool b) {
  if (a) return b;
  else return !a;
}
\<close>

thm C.smoke_types_bool_def

c_source "C" \<open>
int smoke_types_cast(unsigned int x) {
  return (int)x;
}
\<close>

thm C.smoke_types_cast_def

c_source "C" \<open>
enum smoke_types_color { SMOKE_RED = 0, SMOKE_GREEN = 1, SMOKE_BLUE = 2 };
unsigned int smoke_types_enum(void) {
  return SMOKE_GREEN;
}
\<close>

thm C.smoke_types_enum_def

c_source "C" \<open>
typedef unsigned int smoke_uint32;
smoke_uint32 smoke_types_typedef(smoke_uint32 a, smoke_uint32 b) {
  return a + b;
}
\<close>

thm C.smoke_types_typedef_def

c_source "C" \<open>
static unsigned int smoke_types_static(unsigned int x) { return x + 1; }
\<close>

thm C.smoke_types_static_def

c_source "C" \<open>
typedef unsigned short smoke_uint16_t;
smoke_uint16_t smoke_types_u16_add(smoke_uint16_t a, smoke_uint16_t b) { return a + b; }
\<close>

thm C.smoke_types_u16_add_def

c_source "C" \<open>
typedef int smoke_int32_t;
smoke_int32_t smoke_types_i32_negate(smoke_int32_t x) { return 0 - x; }
\<close>

thm C.smoke_types_i32_negate_def

c_source "C" \<open>
typedef unsigned long smoke_size_t;
smoke_size_t smoke_types_size_add(smoke_size_t a, smoke_size_t b) { return a + b; }
\<close>

thm C.smoke_types_size_add_def

c_source "C" \<open>
typedef short smoke_int16_t;
smoke_int16_t smoke_types_ret_helper(smoke_int16_t x) { return x; }
smoke_int16_t smoke_types_ret_caller(smoke_int16_t a, smoke_int16_t b) {
  return smoke_types_ret_helper(a) + smoke_types_ret_helper(b);
}
\<close>

thm C.smoke_types_ret_helper_def C.smoke_types_ret_caller_def

c_source "C" \<open>
/*
 * Isabelle/C 2025-2 rejects the equivalent spelling
 *   register unsigned int x
 * in its environment-markup pass, before its public parser service returns
 * the translation-unit AST.  Keep the storage-class form covered while using
 * a typedef to avoid that upstream parser limitation.
 */
typedef unsigned int smoke_register_uint_t;
unsigned int smoke_types_register(register smoke_register_uint_t x) {
  register smoke_register_uint_t y = x + 1;
  return y;
}
\<close>

thm C.smoke_types_register_def

c_source "C" \<open>
unsigned __int128 smoke_types_u128_add(unsigned __int128 a, unsigned __int128 b) {
  return a + b;
}
\<close>

thm C.smoke_types_u128_add_def

c_source "C" \<open>
__int128 smoke_types_i128_negate(__int128 x) {
  return 0 - x;
}
\<close>

thm C.smoke_types_i128_negate_def

c_source CNat [addr = nat] \<open>
/*
 * Isabelle/C 2025-2 likewise rejects volatile unsigned int in a parameter
 * declarator before exposing the AST.  The typedef preserves the same C type
 * and still exercises the volatile qualifier and pointer lowering.
 */
typedef unsigned int smoke_volatile_uint_t;
unsigned int smoke_types_volatile_read(volatile smoke_volatile_uint_t *p) {
  return *p;
}
\<close>

thm CNat.smoke_types_volatile_read_def

c_source "C" \<open>
unsigned int smoke_types_volatile_local(unsigned int x) {
  volatile unsigned int y = x + 1;
  return y;
}
\<close>

thm C.smoke_types_volatile_local_def

end
