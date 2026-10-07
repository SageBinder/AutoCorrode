theory C_Translation_Smoke_Core
  imports
    C_To_Core_Translation
begin

section \<open>Core Translation Smoke\<close>

c_source "C" \<open>
void smoke_core_void(void) {
  return;
}
\<close>

thm C.smoke_core_void_def

c_source "C" \<open>
int smoke_core_const(void) {
  return 42;
}
\<close>

thm C.smoke_core_const_def

c_source "C" \<open>
void smoke_core_assign(void) {
  int x = 5;
  x = x + 1;
}
\<close>

thm C.smoke_core_assign_def

c_source "C" \<open>
int smoke_core_if(int a, int b) {
  if (a > b) {
    return a;
  } else {
    return b;
  }
}
\<close>

thm C.smoke_core_if_def

c_source "C" \<open>
int smoke_core_add(int a, int b) {
  return a + b;
}
\<close>

c_source "C" \<open>
int smoke_core_add_three(int x, int y, int z) {
  return smoke_core_add(smoke_core_add(x, y), z);
}
\<close>

thm C.smoke_core_add_def C.smoke_core_add_three_def

c_source "C" \<open>
unsigned int smoke_core_comma(unsigned int a, unsigned int b) {
  unsigned int x = (a, b);
  return x;
}
\<close>

thm C.smoke_core_comma_def

c_source "C" \<open>
unsigned int smoke_core_multi_decl(unsigned int a, unsigned int b) {
  unsigned int x = a, y = b;
  return x;
}
\<close>

thm C.smoke_core_multi_decl_def

end
