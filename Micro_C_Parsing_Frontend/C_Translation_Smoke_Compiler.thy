theory C_Translation_Smoke_Compiler
  imports
    C_To_Core_Translation
begin

section \<open>Compiler Profile Smoke Tests\<close>

text \<open>Verify that @{text "compiler:"} parameter selects the expected behavior
  for char signedness, signed right shift, and signed narrowing casts.\<close>

subsection \<open>Char signedness\<close>

text \<open>Under @{text "gcc-x86_64"}, plain @{text "char"} is signed.\<close>

c_source comp_x86 [compiler = gcc-x86_64] \<open>
char comp_char_id(char c) { return c; }
\<close>

thm comp_x86.comp_char_id_def

text \<open>Under @{text "gcc-aarch64"}, plain @{text "char"} is unsigned.\<close>

c_source comp_arm [compiler = gcc-aarch64] \<open>
char comp_char_id(char c) { return c; }
\<close>

thm comp_arm.comp_char_id_def

subsection \<open>Signed right shift\<close>

text \<open>Under @{text "gcc-x86_64"}, signed right shift uses arithmetic (sign-extending) shift.\<close>

c_source comp_shr_gcc [compiler = gcc-x86_64] \<open>
int comp_shr(int a, int b) { return a >> b; }
\<close>

thm comp_shr_gcc.comp_shr_def

text \<open>Under @{text "conservative"}, signed right shift aborts on negative operand.\<close>

c_source comp_shr_con [compiler = conservative] \<open>
int comp_shr(int a, int b) { return a >> b; }
\<close>

thm comp_shr_con.comp_shr_def

subsection \<open>Signed narrowing cast\<close>

text \<open>Under @{text "conservative"}, signed narrowing cast checks for overflow.\<close>

c_source comp_cast_con [compiler = conservative] \<open>
int comp_narrow(long a) { return (int)a; }
\<close>

thm comp_cast_con.comp_narrow_def

text \<open>Under @{text "gcc-aarch64"}, signed narrowing cast silently truncates.\<close>

c_source comp_cast_gcc [compiler = gcc-aarch64] \<open>
int comp_narrow(long a) { return (int)a; }
\<close>

thm comp_cast_gcc.comp_narrow_def

ML_val \<open>
  let
    fun has_constant name theorem =
      Term.exists_subterm
        (fn Const (candidate, _) => candidate = name | _ => false)
        (Thm.prop_of theorem)

    fun require label expected forbidden theorem =
      if has_constant expected theorem andalso
         not (has_constant forbidden theorem)
      then ()
      else error ("compiler-profile semantic audit failed: " ^ label)

    fun require_abort_aware label expected forbidden legacy theorem =
      if has_constant expected theorem andalso
         has_constant \<^const_name>\<open>c_abort\<close> theorem andalso
         not (has_constant forbidden theorem) andalso
         not (has_constant legacy theorem)
      then ()
      else error ("compiler-profile abort-aware semantic audit failed: " ^ label)

    fun theorem name = Proof_Context.get_thm \<^context> name

    val _ =
      require_abort_aware "GCC signed shift"
        \<^const_name>\<open>c_signed_shr_with_abort\<close>
        \<^const_name>\<open>c_signed_shr_conservative_with_abort\<close>
        \<^const_name>\<open>c_signed_shr\<close>
        (theorem "comp_shr_gcc.comp_shr_def")
    val _ =
      require_abort_aware "conservative signed shift"
        \<^const_name>\<open>c_signed_shr_conservative_with_abort\<close>
        \<^const_name>\<open>c_signed_shr_with_abort\<close>
        \<^const_name>\<open>c_signed_shr_conservative\<close>
        (theorem "comp_shr_con.comp_shr_def")
    val _ =
      require "GCC signed narrowing"
        \<^const_name>\<open>c_scast\<close>
        \<^const_name>\<open>c_scast_checked_with_abort\<close>
        (theorem "comp_cast_gcc.comp_narrow_def")
    val _ =
      require_abort_aware "conservative signed narrowing"
        \<^const_name>\<open>c_scast_checked_with_abort\<close>
        \<^const_name>\<open>c_scast\<close>
        \<^const_name>\<open>c_scast_checked\<close>
        (theorem "comp_cast_con.comp_narrow_def")
  in
    ()
  end
\<close>

end
