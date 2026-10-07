theory C_Command_Contract_Smoke
  imports "Micro_C_Parsing_Frontend.C_To_Core_Translation"
begin

section \<open>ABI and compiler profiles\<close>

c_source abi_lp64_le [abi = lp64-le, compiler = default] \<open>
  unsigned int probe(void) { return sizeof(long); }
\<close>

c_source abi_ilp32_le [abi = ilp32-le, compiler = gcc-x86_64] \<open>
  unsigned int probe(void) { return sizeof(long); }
\<close>

c_source abi_lp64_be [abi = lp64-be, compiler = clang-x86_64] \<open>
  unsigned int probe(void) { return sizeof(long); }
\<close>

c_source abi_llp64_le [abi = llp64-le, compiler = gcc-aarch64] \<open>
  unsigned int probe(void) { return sizeof(long); }
\<close>

c_source abi_ilp32_be [abi = ilp32-be, compiler = clang-aarch64] \<open>
  unsigned int probe(void) { return sizeof(long); }
\<close>

c_source compiler_conservative [compiler = conservative] \<open>
  unsigned int probe(void) { return sizeof(long); }
\<close>

lemma abi_and_compiler_profile_values:
  shows "abi_lp64_le.abi_pointer_bits = 64"
    and "abi_lp64_le.abi_long_bits = 64"
    and "abi_lp64_le.abi_big_endian = False"
    and "abi_lp64_le.abi_char_is_signed = False"
    and "abi_ilp32_le.abi_pointer_bits = 32"
    and "abi_ilp32_le.abi_long_bits = 32"
    and "abi_ilp32_le.abi_big_endian = False"
    and "abi_ilp32_le.abi_char_is_signed = True"
    and "abi_lp64_be.abi_pointer_bits = 64"
    and "abi_lp64_be.abi_long_bits = 64"
    and "abi_lp64_be.abi_big_endian = True"
    and "abi_lp64_be.abi_char_is_signed = True"
    and "abi_llp64_le.abi_pointer_bits = 64"
    and "abi_llp64_le.abi_long_bits = 32"
    and "abi_llp64_le.abi_big_endian = False"
    and "abi_llp64_le.abi_char_is_signed = False"
    and "abi_ilp32_be.abi_pointer_bits = 32"
    and "abi_ilp32_be.abi_long_bits = 32"
    and "abi_ilp32_be.abi_big_endian = True"
    and "abi_ilp32_be.abi_char_is_signed = False"
    and "compiler_conservative.abi_char_is_signed = False"
  by (simp_all add:
      abi_lp64_le.abi_pointer_bits_def
      abi_lp64_le.abi_long_bits_def
      abi_lp64_le.abi_big_endian_def
      abi_lp64_le.abi_char_is_signed_def
      abi_ilp32_le.abi_pointer_bits_def
      abi_ilp32_le.abi_long_bits_def
      abi_ilp32_le.abi_big_endian_def
      abi_ilp32_le.abi_char_is_signed_def
      abi_lp64_be.abi_pointer_bits_def
      abi_lp64_be.abi_long_bits_def
      abi_lp64_be.abi_big_endian_def
      abi_lp64_be.abi_char_is_signed_def
      abi_llp64_le.abi_pointer_bits_def
      abi_llp64_le.abi_long_bits_def
      abi_llp64_le.abi_big_endian_def
      abi_llp64_le.abi_char_is_signed_def
      abi_ilp32_be.abi_pointer_bits_def
      abi_ilp32_be.abi_long_bits_def
      abi_ilp32_be.abi_big_endian_def
      abi_ilp32_be.abi_char_is_signed_def
      compiler_conservative.abi_char_is_signed_def)

section \<open>Repeated unit extension\<close>

c_source extension [abi = lp64-le, compiler = conservative] \<open>
  unsigned int first(void) { return 1; }
\<close>

c_source extension [abi = lp64-le, compiler = conservative] \<open>
  unsigned int second(void) { return 2; }
\<close>

thm extension.first_def
thm extension.second_def
thm extension.abi_pointer_bits_def

section \<open>Quoted keyword unit name\<close>

c_source "locale" \<open>
  unsigned int keyword_probe(void) { return 3; }
\<close>

ML \<open>
  val _ =
    Proof_Context.read_const {proper = true, strict = true} @{context}
      "locale.keyword_probe"
\<close>

section \<open>Inline selection\<close>

c_source inline_selection
  [types = [kept_record], functions = [kept_function]]
\<open>
  struct kept_record { unsigned int value; };
  struct omitted_record { unsigned int value; };

  unsigned int kept_function(void) { return 4; }
  unsigned int omitted_function(void) { return 5; }
\<close>

thm inline_selection.kept_record.record_simps
thm inline_selection.kept_function_def

ML \<open>
  fun assert_no_const name =
    if can (Proof_Context.read_const {proper = true, strict = true} @{context}) name
    then error ("unexpected generated constant: " ^ quote name)
    else ()

  fun assert_no_type name =
    if can (Proof_Context.read_type_name {proper = true, strict = true} @{context}) name
    then error ("unexpected generated type: " ^ quote name)
    else ()

  val _ = assert_no_const "inline_selection.omitted_function"
  val _ = assert_no_type "inline_selection.omitted_record"
\<close>

section \<open>File and manifest dependencies\<close>

c_file file_selection [manifest = "c_command_contract_manifest.txt"]
  "c_command_contract_file.c"

thm file_selection.file_record.record_simps
thm file_selection.file_keep_def

ML \<open>
  val _ = assert_no_const "file_selection.file_drop"
  val _ = assert_no_type "file_selection.omitted_file_record"
\<close>

text \<open>
  The source and manifest arguments above are parsed as Isabelle resource files.
  Successful elaboration checks both loads; the command records both file digests
  with Isabelle's resource database, and the positive and negative name checks
  establish that the manifest affects generated declarations.
\<close>

section \<open>Locale-target invocation and struct generation\<close>

locale command_contract_locale =
  fixes locale_token :: 'token
begin

c_source locale_struct [abi = lp64-le, compiler = default] \<open>
  struct locale_record {
    unsigned int value;
    unsigned int tag;
  };

  unsigned int locale_record_size(void) {
    return sizeof(struct locale_record);
  }
\<close>

thm locale_struct.locale_record.record_simps
thm locale_struct.locale_record_size_def

end

section \<open>Negative and failure-atomicity coverage\<close>

text \<open>
  This standalone smoke theory deliberately does not emulate failing commands
  through @{ML Outer_Syntax.parse_text}.  A failed top-level transition does not
  return the partially evaluated state, so inspecting the original theory would
  only prove that the test discarded the transition.  It would not detect leaked
  parser-thread configuration or distinguish command transactionality from the
  top-level driver's rollback.  Robust negative atomicity coverage needs either a
  command-level planning API whose result can be inspected before installation,
  or child-session tests whose expected outcome is failure.
\<close>

end
