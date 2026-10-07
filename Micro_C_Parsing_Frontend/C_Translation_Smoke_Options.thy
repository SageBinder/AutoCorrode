theory C_Translation_Smoke_Options
  imports
    C_To_Core_Translation
    "Shallow_State_Logic.Separation_Algebra"
begin

section \<open>\<^verbatim>\<open>c_source\<close> Unit Smoke\<close>

c_source smoke [types = all, functions = all] \<open>
  struct counter {
    unsigned int value;
  };

  unsigned int bump(struct counter *c) {
    c->value = c->value + 1;
    return c->value;
  }
\<close>

thm smoke.bump_def
thm smoke.counter.record_simps
thm smoke.abi_pointer_bits_def
thm smoke.abi_long_bits_def
thm smoke.abi_char_is_signed_def
thm smoke.abi_big_endian_def

section \<open>\<^verbatim>\<open>c_source\<close> ABI Smoke\<close>

c_source smoke32 [abi = ilp32-le] \<open>
  unsigned int size_long(void) { return sizeof(long); }
  unsigned int size_ptr(void) { return sizeof(int *); }
  unsigned int align_long(void) { return _Alignof(long); }
\<close>

thm smoke32.size_long_def
thm smoke32.size_ptr_def
thm smoke32.align_long_def
thm smoke32.abi_pointer_bits_def
thm smoke32.abi_long_bits_def
thm smoke32.abi_big_endian_def

lemma smoke32_abi_profile_values:
  shows "smoke32.abi_pointer_bits = 32"
    and "smoke32.abi_long_bits = 32"
    and "smoke32.abi_big_endian = False"
  by (simp_all add: smoke32.abi_pointer_bits_def smoke32.abi_long_bits_def smoke32.abi_big_endian_def)

section \<open>\<^verbatim>\<open>c_source\<close> Big-Endian ABI Smoke\<close>

c_source smokebe [abi = lp64-be] \<open>
  unsigned long size_ptr(void) { return sizeof(int *); }
\<close>

thm smokebe.size_ptr_def
thm smokebe.abi_pointer_bits_def
thm smokebe.abi_long_bits_def
thm smokebe.abi_big_endian_def

lemma smokebe_abi_profile_values:
  shows "smokebe.abi_pointer_bits = 64"
    and "smokebe.abi_long_bits = 64"
    and "smokebe.abi_big_endian = True"
  by (simp_all add: smokebe.abi_pointer_bits_def smokebe.abi_long_bits_def smokebe.abi_big_endian_def)

section \<open>Inline Selection Smoke\<close>

c_source selected
  [types = [selected_record], functions = [selected_add]]
\<open>
  struct selected_record { unsigned int value; };
  struct omitted_record { unsigned int value; };

  unsigned int selected_add(unsigned int x) { return x + 1; }
  unsigned int omitted_add(unsigned int x) { return x + 2; }
\<close>

thm selected.selected_record.record_simps
thm selected.selected_add_def

ML \<open>
  val ctxt = @{context}
  val _ =
    if can (Proof_Context.read_const {proper = true, strict = true} ctxt)
         "selected.omitted_add"
    then error "inline function selection failed"
    else ()
  val _ =
    if can (Proof_Context.read_type_name {proper = true, strict = true} ctxt)
         "selected.omitted_record"
    then error "inline type selection failed"
    else ()
\<close>

section \<open>\<^verbatim>\<open>c_file\<close> Unit and Manifest Smoke\<close>

c_file smoke [manifest = "smoke_manifest.txt"] "smoke_manifest_file.c"

thm smoke.keep_add_def
thm smoke.poly_get0_def
thm smoke.poly_t.record_simps

ML \<open>
  val _ =
    ((Proof_Context.read_const {proper = true, strict = true} @{context} "smoke.drop_mul"; error "manifest filtering failed")
      handle ERROR _ => ());
\<close>

section \<open>Two-Phase Type-Then-Function Smoke\<close>

c_file smoke_split [manifest = "smoke_manifest_types.txt"] "smoke_manifest_file_types_phase1.c"

c_file smoke_split [addr = 'addr, gv = 'gv, manifest = "smoke_manifest_phase2.txt"]
  "smoke_manifest_file_types_phase2.c"

thm smoke_split.poly_get0_def
thm smoke_split.poly_t.record_simps

section \<open>\<^verbatim>\<open>c_file\<close> ABI Smoke\<close>

c_file smoke32_file [abi = ilp32-le, manifest = "smoke_manifest_abi.txt"]
  "smoke_manifest_file_abi.c"

thm smoke32_file.keep_add_def
thm smoke32_file.poly_get0_def
thm smoke32_file.poly_t.record_simps
thm smoke32_file.abi_pointer_bits_def
thm smoke32_file.abi_long_bits_def
thm smoke32_file.abi_big_endian_def

section \<open>Custom abort-handler semantics\<close>

datatype routed_c_abort = Routed_C_Abort c_abort

definition route_c_abort ::
    \<open>c_abort \<Rightarrow> ('s, 'v, 'r, routed_c_abort, 'i, 'o) expression\<close> where
  \<open>route_c_abort reason \<equiv> abort (CustomAbort (Routed_C_Abort reason))\<close>

lemma c_signed_add_with_abort_routes:
  fixes handler ::
    \<open>c_abort \<Rightarrow> ('s, c_int, 'r, 'abort, 'i, 'o) expression\<close>
  shows
    \<open>c_signed_add_with_abort handler
       (word_of_int 2147483647 :: c_int) 1 =
       handler SignedOverflow\<close>
  by (simp add: c_signed_add_with_abort_def)

lemma c_unsigned_div_with_abort_routes:
  fixes handler ::
    \<open>c_abort \<Rightarrow> ('s, c_uint, 'r, 'abort, 'i, 'o) expression\<close>
  shows
    \<open>c_unsigned_div_with_abort handler (1 :: c_uint) 0 =
       handler DivisionByZero\<close>
  by (simp add: c_unsigned_div_with_abort_def)

c_source custom_abort_semantics
  [compiler = conservative, abort = route_c_abort]
\<open>
  int signed_add(int x, int y) { return x + y; }
  unsigned int unsigned_div(unsigned int x, unsigned int y) { return x / y; }
  int signed_shift(int x, int y) { return x << y; }
  signed char narrow(int x) { return (signed char)x; }
  int indexed(int values[4], int i) { return values[i]; }
\<close>

ML \<open>
  fun generated_const name =
    Proof_Context.read_const {proper = true, strict = true} @{context}
      ("custom_abort_semantics." ^ name)

  fun definition_constants thm =
    Term.add_const_names (Thm.prop_of thm) []

  fun contains_base base =
    List.exists (fn name => Long_Name.base_name name = base)

  fun assert_routes thm operation =
    let
      val constants = definition_constants thm
      val _ =
        if contains_base "route_c_abort" constants then ()
        else error ("generated operation omits custom abort handler: " ^ operation)
      val _ =
        if contains_base operation constants then ()
        else error ("generated operation omits abort-aware primitive: " ^ operation)
      val _ =
        if contains_base "c_abort" constants orelse
           contains_base "c_bounds_abort" constants
        then error ("generated operation retains a default abort path: " ^ operation)
        else ()
    in () end

  val _ =
    assert_routes @{thm custom_abort_semantics.signed_add_def}
      "c_signed_add_with_abort"
  val _ =
    assert_routes @{thm custom_abort_semantics.unsigned_div_def}
      "c_unsigned_div_with_abort"
  val _ =
    assert_routes @{thm custom_abort_semantics.signed_shift_def}
      "c_signed_shl_with_abort"
  val _ =
    assert_routes @{thm custom_abort_semantics.narrow_def}
      "c_scast_checked_with_abort"

  val indexed_constants =
    definition_constants @{thm custom_abort_semantics.indexed_def}
  val _ =
    if contains_base "route_c_abort" indexed_constants andalso
       contains_base "BufferOverflow" indexed_constants andalso
       not (contains_base "c_bounds_abort" indexed_constants)
    then ()
    else error "generated array bounds check does not route BufferOverflow"

  val _ =
    List.app
      (fn name =>
        let val ty = fastype_of (generated_const name)
        in
          if String.isSubstring "routed_c_abort"
               (Syntax.string_of_typ @{context} ty)
          then ()
          else error ("custom abort type was not propagated to " ^ name)
        end)
      ["signed_add", "unsigned_div", "signed_shift", "narrow", "indexed"]
\<close>

end
