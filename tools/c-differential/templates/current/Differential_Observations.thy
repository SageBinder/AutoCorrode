theory Differential_Observations
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
begin

c_source DiffUnit \<open>
  int diff_const(void) { return 42; }
  unsigned int diff_add(unsigned int a, unsigned int b) { return a + b; }
  unsigned int diff_choose(unsigned int a, unsigned int b) {
    return a > b ? a : b;
  }
  unsigned int diff_and(unsigned int a, unsigned int b) { return a & b; }
  int diff_signed_add(int a, int b) { return a + b; }
  unsigned int diff_div(unsigned int a, unsigned int b) { return a / b; }
  unsigned int diff_shl(unsigned int a, unsigned int b) { return a << b; }
\<close>

c_source Diff32 [abi = ilp32-le] \<open>
  unsigned int diff_sizeof_long(void) { return sizeof(long); }
\<close>

c_source DiffBE [abi = lp64-be] \<open>
  unsigned long diff_sizeof_pointer(void) { return sizeof(void *); }
\<close>

lemma differential_eval_trunc_div:
  "c_trunc_div_int (-7) 3 = -2"
  by eval

lemma differential_eval_unsigned_wrap:
  "evaluate (c_unsigned_add (4294967295 :: c_uint) 1) () =
    Success (0 :: c_uint) ()"
  by (simp add: c_unsigned_add_def evaluate_def literal_def)

lemma differential_eval_unsigned_div:
  "evaluate (c_unsigned_div (7 :: c_uint) 3) () =
    Success (2 :: c_uint) ()"
  by (simp add: c_unsigned_div_def evaluate_def literal_def)

lemma differential_eval_division_by_zero:
  "evaluate (c_unsigned_div (7 :: c_uint) 0) () =
    Abort (CustomAbort DivisionByZero) ()"
  by (simp add: c_unsigned_div_def c_abort_def evaluate_def abort_def)

lemma differential_eval_signed_add:
  "evaluate (c_signed_add (20 :: c_int) 22) () =
    Success (42 :: c_int) ()"
  by (simp add: c_signed_add_def evaluate_def literal_def)

lemma differential_eval_signed_overflow:
  "evaluate (c_signed_add (2147483647 :: c_int) 1) () =
    Abort (CustomAbort SignedOverflow) ()"
  by (simp add: c_signed_add_def c_signed_overflow_def c_abort_def
      evaluate_def abort_def)

lemma differential_abi_values:
  shows "Diff32.abi_pointer_bits = 32"
    and "Diff32.abi_long_bits = 32"
    and "Diff32.abi_big_endian = False"
    and "DiffBE.abi_pointer_bits = 64"
    and "DiffBE.abi_big_endian = True"
  by (simp_all add: Diff32.abi_pointer_bits_def Diff32.abi_long_bits_def
      Diff32.abi_big_endian_def DiffBE.abi_pointer_bits_def
      DiffBE.abi_big_endian_def)

ML \<open>
local
  val ctxt = @{context}

  fun emit kind key value =
    writeln ("ACDIFF|" ^ kind ^ "|" ^ key ^ "|" ^ value)

  fun emit_type key name =
    let
      val term =
        Proof_Context.read_const {proper = true, strict = true} ctxt name
      val text =
        Pretty.string_of_margin 100000
          (Syntax.pretty_typ ctxt (fastype_of term))
    in emit "signature" key text end

  fun emit_contract key name =
    let
      val theorem = Proof_Context.get_thm ctxt name
      val constants =
        Term.add_const_names (Thm.prop_of theorem) []
        |> map Long_Name.base_name
      fun has candidate = member (op =) constants candidate
      fun require_any candidates =
        if exists has candidates then ()
        else error ("generated definition violates contract " ^ quote key ^
          ": expected one of " ^ commas_quote candidates)
      val _ =
        (case key of
           "max" => require_any ["c_unsigned_less"]
         | "signed-overflow" =>
             require_any ["c_signed_add", "c_signed_add_with_abort"]
         | "division-by-zero" =>
             require_any ["c_unsigned_div", "c_unsigned_div_with_abort"]
         | "shift-out-of-range" =>
             require_any ["c_unsigned_shl", "c_unsigned_shl_with_abort"]
         | _ => error ("unknown generated contract: " ^ key))
    in emit "contract" key "lowering-and-semantics-pass" end
in
  val _ = emit "eval" "trunc-div-negative" "pass"
  val _ = emit "eval" "unsigned-wrap" "pass"
  val _ = emit "eval" "unsigned-div" "pass"
  val _ = emit "eval" "division-by-zero" "pass"
  val _ = emit "eval" "signed-add" "pass"
  val _ = emit "eval" "signed-overflow" "pass"
  val _ = emit "abi" "ilp32-pointer-bits" "32"
  val _ = emit "abi" "ilp32-long-bits" "32"
  val _ = emit "abi" "ilp32-big-endian" "false"
  val _ = emit "abi" "lp64be-pointer-bits" "64"
  val _ = emit "abi" "lp64be-big-endian" "true"
  val _ = emit_type "const" "DiffUnit.diff_const"
  val _ = emit_type "unsigned-add" "DiffUnit.diff_add"
  val _ = emit_type "conditional" "DiffUnit.diff_choose"
  val _ = emit_type "bitwise-and" "DiffUnit.diff_and"
  val _ = emit_type "signed-add" "DiffUnit.diff_signed_add"
  val _ = emit_type "unsigned-div" "DiffUnit.diff_div"
  val _ = emit_type "unsigned-shift" "DiffUnit.diff_shl"
  val _ = emit_contract "max" "DiffUnit.diff_choose_def"
  val _ =
    emit_contract "signed-overflow" "DiffUnit.diff_signed_add_def"
  val _ = emit_contract "division-by-zero" "DiffUnit.diff_div_def"
  val _ = emit_contract "shift-out-of-range" "DiffUnit.diff_shl_def"
end
\<close>

end
