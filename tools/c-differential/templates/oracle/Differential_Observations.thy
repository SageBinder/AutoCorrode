theory Differential_Observations
  imports
    "Micro_C_Parsing_Frontend.C_To_Core_Translation"
begin

micro_c_translate \<open>
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

micro_c_translate prefix: diff32_ abi: ilp32-le \<open>
  unsigned int diff_sizeof_long(void) { return sizeof(long); }
\<close>

micro_c_translate prefix: diffbe_ abi: lp64-be \<open>
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
  shows "diff32_abi_pointer_bits = 32"
    and "diff32_abi_long_bits = 32"
    and "diff32_abi_big_endian = False"
    and "diffbe_abi_pointer_bits = 64"
    and "diffbe_abi_big_endian = True"
  by (simp_all add: diff32_abi_pointer_bits_def diff32_abi_long_bits_def
      diff32_abi_big_endian_def diffbe_abi_pointer_bits_def
      diffbe_abi_big_endian_def)

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
  val _ = emit_type "const" "c_diff_const"
  val _ = emit_type "unsigned-add" "c_diff_add"
  val _ = emit_type "conditional" "c_diff_choose"
  val _ = emit_type "bitwise-and" "c_diff_and"
  val _ = emit_type "signed-add" "c_diff_signed_add"
  val _ = emit_type "unsigned-div" "c_diff_div"
  val _ = emit_type "unsigned-shift" "c_diff_shl"
  val _ = emit_contract "max" "c_diff_choose_def"
  val _ = emit_contract "signed-overflow" "c_diff_signed_add_def"
  val _ = emit_contract "division-by-zero" "c_diff_div_def"
  val _ = emit_contract "shift-out-of-range" "c_diff_shl_def"
end
\<close>

end
