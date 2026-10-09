(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Profile_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Complete ABI and compiler cross product\<close>

ML_val \<open>
local
  (* Expectations are independent of the production profile tables. *)
  val abis =
    [("lp64-le", 64, 64, false), ("ilp32-le", 32, 32, false),
     ("lp64-be", 64, 64, true), ("llp64-le", 64, 32, false),
     ("ilp32-be", 32, 32, true)]
  val compilers =
    [("default", false, false), ("gcc-x86_64", true, false),
     ("clang-x86_64", true, false), ("gcc-aarch64", false, false),
     ("clang-aarch64", false, false), ("conservative", false, true)]
  val text =
    "char character(char x) { return x; }\n" ^
    "long identity(long x) { return x; }\n" ^
    "int shift(int a, int b) { return a >> b; }\n" ^
    "signed char narrow(int a) { return (signed char)a; }\n" ^
    "unsigned int size_long(void) { return sizeof(long); }\n" ^
    "unsigned int size_pointer(void) { return sizeof(void *); }"

  fun check ((abi, pointer_bits, long_bits, big_endian),
      (compiler, char_signed, conservative)) =
    let
      val file = "profile-" ^ abi ^ "-" ^ compiler ^ ".c"
      val thy = C_Parser_Test.translate \<^theory> file "Profile"
        ("[abi = " ^ abi ^ ", compiler = " ^ compiler ^ "]") text
      val ctxt = Proof_Context.init_global thy
      fun nat name expected = C_Parser_Test.assert (file ^ ": " ^ name)
        (HOLogic.dest_nat (C_Parser_Test.rhs ctxt ("Profile." ^ name)) = expected)
      fun bool name expected = C_Parser_Test.assert (file ^ ": " ^ name)
        (C_Parser_Test.rhs ctxt ("Profile." ^ name) aconv
          (if expected then \<^term>\<open>True\<close> else \<^term>\<open>False\<close>))
      val _ = nat "abi_pointer_bits" pointer_bits
      val _ = nat "abi_long_bits" long_bits
      val _ = bool "abi_big_endian" big_endian
      val _ = bool "abi_char_is_signed" char_signed
      val _ = C_Parser_Test.require_arguments ctxt "Profile.character"
        [if char_signed then \<^typ>\<open>c_schar\<close> else \<^typ>\<open>c_char\<close>]
      val _ = C_Parser_Test.require_arguments ctxt "Profile.identity"
        [if long_bits = 64 then \<^typ>\<open>c_long\<close> else \<^typ>\<open>c_int\<close>]
      val _ = C_Parser_Test.require_consts ctxt "Profile.shift"
        [if conservative then \<^const_name>\<open>c_signed_shr_conservative_with_abort\<close>
         else \<^const_name>\<open>c_signed_shr_with_abort\<close>,
         \<^const_name>\<open>c_abort\<close>]
        [if conservative then \<^const_name>\<open>c_signed_shr_with_abort\<close>
         else \<^const_name>\<open>c_signed_shr_conservative_with_abort\<close>]
      val _ = C_Parser_Test.require_consts ctxt "Profile.narrow"
        [if conservative then \<^const_name>\<open>c_scast_checked_with_abort\<close>
         else \<^const_name>\<open>c_scast\<close>]
        [if conservative then \<^const_name>\<open>c_scast\<close>
         else \<^const_name>\<open>c_scast_checked_with_abort\<close>]
      val _ = C_Parser_Test.check_definitions ctxt "Profile"
        ["character", "identity", "shift", "narrow", "size_long", "size_pointer"]
      val _ = C_Parser_Test.evaluates ctxt "Profile.size_long"
        ("Success " ^ Int.toString (long_bits div 8))
      val _ = C_Parser_Test.evaluates ctxt "Profile.size_pointer"
        ("Success " ^ Int.toString (pointer_bits div 8))
      val _ = C_Parser_Test.evaluates ctxt "Profile.shift 8 1" "Success 4"
      val _ = C_Parser_Test.evaluates ctxt "Profile.shift (-8) 1"
        (if conservative then "Abort (CustomAbort SignedOverflow)" else "Success (-4)")
      val _ = C_Parser_Test.evaluates ctxt "Profile.narrow 127" "Success 127"
      val _ = C_Parser_Test.evaluates ctxt "Profile.narrow 128"
        (if conservative then "Abort (CustomAbort SignedOverflow)" else "Success (-128)")
    in () end
  val _ = List.app check (maps (fn abi => map (pair abi) compilers) abis)
in
  val _ = ()
end
\<close>

end
