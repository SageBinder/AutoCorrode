(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Semantics_Tests
  imports C_Parser_Expression_Tests C_Parser_Syntax_Tests C_Parser_Function_Tests
    C_Parser_Type_Tests
begin

section \<open>Generated programs with independently specified results\<close>

text \<open>
  These rows prove evaluations of freshly generated function definitions.
  They test both successful values and the exact abort reason, including signed
  boundary cases, C division truncation, wrapping, and skipped failing branches.
\<close>

c_source Semantics \<open>
  int short_and(int a) { return a && (1 / a); }
  int short_or(int a) { return a || (1 / a); }
  int skipped_conditional(int a) { return a ? 7 : (1 / a); }
  unsigned long unevaluated_sizeof(void) { return sizeof(1 / 0); }
  unsigned int unevaluated_generic(void) {
    return _Generic(1U, unsigned int: 7U, default: (1U / 0U));
  }
  int minimum(void) { return (-2147483647 - 1); }
\<close>

ML_val \<open>
local
  val _ = C_Parser_Test.check_definitions \<^context> "Semantics"
    ["short_and", "short_or", "skipped_conditional", "unevaluated_sizeof",
     "unevaluated_generic", "minimum"]
  val successes =
    [("Expressions.decimal", "42"),
     ("Expressions.hexadecimal", "42"),
     ("Expressions.octal", "42"),
     ("Expressions.character", "65"),
     ("Expressions.escaped_character", "10"),
     ("Expressions.add 4294967295 1", "0"),
     ("Expressions.sub 0 1", "4294967295"),
     ("Expressions.mul 2147483648 2", "0"),
     ("Expressions.divide 7 3", "2"),
     ("Expressions.modulo 7 3", "1"),
     ("Expressions.signed_add 20 22", "42"),
     ("Expressions.signed_sub 0 7", "-7"),
     ("Expressions.signed_mul (-7) 3", "-21"),
     ("Expressions.signed_divide (-7) 3", "-2"),
     ("Expressions.signed_divide 7 (-3)", "-2"),
     ("Expressions.signed_divide (-7) (-3)", "2"),
     ("Expressions.signed_modulo (-7) 3", "-1"),
     ("Expressions.signed_modulo 7 (-3)", "1"),
     ("Expressions.bit_and 10 12", "8"),
     ("Expressions.bit_or 10 12", "14"),
     ("Expressions.bit_xor 10 12", "6"),
     ("Expressions.complement 0", "4294967295"),
     ("Expressions.shift_left 1 31", "2147483648"),
     ("Expressions.shift_right 2147483648 31", "1"),
     ("Expressions.less (-1) 0", "1"),
     ("Expressions.less 0 (-1)", "0"),
     ("Expressions.less_equal 3 3", "1"),
     ("Expressions.greater 4 3", "1"),
     ("Expressions.greater_equal 3 3", "1"),
     ("Expressions.equal 3 3", "1"),
     ("Expressions.unequal 3 4", "1"),
     ("Expressions.logical_not 0", "1"),
     ("Expressions.logical_not 7", "0"),
     ("Expressions.logical_and 7 9", "1"),
     ("Expressions.logical_or 0 9", "1"),
     ("Expressions.unary_minus 7", "-7"),
     ("Expressions.choose 0 9", "9"),
     ("Expressions.choose 7 9", "7"),
     ("Expressions.comma 7 9", "9"),
     ("Expressions.narrow 256", "0"),
     ("Expressions.widen (-1)", "-1"),
     ("Expressions.size_type", "4"),
     ("Expressions.size_expression 0", "4"),
     ("Expressions.alignment", "4"),
     ("Expressions.generic 6", "7"),
     ("Expressions.compound_literal", "42"),
     ("Syntax.multiply", "7"),
     ("Syntax.multiply_alternative", "9"),
     ("Syntax.shift", "8"),
     ("Syntax.bitwise", "3"),
     ("Syntax.comparison", "1"),
     ("Syntax.logical", "0"),
     ("Syntax.subtract", "4"),
     ("Syntax.subtract_alternative", "8"),
     ("Syntax.conditional", "2"),
     ("Syntax.cast_prefix", "4294967295"),
     ("Syntax.commented", "3"),
     ("Syntax.dangling_else 0 1", "3"),
     ("Syntax.dangling_else 1 0", "2"),
     ("Syntax.dangling_else 1 1", "1"),
     ("Functions.caller 4", "5"),
     ("Functions.nested 4", "6"),
     ("Functions.call_three", "16"),
     ("Functions.main", "0"),
     ("Functions.pointer_identity (undefined :: (nat, nat, c_uint) State_References.ref)",
       "(undefined :: (nat, nat, c_uint) State_References.ref)"),
     ("Functions.character_identity (undefined :: (nat, nat, c_char) State_References.ref)",
       "(undefined :: (nat, nat, c_char) State_References.ref)"),
     ("Functions.string_return", "[104, 105, 0]"),
     ("Types.enum_values", "14"),
     ("Types.promote 255 65535", "65790"),
     ("Types.mixed (-1) 1", "0"),
     ("Types.record_size", "8"),
     ("Types.record_offset", "4"),
     ("Types.u128 340282366920938463463374607431768211455",
       "340282366920938463463374607431768211455"),
     ("Types.i128 (-170141183460469231731687303715884105728)",
       "-170141183460469231731687303715884105728"),
     ("Semantics.short_and 0", "0"),
     ("Semantics.short_or 1", "1"),
     ("Semantics.skipped_conditional 1", "7"),
     ("Semantics.unevaluated_sizeof", "4"),
     ("Semantics.unevaluated_generic", "7"),
     ("Semantics.minimum", "-2147483648")]
  val aborts =
    [("Expressions.signed_add 2147483647 1", "SignedOverflow"),
     ("Expressions.signed_add (-2147483648) (-1)", "SignedOverflow"),
     ("Expressions.signed_sub (-2147483648) 1", "SignedOverflow"),
     ("Expressions.signed_mul 2147483647 2", "SignedOverflow"),
     ("Expressions.signed_divide (-2147483648) (-1)", "SignedOverflow"),
     ("Expressions.signed_modulo (-2147483648) (-1)", "SignedOverflow"),
     ("Expressions.divide 7 0", "DivisionByZero"),
     ("Expressions.modulo 7 0", "DivisionByZero"),
     ("Expressions.signed_divide 7 0", "DivisionByZero"),
     ("Expressions.signed_modulo 7 0", "DivisionByZero"),
     ("Expressions.shift_left 1 32", "ShiftOutOfRange"),
     ("Expressions.shift_right 1 32", "ShiftOutOfRange"),
     ("Expressions.unary_minus (-2147483648)", "SignedOverflow"),
     ("Semantics.skipped_conditional 0", "DivisionByZero")]
  val _ = List.app (fn (application, result) =>
    C_Parser_Test.evaluates \<^context> application ("Success (" ^ result ^ ")"))
    successes
  val _ = List.app (fn (application, reason) =>
    C_Parser_Test.evaluates \<^context> application
      ("Abort (CustomAbort " ^ reason ^ ")")) aborts
in
  val _ = ()
end
\<close>

section \<open>Custom abort handlers preserve generated failures\<close>

definition test_route_abort ::
    "c_abort \<Rightarrow> ('s, 'v, 'r, c_abort option, 'i, 'o) expression" where
  "test_route_abort reason = abort (CustomAbort (Some reason))"

c_source Routed [compiler = conservative, abort = test_route_abort] \<open>
  int add(int a, int b) { return a + b; }
  unsigned int divide(unsigned int a, unsigned int b) { return a / b; }
  int shift(int a, int b) { return a >> b; }
  signed char narrow(int a) { return (signed char)a; }
\<close>

ML_val \<open>
  val _ = C_Parser_Test.check_definitions \<^context> "Routed"
    ["add", "divide", "shift", "narrow"]
  val _ = List.app (fn (application, reason) =>
    C_Parser_Test.prove \<^context>
      ["shallow_computation_simps", "c_test_eval_simps", "test_route_abort_def"]
      ("evaluate (call (Routed." ^ application ^ ")) () = " ^
       "Abort (CustomAbort (Some " ^ reason ^ ")) ()"))
    [("add 2147483647 1", "SignedOverflow"),
     ("divide 7 0", "DivisionByZero"),
     ("shift (-8) 1", "SignedOverflow"),
     ("narrow 128", "SignedOverflow")]
\<close>

end
