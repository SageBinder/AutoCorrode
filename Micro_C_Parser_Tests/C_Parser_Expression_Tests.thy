(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Expression_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Literals, operators, casts, and selection\<close>

c_source Expressions \<open>
  unsigned int decimal(void) { return 42; }
  unsigned int hexadecimal(void) { return 0x2aU; }
  unsigned int octal(void) { return 052u; }
  unsigned long long_suffix(void) { return 42UL; }
  int character(void) { return 'A'; }
  int escaped_character(void) { return '\n'; }
  unsigned int add(unsigned int a, unsigned int b) { return a + b; }
  unsigned int sub(unsigned int a, unsigned int b) { return a - b; }
  unsigned int mul(unsigned int a, unsigned int b) { return a * b; }
  unsigned int divide(unsigned int a, unsigned int b) { return a / b; }
  unsigned int modulo(unsigned int a, unsigned int b) { return a % b; }
  int signed_add(int a, int b) { return a + b; }
  int signed_sub(int a, int b) { return a - b; }
  int signed_mul(int a, int b) { return a * b; }
  int signed_divide(int a, int b) { return a / b; }
  int signed_modulo(int a, int b) { return a % b; }
  unsigned int bit_and(unsigned int a, unsigned int b) { return a & b; }
  unsigned int bit_or(unsigned int a, unsigned int b) { return a | b; }
  unsigned int bit_xor(unsigned int a, unsigned int b) { return a ^ b; }
  unsigned int complement(unsigned int a) { return ~a; }
  unsigned int shift_left(unsigned int a, unsigned int b) { return a << b; }
  unsigned int shift_right(unsigned int a, unsigned int b) { return a >> b; }
  int less(int a, int b) { return a < b; }
  int less_equal(int a, int b) { return a <= b; }
  int greater(int a, int b) { return a > b; }
  int greater_equal(int a, int b) { return a >= b; }
  int equal(int a, int b) { return a == b; }
  int unequal(int a, int b) { return a != b; }
  int logical_not(int a) { return !a; }
  int logical_and(int a, int b) { return a && b; }
  int logical_or(int a, int b) { return a || b; }
  int unary_plus(int a) { return +a; }
  int unary_minus(int a) { return -a; }
  unsigned int choose(unsigned int a, unsigned int b) { return a ? a : b; }
  unsigned int comma(unsigned int a, unsigned int b) { return (a, b); }
  unsigned char narrow(unsigned int a) { return (unsigned char)a; }
  long widen(int a) { return (long)a; }
  unsigned long size_type(void) { return sizeof(int); }
  unsigned long size_expression(int a) { return sizeof(a + 1); }
  unsigned long alignment(void) { return _Alignof(int); }
  unsigned int generic(unsigned int a) {
    return _Generic(a, unsigned int: a + 1, default: 0);
  }
  unsigned int compound_literal(void) { return (unsigned int){42}; }
\<close>

ML_val \<open>
  val _ = C_Parser_Test.check_definitions \<^context> "Expressions"
    ["decimal", "hexadecimal", "octal", "long_suffix", "character",
     "escaped_character", "add", "sub", "mul", "divide", "modulo",
     "signed_add", "signed_sub", "signed_mul", "signed_divide", "signed_modulo",
     "bit_and", "bit_or", "bit_xor", "complement", "shift_left", "shift_right",
     "less", "less_equal", "greater", "greater_equal", "equal", "unequal",
     "logical_not", "logical_and", "logical_or", "unary_plus", "unary_minus",
     "choose", "comma", "narrow", "widen", "size_type", "size_expression",
     "alignment", "generic", "compound_literal"]

  val arithmetic =
    [("add", \<^const_name>\<open>c_unsigned_add\<close>),
     ("sub", \<^const_name>\<open>c_unsigned_sub\<close>),
     ("mul", \<^const_name>\<open>c_unsigned_mul\<close>),
     ("divide", \<^const_name>\<open>c_unsigned_div_with_abort\<close>),
     ("modulo", \<^const_name>\<open>c_unsigned_mod_with_abort\<close>),
     ("signed_add", \<^const_name>\<open>c_signed_add_with_abort\<close>),
     ("signed_sub", \<^const_name>\<open>c_signed_sub_with_abort\<close>),
     ("signed_mul", \<^const_name>\<open>c_signed_mul_with_abort\<close>),
     ("signed_divide", \<^const_name>\<open>c_signed_div_with_abort\<close>),
     ("signed_modulo", \<^const_name>\<open>c_signed_mod_with_abort\<close>),
     ("bit_and", \<^const_name>\<open>c_unsigned_and\<close>),
     ("bit_or", \<^const_name>\<open>c_unsigned_or\<close>),
     ("bit_xor", \<^const_name>\<open>c_unsigned_xor\<close>),
     ("shift_left", \<^const_name>\<open>c_unsigned_shl_with_abort\<close>),
     ("shift_right", \<^const_name>\<open>c_unsigned_shr_with_abort\<close>)]
  val _ = List.app (fn (name, backend) =>
    C_Parser_Test.require_consts \<^context> ("Expressions." ^ name) [backend] [])
    arithmetic
  val _ = List.app (fn name =>
    C_Parser_Test.require_consts \<^context> ("Expressions." ^ name)
      [\<^const_name>\<open>two_armed_conditional\<close>] [])
    ["choose", "logical_and", "logical_or"]
\<close>

lemma literal_spellings:
  shows "Expressions.decimal = Expressions.hexadecimal"
    and "Expressions.decimal = Expressions.octal"
  by (simp_all add: Expressions.decimal_def Expressions.hexadecimal_def
    Expressions.octal_def c_scast_def shallow_computation_simps c_test_eval_simps
    bind.simps evaluate_def literal_def)

end
