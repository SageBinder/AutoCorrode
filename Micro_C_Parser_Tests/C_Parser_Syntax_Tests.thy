(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Syntax_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Precedence and associativity against explicit grouping\<close>

c_source Syntax \<open>
  unsigned int multiply(void) { return 1U + 2U * 3U; }
  unsigned int multiply_grouped(void) { return 1U + (2U * 3U); }
  unsigned int multiply_alternative(void) { return (1U + 2U) * 3U; }
  unsigned int shift(void) { return 1U << 2U + 1U; }
  unsigned int shift_grouped(void) { return 1U << (2U + 1U); }
  unsigned int bitwise(void) { return 1U | 2U ^ 3U & 4U; }
  unsigned int bitwise_grouped(void) { return 1U | (2U ^ (3U & 4U)); }
  int comparison(void) { return 1 + 2 < 4 == 1; }
  int comparison_grouped(void) { return ((1 + 2) < 4) == 1; }
  int logical(void) { return 0 || 1 && 0; }
  int logical_grouped(void) { return 0 || (1 && 0); }
  unsigned int subtract(void) { return 9U - 3U - 2U; }
  unsigned int subtract_grouped(void) { return (9U - 3U) - 2U; }
  unsigned int subtract_alternative(void) { return 9U - (3U - 2U); }
  unsigned int conditional(void) { return 0U ? 1U : 1U ? 2U : 3U; }
  unsigned int conditional_grouped(void) { return 0U ? 1U : (1U ? 2U : 3U); }
  unsigned int cast_prefix(void) { return (unsigned int)-1; }
  unsigned int cast_prefix_grouped(void) { return (unsigned int)(-1); }
  unsigned int commented(void) {
    /* The comment contains ; } + && tokens. */
    return 1U /* between operands */ + // line comment
      2U;
  }
  unsigned int plain(void) { return 1U + 2U; }
  int dangling_else(int a, int b) {
    if (a) if (b) return 1; else return 2;
    return 3;
  }
  int dangling_else_grouped(int a, int b) {
    if (a) { if (b) return 1; else return 2; }
    return 3;
  }
  void empty_statements(void) { ; ; return; }
  unsigned int empty_block(void) { { } return 4; }
\<close>

ML_val \<open>
  val pairs =
    [("multiply", "multiply_grouped"), ("shift", "shift_grouped"),
     ("bitwise", "bitwise_grouped"), ("comparison", "comparison_grouped"),
     ("logical", "logical_grouped"), ("subtract", "subtract_grouped"),
     ("conditional", "conditional_grouped"), ("cast_prefix", "cast_prefix_grouped"),
     ("commented", "plain"), ("dangling_else", "dangling_else_grouped")]
  val _ = List.app (fn (left, right) =>
    C_Parser_Test.assert ("precedence changed: " ^ left)
      (Term.aconv_untyped
        (C_Parser_Test.rhs \<^context> ("Syntax." ^ left),
         C_Parser_Test.rhs \<^context> ("Syntax." ^ right)))) pairs
  val _ = List.app (fn (left, right) =>
    C_Parser_Test.assert ("grouping control collapsed: " ^ left)
      (not (Term.aconv_untyped
        (C_Parser_Test.rhs \<^context> ("Syntax." ^ left),
         C_Parser_Test.rhs \<^context> ("Syntax." ^ right)))))
    [("multiply", "multiply_alternative"), ("subtract", "subtract_alternative")]
  val _ = C_Parser_Test.check_definitions \<^context> "Syntax"
    (distinct (op =) (maps (fn (a, b) => [a, b]) pairs @
      ["multiply_alternative", "subtract_alternative", "empty_statements", "empty_block"]))
\<close>

end
