(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Function_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Signatures, call ordering, and lexical scope\<close>

c_source Functions \<open>
  unsigned int caller(unsigned int x) { return helper(x); }
  unsigned int helper(unsigned int x) { return x + 1; }
  unsigned int nested(unsigned int x) { return helper(helper(x)); }
  unsigned int zero(void) { return 7; }
  unsigned int one(unsigned int x) { return x; }
  unsigned int two(unsigned int x, unsigned int y) { return x + y; }
  unsigned int three(unsigned int x, unsigned int y, unsigned int z) {
    return two(x, y) + z;
  }
  unsigned int call_three(void) { return three(zero(), one(2), two(3, 4)); }
  unsigned int *pointer_identity(unsigned int *p) { return p; }
  char *character_identity(char *p) { return p; }
  char *string_return(void) { return "hi"; }
  void no_result(void) { return; }
  void call_void(void) { no_result(); return; }
  int main(void) { }
  static unsigned int internal(unsigned int x) { return x; }
  unsigned int through_prototype(unsigned int x);
  unsigned int through_prototype(unsigned int x) { return internal(x); }
  unsigned int shadow(unsigned int x) {
    unsigned int y = x;
    { unsigned int x = 99; y = x; }
    return x;
  }
  unsigned int parameter_update(unsigned int x) { x += 2; return x; }
  unsigned int local_update(unsigned int x) {
    unsigned int y = x;
    y = y + 1;
    return y;
  }
  unsigned int multi_declaration(unsigned int x) {
    unsigned int a = x, b = 2;
    return a + b;
  }
\<close>

ML_val \<open>
  val _ = C_Parser_Test.check_definitions \<^context> "Functions"
    ["caller", "helper", "nested", "zero", "one", "two", "three",
     "call_three", "pointer_identity", "character_identity", "string_return",
     "no_result", "call_void", "main", "internal", "through_prototype",
     "shadow", "parameter_update", "local_update", "multi_declaration"]
  val _ = List.app (fn (name, arguments) =>
    C_Parser_Test.require_arguments \<^context> ("Functions." ^ name) arguments)
    [("zero", []), ("one", [\<^typ>\<open>c_uint\<close>]),
     ("two", [\<^typ>\<open>c_uint\<close>, \<^typ>\<open>c_uint\<close>]),
     ("three", replicate 3 \<^typ>\<open>c_uint\<close>), ("no_result", [])]
  val helper = #1 (dest_Const (C_Parser_Test.constant \<^context> "Functions.helper"))
  val _ = C_Parser_Test.require_consts \<^context> "Functions.caller" [helper] []
  val _ = C_Parser_Test.require_consts \<^context> "Functions.nested" [helper] []
  val _ = C_Parser_Test.require_consts \<^context> "Functions.local_update"
    [\<^const_name>\<open>store_reference_const\<close>,
     \<^const_name>\<open>store_update_const\<close>,
     \<^const_name>\<open>store_dereference_const\<close>] []
  val _ = C_Parser_Test.require_consts \<^context> "Functions.parameter_update"
    [\<^const_name>\<open>store_reference_const\<close>,
     \<^const_name>\<open>store_update_const\<close>] []
\<close>

end
