(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Rejection_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Unsupported language forms and malformed input\<close>

ML_val \<open>
local
  val rows =
    [("float", "float type not supported",
      "float rejected(float x) { return x; }"),
     ("double", "double type not supported",
      "double rejected(double x) { return x; }"),
     ("atomic", "_Atomic",
      "_Atomic int rejected(_Atomic int x) { return x; }"),
     ("variadic", "variadic function definition",
      "int rejected(int x, ...) { return x; }"),
     ("undeclared-call", "call to undeclared function",
      "int rejected(void) { return missing(); }"),
     ("arity-short", "function call arity mismatch",
      "int helper(int x, int y) { return x + y; } int rejected(void) { return helper(1); }"),
     ("arity-long", "function call arity mismatch",
      "int helper(int x) { return x; } int rejected(void) { return helper(1, 2); }"),
     ("unknown-variable", "undefined variable",
      "int rejected(void) { return missing; }"),
     ("multichar-parser", "No matching grammar rule",
      "int rejected(void) { return 'ab'; }"),
     ("void-dereference", "dereference of void pointer",
      "int rejected(void *p) { return *p; }"),
     ("pointer-local-address", "address-of pointer local variable",
      "int **rejected(int *p) { int *q = p; return &q; }"),
     ("global-address", "address-of global const",
      "static const int x = 3; int *rejected(void) { return &x; }"),
     ("unsequenced-binary", "unsequenced side-effect UB",
      "int rejected(void) { int x = 0; return x++ + x; }"),
     ("unsequenced-call", "unsequenced side-effect UB",
      "int helper(int a, int b) { return a + b; } int rejected(void) { int x = 0; return helper(x++, x); }"),
     ("generic-missing", "no matching association and no default",
      "unsigned int rejected(unsigned int x) { return _Generic(x, char: 1); }"),
     ("array-initializer-overflow", "too many initializers for array",
      "void rejected(void) { int a[1] = {1, 2}; }"),
     ("array-string-overflow", "string initializer too long for array",
      "void rejected(void) { char a[1] = \"long\"; }"),
     ("array-designator-overflow", "designator index",
      "void rejected(void) { int a[2] = {[4] = 1}; }"),
     ("global-array-write", "assignment to global constant array element",
      "static const int a[2] = {1, 2}; void rejected(void) { a[0] = 3; }")]

  fun check (label, fragment, text) =
    let
      val file = "rejection-" ^ label ^ ".c"
      val _ = C_Parser_Test.rejects label [fragment, file]
        (fn () => C_Parser_Test.translate \<^theory> file "Rejected"
          "[addr = nat]" text)
      val _ = C_Parser_Test.absent \<^context> "Rejected.rejected"
      val _ = C_Parser_Test.absent \<^context> "Rejected.abi_pointer_bits"
      (* Reuse the failed namespace with a different configuration. This also
         checks that parsing and translation can recover after every rejection. *)
      val recovered = C_Parser_Test.translate \<^theory> ("recovery-" ^ file)
        "Rejected" "[abi = ilp32-be, compiler = conservative]"
        "unsigned int recovered(void) { return 7; }"
      val ctxt = Proof_Context.init_global recovered
      val _ = C_Parser_Test.checked_definition ctxt "Rejected.recovered"
      val _ = C_Parser_Test.assert (label ^ ": stale ABI after recovery")
        (HOLogic.dest_nat (C_Parser_Test.rhs ctxt "Rejected.abi_pointer_bits") = 32)
    in () end

  val _ = List.app check rows
  val malformed =
    [("broken-parameter", "int rejected( { return 0; }"),
     ("missing-semicolon", "int rejected(void) { return 1 }"),
     ("unclosed-block", "int rejected(void) { return 1;"),
     ("unterminated-comment", "/* unterminated")]
  val _ = List.app (fn (label, text) =>
    let val file = "syntax-" ^ label ^ ".c"
    in
      C_Parser_Test.rejects label [file]
        (fn () => Micro_C_Isabelle_C_Adapter.parse_translation_unit
          (C_Parser_Test.source file text) \<^theory>) |> K ()
    end) malformed
in
  val _ = ()
end
\<close>

end
