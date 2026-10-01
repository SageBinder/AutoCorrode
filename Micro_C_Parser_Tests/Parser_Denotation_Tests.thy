(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Denotation_Tests
  imports
    Micro_C_Parsing_Frontend.C_Translation
    Shallow_Computation.Core_Expression_Lemmas
begin

c_translate \<open>
int constant(void) {
  return 42;
}
\<close>

c_translate \<open>
int identity(int x) {
  return x;
}
\<close>

c_translate \<open>
int add(int x, int y) {
  return x + y;
}
\<close>

lemma c_constant_shape:
  shows \<open>c_constant =
    FunctionBody (return_func (literal (42 :: c_int)))\<close>
  by (simp add: c_constant_def)

lemma c_identity_shape:
  shows \<open>c_identity x =
    FunctionBody (return_func (literal x))\<close>
  by (simp add: c_identity_def)

lemma c_add_shape:
  shows \<open>c_add x y =
    FunctionBody
      (return_func
        (bind2 c_signed_add (literal x) (literal y)))\<close>
  by (simp add: c_add_def)

lemma c_add_evaluates:
  shows \<open>evaluate
    (function_body (c_add (20 :: c_int) (22 :: c_int))) () =
      Return (42 :: c_int) ()\<close>
  by (simp add:
    c_add_def c_signed_add_def return_func_def return_val_def
    bind2_def Core_Expression.bind.simps literal_def evaluate_def)

lemma c_add_overflow_aborts:
  shows \<open>evaluate
    (function_body (c_add (2147483647 :: c_int) (1 :: c_int))) () =
      Abort (CustomAbort SignedOverflow) ()\<close>
  by (simp add:
    c_add_def c_signed_add_def return_func_def return_val_def abort_def
    bind2_def Core_Expression.bind.simps literal_def evaluate_def)

ML_val\<open>
local
  fun assert message condition =
    if condition then ()
    else error ("C denotation test: " ^ message)

  fun source text =
    let
      val start = \<^here>
      val stop = Position.symbol_explode text start
    in
      Input.source true text (Position.range (start, stop))
    end

  val thy = Proof_Context.theory_of \<^context>
  val _ = assert "failed-name precondition"
    (not (Sign.declared_const thy "c_failed"))
  val failure =
    Exn.capture
      (C_Translation.translate
        (source "int failed(void) { return missing; }"))
      \<^context>
  val _ =
    (case failure of
       Exn.Exn (ERROR message) =>
         assert "wrong failed translation diagnostic"
           (String.isSubstring "unknown identifier" message)
     | Exn.Exn exn => Exn.reraise exn
     | Exn.Res _ => error "C denotation test: failed translation succeeded")
  val _ =
    assert "failed translation installed a declaration"
      (not (Sign.declared_const
        (Proof_Context.theory_of \<^context>) "c_failed"))

  val duplicate =
    Exn.capture
      (C_Translation.translate
        (source "int add(void) { return 0; }"))
      (Named_Target.theory_init thy)
  val _ =
    (case duplicate of
       Exn.Exn (ERROR message) =>
         assert ("wrong duplicate binding diagnostic: " ^ message)
           (String.isSubstring "already exists" message)
     | Exn.Exn exn => Exn.reraise exn
     | Exn.Res _ => error "C denotation test: duplicate binding succeeded")

  val simps =
    Named_Theorems.get \<^context>
      \<^named_theorems>\<open>shallow_computation_simps\<close>
  val add_definition = Proof_Context.get_thm \<^context> "c_add_def"
  val _ =
    assert "generated theorem not registered"
      (exists (fn theorem => Thm.eq_thm_prop (theorem, add_definition)) simps)
in
  val _ = ()
end
\<close>

end
