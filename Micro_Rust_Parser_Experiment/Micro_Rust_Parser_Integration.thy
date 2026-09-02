theory Micro_Rust_Parser_Integration
  imports Micro_Rust_Parser
begin

section\<open> Parser semantic bridge \<close>

text\<open>
The matcher runtime uses a thunked conditional so generated code does not evaluate an unselected
continuation.  This theory exposes that construct through the existing shallow-\<mu>Rust conditional
and keeps the integration boundary deliberately narrow.  The parser's conformance command uses its
controlled matcher normalizer directly; no public parser proof method or dedicated Eval, WP, or
Crush rule is introduced here.
\<close>

lemma urust_lazy_conditional_as_two_armed:
  \<open>
    urust_lazy_conditional condition then_thunk else_thunk =
      two_armed_conditional condition
        (then_thunk ()) (else_thunk ())
  \<close>
  by (simp add:
    urust_lazy_conditional_def
    two_armed_conditional_def)

declare urust_matcher_fail_def [micro_rust_simps]
declare urust_matcher_succeed_def [micro_rust_simps]
declare urust_lazy_conditional_as_two_armed [micro_rust_simps]

end
