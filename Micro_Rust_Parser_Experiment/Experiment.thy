theory Experiment
  imports Shallow_Micro_Rust.Micro_Rust
begin

text \<open>Tracing the shallow embedding of the µRust example:  let x = f(a); x + 1

  µRust is a shallow embedding: the surface syntax inside \<lbrakk> \<dots> \<rbrakk> elaborates
  directly into HOL terms of type \<open>expression\<close>. There is no reified AST.\<close>

text \<open>(1) The parsed term, pretty-printed. Isabelle folds it back into µRust
  surface syntax, so this prints roughly as we wrote it.\<close>

term \<open>\<lbrakk> let x = f(a); x + 1 \<rbrakk>\<close>

text \<open>(2) The raw internal HOL term tree. \<^ML>\<open>@{make_string}\<close> bypasses the
  pretty-printer, exposing the underlying constants:
    • \<open>bind\<close>            — the \<open>let\<close>
    • \<open>funcall1\<close>        — the call \<open>f(a)\<close>
    • \<open>literal\<close>         — lifts a value into an \<open>expression\<close>
    • \<open>word_add_no_wrap\<close>— the checked \<open>+\<close>
  The bound \<open>x\<close> appears as a de Bruijn \<open>Bound 0\<close> inside the lambda that \<open>bind\<close>
  takes as its second argument.\<close>

ML \<open>
  val t = @{term \<open>\<lbrakk> let x = f(a); x + 1 \<rbrakk>\<close>};
  writeln (@{make_string} t)
\<close>

end
