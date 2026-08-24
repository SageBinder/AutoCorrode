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

section \<open>Binding experiment: does a µRust binder capture a name inside a HOL antiquotation?\<close>

text \<open>Disputed case: the name \<open>y\<close> is bound by BOTH an outer HOL binder and an inner µRust
  \<open>let\<close>, then referenced inside the antiquotation \<open>\<llangle>y\<rrangle>\<close>. The raw make-string tree is
  decisive: capture \<Rightarrow> a Bound var at the \<llangle>y\<rrangle> position and NO free y; context \<Rightarrow> a free y
  there (with the let's lambda binding an unused variable).\<close>

context fixes y :: nat and w :: nat
begin

text \<open>(P1) The disputed same-name probe (outer HOL binder = context-fixed \<open>y\<close>):\<close>
term \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>
ML \<open>writeln ("P1 same-name: " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>})\<close>

text \<open>(P3, free oracle) antiquotation refers to a DISTINCT context var \<open>w\<close> — definitely free:\<close>
term \<open>\<lbrakk> let y = 99; \<llangle>w\<rrangle> \<rbrakk>\<close>
ML \<open>writeln ("P3 distinct-free: " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<llangle>w\<rrangle> \<rbrakk>\<close>})\<close>

end

text \<open>(P2, capture oracle) no outer \<open>y\<close>: the antiquotation \<open>y\<close> can ONLY be the µRust let binder:\<close>
term \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>
ML \<open>writeln ("P2 no-outer: " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>})\<close>

text \<open>(D) Definition discriminator: outer HOL binder = the parameter \<open>y\<close>. If \<llangle>y\<rrangle> is the
  parameter, bind_probe returns its argument; if captured by the let, it ignores its argument.\<close>
definition bind_probe :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close> where
  \<open>bind_probe y \<equiv> FunctionBody \<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>
ML \<open>writeln ("D bind_probe_def: " ^ @{make_string} @{thm bind_probe_def})\<close>

section \<open>Binding experiment (variant): the \<epsilon>\<open>\<dots>\<close> expression antiquotation directly\<close>

text \<open>Same probes, but using the expression antiquotation \<epsilon>\<open>literal y\<close> instead of the
  value antiquotation \<llangle>y\<rrangle>. Question: does the µRust let still capture the y inside \<epsilon>\<open>\<dots>\<close>?\<close>

context fixes y :: nat and w :: nat
begin

text \<open>(E1) same-name via \<epsilon>:\<close>
term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>literal y\<close> \<rbrakk>\<close>
ML \<open>writeln ("E1 same-name (eps): " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>literal y\<close> \<rbrakk>\<close>})\<close>

text \<open>(E3) distinct free var w via \<epsilon> (oracle):\<close>
term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>literal w\<close> \<rbrakk>\<close>
ML \<open>writeln ("E3 distinct-free (eps): " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>literal w\<close> \<rbrakk>\<close>})\<close>

end

text \<open>(ED) definition discriminator via \<epsilon>: parameter y vs let y:\<close>
definition bind_probe_eps :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close> where
  \<open>bind_probe_eps y \<equiv> FunctionBody \<lbrakk> let y = 99; \<epsilon>\<open>literal y\<close> \<rbrakk>\<close>
ML \<open>writeln ("ED bind_probe_eps_def: " ^ @{make_string} @{thm bind_probe_eps_def})\<close>

section \<open>Binding experiment (\<epsilon>, no \<open>literal\<close>): antiquotation content is an opaque expression\<close>

text \<open>Here the \<epsilon>\<open>\<dots>\<close> content uses NO \<open>literal\<close>: \<open>y\<close> is just the argument of an opaque
  context-fixed, expression-valued function \<open>g\<close>. Does the µRust \<open>let y\<close> still capture it?\<close>

context
  fixes y :: nat
    and g :: \<open>nat \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
begin

text \<open>(N1) same-name, no literal:\<close>
term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>g y\<close> \<rbrakk>\<close>
ML \<open>writeln ("N1 no-literal same-name (eps): " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>g y\<close> \<rbrakk>\<close>})\<close>

end

section \<open>Lemma: the µRust binder captures inside the antiquotation\<close>

context fixes y :: nat
begin

text \<open>LHS shadows the context-fixed \<open>y\<close> with a µRust \<open>let y\<close>, and the antiquotation \<open>\<llangle>y\<rrangle>\<close>
  refers to that name. RHS is the same program with a fresh, non-shadowing name \<open>z\<close>. If the
  \<open>let\<close> captures the \<open>\<llangle>y\<rrangle>\<close> (as the experiments show), the two elaborate to \<alpha>-equal terms and
  \<open>refl\<close> closes the goal. If \<open>\<llangle>y\<rrangle>\<close> instead meant the free context \<open>y\<close>, the LHS would carry a
  free \<open>y\<close> that the RHS lacks, and \<open>refl\<close> would fail — so this lemma *is* the proof of capture.\<close>
lemma binder_captures_antiquotation:
  shows \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk> = \<lbrakk> let z = 99; \<llangle>z\<rrangle> \<rbrakk>\<close>
  by (rule refl)
end

section \<open>Match variant: does a match-arm pattern binder capture inside the antiquotation?\<close>

context fixes y :: nat
begin

text \<open>(MM) probe: match on \<open>Some(5)\<close>; the arm pattern binds \<open>y\<close>; antiquotation \<open>\<llangle>y\<rrangle>\<close>:\<close>
term \<open>\<lbrakk> match (Some(5)) { Some(y) \<Rightarrow> \<llangle>y\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>\<close>
ML \<open>writeln ("MM match same-name: " ^ @{make_string} @{term \<open>\<lbrakk> match (Some(5)) { Some(y) \<Rightarrow> \<llangle>y\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>\<close>})\<close>

text \<open>Lemma: shadowing arm-binder LHS equals fresh-name arm-binder RHS (proof of capture):\<close>
lemma match_binder_captures_antiquotation:
  shows \<open>\<lbrakk> match (Some(5)) { Some(y) \<Rightarrow> \<llangle>y\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>
       = \<lbrakk> match (Some(5)) { Some(z) \<Rightarrow> \<llangle>z\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>\<close>
  by (rule refl)

end

text \<open>Need to be careful with binders here:\<close>

definition \<open>special_num \<equiv> 1 :: nat\<close>

(* term\<open>case Some 1 of Some special_num \<Rightarrow> 0\<close> *)

end
