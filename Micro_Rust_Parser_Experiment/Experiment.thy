theory Experiment
  imports Shallow_Micro_Rust.Micro_Rust
begin

text\<open>
The shallow \<mu>Rust term \<open>let x = f(a); x + 1\<close> elaborates directly to a HOL
\<open>expression\<close>; it has no reified AST.
\<close>

text\<open> Pretty-printing reconstructs the surface syntax. \<close>

term \<open>\<lbrakk> let x = f(a); x + 1 \<rbrakk>\<close>

text\<open>
\<^ML>\<open>@{make_string}\<close> exposes \<open>bind\<close> (the \<open>let\<close>), \<open>funcall1\<close>
(the call), \<open>literal\<close> (value lifting), and \<open>word_add_no_wrap\<close>. The bound
\<open>x\<close> is \<open>Bound 0\<close> in \<open>bind\<close>'s continuation.
\<close>

ML \<open>
  val t = @{term \<open>\<lbrakk> let x = f(a); x + 1 \<rbrakk>\<close>};
  writeln (@{make_string} t)
\<close>

section \<open>Binding experiment: does a µRust binder capture a name inside a HOL antiquotation?\<close>

text\<open>
Both the HOL context and the inner \<mu>Rust \<open>let\<close> bind \<open>y\<close>. At
\<open>\<llangle>y\<rrangle>\<close>, \<open>Bound 0\<close> proves capture; \<open>Free y\<close> would select the
outer context.
\<close>

context fixes y :: nat and w :: nat
begin

text\<open> (P1) Same-name probe with context-fixed \<open>y\<close>. \<close>
term \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>
ML \<open>writeln ("P1 same-name: " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>})\<close>

text\<open> (P3) Distinct context variable \<open>w\<close>; necessarily free. \<close>
term \<open>\<lambda>w. \<lbrakk> let y = 99; \<llangle>w\<rrangle> \<rbrakk>\<close>
ML \<open>writeln ("P3 distinct-free: " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<llangle>w\<rrangle> \<rbrakk>\<close>})\<close>

end

text\<open> (P2) With no outer \<open>y\<close>, the antiquotation must select the \<mu>Rust binder. \<close>
term \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>
ML \<open>writeln ("P2 no-outer: " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>})\<close>

text\<open>
(D) If \<open>\<llangle>y\<rrangle>\<close> selects the parameter, \<open>bind_probe\<close> returns it;
capture makes the parameter unused.
\<close>
definition bind_probe :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close> where
  \<open>bind_probe y \<equiv> FunctionBody \<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk>\<close>
ML \<open>writeln ("D bind_probe_def: " ^ @{make_string} @{thm bind_probe_def})\<close>

section \<open>Binding experiment (variant): the \<epsilon>\<open>\<dots>\<close> expression antiquotation directly\<close>

text\<open> Repeat the probes with expression antiquotation \<open>\<epsilon>\<open>literal y\<close>\<close>. \<close>

context fixes y :: nat and w :: nat
begin

text\<open> (E1) Same name via \<open>\<epsilon>\<close>. \<close>
term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>literal y\<close> \<rbrakk>\<close>
ML \<open>writeln ("E1 same-name (eps): " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>literal y\<close> \<rbrakk>\<close>})\<close>

text\<open> (E3) Distinct free variable \<open>w\<close> via \<open>\<epsilon>\<close>. \<close>
term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>literal w\<close> \<rbrakk>\<close>
ML \<open>writeln ("E3 distinct-free (eps): " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>literal w\<close> \<rbrakk>\<close>})\<close>

end

text\<open> (ED) Parameter versus \<open>let\<close> binder via \<open>\<epsilon>\<close>. \<close>
definition bind_probe_eps :: \<open>nat \<Rightarrow> ('s, nat, 'abort, 'i, 'o) function_body\<close> where
  \<open>bind_probe_eps y \<equiv> FunctionBody \<lbrakk> let y = 99; \<epsilon>\<open>literal y\<close> \<rbrakk>\<close>
ML \<open>writeln ("ED bind_probe_eps_def: " ^ @{make_string} @{thm bind_probe_eps_def})\<close>

section \<open>Binding experiment (\<epsilon>, no \<open>literal\<close>): antiquotation content is an opaque expression\<close>

text\<open>
Use opaque \<open>g y\<close> to test capture independently of \<open>literal\<close>.
\<close>

context
  fixes y :: nat
    and g :: \<open>nat \<Rightarrow> ('s, 'v, 'r, 'abort, 'i, 'o) expression\<close>
begin

text\<open> (N1) Same name without \<open>literal\<close>. \<close>
term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>g y\<close> \<rbrakk>\<close>
ML \<open>writeln ("N1 no-literal same-name (eps): " ^ @{make_string} @{term \<open>\<lbrakk> let y = 99; \<epsilon>\<open>g y\<close> \<rbrakk>\<close>})\<close>

end

section \<open>Lemma: the µRust binder captures inside the antiquotation\<close>

context fixes y :: nat
begin

text\<open>
The RHS renames the inner binder to \<open>z\<close>. Reflexivity proves capture:
selecting the context-fixed \<open>y\<close> would make the terms differ.
\<close>
lemma binder_captures_antiquotation:
  shows \<open>\<lbrakk> let y = 99; \<llangle>y\<rrangle> \<rbrakk> = \<lbrakk> let z = 99; \<llangle>z\<rrangle> \<rbrakk>\<close>
  by (rule refl)
end

section \<open>Match variant: does a match-arm pattern binder capture inside the antiquotation?\<close>

context fixes y :: nat
begin

text\<open> (MM) Match-arm binder referenced by \<open>\<llangle>y\<rrangle>\<close>. \<close>
term \<open>\<lbrakk> match (Some(5)) { Some(y) \<Rightarrow> \<llangle>y\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>\<close>
ML \<open>writeln ("MM match same-name: " ^ @{make_string} @{term \<open>\<lbrakk> match (Some(5)) { Some(y) \<Rightarrow> \<llangle>y\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>\<close>})\<close>

text\<open> Renaming the arm binder proves capture. \<close>
lemma match_binder_captures_antiquotation:
  shows \<open>\<lbrakk> match (Some(5)) { Some(y) \<Rightarrow> \<llangle>y\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>
       = \<lbrakk> match (Some(5)) { Some(z) \<Rightarrow> \<llangle>z\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>\<close>
  by (rule refl)

end

definition \<open>special_num \<equiv> 1 :: nat\<close>

(* term\<open>case Some 1 of Some special_num \<Rightarrow> 0\<close> *)

section \<open>Match-arm binder vs. an EXISTING name: does the binder shadow a HOL constant / a \<mu>Rust notation?\<close>

text\<open>
These probes bind names that already denote a HOL constant (\<open>id\<close>) or registered
notation (\<open>clash\<close>). In bare and antiquotation positions, the arm binder wins and
elaborates to \<open>Bound 0\<close>. Equality with a fresh-name oracle proves capture by
reflexivity.
\<close>

definition exp_backend :: nat where \<open> exp_backend \<equiv> 7 \<close>
micro_rust_notation (literal) exp_backend ("clash")

text\<open>
(a) Arm binder \<open>id\<close> shadows \<^const>\<open>Fun.id\<close> both bare and inside the
antiquotation.
\<close>
term \<open> \<lbrakk> match (Some(5)) { Some(id) \<Rightarrow> id, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>
term \<open> \<lbrakk> match (Some(5)) { Some(id) \<Rightarrow> \<llangle>id\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>
ML \<open>writeln ("a-aq (const id via antiquotation): " ^
  @{make_string} @{term \<open> \<lbrakk> match (Some(5)) { Some(id) \<Rightarrow> \<llangle>id\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>})\<close>

lemma match_binder_shadows_hol_const_bare:
  shows \<open> \<lbrakk> match (Some(5)) { Some(id) \<Rightarrow> id, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>
        = \<lbrakk> match (Some(5)) { Some(qq) \<Rightarrow> qq, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>
  by (rule refl)

lemma match_binder_shadows_hol_const_antiquotation:
  shows \<open> \<lbrakk> match (Some(5)) { Some(id) \<Rightarrow> \<llangle>id\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>
        = \<lbrakk> match (Some(5)) { Some(qq) \<Rightarrow> \<llangle>qq\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>
  by (rule refl)

text\<open>
(b) Arm binder \<open>clash\<close> shadows notation dispatch when bare; inside the
antiquotation it is an ordinary captured HOL name.
\<close>
term \<open> \<lbrakk> match (Some(5)) { Some(clash) \<Rightarrow> clash, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>
term \<open> \<lbrakk> match (Some(5)) { Some(clash) \<Rightarrow> \<llangle>clash\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>

lemma match_binder_shadows_notation_bare:
  shows \<open> \<lbrakk> match (Some(5)) { Some(clash) \<Rightarrow> clash, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>
        = \<lbrakk> match (Some(5)) { Some(qq) \<Rightarrow> qq, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>
  by (rule refl)

lemma match_binder_shadows_notation_antiquotation:
  shows \<open> \<lbrakk> match (Some(5)) { Some(clash) \<Rightarrow> \<llangle>clash\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk>
        = \<lbrakk> match (Some(5)) { Some(qq) \<Rightarrow> \<llangle>qq\<rrangle>, None \<Rightarrow> \<llangle>0\<rrangle> } \<rbrakk> \<close>
  by (rule refl)

text\<open>
Required parser behavior: lexical binders precede HOL constants and notation dispatch
throughout their scope, including antiquotations. This matches environment lookup before
dispatch.
\<close>

end
