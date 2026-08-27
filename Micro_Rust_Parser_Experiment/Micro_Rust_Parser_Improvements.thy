theory Micro_Rust_Parser_Improvements
  imports Micro_Rust_Parser_Conformance
  keywords
    "old_urust_rejects" :: thy_decl
begin

section\<open> Test support \<close>

text\<open>
Each example is accepted by \<open>urust_expr\<close>. The paired command feeds the same
source to the old inner-syntax frontend and requires it to reject.
\<close>

ML\<open>
fun old_urust_source source = "\<lbrakk> " ^ source ^ " \<rbrakk>"

val _ = Syntax.read_term \<^context> (old_urust_source "()")

fun old_urust_rejects source lthy =
  let
    val pos = Input.pos_of source
    val wrapped = old_urust_source (Input.string_of source)
    fun fail term =
      error ("old_urust_rejects: expected the old frontend to reject, but it accepted:\n" ^
        Syntax.string_of_term lthy term ^ Position.here pos)
  in
    (case Exn.result (Syntax.read_term lthy) wrapped of
       Exn.Res term => fail term
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           (writeln ("old frontend rejected as expected: " ^ Runtime.exn_message exn);
            lthy))
  end

val _ = Outer_Syntax.local_theory \<^command_keyword>\<open>old_urust_rejects\<close>
  "Assert that the old inner-syntax uRust frontend rejects a source expression"
  (Parse.input Parse.cartouche >> old_urust_rejects)
\<close>


section\<open> Compositional range patterns \<close>

datatype improvement_packet =
    ImprovementPacket
      (improvement_tag: nat)
      (improvement_values: "nat list")
  | ImprovementEmpty

text\<open>
The new pattern grammar permits ranges wherever another pattern is expected. Here
one range occupies a struct field and another occupies a nonfinal slice element.
The old frontend's mixfix priorities cannot parse either composition.
\<close>

urust_expr improvement_struct_and_slice_ranges
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      ImprovementPacket {
        improvement_tag: 1..=3,
        improvement_values: [4..=6, last]
      } \<Rightarrow>
        last,
      _ \<Rightarrow>
        0
    }
  \<close>

old_urust_rejects
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      ImprovementPacket {
        improvement_tag: 1..=3,
        improvement_values: [4..=6, last]
      } \<Rightarrow>
        last,
      _ \<Rightarrow>
        0
    }
  \<close>

text\<open>
The same design makes a range valid in a nonfinal positional constructor
argument. The old grammar accepts a range only where its low-priority parse
cannot be interrupted by the argument comma.
\<close>

urust_expr improvement_constructor_range
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      ImprovementPacket(1..=3, values) \<Rightarrow>
        1,
      _ \<Rightarrow>
        0
    }
  \<close>

old_urust_rejects
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      ImprovementPacket(1..=3, values) \<Rightarrow>
        1,
      _ \<Rightarrow>
        0
    }
  \<close>


section\<open> Hygienic aliases across nested lowering \<close>

text\<open>
Slice-rest patterns require generated nested matches. The new parser represents
the alias structurally, so \<open>whole\<close> remains bound to the packet rather than to
an internal list value. The old frontend captures its generated helper instead
and the expression becomes ill-typed.
\<close>

urust_expr improvement_hygienic_alias
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      whole @ ImprovementPacket {
        improvement_tag: _,
        improvement_values: [head, .., tail]
      } \<Rightarrow>
        whole,
      _ \<Rightarrow>
        \<llangle>ImprovementEmpty\<rrangle>
    }
  \<close>

old_urust_rejects
  \<open>
    match \<llangle>ImprovementPacket 2 [5, 8]\<rrangle> {
      whole @ ImprovementPacket {
        improvement_tag: _,
        improvement_values: [head, .., tail]
      } \<Rightarrow>
        whole,
      _ \<Rightarrow>
        \<llangle>ImprovementEmpty\<rrangle>
    }
  \<close>


section\<open> Hygienic mutable wildcard \<close>

definition improvement_reference_fixture ::
  \<open>'v \<Rightarrow> (unit, (unit, unit, 'v) Global_Store.ref, unit, unit, unit) function_body\<close>
  where \<open> improvement_reference_fixture \<equiv> undefined \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> improvement_reference_fixture

text\<open>
The custom pattern AST gives \<open>let mut _\<close> the same allocated-reference term shape
as a legacy mutable name that is not used, while representing the continuation binder
as an anonymous abstraction. The old frontend has no wildcard production at this site.
\<close>

urust_expr improvement_mutable_wildcard
  \<open>
    let keep = \<llangle>5 :: nat\<rrangle>;
    let mut _ = \<llangle>7 :: nat\<rrangle>;
    keep
  \<close>

lemma \<open> improvement_mutable_wildcard =
    \<lbrakk>
      let keep = \<llangle>5 :: nat\<rrangle>;
      let mut ignored = \<llangle>7 :: nat\<rrangle>;
      keep
    \<rbrakk> \<close>
  unfolding improvement_mutable_wildcard_def by (rule refl)

old_urust_rejects
  \<open>
    let keep = \<llangle>5 :: nat\<rrangle>;
    let mut _ = \<llangle>7 :: nat\<rrangle>;
    keep
  \<close>

no_adhoc_overloading store_reference_const \<rightleftharpoons> improvement_reference_fixture


section\<open> Recursive reference-prefix composition \<close>

text\<open>
The recursive reference-prefix tier accepts mixed and deeper unparenthesized
compositions. The old frontend has individual single-prefix productions and one
dedicated double-dereference production, so it requires explicit parentheses for
the equivalent mixed terms and cannot spell a triple dereference directly.
\<close>

adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture

context
  fixes rr ::
    \<open>(unit, unit, (unit, unit, 32 word) Global_Store.ref) Global_Store.ref\<close>
    and rrr ::
      \<open>(unit, unit,
          (unit, unit, (unit, unit, 32 word) Global_Store.ref) Global_Store.ref)
        Global_Store.ref\<close>
    and r :: \<open>(unit, unit, 32 word) Global_Store.ref\<close>
begin

urust_expr improvement_recursive_borrow_deref \<open> &*rr \<close>
lemma \<open> improvement_recursive_borrow_deref = \<lbrakk> &(*rr) \<rbrakk> \<close>
  unfolding improvement_recursive_borrow_deref_def by (rule refl)
old_urust_rejects \<open> &*rr \<close>

urust_expr improvement_recursive_deref_mut_borrow \<open> *& mut r \<close>
lemma \<open> improvement_recursive_deref_mut_borrow = \<lbrakk> *(& mut r) \<rbrakk> \<close>
  unfolding improvement_recursive_deref_mut_borrow_def by (rule refl)
old_urust_rejects \<open> *& mut r \<close>

urust_expr improvement_recursive_triple_deref \<open> ***rrr \<close>
lemma \<open> improvement_recursive_triple_deref = \<lbrakk> *(*(*rrr)) \<rbrakk> \<close>
  unfolding improvement_recursive_triple_deref_def by (rule refl)
old_urust_rejects \<open> ***rrr \<close>

end

no_adhoc_overloading store_dereference_const \<rightleftharpoons> parser_dereference_fixture


section\<open> Composable postfix expressions \<close>

text\<open>
The custom parser treats propagation, fields, and methods as one left-associative
postfix tier. The old frontend requires parentheses after propagation before a method
postfix.
\<close>

context fixes self :: postfix_outer
begin
urust_expr improvement_propagate_method
  \<open> self.optional?.to_value() \<close>

lemma \<open> improvement_propagate_method = \<lbrakk> (self.optional?).to_value() \<rbrakk> \<close>
  unfolding improvement_propagate_method_def by (rule refl)

old_urust_rejects
  \<open> self.optional?.to_value() \<close>
end

end
