theory Parser_Old_New_Comparison
  imports Micro_Rust_Parser_Impl.Parser_Impl_Command
begin

declare [[urust_conformance = false]]
declare [[urust_pp_test = true]]
declare [[show_results = false]]

chapter\<open> Old and new parser comparison \<close>

text\<open>
This theory is a presentation-oriented comparison rather than a conformance suite. Every section
contains one source parsed explicitly through the legacy \<open>\<lbrakk>...\<rbrakk>\<close> frontend and one
source parsed explicitly through the dedicated parser. There are deliberately no equality proofs,
generated conformance facts, or \<open>against\<close> clauses.

Each comparison keeps the legacy and dedicated source snippets within forty lines together. The
pairs remain compositional rather than becoming targeted unit tests. In Isabelle/jEdit, compare the
source markup directly: the dedicated parser distinguishes Rust keywords, operators, delimiters,
literals, binders, registered calls, constructor paths, and embedded HOL, and it gives registered
path segments useful hover and navigation targets.
\<close>

section\<open> Shared source and PIDE navigation \<close>

definition comparison_bump ::
    \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> comparison_bump \<equiv> lift_fun1 (\<lambda>value. value + 1) \<close>

definition comparison_mix ::
    \<open>64 word \<Rightarrow> 64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> comparison_mix \<equiv> lift_fun2 (\<lambda>left right. left * 3 + right) \<close>

definition comparison_generic_bump ::
    \<open>nat \<Rightarrow> 64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> comparison_generic_bump _ \<equiv> comparison_bump \<close>

definition comparison_generic_parameter :: nat
  where \<open> comparison_generic_parameter = 1 \<close>

urust_notation (call) comparison_generic_bump ("Comparison::bump")

text\<open>
The first two pairs use identical source on both sides. The first composes collection and matching
syntax; the second concentrates the PIDE comparison around a registered path, lexical references,
tuple projections, a method call, a formal comment, and both kinds of embedded HOL.
\<close>

subsection\<open> Collections, macros, and guarded matching \<close>

definition comparison_collections_old
  where
    \<open>
      comparison_collections_old \<equiv>
        \<lbrakk>
          let candidates = vec![Some(5_u64), Some(2_u64), None];
          let first = candidates[0_usize];
          match first {
            Some(value) if matches!(Some(value), Some(_)) \<Rightarrow>
              value,
            None \<Rightarrow>
              0_u64,
            _ \<Rightarrow>
              1_u64
          }
        \<rbrakk>
    \<close>

urust_expr
  comparison_collections_new
  \<open>
    let candidates = vec![Some(5_u64), Some(2_u64), None];
    let first = candidates[0_usize];
    match first {
      Some(value) if matches!(Some(value), Some(_)) \<Rightarrow>
        value,
      None \<Rightarrow>
        0_u64,
      _ \<Rightarrow>
        1_u64
    }
  \<close>

subsection\<open> Registered paths, embeddings, and editor navigation \<close>

definition comparison_navigation_old
  where
    \<open>
      comparison_navigation_old \<equiv>
        \<lbrakk>
          \<comment> \<open>Isabelle document source inside active uRust source.\<close>
          let callable = \<llangle>comparison_bump\<rrangle>;
          let direct =
            Comparison::bump::<comparison_generic_parameter + 1>(
              \<epsilon>\<open>callable\<close>(5_u64)
            );
          let projected = (direct, (Some(2_u64), true));
          assert!(projected.1.1);
          if let Some(extra) = projected.1.0 {
            direct.comparison_mix(extra)
          } else {
            direct
          }
        \<rbrakk>
    \<close>

urust_expr
  comparison_navigation_new
  \<open>
    \<comment> \<open>Isabelle document source inside active uRust source.\<close>
    let callable = \<llangle>comparison_bump\<rrangle>;
    let direct =
      Comparison::bump::<comparison_generic_parameter + 1>(
        \<epsilon>\<open>callable\<close>(5_u64)
      );
    let projected = (direct, (Some(2_u64), true));
    assert!(projected.1.1);
    if let Some(extra) = projected.1.0 {
      direct.comparison_mix(extra)
    } else {
      direct
    }
  \<close>

section\<open> Composed Rust-shaped source improvements \<close>

definition comparison_u64_max :: \<open>64 word\<close>
  where \<open> comparison_u64_max = 63 \<close>

definition comparison_references ::
    \<open>(unit, unit, 64 word) Global_Store.ref list\<close>
  where \<open> comparison_references = undefined \<close>

definition comparison_dereference ::
    \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow>
      (unit, 'v, unit, unit, unit) function_body\<close>
  where \<open> comparison_dereference = undefined \<close>

micro_rust_notation (literal) comparison_u64_max ("u64::MAX")

adhoc_overloading store_dereference_const \<rightleftharpoons> comparison_dereference

text\<open>
These three pairs contrast legacy compatibility spellings with dedicated-parser syntax. Together
they retain the lexer, array, path, call, control-flow, total-binding, precedence, and block
improvements without placing every improvement in one source block.
\<close>

subsection\<open> Comments, arrays, suffixes, and primitive paths \<close>

definition comparison_arrays_old
  where
    \<open>
      comparison_arrays_old \<equiv>
        \<lbrakk>
          let seeds = [1_u64, 2_u64];
          let seed = seeds[0_usize];
          let repeated =
            [seed + 1_u64, seed + 1_u64, seed + 1_u64];
          let limit = comparison_u64_max;
          (repeated[1_usize], limit)
        \<rbrakk>
    \<close>

urust_expr
  comparison_arrays_new
  \<open>
    // The dedicated lexer owns Rust comments and reports their complete spans.
    let seeds = [1u64, 2u64,];
    let seed = seeds[0usize];
    let repeated = [
      const {
        /* Nested comment /* inner comment */ remains layout. */
        seed + 1u64
      };
      3usize
    ];
    let limit = u64::MAX;
    (repeated[1usize], limit)
  \<close>

subsection\<open> Propagation, methods, trailing commas, and else-if chains \<close>

definition comparison_control_old
  where
    \<open>
      comparison_control_old \<equiv>
        \<lbrakk>
          let seed = 1_u64;
          let limit = comparison_u64_max;
          let bumped =
            (Some(comparison_bump(seed))?).comparison_bump();
          if seed == 0_u64 {
            seed
          } else {
            if let Some(value) = Some(bumped) {
              value
            } else {
              if bumped > limit {
                bumped
              } else {
                seed
              }
            }
          }
        \<rbrakk>
    \<close>

urust_expr
  comparison_control_new
  \<open>
    let seed = 1u64;
    let limit = u64::MAX;
    let bumped = Some(comparison_bump(seed,))?.comparison_bump();
    if seed == 0u64 {
      seed
    } else if let Some(value) = Some(bumped) {
      value
    } else if bumped > limit {
      bumped
    } else {
      seed
    }
  \<close>

subsection\<open> Total bindings, precedence, ASCII arrows, and empty blocks \<close>

definition comparison_total_old
  where
    \<open>
      comparison_total_old \<equiv>
        \<lbrakk>
          let selected = 1_u64;
          let total = selected;
          let references = \<llangle>comparison_references\<rrangle>;
          let dereferenced = *(references[0_usize]);
          let narrowed = (!total) as u8;
          let widened = narrowed as u64;
          match Some(total) {
            Some(value) \<Rightarrow>
              (value, dereferenced, widened, { () }, unsafe { () }),
            None \<Rightarrow>
              (0_u64, dereferenced, widened, { () }, unsafe { () })
          }
        \<rbrakk>
    \<close>

urust_expr
  comparison_total_new
  \<open>
    let selected = 1u64;
    let total =
      if let selected_value = selected {
        selected_value
      } else {
        false
      };
    let references = \<llangle>comparison_references\<rrangle>;
    let dereferenced = *references[0usize];
    let narrowed = !total as u8;
    let widened = narrowed as u64;
    match Some(total) {
      Some(value) => (value, dereferenced, widened, {}, unsafe {},),
      None => (0u64, dereferenced, widened, {}, unsafe {},),
    }
  \<close>

no_adhoc_overloading store_dereference_const \<rightleftharpoons> comparison_dereference

section\<open> Matching semantics and hygienic binders \<close>

datatype comparison_status =
    ComparisonPrimary
  | ComparisonSecondary
  | ComparisonTertiary

micro_rust_notation (literal)
  comparison_status.ComparisonPrimary
  ("ComparisonStatus::Primary")
micro_rust_notation (literal)
  comparison_status.ComparisonSecondary
  ("ComparisonStatus::Secondary")
micro_rust_notation (literal)
  comparison_status.ComparisonTertiary
  ("ComparisonStatus::Tertiary")

text\<open>
These pairs again use identical source. Both frontends accept them, but the legacy matcher is known
to miscompile the qualified registered nullary constructor nested beneath \<open>Err\<close> and the fallback
that refers to an outer binder sharing its spelling with a guarded arm binder. The dedicated parser
retains authenticated constructor identity, allocates fresh lexical identities per source binder,
and preserves source-arm fallthrough for the overlapping guarded or-pattern.
\<close>

subsection\<open> Registered nullary constructors beneath outer patterns \<close>

(* BUG: The legacy matcher loses registered constructor identity for a qualified nullary constructor nested beneath Err. *)
definition comparison_constructor_old
  where
    \<open>
      comparison_constructor_old \<equiv>
        \<lbrakk>
          match \<llangle>Err ComparisonSecondary ::
              (unit, comparison_status) result\<rrangle> {
            Err(ComparisonStatus::Primary) \<Rightarrow>
              \<llangle>10 :: nat\<rrangle>,
            result \<Rightarrow>
              match result {
                Ok(_) \<Rightarrow> \<llangle>30 :: nat\<rrangle>,
                Err(_) \<Rightarrow> \<llangle>20 :: nat\<rrangle>
              }
          }
        \<rbrakk>
    \<close>

urust_expr
  comparison_constructor_new
  \<open>
    match \<llangle>Err ComparisonSecondary ::
        (unit, comparison_status) result\<rrangle> {
      Err(ComparisonStatus::Primary) \<Rightarrow>
        \<llangle>10 :: nat\<rrangle>,
      result \<Rightarrow>
        match result {
          Ok(_) \<Rightarrow> \<llangle>30 :: nat\<rrangle>,
          Err(_) \<Rightarrow> \<llangle>20 :: nat\<rrangle>
        }
    }
  \<close>

subsection\<open> Shadowed fallbacks and guarded or-patterns \<close>

(* BUG: The legacy matcher captures the outer fallback through a same-named arm binder and mishandles guarded or-pattern fallthrough. *)
definition comparison_hygiene_old
  where
    \<open>
      comparison_hygiene_old \<equiv>
        \<lbrakk>
          let outer = \<llangle>0 :: nat\<rrangle>;
          let shadowed =
            match \<llangle>Some (1 :: nat)\<rrangle> {
              Some(outer) if False \<Rightarrow>
                \<llangle>outer\<rrangle>,
              _ \<Rightarrow>
                outer
            };
          let guarded =
            match true {
              true | _ if False \<Rightarrow>
                \<llangle>1 :: nat\<rrangle>,
              _ \<Rightarrow>
                \<llangle>2 :: nat\<rrangle>
            };
          (shadowed, guarded)
        \<rbrakk>
    \<close>

urust_expr
  comparison_hygiene_new
  \<open>
    let outer = \<llangle>0 :: nat\<rrangle>;
    let shadowed =
      match \<llangle>Some (1 :: nat)\<rrangle> {
        Some(outer) if False \<Rightarrow>
          \<llangle>outer\<rrangle>,
        _ \<Rightarrow>
          outer
      };
    let guarded =
      match true {
        true | _ if False \<Rightarrow>
          \<llangle>1 :: nat\<rrangle>,
        _ \<Rightarrow>
          \<llangle>2 :: nat\<rrangle>
      };
    (shadowed, guarded)
  \<close>

section\<open> Function declarations and command integration \<close>

definition comparison_invoke ::
    \<open>64 word \<Rightarrow>
      (64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body) \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> comparison_invoke value closure \<equiv> closure value \<close>

text\<open>
The legacy frontend parses only the body, so the surrounding Isabelle definition must repeat the
complete type, parameters, equation, and \<open>FunctionBody\<close> wrapper. The dedicated command parses
the same kind of complete function from typed lexical parameters, generates the declaration, and
checks its canonical parse-print-parse roundtrip. The declaration body retains the dedicated
parser's binder, token-role, embedded-HOL, and navigation markup without requesting a conformance
phase.
\<close>

subsection\<open> Legacy frontend and handwritten declaration boilerplate \<close>

definition comparison_pipeline_old ::
    \<open>64 word \<Rightarrow> 64 word \<Rightarrow>
      (unit, 64 word, unit, unit, unit) function_body\<close>
  where
    \<open>
      comparison_pipeline_old left right \<equiv>
        FunctionBody
          \<lbrakk>
            let inputs = [left, right, 1_u64];
            let paired =
              (inputs[0_usize], (inputs[1_usize], true));
            let chosen =
              if paired.1.1 && paired.0 >= paired.1.0 {
                comparison_bump(paired.0)
              } else {
                paired.1.0
              };
            comparison_invoke(
              chosen,
              |item| {
                let adjusted = item.comparison_mix(right);
                if adjusted > 0_u64 {
                  return adjusted;
                } else {
                  return left;
                }
              }
            )
          \<rbrakk>
    \<close>

subsection\<open> Dedicated parser and generated declaration \<close>

urust_fn
  comparison_pipeline_new ::
  \<open>64 word \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  (left, right)
  \<open>
    let inputs = [left, right, 1u64,];
    let paired =
      (inputs[0usize], (inputs[1usize], true));
    let chosen =
      if paired.1.1 && paired.0 >= paired.1.0 {
        comparison_bump(paired.0)
      } else {
        paired.1.0
      };
    comparison_invoke(
      chosen,
      |item| {
        let adjusted = item.comparison_mix(right);
        if adjusted > 0u64 {
          return adjusted
        } else {
          return left
        }
      },
    )
  \<close>

ML_val\<open>
  val comparison_names =
    ["comparison_collections_new_conformance",
     "comparison_navigation_new_conformance",
     "comparison_arrays_new_conformance",
     "comparison_control_new_conformance",
     "comparison_total_new_conformance",
     "comparison_constructor_new_conformance",
     "comparison_hygiene_new_conformance",
     "comparison_pipeline_new_conformance"]
  val _ =
    if exists (Global_Theory.defined_fact \<^theory>) comparison_names
    then error "old/new comparison unexpectedly generated a conformance theorem"
    else ()
\<close>

end
