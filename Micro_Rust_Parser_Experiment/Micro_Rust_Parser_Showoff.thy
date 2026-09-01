theory Micro_Rust_Parser_Showoff
  imports Micro_Rust_Parser
begin

section\<open> Showcase \<close>

text\<open>
These examples intentionally combine features. Shared-source examples check the
same text against the existing frontend; the improvements example checks an
explicit equivalent old-frontend term. Every equality is proved by \<open>refl\<close>.
\<close>

subsection\<open> Expressions, bindings, and control flow \<close>

text\<open>
Features: suffixed decimal and hexadecimal literals, nested tuple destructuring,
\<open>let\<close> and \<open>const\<close>, operator precedence, strings, and \<open>if\<close>/\<open>else\<close>.
\<close>

urust_expr_with_check showoff_expression
  \<open>
    let (base, (mask, enabled)) =
      (0x10_u32, (0x0f_u32, true));
    const shift = 1_u64;
    let computed = (base | mask) << shift;
    if enabled && computed > 0x20_u32 {
      (computed, "large")
    } else {
      (computed + 1_u32, "small")
    }
  \<close>


subsection\<open> Calls, methods, and propagation \<close>

definition showoff_bump ::
    \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_bump \<equiv> lift_fun1 (\<lambda>x. x + 1) \<close>

definition showoff_mix ::
    \<open>64 word \<Rightarrow> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_mix \<equiv> lift_fun2 (\<lambda>x y. x * 3 + y) \<close>

text\<open>
Features: a let-bound callee, nested calls, receiver-prepended method calls,
method chaining, Option propagation around call and method results, propagation
grouped before a method, a conditional argument, comparisons, and lexical binders.
\<close>

urust_expr_with_check showoff_calls
  \<open>
    let seed = 5_u64;
    let callable = \<llangle>showoff_bump\<rrangle>;
    let direct = Some(callable(seed))?;
    let chained =
      (Some(direct.showoff_mix(showoff_bump(2_u64)))?).showoff_bump();
    if chained >= 20_u64 {
      Some(
        chained.showoff_mix(
          (if true { Some(1_u64)? } else { Some(0_u64)? })
        )
      )?
    } else {
      Some(seed.showoff_bump().showoff_bump())?
    }
  \<close>


subsection\<open> Nested and guarded matches \<close>

datatype showoff_event =
    ShowoffData "nat option" bool
  | ShowoffRetry "nat option"
  | ShowoffStop

text\<open>
Features: automatic case routing, an explicit numeric switch, constructor and
value patterns, or-patterns, guards, nested matches, ordered fall-through, and
antiquotation capture of both a let-bound variable and an arm binder.
\<close>

text\<open>
C1-I5 gives a guarded or-pattern one source-arm guard and next-arm fall-through, so this showcase
uses the corrected semantics instead of asserting equality with the old alternative expansion.
\<close>

urust_expr showoff_matches
  \<open>
    let floor = \<llangle>2 :: nat\<rrangle>;
    match \<llangle>ShowoffData (Some 7) True\<rrangle> {
      ShowoffData(Some(x), true) | ShowoffRetry(Some(x))
          if x > floor \<Rightarrow>
        match_switch x {
          0 | 1 \<Rightarrow> floor,
          _ \<Rightarrow> \<llangle>x + floor\<rrangle>
        },
      ShowoffData(Some(x), false)
          if (match Some(x) {
            Some(_) \<Rightarrow> true,
            None \<Rightarrow> false
          }) \<Rightarrow>
        x,
      ShowoffData(None, _) | ShowoffRetry(None) | ShowoffStop \<Rightarrow>
        0,
      _ \<Rightarrow>
        1
    }
  \<close>


subsection\<open> Advanced patterns \<close>

datatype showoff_packet =
    ShowoffPacket
      (showoff_tag: nat)
      (showoff_payload: "nat list")
      (showoff_fallback: "nat option")
  | ShowoffEmpty

text\<open>
Features: struct, slice-rest, constructor, and or-patterns in one match, followed
by a guard and antiquotation capture of bindings from deep inside the pattern.
\<close>

urust_expr showoff_patterns
  \<open>
    match \<llangle>ShowoffPacket 2 [3, 5, 8] (Some 13)\<rrangle> {
      ShowoffPacket {
        showoff_tag: tag,
        showoff_payload: [head, .., tail],
        showoff_fallback: Some(backup)
      } if tag > 0 && backup > 0 \<Rightarrow>
        \<llangle>head + tail + backup\<rrangle>,
      ShowoffPacket {
        showoff_tag: _,
        showoff_payload: [],
        ..
      } | ShowoffEmpty \<Rightarrow>
        0,
      _ \<Rightarrow>
        1
    }
  \<close>


subsection\<open> Fueled loops and mutable state \<close>

definition showoff_reference ::
    \<open>'v \<Rightarrow> (unit, (unit, unit, 'v) Global_Store.ref, unit, unit, unit) function_body\<close>
  where \<open> showoff_reference \<equiv> undefined \<close>

definition showoff_dereference ::
    \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> (unit, 'v, unit, unit, unit) function_body\<close>
  where \<open> showoff_dereference \<equiv> undefined \<close>

definition showoff_update ::
    \<open>(unit, unit, 'v) Global_Store.ref \<Rightarrow> 'v \<Rightarrow>
      (unit, unit, unit, unit, unit) function_body\<close>
  where \<open> showoff_update \<equiv> undefined \<close>

adhoc_overloading store_reference_const \<rightleftharpoons> showoff_reference
adhoc_overloading store_dereference_const \<rightleftharpoons> showoff_dereference
adhoc_overloading store_update_const \<rightleftharpoons> showoff_update

text\<open>
Features: fuel captured from local binders, nested fueled loops, semicolon-free
loop sequencing, iterator conversion and loop-pattern binders, mutable word,
boolean, and optional state, numeric switching, assignment, and
\<open>while let\<close> termination.
\<close>

urust_expr_with_check showoff_nested_loops
  \<open>
    let outer_fuel = \<llangle>4 :: nat\<rrangle>;
    let inner_fuel = \<llangle>2 :: nat\<rrangle>;
    let mut phase = 0_u32;
    let mut active = \<llangle>True\<rrangle>;
    #[fuel(\<epsilon>\<open>outer_fuel\<close>)] while (*active) {
      match_switch *phase {
        0 \<Rightarrow> {
          *phase = *phase + 1_u32;
        },
        1 \<Rightarrow> {
          #[fuel(\<epsilon>\<open>inner_fuel\<close>)] loop {
            *phase = *phase + 1_u32;
          }
          *active = false;
        },
        _ \<Rightarrow> {
          *active = false;
        }
      };
    }
    (*phase, *active)
  \<close>

urust_expr_with_check showoff_for_and_while_let
  \<open>
    let values = \<llangle>[1 :: 32 word, 2, 3]\<rrangle>;
    let mut total = 0_u32;
    for value in values {
      *total += value;
    }
    let steps = \<llangle>2 :: nat\<rrangle>;
    let mut pending = \<llangle>Some (4 :: 32 word)\<rrangle>;
    #[fuel(\<epsilon>\<open>steps\<close>)] while let Some(extra) = *pending {
      *total += extra;
      *pending = None;
    }
    *total
  \<close>

text\<open>
Features: a match expression in the while condition, a direct function call on
dereferenced state, conditional loop-body control flow, a nested unconditional
loop, assignment from call results, and capture of two independent fuel binders.
\<close>

urust_expr_with_check showoff_loop_pipeline
  \<open>
    let scan_fuel = \<llangle>5 :: nat\<rrangle>;
    let burst_fuel = \<llangle>2 :: nat\<rrangle>;
    let mut cursor = 0_u64;
    #[fuel(\<epsilon>\<open>scan_fuel\<close>)] while (
      match_switch *cursor {
        0 | 1 | 2 \<Rightarrow> true,
        _ \<Rightarrow> false
      }
    ) {
      let next = showoff_bump(*cursor);
      if next == 2_u64 {
        #[fuel(\<epsilon>\<open>burst_fuel\<close>)] loop {
          *cursor = showoff_bump(*cursor);
        }
      } else {
        *cursor = next;
      }
    }
    *cursor
  \<close>


subsection\<open> Accepted-surface improvements \<close>

text\<open>
Features: Rust line comments and glued suffixes, trailing separators on calls,
tuples, and match arms, ASCII match arrows, propagation directly into a method,
and empty ordinary and unsafe blocks.
\<close>

urust_expr_with_check' showoff_improvements
  \<open>
    // These spellings are accepted only by the dedicated parser.
    let seed = 1u64;
    let bumped = Some(showoff_bump(seed,))?.showoff_bump();
    match Some(bumped) {
      Some(value) => (value, {}, unsafe {},),
      None => (0u64, {}, unsafe {},),
    }
  \<close>
  \<open>
    \<lbrakk>
      let seed = 1_u64;
      let bumped = (Some(showoff_bump(seed))?).showoff_bump();
      match Some(bumped) {
        Some(value) \<Rightarrow> (value, { () }, unsafe { () }),
        None \<Rightarrow> (0_u64, { () }, unsafe { () })
      }
    \<rbrakk>
  \<close>

no_adhoc_overloading store_reference_const \<rightleftharpoons> showoff_reference
no_adhoc_overloading store_dereference_const \<rightleftharpoons> showoff_dereference
no_adhoc_overloading store_update_const \<rightleftharpoons> showoff_update

end
