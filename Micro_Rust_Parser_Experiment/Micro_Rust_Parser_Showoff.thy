theory Micro_Rust_Parser_Showoff
  imports Micro_Rust_Parser
begin

section\<open> Showcase \<close>

text\<open>
These examples intentionally combine features. The corresponding frontend-parity
proofs are grouped at the end so the examples themselves remain easy to skim.
\<close>

subsection\<open> Expressions, bindings, and control flow \<close>

text\<open>
Features: suffixed decimal and hexadecimal literals, nested tuple destructuring,
\<open>let\<close> and \<open>const\<close>, operator precedence, strings, and \<open>if\<close>/\<open>else\<close>.
\<close>

urust_expr showoff_expression
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


subsection\<open> Calls and methods \<close>

definition showoff_bump ::
    \<open>64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_bump \<equiv> lift_fun1 (\<lambda>x. x + 1) \<close>

definition showoff_mix ::
    \<open>64 word \<Rightarrow> 64 word \<Rightarrow> (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> showoff_mix \<equiv> lift_fun2 (\<lambda>x y. x * 3 + y) \<close>

text\<open>
Features: a let-bound callee, nested calls, receiver-prepended method calls,
method chaining, a conditional argument, comparisons, and lexical binders.
\<close>

urust_expr showoff_calls
  \<open>
    let seed = 5_u64;
    let callable = \<llangle>showoff_bump\<rrangle>;
    let direct = callable(seed);
    let chained =
      direct.showoff_mix(showoff_bump(2_u64)).showoff_bump();
    if chained >= 20_u64 {
      showoff_mix(
        chained,
        (if true { 1_u64 } else { 0_u64 })
      )
    } else {
      showoff_bump(showoff_bump(seed))
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


section\<open> Frontend parity \<close>

lemma showoff_expression_frontend:
  \<open> showoff_expression =
    \<lbrakk>
      let (base, (mask, enabled)) =
        (0x10_u32, (0x0f_u32, true));
      const shift = 1_u64;
      let computed = (base | mask) << shift;
      if enabled && computed > 0x20_u32 {
        (computed, "large")
      } else {
        (computed + 1_u32, "small")
      }
    \<rbrakk> \<close>
  unfolding showoff_expression_def by (rule refl)

lemma showoff_calls_frontend:
  \<open> showoff_calls =
    \<lbrakk>
      let seed = 5_u64;
      let callable = \<llangle>showoff_bump\<rrangle>;
      let direct = callable(seed);
      let chained =
        direct.showoff_mix(showoff_bump(2_u64)).showoff_bump();
      if chained >= 20_u64 {
        showoff_mix(
          chained,
          (if true { 1_u64 } else { 0_u64 })
        )
      } else {
        showoff_bump(showoff_bump(seed))
      }
    \<rbrakk> \<close>
  unfolding showoff_calls_def by (rule refl)

lemma showoff_matches_frontend:
  \<open> showoff_matches =
    \<lbrakk>
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
    \<rbrakk> \<close>
  unfolding showoff_matches_def by (rule refl)

lemma showoff_patterns_frontend:
  \<open> showoff_patterns =
    \<lbrakk>
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
    \<rbrakk> \<close>
  unfolding showoff_patterns_def by (rule refl)

end
