theory Parser_Test_Regression_Audit
  imports
    Parser_Test_Improvements
    Parser_Test_Negative_Conformance
    Parser_Test_Utils
begin

section\<open> Frontend-shape structural audit \<close>

text\<open>
Guarded case compilation must reproduce the existing frontend's expanded term directly. In
particular, the scrutinee is evaluated once, source handlers are duplicated across expanded
or-alternatives exactly as in the frontend, and a false source guard enters the next source arm rather
than retrying a sibling alternative. No parser-private HOL constant may mediate that term shape.
\<close>

datatype cycle1_case =
    Cycle1_A | Cycle1_B

consts
  cycle1_scrutinee :: cycle1_case
  cycle1_guard_marker :: \<open>nat \<Rightarrow> bool\<close>
  cycle1_first_body :: nat
  cycle1_next_body :: nat
  cycle1_last_body :: nat
  cycle1_while_body_marker :: unit

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 1 pattern audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source source)

    fun antiquotation source =
      "\<llangle>" ^ source ^ "\<rrangle>"

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_named_constant base_name term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if Long_Name.base_name name = base_name
              then Integer.add 1
              else I
          | _ => I)
        term 0

    fun conditional_branches term =
      let
        fun collect
            (Const (name, _) $ condition $ then_branch $ else_branch) branches =
              let
                val nested =
                  collect condition
                    (collect then_branch
                      (collect else_branch branches))
              in
                if name = \<^const_name>\<open>two_armed_conditional\<close>
                then (condition, then_branch, else_branch) :: nested
                else nested
              end
          | collect (left $ right) branches =
              collect left (collect right branches)
          | collect (Abs (_, _, body)) branches =
              collect body branches
          | collect _ branches = branches
      in collect term [] end

    val fallthrough =
      checked
        ("match " ^ antiquotation "cycle1_scrutinee" ^ " { " ^
         "Cycle1_A | Cycle1_B if " ^
         antiquotation "cycle1_guard_marker 99" ^ " \<Rightarrow> " ^
         antiquotation "cycle1_first_body" ^
         ", Cycle1_B \<Rightarrow> " ^ antiquotation "cycle1_next_body" ^
         ", _ \<Rightarrow> " ^ antiquotation "cycle1_last_body" ^ " }")
    val _ =
      audit_assert "the guarded match did not bind its scrutinee exactly once"
        (count_constant \<^const_name>\<open>cycle1_scrutinee\<close> fallthrough = 1)
    val _ =
      audit_assert "the guarded source body did not retain frontend expansion"
        (count_constant \<^const_name>\<open>cycle1_first_body\<close> fallthrough = 2)
    val _ =
      audit_assert "the term contains a parser-private administrative constant"
        (count_named_constant "urust_admin_let" fallthrough = 0)
    val guarded =
      filter
        (fn (_, then_branch, _) =>
          count_constant \<^const_name>\<open>cycle1_first_body\<close>
            then_branch > 0)
        (conditional_branches fallthrough)
    val _ =
      audit_assert "the direct term contains no source-guard false branch"
        (not (null guarded))
    val _ =
      List.app
        (fn (_, _, else_branch) =>
          (audit_assert
             "a false source guard retried a sibling or-alternative"
             (count_constant \<^const_name>\<open>cycle1_first_body\<close>
                else_branch = 0);
           audit_assert
             "a false source guard did not continue with the next source arm"
             (count_constant \<^const_name>\<open>cycle1_next_body\<close>
                else_branch > 0)))
        guarded
  in
    val _ = ()
  end
\<close>

section\<open> Full guard-body grammar audit \<close>

text\<open>
Match guards reuse the complete non-nullable body grammar. This audit checks the AST before
elaboration, including branches whose final type is intentionally not boolean.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>
    val arm_prefix = "match_case Some(()) { Some(_) if "
    val arm_suffix = " => (), None => (), }"

    fun audit_assert message condition =
      if condition then ()
      else error ("full guard-body grammar audit: " ^ message)

    fun source_text guard = arm_prefix ^ guard ^ arm_suffix

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "full guard-body grammar audit: empty parse")

    fun guard_of source =
      (case parse source of
         UE_Match
           (MF_Case, _,
            UR_Arm (_, SOME (guard, if_pos), UE_Unit _) ::
              UR_Arm (_, NONE, UE_Unit _) :: [],
            _) =>
           (guard, if_pos)
       | _ =>
           error
             "full guard-body grammar audit: wrapper AST changed")

    fun parse_guard guard =
      guard_of
        (Parser_Lex_Util.text_source (source_text guard))

    fun check_guard label guard expected =
      let val (expression, _) = parse_guard guard
      in
        audit_assert (label ^ " AST changed") (expected expression)
      end

    fun is_true (UE_Literal (LP_Bool (true, _))) = true
      | is_true _ = false

    fun is_unit (UE_Unit _) = true
      | is_unit _ = false

    fun is_path name (UE_Path path) = render_path path = name
      | is_path _ _ = false

    val _ = check_guard "terminal value" "true" is_true
    val _ =
      check_guard "semicolon value sequence" "(); true"
        (fn UE_Seq (left, right) =>
              is_unit left andalso is_true right
          | _ => false)
    val _ =
      check_guard "terminal statement" "();"
        (fn UE_Seq (left, right) =>
              is_unit left andalso is_unit right
          | _ => false)
    val _ =
      check_guard "block prefix" "{ () } true"
        (fn UE_Seq (UE_Block (body, _), right) =>
              is_unit body andalso is_true right
          | _ => false)
    val _ =
      check_guard "unsafe-block prefix" "unsafe { () } true"
        (fn UE_Seq (UE_Block (body, _), right) =>
              is_unit body andalso is_true right
          | _ => false)
    val _ =
      check_guard "conditional prefix"
        "if false { () } else { () } true"
        (fn UE_Seq (UE_If _, right) => is_true right
          | _ => false)
    val _ =
      check_guard "while prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while (false) { () } true")
        (fn UE_Seq (UE_While _, right) => is_true right
          | _ => false)
    val _ =
      check_guard "loop prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () } true")
        (fn UE_Seq (UE_Loop _, right) => is_true right
          | _ => false)
    val _ =
      check_guard "for prefix"
        "for item in values { () } true"
        (fn UE_Seq (UE_For (P_Ident ("item", _), _, _, _), right) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "while-let prefix"
        ("#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
         "Some(item) = Some(()) { () } true")
        (fn UE_Seq
              (UE_WhileLet
                (_, P_Constr (path, [P_Ident ("item", _)]),
                 _, _, _),
               right) =>
              render_path path = "Some" andalso is_true right
          | _ => false)
    val _ =
      check_guard "bare-match prefix"
        "match true { true => (), false => () } true"
        (fn UE_Seq (UE_Match (MF_Auto, _, _, _), right) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "explicit case-match prefix"
        "match_case Some(()) { Some(value) => value, None => () } true"
        (fn UE_Seq (UE_Match (MF_Case, _, _, _), right) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "explicit switch-match prefix"
        "match_switch 0 { 0 => (), _ => () } true"
        (fn UE_Seq (UE_Match (MF_Switch, _, _, _), right) =>
              is_true right
          | _ => false)
    val _ =
      check_guard "let binding"
        "let flag = true; flag"
        (fn UE_Let (P_Ident ("flag", _), value, body) =>
              is_true value andalso is_path "flag" body
          | _ => false)
    val _ =
      check_guard "mutable binding"
        "let mut flag = true; true"
        (fn UE_LetMut (P_Ident ("flag", _), value, body, _) =>
              is_true value andalso is_true body
          | _ => false)
    val _ =
      check_guard "const binding"
        "const FLAG = true; FLAG"
        (fn UE_Const (P_Ident ("FLAG", _), value, body) =>
              is_true value andalso is_path "FLAG" body
          | _ => false)
    val _ =
      check_guard "let-else binding"
        "let Some(flag) = Some(true) else { false }; flag"
        (fn UE_LetElse
              (P_Constr (path, [P_Ident ("flag", _)]),
               _, UE_Block (fallback, _), body, _) =>
              render_path path = "Some" andalso is_path "flag" body andalso
                (case fallback of
                   UE_Literal (LP_Bool (false, _)) => true
                 | _ => false)
          | _ => false)
    val _ =
      check_guard "right-associated bindings"
        "let first = true; const SECOND = first; SECOND"
        (fn UE_Let
              (P_Ident ("first", _), _,
               UE_Const
                 (P_Ident ("SECOND", _), first, second)) =>
              is_path "first" first andalso is_path "SECOND" second
          | _ => false)
    val _ =
      check_guard "if-let value"
        "if let Some(flag) = Some(true) { flag } else { false }"
        (fn UE_IfLet
              (P_Constr (path, [P_Ident ("flag", _)]),
               _, UE_Block (body, _),
               SOME (UE_Block (UE_Literal (LP_Bool (false, _)), _)), _) =>
              render_path path = "Some" andalso is_path "flag" body
          | _ => false)
    val _ =
      check_guard "legacy return with operand" "return true;"
        (fn UE_Return (SOME value, _) => is_true value
          | _ => false)
    val _ =
      check_guard "legacy operandless return" "return;"
        (fn UE_Return (NONE, _) => true
          | _ => false)
    val _ =
      check_guard "tail return" "return true"
        (fn UE_Return (SOME value, _) => is_true value
          | _ => false)

    val positioned_guard =
      "if let Some(flag) = Some(true) { flag } else { false }"
    val positioned_text = source_text positioned_guard
    val positioned_start =
      Position.make0 17 80 200 "" "" "full-guard-body-ast-audit"
    val (positioned_ast, arm_if_pos) =
      guard_of
        (Parser_Lex_Util.positioned_content_source
          positioned_text positioned_start)
    val arm_if_raw = size arm_prefix - size "if "
    val guard_stop_raw = size arm_prefix + size positioned_guard
    fun position_at raw =
      Position.symbol_explode
        (String.substring (positioned_text, 0, raw))
        positioned_start
    val _ =
      audit_assert "guard keyword position moved"
        (Position.offset_of arm_if_pos =
          Position.offset_of (position_at arm_if_raw))
    val _ =
      (case positioned_ast of
         UE_IfLet (_, _, _, _, span) =>
           (audit_assert "if-let guard span start moved"
              (Position.offset_of span =
                Position.offset_of (position_at (size arm_prefix)));
            audit_assert "if-let guard span stopped before the arrow"
              (Position.end_offset_of span =
                Position.offset_of (position_at guard_stop_raw)))
       | _ =>
           error
             "full guard-body grammar audit: positioned if-let AST changed")

    val positioned_let_else =
      "let Some(flag) = Some(true) else { false }; flag"
    val positioned_let_else_text = source_text positioned_let_else
    val (positioned_let_else_ast, _) =
      guard_of
        (Parser_Lex_Util.positioned_content_source
          positioned_let_else_text positioned_start)
    val positioned_let_else_stop =
      Position.symbol_explode
        (String.substring
          (positioned_let_else_text, 0,
           size arm_prefix + size positioned_let_else))
        positioned_start
    val _ =
      (case positioned_let_else_ast of
         UE_LetElse (_, _, _, _, span) =>
           (audit_assert "let-else guard span start moved"
              (Position.offset_of span =
                Position.offset_of (position_at (size arm_prefix)));
            audit_assert "let-else guard span stopped before the arrow"
              (Position.end_offset_of span =
                Position.offset_of positioned_let_else_stop))
       | _ =>
           error
             "full guard-body grammar audit: positioned let-else AST changed")

    val non_boolean_source = source_text "();"
    val (non_boolean_ast, _) =
      guard_of (Parser_Lex_Util.text_source non_boolean_source)
    val _ =
      audit_assert "non-boolean terminal statement did not parse"
        (case non_boolean_ast of
           UE_Seq (left, right) =>
             is_unit left andalso is_unit right
         | _ => false)
    val _ =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source non_boolean_source)) () of
         Exn.Res _ =>
           error
             "full guard-body grammar audit: non-boolean guard type-checked"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "non-boolean guard failed outside boolean checking"
               (String.isSubstring "bool" (Runtime.exn_message exn)))
  in
    val _ = writeln "Full guard-body grammar audit passed"
  end
\<close>

section\<open> Conservative while-let coverage \<close>

text\<open>
C1-I6 removes the false continuation only for coverage proved by the resolved-pattern metadata.
The condition still sequences the source body with true, and the bounded loop body remains skip.
Partial patterns retain exactly one false fallback.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("Cycle 1 while-let audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source source)

    fun antiquotation source =
      "\<llangle>" ^ source ^ "\<rrangle>"

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun loop_source pattern scrutinee =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let " ^
      pattern ^ " = " ^ scrutinee ^ " { let _ = " ^
      antiquotation "cycle1_while_body_marker" ^ "; () }"

    fun bounded_while_arguments term =
      let
        fun find
            (Const (name, _) $ fuel $ condition $ body) =
              if name = \<^const_name>\<open>bounded_while\<close>
              then SOME (fuel, condition, body)
              else
                get_first find [fuel, condition, body]
          | find (left $ right) =
              (case find left of
                 SOME result => SOME result
               | NONE => find right)
          | find (Abs (_, _, body)) = find body
          | find _ = NONE
      in
        (case find term of
           SOME result => result
         | NONE => error "Cycle 1 while-let audit: bounded_while was not generated")
      end

    fun is_skip term =
      (case Term.strip_comb term of
         (Const (literal_name, _), [Const (unit_name, _)]) =>
           literal_name = \<^const_name>\<open>literal\<close> andalso
             unit_name = \<^const_name>\<open>Product_Type.Unity\<close>
       | _ => false)

    fun check_exhaustive label source =
      let
        val term = checked source
        val (_, condition, body) = bounded_while_arguments term
      in
        audit_assert (label ^ " retained a false fallback")
          (count_constant \<^const_name>\<open>False\<close> term = 0);
        audit_assert (label ^ " moved the source body out of the condition")
          (count_constant
             \<^const_name>\<open>cycle1_while_body_marker\<close>
             condition > 0);
        audit_assert (label ^ " did not keep skip as the bounded loop body")
          (is_skip body)
      end

    val _ =
      check_exhaustive "TNil"
        (loop_source "TNil" "TNil")
    val _ =
      check_exhaustive "complete option family"
        (loop_source "Some(_) | None"
          (antiquotation "Some (1 :: nat)"))
    val _ =
      check_exhaustive "nested complete option family"
        (loop_source "Some(Some(_) | None) | None"
          (antiquotation "Some (None :: nat option)"))

    val partial =
      checked
        (loop_source "Some(_)"
          (antiquotation "None :: nat option"))
    val (_, partial_condition, partial_body) =
      bounded_while_arguments partial
    val _ =
      audit_assert "a partial while-let pattern lost its false fallback"
        (count_constant \<^const_name>\<open>False\<close> partial = 1)
    val _ =
      audit_assert "a partial while-let moved the source body out of the condition"
        (count_constant
           \<^const_name>\<open>cycle1_while_body_marker\<close>
           partial_condition > 0)
    val _ =
      audit_assert "a partial while-let did not keep skip as the bounded loop body"
        (is_skip partial_body)
  in
    val _ = writeln "Cycle 1 conservative while-let coverage audit passed"
  end
\<close>

section\<open> Conditional binding structure and markup \<close>

text\<open>
Certified-total conditional bindings use the same case shape as an explicit complete match and omit
the unreachable fallback only after lowering it. Partial patterns retain the frontend-shaped wildcard
case. These audits also pin mixed-chain pruning, the top-level tuple exception, conservative coverage,
scope, diagnostics, recovery, and editor markup.
\<close>

consts
  conditional_let_scrutinee_marker :: \<open>nat option\<close>
  conditional_let_success_marker :: nat
  conditional_let_fallback_marker :: nat
  conditional_chain_first_scrutinee_marker :: \<open>nat option\<close>
  conditional_chain_second_condition_marker :: bool
  conditional_chain_last_scrutinee_marker :: \<open>nat option\<close>
  conditional_chain_first_success_marker :: nat
  conditional_chain_second_success_marker :: nat
  conditional_chain_last_success_marker :: nat
  conditional_chain_fallback_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("conditional-binding regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "conditional-binding regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse_text text)

    fun path_named name path = render_path path = name
    fun expression_named name (UE_Path path) = path_named name path
      | expression_named _ _ = false
    fun call_named name (UE_Call (UC_Path path, _, _)) =
          path_named name path
      | call_named _ _ = false

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    val if_text =
      "if let Some(value) = Some(1) { value } else { 0 }"
    val if_start =
      Position.make0 7 30 0 "" "" "conditional-binding-ast-audit"
    val if_stop =
      Position.symbol_explode if_text if_start
    val if_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          if_text if_start)
    val _ =
      (case if_ast of
         UE_IfLet
           (P_Constr (pattern_path, [P_Ident ("value", _)]),
            call,
            UE_Block (body, _),
            SOME (UE_Block (UE_Literal (LP_Integer ("0", _)), _)),
            position) =>
           (audit_assert "if-let path structure changed"
              (path_named "Some" pattern_path andalso
               call_named "Some" call andalso
               expression_named "value" body);
            audit_assert "if-let span start moved"
              (Position.offset_of position =
                Position.offset_of if_start);
            audit_assert "if-let span end moved"
              (Position.end_offset_of position =
                Position.offset_of if_stop))
       | _ =>
           error "conditional-binding regression audit: if-let AST changed")

    val mixed_text =
      "if let Some(first) = Some(1) { first } else if false { 2 } " ^
      "else if let Some(last) = Some(3) { last } else { 4 }"
    val mixed_start =
      Position.make0 13 70 0 "" "" "conditional-chain-ast-audit"
    val mixed_stop =
      Position.symbol_explode mixed_text mixed_start
    val mixed_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          mixed_text mixed_start)
    val _ =
      (case mixed_ast of
         UE_IfLet
           (P_Constr (first_pattern_path, [P_Ident ("first", _)]),
            first_call,
            UE_Block (first_body, _),
            SOME
              (UE_If
                (UE_Literal (LP_Bool (false, _)),
                 UE_Block (UE_Literal (LP_Integer ("2", _)), _),
                 SOME
                   (UE_IfLet
                     (P_Constr (last_pattern_path, [P_Ident ("last", _)]),
                      last_call,
                      UE_Block (last_body, _),
                      SOME
                        (UE_Block
                          (UE_Literal (LP_Integer ("4", _)), _)),
                      nested_position)),
                 _)),
            position) =>
           (audit_assert "mixed-chain path structure changed"
              (path_named "Some" first_pattern_path andalso
               call_named "Some" first_call andalso
               expression_named "first" first_body andalso
               path_named "Some" last_pattern_path andalso
               call_named "Some" last_call andalso
               expression_named "last" last_body);
            audit_assert "mixed-chain span start moved"
              (Position.offset_of position =
                Position.offset_of mixed_start);
            audit_assert "mixed-chain span stopped before the final arm"
              (Position.end_offset_of position =
                Position.offset_of mixed_stop);
            audit_assert "nested if-let span stopped before its fallback"
              (Position.end_offset_of nested_position =
                Position.offset_of mixed_stop))
       | _ =>
           error
             "conditional-binding regression audit: mixed-chain AST changed")

    val let_text =
      "let Some(value) = Some(1) else { 0 }; value"
    val let_start =
      Position.make0 11 50 0 "" "" "conditional-binding-ast-audit"
    val let_stop =
      Position.symbol_explode let_text let_start
    val let_ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          let_text let_start)
    val _ =
      (case let_ast of
         UE_LetElse
           (P_Constr (pattern_path, [P_Ident ("value", _)]),
            call,
            UE_Block (UE_Literal (LP_Integer ("0", _)), _),
            body,
            position) =>
           (audit_assert "let-else path structure changed"
              (path_named "Some" pattern_path andalso
               call_named "Some" call andalso
               expression_named "value" body);
            audit_assert "let-else span start moved"
              (Position.offset_of position =
                Position.offset_of let_start);
            audit_assert "let-else span end moved"
              (Position.end_offset_of position =
                Position.offset_of let_stop))
       | _ =>
           error "conditional-binding regression audit: let-else AST changed")

    val mixed_chain =
      checked
        ("if let Some(first) = " ^
         "\<llangle>conditional_chain_first_scrutinee_marker\<rrangle> { " ^
         "let _ = first; " ^
         "\<llangle>conditional_chain_first_success_marker\<rrangle> " ^
         "} else if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else if let Some(last) = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "let _ = last; " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> }")
    val nested_mixed_chain =
      checked
        ("if let Some(first) = " ^
         "\<llangle>conditional_chain_first_scrutinee_marker\<rrangle> { " ^
         "let _ = first; " ^
         "\<llangle>conditional_chain_first_success_marker\<rrangle> " ^
         "} else { if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else { if let Some(last) = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "let _ = last; " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> } } }")
    val _ =
      audit_assert "mixed chain lost right-associated branch order"
        (Term.aconv (mixed_chain, nested_mixed_chain))
    val _ =
      List.app
        (fn (name, label) =>
          audit_assert (label ^ " was not lowered exactly once")
            (count_constant name mixed_chain = 1))
        [(\<^const_name>\<open>conditional_chain_first_scrutinee_marker\<close>,
          "first mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_second_condition_marker\<close>,
          "mixed-chain ordinary condition"),
         (\<^const_name>\<open>conditional_chain_last_scrutinee_marker\<close>,
          "last mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_first_success_marker\<close>,
          "first mixed-chain success branch"),
         (\<^const_name>\<open>conditional_chain_second_success_marker\<close>,
          "mixed-chain ordinary success branch"),
         (\<^const_name>\<open>conditional_chain_last_success_marker\<close>,
          "last mixed-chain success branch"),
         (\<^const_name>\<open>conditional_chain_fallback_marker\<close>,
          "mixed-chain final fallback")]

    val total_mixed_chain =
      checked
        ("if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else if let _ = " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> " ^
         "} else { " ^
         "\<llangle>conditional_chain_fallback_marker\<rrangle> }")
    val explicit_total_mixed_chain =
      checked
        ("if " ^
         "\<llangle>conditional_chain_second_condition_marker\<rrangle> { " ^
         "\<llangle>conditional_chain_second_success_marker\<rrangle> " ^
         "} else { match_case " ^
         "\<llangle>conditional_chain_last_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_chain_last_success_marker\<rrangle> } }")
    val _ =
      audit_assert "a total mixed-chain arm retained its unreachable remainder"
        (Term.aconv (total_mixed_chain, explicit_total_mixed_chain))
    val _ =
      List.app
        (fn (name, expected, label) =>
          audit_assert (label ^ " has the wrong occurrence count")
            (count_constant name total_mixed_chain = expected))
        [(\<^const_name>\<open>conditional_chain_second_condition_marker\<close>,
          1, "total mixed-chain ordinary condition"),
         (\<^const_name>\<open>conditional_chain_second_success_marker\<close>,
          1, "total mixed-chain ordinary success"),
         (\<^const_name>\<open>conditional_chain_last_scrutinee_marker\<close>,
          1, "total mixed-chain scrutinee"),
         (\<^const_name>\<open>conditional_chain_last_success_marker\<close>,
          1, "total mixed-chain success"),
         (\<^const_name>\<open>conditional_chain_fallback_marker\<close>,
          0, "total mixed-chain unreachable fallback")]

    val two_armed =
      checked
        ("if let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val explicit_two_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle>, _ \<Rightarrow> " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "two-armed if-let stopped using the explicit case shape"
        (Term.aconv (two_armed, explicit_two_armed))
    val _ =
      audit_assert "if-let lowered its scrutinee more than once"
        (count_constant
          \<^const_name>\<open>conditional_let_scrutinee_marker\<close>
          two_armed = 1)
    val _ =
      audit_assert "if-let lost success/fallback ordering"
        (count_constant
          \<^const_name>\<open>conditional_let_success_marker\<close>
          two_armed = 1 andalso
         count_constant
          \<^const_name>\<open>conditional_let_fallback_marker\<close>
          two_armed = 1)

    val total_two_armed =
      checked
        ("if let _ = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val explicit_total_two_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle> }")
    val _ =
      audit_assert "total if-let did not match a complete case without fallback"
        (Term.aconv (total_two_armed, explicit_total_two_armed))
    val _ =
      audit_assert "total if-let changed scrutinee/success multiplicity"
        (count_constant
           \<^const_name>\<open>conditional_let_scrutinee_marker\<close>
           total_two_armed = 1 andalso
         count_constant
           \<^const_name>\<open>conditional_let_success_marker\<close>
           total_two_armed = 1)
    val _ =
      audit_assert "total if-let retained its unreachable fallback"
        (count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           total_two_armed = 0)

    val one_armed =
      checked
        ("if let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { let _ = " ^
         "\<llangle>conditional_let_success_marker\<rrangle>; () }")
    val explicit_one_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> { let _ = " ^
         "\<llangle>conditional_let_success_marker\<rrangle>; () }, _ \<Rightarrow> () }")
    val _ =
      audit_assert "one-armed if-let lost its skip fallback"
        (Term.aconv (one_armed, explicit_one_armed))
    val _ =
      audit_assert "partial one-armed if-let lost its synthetic skip"
        (count_constant
           \<^const_name>\<open>Product_Type.Unity\<close>
           one_armed = 2)

    val total_one_armed =
      checked
        ("if let value = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { let _ = " ^
         "value; \<llangle>conditional_let_success_marker\<rrangle> }")
    val explicit_total_one_armed =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "value \<Rightarrow> { let _ = value; " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } }")
    val _ =
      audit_assert "total one-armed if-let retained synthetic skip"
        (Term.aconv (total_one_armed, explicit_total_one_armed) andalso
         count_constant
           \<^const_name>\<open>Product_Type.Unity\<close>
           total_one_armed = 0)

    val let_else =
      checked
        ("let Some(value) = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }; " ^
         "\<llangle>value + conditional_let_success_marker\<rrangle>")
    val explicit_let_else =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "Some(value) \<Rightarrow> " ^
         "\<llangle>value + conditional_let_success_marker\<rrangle>, _ \<Rightarrow> " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "let-else stopped placing its continuation in the success arm"
        (Term.aconv (let_else, explicit_let_else))

    val total_let_else =
      checked
        ("let _ = " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }; " ^
         "\<llangle>conditional_let_success_marker\<rrangle>")
    val explicit_total_let_else =
      checked
        ("match_case " ^
         "\<llangle>conditional_let_scrutinee_marker\<rrangle> { " ^
         "_ \<Rightarrow> " ^
         "\<llangle>conditional_let_success_marker\<rrangle> }")
    val _ =
      audit_assert "total let-else retained its unreachable fallback"
        (Term.aconv (total_let_else, explicit_total_let_else) andalso
         count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           total_let_else = 0)

    val tuple_if =
      checked
        ("if let (left, right) = " ^
         "(\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>) { " ^
         "\<llangle>left + right\<rrangle> } else { missing_tuple_audit }")
    val tuple_bind =
      checked
        ("let (left, right) = " ^
         "(\<llangle>1 :: nat\<rrangle>, \<llangle>2 :: nat\<rrangle>); " ^
         "\<llangle>left + right\<rrangle>")
    val _ =
      audit_assert "top-level tuple stopped using the frontend's direct binding"
        (Term.aconv (tuple_if, tuple_bind))

    fun conditional_source pattern scrutinee =
      "if let " ^ pattern ^ " = " ^ scrutinee ^ " { " ^
      "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
      "\<llangle>conditional_let_fallback_marker\<rrangle> }"

    fun explicit_case_source pattern scrutinee fallback =
      "match_case " ^ scrutinee ^ " { " ^ pattern ^ " \<Rightarrow> " ^
      "\<llangle>conditional_let_success_marker\<rrangle>" ^
      (if fallback
       then ", _ \<Rightarrow> \<llangle>conditional_let_fallback_marker\<rrangle>"
       else "") ^ " }"

    fun check_total label pattern scrutinee =
      let
        val actual = unchecked (conditional_source pattern scrutinee)
        val explicit =
          unchecked (explicit_case_source pattern scrutinee false)
      in
        audit_assert (label ^ " did not use the complete case shape")
          (Term.aconv (actual, explicit));
        audit_assert (label ^ " retained a fallback")
          (count_constant
             \<^const_name>\<open>conditional_let_fallback_marker\<close>
             actual = 0)
      end

    val _ =
      List.app
        (fn (label, pattern, scrutinee) =>
          check_total label pattern scrutinee)
        [("wildcard totality", "_", "\<llangle>1 :: nat\<rrangle>"),
         ("identifier totality", "value", "\<llangle>1 :: nat\<rrangle>"),
         ("group totality", "(value)", "\<llangle>1 :: nat\<rrangle>"),
         ("alias totality", "whole @ _", "\<llangle>1 :: nat\<rrangle>"),
         ("grouped recursive tuple totality",
          "((left, (middle, right)))",
          "(\<llangle>1 :: nat\<rrangle>, " ^
            "(\<llangle>2 :: nat\<rrangle>, \<llangle>3 :: nat\<rrangle>))"),
         ("sole-constructor totality", "TNil", "TNil"),
         ("complete option totality", "Some(_) | None",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("nested complete option totality",
          "Some(Some(_) | None) | None",
          "\<llangle>Some (Some (1 :: nat))\<rrangle>"),
         ("wildcard-alternative totality", "Some(_) | _",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("borrow-wrapper totality", "&_", "\<llangle>1 :: nat\<rrangle>")]

    fun check_partial label pattern scrutinee =
      let
        val actual = unchecked (conditional_source pattern scrutinee)
        val explicit =
          unchecked (explicit_case_source pattern scrutinee true)
      in
        audit_assert (label ^ " lost the explicit wildcard-case shape")
          (Term.aconv (actual, explicit));
        audit_assert (label ^ " incorrectly discarded its fallback")
          (count_constant
             \<^const_name>\<open>conditional_let_fallback_marker\<close>
             actual > 0)
      end

    val _ =
      List.app
        (fn (label, pattern, scrutinee) =>
          check_partial label pattern scrutinee)
        [("Some-only option coverage", "Some(_)",
          "\<llangle>Some (1 :: nat)\<rrangle>"),
         ("None-only option coverage", "None",
          "\<llangle>None :: nat option\<rrangle>"),
         ("incomplete multi-constructor family",
          "ConditionalLetA(_) | ConditionalLetB(_)",
          "\<llangle>ConditionalLetA 1\<rrangle>"),
         ("internally complete but externally partial family",
          "Some(Some(_) | None)",
          "\<llangle>Some (Some (1 :: nat))\<rrangle>"),
         ("literal pattern", "true", "\<llangle>True\<rrangle>"),
         ("value pattern", "\<llangle>1 :: nat\<rrangle>",
          "\<llangle>1 :: nat\<rrangle>"),
         ("range pattern", "1..=3", "\<llangle>2 :: nat\<rrangle>"),
         ("slice pattern", "[_, ..]", "\<llangle>[1 :: nat, 2]\<rrangle>"),
         ("struct pattern",
          "AdvStruct { adv_left: _, adv_right: _ }",
          "\<llangle>AdvStruct 1 2\<rrangle>"),
         ("nonconstructor path pattern", "Color::Red", "Color::Red"),
         ("constructor with a partial argument", "Some(true)",
          "\<llangle>Some True\<rrangle>"),
         ("or-pattern from different constructor families",
          "Some(_) | ConditionalLetA(_)",
          "\<llangle>Some (1 :: nat)\<rrangle>")]

    val callback_ast =
      parse_text
        ("if let _ = callback_scrutinee { callback_success } " ^
         "else { callback_fallback }")
    val callback_count = Unsynchronized.ref 0
    fun callback_lower _ _ =
      let
        val index = !callback_count + 1
        val _ = callback_count := index
      in
        (case index of
           1 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_scrutinee_marker\<close>
         | 2 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_success_marker\<close>
         | 3 =>
             URust_Shallow_Terms.literal
               \<^term>\<open>conditional_let_fallback_marker\<close>
         | _ =>
             error
               "conditional-binding regression audit: lowering callback called too often")
      end
    val callback_term =
      (case callback_ast of
         UE_IfLet (pattern, scrutinee, success, fallback, position) =>
           URust_Matching.lower_if_let callback_lower ctxt
             URust_Resolution.empty_environment
             (pattern, scrutinee, success, fallback, position)
       | _ =>
           error
             "conditional-binding regression audit: callback fixture AST changed")
    val _ =
      audit_assert "discarded total fallback was not lowered exactly once"
        (!callback_count = 3)
    val _ =
      audit_assert "discarded callback fallback leaked into the final term"
        (count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           callback_term = 0)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("conditional-binding regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun expect_positioned_rejection label text start expected needle =
      let
        val (_, position) = token_position text start needle 0
        val expected_here =
          XML.content_of (YXML.parse_body (Position.here position))
      in
        (case Exn.result
            (fn () =>
              Parser_Test_Elaboration.expression ctxt
                (Parser_Lex_Util.positioned_content_source
                  text start)) () of
           Exn.Res _ =>
             error
               ("conditional-binding regression audit: " ^ label ^
                " unexpectedly elaborated")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else
               let
                 val message =
                   XML.content_of
                     (YXML.parse_body (Runtime.exn_message exn))
               in
                 audit_assert (label ^ " changed its diagnostic")
                   (String.isSubstring expected message);
                 audit_assert (label ^ " moved its diagnostic")
                   (String.isSubstring expected_here message)
               end)
      end

    val bad_total_text =
      "if let _ = \<llangle>1 :: nat\<rrangle> { 1 } else { " ^
      "unknown_total_fallback!() }"
    val bad_total_start =
      Position.make0 19 120 900 "" ""
        "conditional-total-fallback-diagnostic-audit"
    val _ =
      expect_positioned_rejection "total fallback"
        bad_total_text bad_total_start
        "unknown macro \"unknown_total_fallback!\""
        "unknown_total_fallback"

    val bad_partial_text =
      "if let Some(_) = \<llangle>Some (1 :: nat)\<rrangle> { 1 } else { " ^
      "unknown_partial_fallback!() }"
    val bad_partial_start =
      Position.make0 23 160 1200 "" ""
        "conditional-partial-fallback-diagnostic-audit"
    val _ =
      expect_positioned_rejection "partial fallback"
        bad_partial_text bad_partial_start
        "unknown macro \"unknown_partial_fallback!\""
        "unknown_partial_fallback"

    val recovered_total =
      checked
        ("if let _ = \<llangle>1 :: nat\<rrangle> { " ^
         "\<llangle>conditional_let_success_marker\<rrangle> } else { " ^
         "\<llangle>conditional_let_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "failed total fallback leaked state into the next command"
        (count_constant
           \<^const_name>\<open>conditional_let_success_marker\<close>
           recovered_total = 1 andalso
         count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           recovered_total = 0)

    val total_markup_text =
      "let outer = \<llangle>1 :: nat\<rrangle>; " ^
      "if let _ = \<llangle>2 :: nat\<rrangle> { 3 } else { outer }"
    val total_markup_start =
      Position.make0 29 200 1600 "" ""
        "conditional-total-fallback-markup-audit"
    val partial_markup_text =
      "let outer = \<llangle>1 :: nat\<rrangle>; " ^
      "if let Some(_) = \<llangle>Some (2 :: nat)\<rrangle> { 3 } " ^
      "else { outer }"
    val partial_markup_start =
      Position.make0 31 220 2000 "" ""
        "conditional-partial-fallback-markup-audit"

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source
                      text start))) ())
          ())
    val _ = capture_elaboration total_markup_text total_markup_start
    val _ = capture_elaboration partial_markup_text partial_markup_start
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    if_text if_start)) ())
          ())
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    mixed_text mixed_start)) ())
          ())
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    let_text let_start)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun entity_id property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               "conditional-binding regression audit: binder entity markup changed")
      end

    val (total_outer_offset, total_outer_definition) =
      token_position total_markup_text total_markup_start "outer" 0
    val (_, total_outer_fallback) =
      token_position total_markup_text total_markup_start "outer"
        (total_outer_offset + size "outer")
    val (partial_outer_offset, partial_outer_definition) =
      token_position partial_markup_text partial_markup_start "outer" 0
    val (_, partial_outer_fallback) =
      token_position partial_markup_text partial_markup_start "outer"
        (partial_outer_offset + size "outer")
    val _ =
      audit_assert "discarded total fallback lost outer-scope resolution markup"
        (has_markup Markup.boundN total_outer_fallback andalso
         entity_id Markup.defN total_outer_definition =
           entity_id Markup.refN total_outer_fallback)
    val _ =
      audit_assert "partial fallback outer-scope resolution markup changed"
        (has_markup Markup.boundN partial_outer_fallback andalso
         entity_id Markup.defN partial_outer_definition =
           entity_id Markup.refN partial_outer_fallback)

    val (_, if_keyword) = token_position if_text if_start "if" 0
    val (if_offset, if_let_keyword) =
      token_position if_text if_start "let" 0
    val (if_let_offset, if_equals) =
      token_position if_text if_start "=" (if_offset + 2)
    val (_, if_else_keyword) =
      token_position if_text if_start "else" (if_let_offset + 3)
    val (mixed_else_offset, mixed_else_keyword) =
      token_position mixed_text mixed_start "else" 0
    val (mixed_if_offset, mixed_if_keyword) =
      token_position mixed_text mixed_start "if" (mixed_else_offset + 4)
    val (mixed_second_else_offset, mixed_second_else_keyword) =
      token_position mixed_text mixed_start "else" (mixed_if_offset + 2)
    val (mixed_if_let_offset, mixed_if_let_keyword) =
      token_position mixed_text mixed_start "if"
        (mixed_second_else_offset + 4)
    val (_, mixed_let_keyword) =
      token_position mixed_text mixed_start "let" (mixed_if_let_offset + 2)
    val (_, let_semicolon) =
      token_position let_text let_start ";" 0
    val _ =
      audit_assert "if keyword markup changed"
        (has_markup Markup.keyword1N if_keyword)
    val _ =
      audit_assert "let keyword markup changed"
        (has_markup Markup.keyword1N if_let_keyword)
    val _ =
      audit_assert "equals delimiter markup changed"
        (has_markup Markup.delimiterN if_equals)
    val _ =
      audit_assert "else keyword markup changed"
        (has_markup Markup.keyword1N if_else_keyword)
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " keyword markup changed")
            (has_markup Markup.keyword1N position))
        [(mixed_else_keyword, "mixed-chain else"),
         (mixed_if_keyword, "mixed-chain ordinary if"),
         (mixed_second_else_keyword, "mixed-chain second else"),
         (mixed_if_let_keyword, "mixed-chain if-let if"),
         (mixed_let_keyword, "mixed-chain if-let let")]
    val _ =
      audit_assert "let-else semicolon delimiter markup changed"
        (has_markup Markup.delimiterN let_semicolon)
  in
    val _ = writeln "Conditional-binding structure and markup regressions passed"
  end
\<close>

section\<open> Antiquotation markup under HOL shadowing \<close>

text\<open>
Antiquotation navigation follows the positioned term that Isabelle parsed. An inner HOL binder keeps
Isabelle's native \<open>bound\<close> entity, while a same-spelled occurrence outside that binder still
targets the enclosing micro-Rust local.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("antiquotation shadowing markup audit: " ^ message)

    val source_text =
      "let x = \<llangle>1 :: nat\<rrangle>; " ^
      "\<llangle>(\<lambda>x :: nat. x) x\<rrangle>"
    val source_start =
      Position.make0 37 300 2400 "" ""
        "antiquotation-shadowing-markup-audit"
    val source =
      Parser_Lex_Util.positioned_content_source source_text source_start
    val expected =
      Syntax.parse_term ctxt
        ("\<lbrakk> let x = \<llangle>1 :: nat\<rrangle>; " ^
         "\<llangle>(\<lambda>x :: nat. x) x\<rrangle> \<rbrakk>")
      |> Syntax.check_term ctxt

    val captured_reports =
      Synchronized.var "antiquotation_shadowing_markup_audit"
        ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val actual =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression ctxt source) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []

    fun find_from needle offset =
      if offset + size needle > size source_text then
        error
          ("antiquotation shadowing markup audit: missing " ^
            quote needle)
      else if
        String.substring (source_text, offset, size needle) = needle
      then offset
      else find_from needle (offset + 1)

    fun token_position needle offset =
      let
        val raw = find_from needle offset
        val start =
          Position.symbol_explode
            (String.substring (source_text, 0, raw)) source_start
      in
        (raw,
         Position.range_position
           (Position.range
             (start, Position.symbol_explode needle start)))
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun entity_ids kind property position =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
               Properties.get properties Markup.kindN = SOME kind andalso
               has_position properties position
            then Properties.get properties property
            else NONE)
      |> distinct (op =)

    fun entity_id kind property position =
      (case entity_ids kind property position of
         [id] => id
       | ids =>
           error
             ("antiquotation shadowing markup audit: expected one " ^
               quote property ^ " entity at" ^
               Position.here position ^ ", found [" ^
               commas_quote ids ^ "]"))

    val (outer_offset, outer_definition) =
      token_position "x" 0
    val (hol_binder_offset, hol_binder) =
      token_position "x" (outer_offset + 1)
    val (hol_use_offset, hol_bound_use) =
      token_position "x" (hol_binder_offset + 1)
    val (_, outer_reference) =
      token_position "x" (hol_use_offset + 1)

    val outer_id =
      entity_id "urust_var" Markup.defN outer_definition
    val hol_binder_id =
      entity_id Markup.boundN Markup.defN hol_binder
    val hol_use_id =
      entity_id Markup.boundN Markup.refN hol_bound_use

    val _ =
      audit_assert "checked term differs from the legacy frontend"
        (Term.aconv (actual, expected))
    val _ =
      audit_assert "native HOL binder navigation changed"
        (hol_binder_id = hol_use_id)
    val _ =
      audit_assert "HOL lambda declaration received a urust_var entity"
        (null (entity_ids "urust_var" Markup.defN hol_binder) andalso
         null (entity_ids "urust_var" Markup.refN hol_binder))
    val _ =
      audit_assert "HOL bound use received a urust_var entity"
        (null (entity_ids "urust_var" Markup.defN hol_bound_use) andalso
         null (entity_ids "urust_var" Markup.refN hol_bound_use))
    val _ =
      audit_assert "outer micro-Rust reference lost navigation"
        (entity_id "urust_var" Markup.refN outer_reference = outer_id)
  in
    val _ =
      writeln
        "Antiquotation HOL-shadowing semantics and markup regressions passed"
  end
\<close>

section\<open> Positions and pattern grammar \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("parser regression audit: " ^ message)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "parser regression audit: empty parse")

    fun pattern_source pattern =
      "match_case \<llangle>undefined\<rrangle> { " ^ pattern ^
      " \<Rightarrow> \<llangle>undefined\<rrangle> }"

    fun parse_pattern pattern =
      (case parse (pattern_source pattern) of
         UE_Match (_, _, [UR_Arm (result, NONE, _)], _) => result
       | _ => error "parser regression audit: unexpected pattern AST")

    fun integer text (P_Literal (LP_Integer (actual, _))) =
          actual = text
      | integer _ _ = false

    fun range kind lower upper
        (P_Range (actual_kind, actual_lower, actual_upper, _)) =
          actual_kind = kind andalso
          integer lower actual_lower andalso
          integer upper actual_upper
      | range _ _ _ _ = false

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("parser regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    val _ =
      audit_assert "exclusive range shape changed"
        (range RK_Exclusive "5" "7"
          (parse_pattern "5..7"))
    val _ =
      audit_assert "inclusive range shape changed"
        (range RK_Inclusive "5" "7"
          (parse_pattern "5..=7"))

    val borrow_text = pattern_source "& mut &value"
    val outer_borrow_offset = find_from borrow_text "&" 0
    val inner_borrow_offset = find_from borrow_text "&" (outer_borrow_offset + 1)
    val borrow_start = Position.make0 11 4 0 "" "" ""
    val outer_borrow_position =
      Position.symbol_explode
        (String.substring (borrow_text, 0, outer_borrow_offset))
        borrow_start
    val inner_borrow_position =
      Position.symbol_explode
        (String.substring (borrow_text, 0, inner_borrow_offset))
        borrow_start
    val _ =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.positioned_content_source
            borrow_text borrow_start) of
         SOME
           (UE_Match
             (_, _,
              [UR_Arm
                (P_Borrow
                  (BM_Mut,
                   P_Borrow (BM_Imm, P_Ident ("value", _), inner_pos),
                   outer_pos),
                 NONE, _)],
              _)) =>
           (audit_assert "outer borrow-pattern mode or position changed"
              (Position.offset_of outer_pos =
                Position.offset_of outer_borrow_position);
            audit_assert "inner borrow-pattern mode or position changed"
              (Position.offset_of inner_pos =
                Position.offset_of inner_borrow_position))
       | _ =>
           error
             "parser regression audit: nested borrow-pattern AST changed")

    val _ =
      (case parse_pattern "whole @ 5..=7" of
         P_Alias ("whole", _, inner, _) =>
           audit_assert "alias did not bind the whole range"
             (range RK_Inclusive "5" "7" inner)
       | _ =>
           error "parser regression audit: range alias shape changed")

    val _ =
      (case parse_pattern "outer @ inner @ 5..7" of
         P_Alias ("outer", _,
           P_Alias ("inner", _, nested, _), _) =>
             audit_assert "nested aliases lost right associativity"
               (range RK_Exclusive "5" "7" nested)
       | _ =>
           error "parser regression audit: nested alias shape changed")

    val _ =
      (case parse_pattern "whole @ Some(5..=7)" of
         P_Alias ("whole", _,
           P_Constr (path, [nested]), _) =>
             audit_assert "constructor alias lost its path or range argument"
               (render_path path = "Some" andalso
                range RK_Inclusive "5" "7" nested)
       | _ =>
           error
             "parser regression audit: constructor alias shape changed")

    val _ =
      (case parse_pattern "whole @ Head { field: 5..7 }" of
         P_Alias ("whole", _,
           P_Struct (path,
             [SF_Field ("field", _, nested)]), _) =>
             audit_assert "struct alias lost its path or range field"
               (render_path path = "Head" andalso
                range RK_Exclusive "5" "7" nested)
       | _ =>
           error "parser regression audit: struct alias shape changed")

    val _ =
      (case parse_pattern "left @ 1..2 | right @ 3..=4" of
         P_Or
           ([P_Alias ("left", _, left, _),
             P_Alias ("right", _, right, _)], _) =>
             (audit_assert "exclusive range lost alias precedence"
                (range RK_Exclusive "1" "2" left);
              audit_assert "inclusive range lost alias precedence"
                (range RK_Inclusive "3" "4" right))
       | _ =>
           error
             "parser regression audit: alias/range/or precedence changed")

    val chained_text =
      pattern_source "1..2..3"
    val chained_start =
      Position.make0 7 1 0 "" "" ""

    val first_range =
      find_from chained_text ".." 0
    val second_range =
      find_from chained_text ".." (first_range + 2)
    val second_range_position =
      Position.symbol_explode
        (String.substring (chained_text, 0, second_range))
        chained_start
    val second_range_here =
      XML.content_of
        (YXML.parse_body
          (Position.here second_range_position))
    val _ =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.positioned_content_source
                chained_text chained_start)) () of
         Exn.Res _ =>
           error
             "parser regression audit: chained range unexpectedly elaborated"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message =
                 XML.content_of
                   (YXML.parse_body
                     (Runtime.exn_message exn))
             in
               audit_assert "chained range missed semantic validation"
                 (String.isSubstring
                   "range patterns are non-associative" message);
               audit_assert "chained range diagnostic moved"
                 (String.isSubstring second_range_here message)
             end)

    fun alternative_name index =
      "regression_alt_" ^ string_of_int index

    fun audit_alternatives count =
      let
        val alternatives =
          space_implode " | "
            (map alternative_name (0 upto (count - 1)))
      in
        (case parse_pattern alternatives of
           P_Or (patterns, _) =>
             (audit_assert
                ("large or-pattern was not flattened at " ^
                  string_of_int count)
                (length patterns = count);
              audit_assert
                ("large or-pattern source order changed at " ^
                  string_of_int count)
                (case (hd patterns, List.last patterns) of
                   (P_Ident (first, _), P_Ident (last, _)) =>
                     first = alternative_name 0 andalso
                     last = alternative_name (count - 1)
                 | _ => false))
         | _ =>
             error
               ("parser regression audit: large or-pattern AST changed at " ^
                 string_of_int count))
      end

    val _ = audit_alternatives 4096
    val _ = audit_alternatives 16384

    fun expect_positioned_rejection
        label text start expected expected_position =
      let
        val expected_here =
          XML.content_of
            (YXML.parse_body (Position.here expected_position))
      in
        (case Exn.result
            (fn () =>
              Parser_Test_Elaboration.expression ctxt
                (Parser_Lex_Util.positioned_content_source
                  text start)) () of
           Exn.Res _ =>
             error
               ("parser regression audit: " ^ label ^
                 " unexpectedly parsed")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else
               let
                 val message =
                   XML.content_of
                     (YXML.parse_body
                       (Runtime.exn_message exn))
               in
                 audit_assert (label ^ " diagnostic changed")
                   (String.isSubstring expected message);
                 audit_assert (label ^ " position changed")
                   (String.isSubstring expected_here message)
               end)
      end

    val operator_text = "1 + 2 ++ 3"
    val operator_start =
      Position.make0 4 10 0 "" "" ""
    val second_operator =
      Position.symbol_explode
        (String.substring (operator_text, 0, 7))
        operator_start
    val _ =
      expect_positioned_rejection
        "malformed operator"
        operator_text operator_start
        "syntax error found at +"
        second_operator

    val eof_text = "{ ()"
    val eof_start =
      Position.make0 3 12 0 "" "" ""
    val eof_stop =
      Position.symbol_explode eof_text eof_start
    val _ =
      expect_positioned_rejection
        "malformed EOF"
        eof_text eof_start
        "syntax error found at end of input"
        eof_stop
  in
    val _ = writeln "Parser position and pattern grammar regressions passed"
  end
\<close>

section\<open> Range, array, and indexing structure \<close>

text\<open>
The public AST keeps each source form explicit, while the term layer emits only
the frontend vocabulary before the command's single final \<open>Syntax.check_term\<close>.
Same-source commands in \<open>Parser_Test_Expr_Conformance\<close> separately require the
checked terms to close by \<open>refl\<close>.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("range/array/index regression audit: " ^ message)

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE =>
           error "range/array/index regression audit: empty parse")

    fun integer text (UE_Literal (LP_Integer (actual, _))) =
          actual = text
      | integer _ _ = false

    fun identifier text (UE_Path path) = render_path path = text
      | identifier _ _ = false

    val _ =
      (case parse "1..2" of
         UE_Range (RK_Exclusive, lower, upper, _) =>
           audit_assert "exclusive range AST changed"
             (integer "1" lower andalso integer "2" upper)
       | _ => error "range/array/index regression audit: exclusive range AST changed")

    val _ =
      (case parse "1..=2" of
         UE_Range (RK_Inclusive, lower, upper, _) =>
           audit_assert "inclusive range AST changed"
             (integer "1" lower andalso integer "2" upper)
       | _ => error "range/array/index regression audit: inclusive range AST changed")

    val _ =
      (case parse "[]" of
         UE_Array ([], _) => ()
       | _ => error "range/array/index regression audit: empty array AST changed")

    val _ =
      (case parse "[1, 2]" of
         UE_Array ([first, second], _) =>
           audit_assert "array element order changed"
             (integer "1" first andalso integer "2" second)
       | _ => error "range/array/index regression audit: array AST changed")

    val _ =
      (case parse "xs[0].field[1]" of
         UE_Index
           (UE_Field
             (UE_Index (base, first_index, _), "field", _),
            second_index, _) =>
           audit_assert "postfix index/field nesting changed"
             (identifier "xs" base andalso
              integer "0" first_index andalso
              integer "1" second_index)
       | _ =>
           error
             "range/array/index regression audit: postfix nesting AST changed")

    val _ =
      (case parse "xs[0] += 1" of
         UE_Assign
           (AssignAdd,
            UP_Index (UP_Path path, index, _),
            rhs, _) =>
           audit_assert "indexed place conversion changed"
             (render_path path = "xs" andalso
              integer "0" index andalso integer "1" rhs)
       | _ =>
           error
             "range/array/index regression audit: indexed place AST changed")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    fun has_head name arity term =
      (case Term.strip_comb term of
         (Const (actual, _), arguments) =>
           actual = name andalso length arguments = arity
       | _ => false)

    fun function_call2 target term =
      (case Term.strip_comb term of
         (Const (call, _), Const (actual, _) :: arguments) =>
           call = \<^const_name>\<open>funcall2\<close> andalso
           actual = target andalso length arguments = 2
       | _ => false)

    val _ =
      audit_assert "exclusive range term shape changed"
        (function_call2 \<^const_name>\<open>range_new\<close>
          (unchecked "1..2"))

    val _ =
      audit_assert "inclusive range term shape changed"
        (function_call2 \<^const_name>\<open>range_eq_new\<close>
          (unchecked "1..=2"))

    fun array_shape [] term =
          (case Term.strip_comb term of
             (Const (literal_name, _), [Const (nil_name, _)]) =>
               literal_name = \<^const_name>\<open>literal\<close> andalso
               nil_name = \<^const_name>\<open>List.Nil\<close>
           | _ => false)
      | array_shape (_ :: rest) term =
          (case Term.strip_comb term of
             (Const (bindlift_name, _),
              [Const (cons_name, _), _, tail]) =>
               bindlift_name = \<^const_name>\<open>bindlift2\<close> andalso
               cons_name = \<^const_name>\<open>List.Cons\<close> andalso
               array_shape rest tail
           | _ => false)

    val _ =
      audit_assert "empty array term shape changed"
        (array_shape [] (unchecked "[]"))

    val _ =
      audit_assert "nonempty array term shape changed"
        (array_shape [(), (), ()] (unchecked "[1, 2, 3]"))

    val _ =
      audit_assert "index term shape changed"
        (function_call2 \<^const_name>\<open>index_const\<close>
          (unchecked "[1][0]"))

    val _ =
      audit_assert "direct array borrow stopped erasing"
        (Term.aconv (unchecked "&[1, 2]", unchecked "[1, 2]"))

    val indexed_assignment = unchecked "xs[0] = 1"
    val _ =
      audit_assert "indexed assignment lost store-update lowering"
        (has_head \<^const_name>\<open>bind2\<close> 3 indexed_assignment)
    val index_count =
      Term.fold_aterms
        (fn Const (name, _) =>
              if name = \<^const_name>\<open>index_const\<close>
              then Integer.add 1
              else I
          | _ => I)
        indexed_assignment 0
    val _ =
      audit_assert "indexed assignment did not lower its place exactly once"
        (index_count = 1)
  in
    val _ = writeln "Range, array, and indexing regressions passed"
  end
\<close>

section\<open> Numeric tuple projection structure, ranges, and markup \<close>

consts
  tuple_projection_audit_marker ::
    \<open>
      (unit,
       nat \<times> nat \<times> nat \<times>
         (bool \<times> bool \<times> Tuple.tnil) \<times> Tuple.tnil,
       unit, unit, unit, unit) expression
    \<close>

text\<open>
These checks keep numeric projections distinct from fields and bracket indexing.
They pin the canonical index payload, left-associated AST, numeric-token ranges,
lexer markup, direct expanded \<open>tuple_index_N\<close> shape, recovery, value-only
assignment policy, and exactly-once receiver lowering.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("tuple-projection regression audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "tuple-projection regression audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)
      |> Term_Position.strip_positions

    fun path_named name (UE_Path path) = render_path path = name
      | path_named _ _ = false

    fun projection index receiver (UE_TupleProjection (actual, stored, _)) =
          stored = index andalso receiver actual
      | projection _ _ _ = false

    val _ =
      List.app
        (fn index =>
          audit_assert
            ("AST index " ^ string_of_int index ^ " changed")
            (projection index (path_named "source")
              (parse ("source." ^ string_of_int index))))
        [0, 1, 10, 15]

    val _ =
      (case parse "source.2.0" of
         UE_TupleProjection
           (UE_TupleProjection (base, 2, _), 0, _) =>
           audit_assert "projection chain base changed"
             (path_named "source" base)
       | _ => error "tuple-projection regression audit: chain AST changed")

    val _ =
      (case parse "source.field[0].1" of
         UE_TupleProjection
           (UE_Index
             (UE_Field (base, "field", _),
              UE_Literal (LP_Integer ("0", _)), _),
            1, _) =>
           audit_assert "field/index/projection source order changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: mixed postfix AST changed")

    val _ =
      (case parse "!source.0" of
         UE_Unary
           (U_Not, UE_TupleProjection (base, 0, _), _) =>
           audit_assert "projection/prefix precedence changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: prefix AST changed")

    val _ =
      (case parse "source.0 + other" of
         UE_Bin
           (Add, UE_TupleProjection (base, 0, _), other, _) =>
           audit_assert "projection/binary precedence changed"
             (path_named "source" base andalso
              path_named "other" other)
       | _ =>
           error
             "tuple-projection regression audit: binary AST changed")

    val _ =
      (case parse "if source.0 { () } else { () }" of
         UE_If
           (UE_TupleProjection (base, 0, _),
            UE_Block (UE_Unit _, _),
            SOME (UE_Block (UE_Unit _, _)), _) =>
           audit_assert "restricted control-head projection changed"
             (path_named "source" base)
       | _ =>
           error
             "tuple-projection regression audit: control-head AST changed")

    fun find_from text needle offset =
      if offset + size needle > size text
      then
        error
          ("tuple-projection regression audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun same_range actual expected =
      Position.offset_of actual = Position.offset_of expected andalso
      Position.end_offset_of actual = Position.end_offset_of expected

    val ranged_text =
      "\<llangle>tuple_projection_audit_marker\<rrangle>.10.15"
    val ranged_start =
      Position.make0 13 70 700 "" ""
        "tuple-projection-range-audit"
    val (ten_offset, ten_position) =
      token_position ranged_text ranged_start "10" 0
    val (_, fifteen_position) =
      token_position ranged_text ranged_start "15"
        (ten_offset + size "10")
    val ranged_ast =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          ranged_text ranged_start)
    val _ =
      (case ranged_ast of
         UE_TupleProjection
           (UE_TupleProjection
             (UE_Literal (LP_ValAntiq _), 10, inner_position),
            15, outer_position) =>
           (audit_assert "inner two-digit token range changed"
              (same_range inner_position ten_position);
            audit_assert "outer two-digit token range changed"
              (same_range outer_position fifteen_position);
            audit_assert "expression_position lost the outer numeric token"
              (same_range
                (expression_position ranged_ast) fifteen_position))
       | _ =>
           error
             "tuple-projection regression audit: ranged AST changed")

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun decoded_message exn =
      XML.content_of (YXML.parse_body (Runtime.exn_message exn))

    fun expect_positioned_failure label text start expected position =
      (case Exn.result
          (fn () =>
            parse_source
              (Parser_Lex_Util.positioned_content_source text start)) () of
         Exn.Res _ =>
           error
             ("tuple-projection regression audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
               val markup = fold collect_markup body []
             in
               audit_assert (label ^ " diagnostic changed")
                 (String.isSubstring expected message);
               audit_assert (label ^ " diagnostic position changed")
                 (exists
                   (fn (name, properties) =>
                     name = Markup.positionN andalso
                       has_position properties position)
                   markup)
             end)

    val assignment_text = "source.0 = rhs"
    val assignment_start =
      Position.make0 19 90 900 "" ""
        "tuple-projection-assignment-audit"
    val (_, assignment_index_position) =
      token_position assignment_text assignment_start "0" 0
    val _ =
      expect_positioned_failure
        "value-only assignment"
        assignment_text assignment_start
        "invalid assignment target"
        assignment_index_position

    val invalid_start =
      Position.make0 23 110 1100 "" ""
        "tuple-projection-invalid-index-audit"
    fun expect_invalid_projection (text, token) =
      let
        val (_, token_position) =
          token_position text invalid_start token 0
      in
        expect_positioned_failure
          ("invalid index " ^ quote token)
          text invalid_start
          ("invalid tuple projection index " ^ quote token ^
            " (expected an unsuffixed decimal integer from 0 through 15)")
          token_position
      end
    val _ =
      List.app expect_invalid_projection
        [("source.16", "16"),
         ("source.00", "00"),
         ("source.01", "01"),
         ("source.0x1", "0x1"),
         ("source.1u8", "1u8"),
         ("source.1_u8", "1_u8")]

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun projection_parts expected_index term =
      (case Term.strip_comb term of
         (Const (bindlift, _), [selector, receiver]) =>
           (audit_assert
              ("projection " ^ string_of_int expected_index ^
                " did not use bindlift1")
              (bindlift = \<^const_name>\<open>bindlift1\<close>);
            audit_assert
              ("projection " ^ string_of_int expected_index ^
                " selector lost fst")
              (count_constant \<^const_name>\<open>fst\<close> selector = 1);
            audit_assert
              ("projection " ^ string_of_int expected_index ^
                " selector has the wrong snd depth")
              (count_constant \<^const_name>\<open>snd\<close> selector =
                expected_index);
            receiver)
       | _ =>
           error
             ("tuple-projection regression audit: projection " ^
               string_of_int expected_index ^ " term shape changed"))

    fun marker_projection index =
      unchecked
        ("\<epsilon>\<open>tuple_projection_audit_marker\<close>." ^
          string_of_int index)

    val _ =
      List.app
        (fn index =>
          let
            val term = marker_projection index
            val receiver = projection_parts index term
          in
            audit_assert
              ("projection " ^ string_of_int index ^
                " receiver changed or was duplicated")
              (count_constant
                 \<^const_name>\<open>tuple_projection_audit_marker\<close>
                 receiver = 1);
            audit_assert
              ("projection " ^ string_of_int index ^
                " introduced field/index/literal lowering")
              (count_constant
                 \<^const_name>\<open>focus_lens_const\<close> term = 0 andalso
               count_constant \<^const_name>\<open>index_const\<close> term = 0 andalso
               count_constant \<^const_name>\<open>literal\<close> term = 0)
          end)
        [0, 1, 10, 15]

    val chain =
      unchecked
        "\<epsilon>\<open>tuple_projection_audit_marker\<close>.3.0"
    val inner = projection_parts 0 chain
    val receiver = projection_parts 3 inner
    val _ =
      audit_assert "chained receiver was not lowered exactly once"
        (count_constant
           \<^const_name>\<open>tuple_projection_audit_marker\<close>
           chain = 1)
    val _ =
      audit_assert "chained projections lost one selected operation"
        (count_constant \<^const_name>\<open>bindlift1\<close> chain = 2)
    val _ =
      audit_assert "chained projection receiver changed"
        (count_constant
           \<^const_name>\<open>tuple_projection_audit_marker\<close>
           receiver = 1)

    fun expect_failure text expected =
      (case Exn.result (fn () => parse text) () of
         Exn.Res _ =>
           error
             ("tuple-projection regression audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (decoded_message exn)))

    val _ =
      (expect_failure "source.16"
         "invalid tuple projection index \"16\"";
       audit_assert "parser did not recover after invalid index"
         (projection 15 (path_named "source") (parse "source.15"));
       expect_failure "source."
         "syntax error found at end of input";
       audit_assert "parser did not recover after trailing dot"
         (projection 15 (path_named "source") (parse "source.15")))

    val captured_reports =
      Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (parse_source
                    (Parser_Lex_Util.positioned_content_source
                      ranged_text ranged_start))) ())
          ())

    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun has_any_entity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            has_position properties position)
        markup
    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size ranged_text
          then rev positions
          else
            (case try (find_from ranged_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position ranged_text ranged_start needle raw
                 in
                   collect (raw + size needle)
                     (position :: positions)
                 end
             | NONE => rev positions)
      in collect 0 [] end

    val _ =
      List.app
        (fn position =>
          audit_assert "projection dot lost delimiter markup"
            (has_markup Markup.delimiterN position))
        (all_token_positions ".")
    val _ =
      List.app
        (fn position =>
          (audit_assert "projection index lost numeral markup"
             (has_markup Markup.numeralN position);
           audit_assert "projection index lost typing markup"
             (has_markup Markup.typingN position);
           audit_assert "projection index received field/free markup"
             (not (has_markup Markup.freeN position));
           audit_assert "projection index received entity markup"
             (not (has_any_entity position))))
        [ten_position, fifteen_position]
  in
    val _ =
      writeln
        "Numeric tuple projection AST, range, markup, lowering, and recovery regressions passed"
  end
\<close>

section\<open> Legacy macro structure, spans, and markup \<close>

consts
  macro_audit_scrutinee :: \<open>nat option\<close>
  macro_audit_ref :: \<open>('a, 'b, 'v) Global_Store.ref\<close>
  macro_audit_marker :: bool
  macro_audit_ignored_marker :: bool
  macro_audit_vec_first :: nat
  macro_audit_vec_second :: nat

text\<open>
These checks pin complete-body macro payload boundaries, source spans, markup, recovery,
and the exact shallow term vocabulary. They also prove that retained bindings evaluate
once, discarded arguments never enter semantic lowering, \<open>vec!\<close> preserves
complete-body element order through the array builder, address macros retain the exact
legacy \<open>ref_address\<close> target, registered bang-names win only when adjacent, and
\<open>matches!\<close> uses the ordinary case compiler with one scrutinee evaluation and
false fallback.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("legacy macro regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "legacy macro regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse_text text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("legacy macro regression audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    val full_body_text =
      "debug_assert!(let flag = true; " ^
      "if let Some(_) = Some(flag) { flag } else { false })"
    val full_body_start =
      Position.make0 7 30 0 "" "" "macro-full-body-span-audit"
    val full_body_stop =
      Position.symbol_explode full_body_text full_body_start
    val full_body =
      parse
        (Parser_Lex_Util.positioned_content_source
          full_body_text full_body_start)
    val (full_body_name_pos, full_body_bang_pos,
         full_body_invocation_pos, full_body_binder_pos,
         full_body_literal_pos, full_body_if_pos) =
      (case full_body of
         UE_Macro
           (path, bang_pos,
            MP_Arguments
              [UE_Let
                (P_Ident ("flag", binder_pos),
                 UE_Literal (LP_Bool (true, literal_pos)),
                 UE_IfLet
                   (P_Constr (pattern_path, [P_Wild _]),
                    UE_Call
                      (UC_Path call_path, [UE_Path scrutinee_path], _),
                    UE_Block (UE_Path then_path, _),
                    SOME
                      (UE_Block
                        (UE_Literal (LP_Bool (false, _)), _)),
                    if_pos))],
           invocation_pos) =>
           (audit_assert "full-body macro path changed"
              (render_path path = "debug_assert");
            audit_assert "full-body condition escaped its binding continuation"
              (render_path pattern_path = "Some" andalso
               render_path call_path = "Some" andalso
               render_path scrutinee_path = "flag" andalso
               render_path then_path = "flag");
            (path_position path, bang_pos, invocation_pos,
             binder_pos, literal_pos, if_pos))
       | _ =>
           error "legacy macro regression audit: full-body macro AST changed")
    val _ =
      audit_assert "full-body invocation start moved"
        (Position.offset_of full_body_invocation_pos =
          Position.offset_of full_body_start)
    val _ =
      audit_assert "full-body invocation end moved"
        (Position.end_offset_of full_body_invocation_pos =
          Position.offset_of full_body_stop)
    val (_, full_body_binder_token) =
      token_position full_body_text full_body_start "flag" 0
    val (_, full_body_literal_token) =
      token_position full_body_text full_body_start "true" 0
    val (_, full_body_if_token) =
      token_position full_body_text full_body_start "if" 0
    val (full_body_name_raw, full_body_name_token) =
      token_position full_body_text full_body_start "debug_assert" 0
    val (_, full_body_bang_token) =
      token_position full_body_text full_body_start "!"
        (full_body_name_raw + size "debug_assert")
    val (first_brace_raw, _) =
      token_position full_body_text full_body_start "}" 0
    val (_, full_body_final_brace) =
      token_position full_body_text full_body_start "}"
        (first_brace_raw + 1)
    val _ =
      audit_assert "full-body binder position moved"
        (Position.offset_of full_body_binder_pos =
           Position.offset_of full_body_binder_token andalso
         Position.end_offset_of full_body_binder_pos =
           Position.end_offset_of full_body_binder_token)
    val _ =
      audit_assert "full-body literal position moved"
        (Position.offset_of full_body_literal_pos =
           Position.offset_of full_body_literal_token andalso
         Position.end_offset_of full_body_literal_pos =
           Position.end_offset_of full_body_literal_token)
    val _ =
      audit_assert "nested conditional span moved"
        (Position.offset_of full_body_if_pos =
           Position.offset_of full_body_if_token andalso
         Position.end_offset_of full_body_if_pos =
           Position.end_offset_of full_body_final_brace)
    val _ =
      audit_assert "full-body macro name span moved"
        (Position.offset_of full_body_name_pos =
           Position.offset_of full_body_name_token andalso
         Position.end_offset_of full_body_name_pos =
           Position.end_offset_of full_body_name_token)
    val full_body_bang_markup_pos =
      Position.range_position
        (full_body_bang_pos,
         Position.symbol_explode "!" full_body_bang_pos)
    val _ =
      audit_assert "full-body macro bang span moved"
        (Position.offset_of full_body_bang_markup_pos =
           Position.offset_of full_body_bang_token andalso
         Position.end_offset_of full_body_bang_markup_pos =
           Position.end_offset_of full_body_bang_token)
    val _ =
      audit_assert "full-body macro name and bang stopped being adjacent"
        (Position.end_offset_of full_body_name_pos =
           Position.offset_of full_body_bang_pos)

    val bracket_body_text =
      "assert_eq![let left = true; left, " ^
      "const right = false; if right { false } else { true }]"
    val bracket_body_start =
      Position.make0 9 60 0 "" "" "macro-bracket-body-span-audit"
    val bracket_body_stop =
      Position.symbol_explode bracket_body_text bracket_body_start
    val bracket_body =
      parse
        (Parser_Lex_Util.positioned_content_source
          bracket_body_text bracket_body_start)
    val bracket_body_invocation_pos =
      (case bracket_body of
         UE_Macro
           (path, _,
            MP_Arguments
              [UE_Let
                (P_Ident ("left", _),
                 UE_Literal (LP_Bool (true, _)),
                 UE_Path left_path),
               UE_Const
                (P_Ident ("right", _),
                 UE_Literal (LP_Bool (false, _)),
                 UE_If
                   (UE_Path right_path, UE_Block _, SOME (UE_Block _), _))],
            invocation_pos) =>
           (audit_assert "bracket full-body macro path changed"
              (render_path path = "assert_eq");
            audit_assert "bracket full-body argument order changed"
              (render_path left_path = "left" andalso
               render_path right_path = "right");
            invocation_pos)
       | _ =>
           error "legacy macro regression audit: bracket full-body AST changed")
    val _ =
      audit_assert "bracket full-body invocation start moved"
        (Position.offset_of bracket_body_invocation_pos =
          Position.offset_of bracket_body_start)
    val _ =
      audit_assert "bracket full-body invocation end moved"
        (Position.end_offset_of bracket_body_invocation_pos =
          Position.offset_of bracket_body_stop)

    val spaced_text = "assert\n  ! [\<llangle>True\<rrangle>]"
    val spaced_start =
      Position.make0 11 40 0 "" "" "macro-span-audit"
    val spaced_stop =
      Position.symbol_explode spaced_text spaced_start
    val spaced =
      parse
        (Parser_Lex_Util.positioned_content_source
          spaced_text spaced_start)
    val (spaced_name_pos, spaced_bang_pos, spaced_invocation_pos) =
      (case spaced of
         UE_Macro
           (path, bang_pos,
            MP_Arguments [UE_Literal (LP_ValAntiq _)],
            invocation_pos) =>
           let val name_pos = path_position path in
           (audit_assert "generic macro path changed"
              (render_path path = "assert");
            audit_assert "generic macro name span moved"
              (Position.offset_of name_pos =
                Position.offset_of spaced_start);
            audit_assert "generic whitespace before bang was lost"
              (Position.end_offset_of name_pos <>
                Position.offset_of bang_pos);
            audit_assert "generic invocation start moved"
              (Position.offset_of invocation_pos =
                Position.offset_of spaced_start);
            audit_assert "generic invocation end moved"
              (Position.end_offset_of invocation_pos =
                Position.offset_of spaced_stop);
            (name_pos, bang_pos, invocation_pos))
           end
       | _ =>
           error "legacy macro regression audit: generic macro AST changed")

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression ctxt
                  (Parser_Lex_Util.positioned_content_source
                    text start)) ())
          ())
    val _ = capture_elaboration spaced_text spaced_start
    val _ = capture_elaboration full_body_text full_body_start
    val _ = capture_elaboration bracket_body_text bracket_body_start

    val ignored_markup_text =
      "debug_assert!(true, let ignored = unknown_macro_markup; ignored)"
    val ignored_markup_start =
      Position.make0 13 90 0 "" "" "macro-ignored-body-markup-audit"
    val _ =
      capture_elaboration ignored_markup_text ignored_markup_start

    val matches_text =
      "matches!(Some(\<llangle>1 :: nat\<rrangle>), Some(_))"
    val matches_start =
      Position.make0 17 80 0 "" "" "macro-markup-audit"
    val matches_stop =
      Position.symbol_explode matches_text matches_start
    val matches =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse
                  (Parser_Lex_Util.positioned_content_source
                    matches_text matches_start)) ())
          ())
    val (matches_name_pos, matches_bang_pos, matches_invocation_pos) =
      (case matches of
         UE_Macro
           (path, bang_pos,
            MP_Matches
              (UE_Call (UC_Path call_path, [_], _),
               P_Constr (pattern_path, [P_Wild _])),
            invocation_pos) =>
           if render_path path = "matches" andalso
               render_path call_path = "Some" andalso
               render_path pattern_path = "Some"
           then (path_position path, bang_pos, invocation_pos)
           else error "legacy macro regression audit: matches paths changed"
       | _ =>
           error "legacy macro regression audit: matches macro AST changed")
    val _ =
      audit_assert "matches name and bang stopped being adjacent"
        (Position.end_offset_of matches_name_pos =
          Position.offset_of matches_bang_pos)
    val _ =
      audit_assert "matches invocation start moved"
        (Position.offset_of matches_invocation_pos =
          Position.offset_of matches_start)
    val _ =
      audit_assert "matches invocation end moved across Isabelle symbols"
        (Position.end_offset_of matches_invocation_pos =
          Position.offset_of matches_stop)

    val registered_text = "shout!(true)"
    val registered_start =
      Position.make0 23 120 0 "" "" "macro-registered-markup-audit"
    val registered =
      parse
        (Parser_Lex_Util.positioned_content_source
          registered_text registered_start)
    val (registered_name_pos, registered_bang_pos) =
      (case registered of
         UE_Macro
           (path, bang_pos,
            MP_Arguments [UE_Literal (LP_Bool (true, _))], _) =>
           if render_path path = "shout"
           then (path_position path, bang_pos)
           else error "legacy macro regression audit: registered macro path changed"
       | _ =>
           error "legacy macro regression audit: registered macro AST changed")
    val _ =
      audit_assert "registered macro name and bang stopped being adjacent"
        (Position.end_offset_of registered_name_pos =
          Position.offset_of registered_bang_pos)
    val registered_complete_name_pos =
      Position.range_position
        (registered_name_pos,
         Position.symbol_explode "!" registered_bang_pos)
    val _ = capture_elaboration registered_text registered_start

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)
    fun has_markup markup_name pos =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties pos)
        markup
    fun has_entity_markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup
    fun has_urust_entity pos =
      has_entity_markup "urust_var" pos
    fun entity_id property pos =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties pos
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               "legacy macro regression audit: binder entity markup changed")
      end
    val _ =
      audit_assert "generic built-in macro keyword markup moved"
        (has_markup Markup.keyword1N spaced_name_pos)
    val spaced_bang_markup_pos =
      Position.range_position
        (spaced_bang_pos,
         Position.symbol_explode "!" spaced_bang_pos)
    val _ =
      audit_assert "generic built-in macro bang markup moved"
        (has_markup Markup.operatorN spaced_bang_markup_pos)
    val _ =
      audit_assert "generic macro invocation lost its symbol-counted end"
        (Position.end_offset_of spaced_invocation_pos =
          Position.offset_of spaced_stop)
    val _ =
      audit_assert "matches keyword markup moved"
        (has_markup Markup.keyword1N matches_name_pos)
    val matches_bang_markup_pos =
      Position.range_position
        (matches_bang_pos,
         Position.symbol_explode "!" matches_bang_pos)
    val _ =
      audit_assert "matches bang operator markup moved"
        (has_markup Markup.operatorN matches_bang_markup_pos)
    val _ =
      audit_assert "registered complete-bang-name notation markup moved"
        (has_entity_markup
          Micro_Rust_Names.notationN registered_complete_name_pos)
    val _ =
      audit_assert "registered complete-bang-name dispatch styling moved"
        (has_markup Markup.keyword3N registered_complete_name_pos)

    val (_, full_body_let_keyword) =
      token_position full_body_text full_body_start "let" 0
    val (_, full_body_else_keyword) =
      token_position full_body_text full_body_start "else" 0
    val (_, full_body_semicolon) =
      token_position full_body_text full_body_start ";" 0
    val (_, full_body_left_paren) =
      token_position full_body_text full_body_start "(" 0
    val (_, full_body_right_paren) =
      token_position full_body_text full_body_start ")"
        (size full_body_text - 1)
    val (full_body_definition_raw, full_body_definition) =
      token_position full_body_text full_body_start "flag" 0
    val (_, full_body_reference) =
      token_position full_body_text full_body_start "flag"
        (full_body_definition_raw + size "flag")
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " keyword markup moved")
            (has_markup Markup.keyword1N position))
        [(full_body_let_keyword, "full-body let"),
         (full_body_if_token, "full-body if"),
         (full_body_else_keyword, "full-body else")]
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " delimiter markup moved")
            (has_markup Markup.delimiterN position))
        [(full_body_semicolon, "full-body semicolon"),
         (full_body_left_paren, "full-body opening parenthesis"),
         (full_body_right_paren, "full-body closing parenthesis")]
    val _ =
      audit_assert "full-body built-in macro keyword markup moved"
        (has_markup Markup.keyword1N full_body_name_pos)
    val _ =
      audit_assert "full-body macro bang operator markup moved"
        (has_markup Markup.operatorN full_body_bang_markup_pos)
    val _ =
      audit_assert "retained full-body binder navigation changed"
        (has_markup Markup.boundN full_body_definition andalso
         has_markup Markup.boundN full_body_reference andalso
         entity_id Markup.defN full_body_definition =
           entity_id Markup.refN full_body_reference)

    val (_, bracket_const_keyword) =
      token_position bracket_body_text bracket_body_start "const" 0
    val (_, bracket_comma) =
      token_position bracket_body_text bracket_body_start "," 0
    val (_, bracket_semicolon) =
      token_position bracket_body_text bracket_body_start ";" 0
    val (_, bracket_left) =
      token_position bracket_body_text bracket_body_start "[" 0
    val (_, bracket_right) =
      token_position bracket_body_text bracket_body_start "]" 0
    val _ =
      audit_assert "full-body const keyword markup moved"
        (has_markup Markup.keyword1N bracket_const_keyword)
    val _ =
      List.app
        (fn (position, label) =>
          audit_assert (label ^ " delimiter markup moved")
            (has_markup Markup.delimiterN position))
        [(bracket_comma, "full-body top-level comma"),
         (bracket_semicolon, "bracket full-body semicolon"),
         (bracket_left, "full-body opening bracket"),
         (bracket_right, "full-body closing bracket")]

    val (_, ignored_let_keyword) =
      token_position ignored_markup_text ignored_markup_start "let" 0
    val (_, ignored_semicolon) =
      token_position ignored_markup_text ignored_markup_start ";" 0
    val (ignored_definition_raw, ignored_definition) =
      token_position ignored_markup_text ignored_markup_start "ignored" 0
    val (_, ignored_reference) =
      token_position ignored_markup_text ignored_markup_start "ignored"
        (ignored_definition_raw + size "ignored")
    val _ =
      audit_assert "ignored full-body let lost syntactic keyword markup"
        (has_markup Markup.keyword1N ignored_let_keyword)
    val _ =
      audit_assert "ignored full-body semicolon lost delimiter markup"
        (has_markup Markup.delimiterN ignored_semicolon)
    val _ =
      audit_assert "ignored full-body binder entered semantic markup"
        (not (has_markup Markup.boundN ignored_definition) andalso
         not (has_markup Markup.boundN ignored_reference) andalso
         not (has_urust_entity ignored_definition) andalso
         not (has_urust_entity ignored_reference))

    val full_body_parent_term =
      checked
        ("debug_assert!(let observed = macro_audit_marker; " ^
         "if observed { observed } else { false })")
    val full_body_bracket_term =
      checked
        ("debug_assert![let observed = macro_audit_marker; " ^
         "if observed { observed } else { false }]")
    val _ =
      audit_assert "full-body delimiters changed lowering"
        (Term.aconv (full_body_parent_term, full_body_bracket_term))
    val _ =
      audit_assert "retained full-body initializer evaluated more than once"
        (count_constant
          \<^const_name>\<open>macro_audit_marker\<close>
          full_body_parent_term = 1)

    val ignored_full_body_term =
      checked
        ("debug_assert!(true, " ^
         "let ignored = macro_audit_ignored_marker; ignored)")
    val _ =
      audit_assert "ignored full-body assertion argument entered the term"
        (Term.aconv
          (ignored_full_body_term, checked "debug_assert!(true)"))
    val _ =
      audit_assert "ignored full-body initializer entered the term"
        (count_constant
          \<^const_name>\<open>macro_audit_ignored_marker\<close>
          ignored_full_body_term = 0)
    val _ =
      audit_assert "ignored full-body message argument entered the term"
        (Term.aconv
          (checked
            ("panic!(\"kept\", " ^
             "let ignored = macro_audit_ignored_marker; ignored)"),
           checked "panic!(\"kept\")"))

    val vec_full_body_term =
      checked
        ("vec![" ^
         "let first = macro_audit_vec_first; first, " ^
         "let second = macro_audit_vec_second; second]")
    val vec_grouped_array_term =
      checked
        ("[(let first = macro_audit_vec_first; first), " ^
         "(let second = macro_audit_vec_second; second)]")
    val _ =
      audit_assert "vec! complete-body element order changed"
        (Term.aconv (vec_full_body_term, vec_grouped_array_term))
    val _ =
      audit_assert "vec! complete-body elements were not evaluated once each"
        (count_constant
           \<^const_name>\<open>macro_audit_vec_first\<close>
           vec_full_body_term = 1 andalso
         count_constant
           \<^const_name>\<open>macro_audit_vec_second\<close>
           vec_full_body_term = 1)

    val _ =
      audit_assert "ignored assertion arguments entered the term"
        (Term.aconv
          (unchecked "assert!(true, unknown_ignored, 1 + false)",
           unchecked "assert!(true)"))
    val _ =
      audit_assert "ignored panic arguments entered the term"
        (Term.aconv
          (unchecked "panic!(\"kept\", unknown_ignored, { return missing; })",
           unchecked "panic!(\"kept\")"))
    val _ =
      audit_assert "debug_assert! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert!(true)",
           unchecked "assert!(true)"))
    val _ =
      audit_assert "debug_assert_eq! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert_eq!(1, 1)",
           unchecked "assert_eq!(1, 1)"))
    val _ =
      audit_assert "debug_assert_ne! selected a non-legacy target"
        (Term.aconv
          (unchecked "debug_assert_ne!(1, 2)",
           unchecked "assert_ne!(1, 2)"))
    val _ =
      audit_assert "todo! stopped aliasing unimplemented!"
        (Term.aconv
          (unchecked "todo!(\"later\")",
           unchecked "unimplemented!(\"later\")"))
    val _ =
      audit_assert "unreachable! stopped aliasing panic!"
        (Term.aconv
          (unchecked "unreachable!(\"never\")",
           unchecked "panic!(\"never\")"))
    val _ =
      audit_assert "vec! stopped reusing the array builder"
        (Term.aconv
          (unchecked "vec![1, 2, 3]",
           unchecked "[1, 2, 3]"))
    val legacy_ref_address =
      Term.map_types (K dummyT) \<^term>\<open>ref_address\<close>
    fun address_target source =
      (case unchecked source of
         Const (name, _) $ target $ _
           => if name = \<^const_name>\<open>bindlift1\<close> then target
              else error "legacy macro regression audit: address macro stopped using bindlift1"
       | _ =>
           error "legacy macro regression audit: address macro term shape changed")
    val _ =
      audit_assert "addr_of! stopped using the exact legacy ref_address target"
        (Term.aconv
          (address_target "addr_of!(macro_audit_ref)",
           legacy_ref_address))
    val _ =
      audit_assert "addr_of_mut! stopped using the exact legacy ref_address target"
        (Term.aconv
          (address_target "addr_of_mut!(macro_audit_ref)",
           legacy_ref_address))

    fun is_recovered_full_body expression =
      (case expression of
         UE_Macro
           (path, _,
            MP_Arguments
              [UE_Let
                (P_Ident ("recovered", _),
                 UE_Literal (LP_Bool (true, _)),
                 UE_If
                   (UE_Path condition_path,
                    UE_Block (UE_Path then_path, _),
                    SOME (UE_Block _), _))],
            _) =>
           render_path path = "debug_assert" andalso
           render_path condition_path = "recovered" andalso
           render_path then_path = "recovered"
       | _ => false)
    fun reject_then_recover bad =
      let
        val _ =
          (case Exn.result parse_text bad of
             Exn.Res _ =>
               error
                 ("legacy macro regression audit: malformed full body " ^
                  quote bad ^ " unexpectedly parsed")
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn else ())
        val recovered =
          parse_text
            ("debug_assert!(let recovered = true; " ^
             "if recovered { recovered } else { false })")
      in
        audit_assert
          ("malformed full body leaked parser state after " ^ quote bad)
          (is_recovered_full_body recovered)
      end
    val _ =
      List.app reject_then_recover
        ["debug_assert!(let flag = true;)",
         "assert_eq!(let left = true; left,, false)",
         "debug_assert!(let flag = true; if flag { true } else { false)",
         "debug_assert![let flag = true; flag)"]

    val matches_term =
      checked "matches!(macro_audit_scrutinee, Some(_))"
    val explicit_case =
      checked
        "match_case macro_audit_scrutinee { Some(_) \<Rightarrow> \<llangle>True\<rrangle>, _ \<Rightarrow> \<llangle>False\<rrangle> }"
    val _ =
      audit_assert "matches! stopped using ordinary case compilation"
        (Term.aconv (matches_term, explicit_case))
    val _ =
      audit_assert "matches! evaluated its scrutinee more than once"
        (count_constant
          \<^const_name>\<open>macro_audit_scrutinee\<close>
          matches_term = 1)
    val _ =
      audit_assert "matches! lost its requested-pattern true branch"
        (count_constant \<^const_name>\<open>True\<close> matches_term = 1)
    val _ =
      audit_assert "matches! lost its wildcard false fallback"
        (count_constant \<^const_name>\<open>False\<close> matches_term = 1)
  in
    val _ = writeln "Legacy macro structure, span, and markup regressions passed"
  end
\<close>

section\<open> Expression-antiquotation callee audit \<close>

definition antiquotation_call_audit_direct ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open> antiquotation_call_audit_direct \<equiv> lift_fun2 (+) \<close>

definition antiquotation_call_audit_notation ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open> antiquotation_call_audit_notation \<equiv> lift_fun2 (+) \<close>

consts
  antiquotation_call_audit_first :: nat
  antiquotation_call_audit_second :: nat

micro_rust_notation (call) antiquotation_call_audit_notation
  ("antiquotation_call_audit_direct")

text\<open>
These checks pin the deliberately narrow callable-antiquotation boundary. The AST retains the exact
body source and the complete invocation span; lowering parses that source directly, bypasses call
notation and \<open>literal\<close>, preserves argument order, and retains binder navigation inside the
antiquotation.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("expression-antiquotation callee audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "expression-antiquotation callee audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun is_path name (UE_Path path) = render_path path = name
      | is_path _ _ = false

    val opener = "\<epsilon>\<open>"
    val body = "  antiquotation_call_audit_direct\n"
    val ast_text = opener ^ body ^ "\<close>(first, second)"
    val ast_start =
      Position.make0 7 30 300 "" "" "antiquotation-call-ast-audit"
    val body_start = Position.symbol_explode opener ast_start
    val body_stop = Position.symbol_explode (opener ^ body) ast_start
    val call_stop = Position.symbol_explode ast_text ast_start
    val ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          ast_text ast_start)
    val _ =
      (case ast of
         UE_Call
           (UC_Antiq source, [first, second], call_pos) =>
           (audit_assert "callee constructor changed"
              (is_path "first" first andalso is_path "second" second);
            audit_assert "retained body text changed"
              (Input.string_of source = body);
            audit_assert "retained body range start moved"
              (Position.offset_of (#1 (Input.range_of source)) =
                Position.offset_of body_start);
            audit_assert "retained body range end moved"
              (Position.offset_of (#2 (Input.range_of source)) =
                Position.offset_of body_stop);
            audit_assert "call span no longer starts at the antiquotation opener"
              (Position.offset_of call_pos =
                Position.offset_of ast_start);
            audit_assert "call span no longer includes the closing parenthesis"
              (Position.end_offset_of call_pos =
                Position.offset_of call_stop);
            audit_assert "expression_position lost the complete call span"
              (Position.offset_of (expression_position ast) =
                 Position.offset_of call_pos andalso
               Position.end_offset_of (expression_position ast) =
                 Position.end_offset_of call_pos))
       | _ =>
           error "expression-antiquotation callee audit: call AST changed")

    val direct =
      checked
        ("\<epsilon>\<open>antiquotation_call_audit_direct\<close>(" ^
         "\<llangle>antiquotation_call_audit_first\<rrangle>, " ^
         "\<llangle>antiquotation_call_audit_second\<rrangle>)")
      |> Term_Position.strip_positions
    val ordinary =
      checked
        ("antiquotation_call_audit_direct(" ^
         "\<llangle>antiquotation_call_audit_first\<rrangle>, " ^
         "\<llangle>antiquotation_call_audit_second\<rrangle>)")
      |> Term_Position.strip_positions
    val (direct_head, direct_arguments) = Term.strip_comb direct
    val _ =
      audit_assert "direct call did not use funcall2"
        (case direct_head of
           Const (name, _) => name = \<^const_name>\<open>funcall2\<close>
         | _ => false)
    val _ =
      (case direct_arguments of
         [Const (callee, _), first, second] =>
           let
             fun is_literal expected argument =
               (case Term_Position.strip_positions argument of
                  Const (literal_name, _) $ Const (actual, _) =>
                    literal_name = \<^const_name>\<open>literal\<close> andalso
                    actual = expected
                | _ => false)
           in
             audit_assert "embedded callee was not passed directly"
               (callee =
                 \<^const_name>\<open>antiquotation_call_audit_direct\<close>);
             audit_assert "first argument moved or changed"
               (is_literal
                 \<^const_name>\<open>antiquotation_call_audit_first\<close>
                 first);
             audit_assert "second argument moved or changed"
               (is_literal
                 \<^const_name>\<open>antiquotation_call_audit_second\<close>
                 second)
           end
       | _ =>
           error
             "expression-antiquotation callee audit: funcall2 argument shape changed")
    val _ =
      audit_assert "embedded callee was parsed more than once"
        (count_constant
          \<^const_name>\<open>antiquotation_call_audit_direct\<close>
          direct = 1)
    val _ =
      audit_assert "embedded callee received a literal wrapper"
        (count_constant \<^const_name>\<open>literal\<close> direct = 2)
    val _ =
      audit_assert "embedded callee entered notation dispatch"
        (count_constant
          \<^const_name>\<open>antiquotation_call_audit_notation\<close>
          direct = 0 andalso
         count_constant \<^const_name>\<open>urust_dispatch\<close> direct = 0)
    val _ =
      audit_assert "notation-collision fixture did not dispatch an ordinary call"
        (count_constant
          \<^const_name>\<open>antiquotation_call_audit_notation\<close>
          ordinary = 1)

    fun expect_rejection text expected =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source text)) () of
         Exn.Res _ =>
           error
             ("expression-antiquotation callee audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (Runtime.exn_message exn)))

    val malformed =
      [("\<epsilon>\<open>antiquotation_call_audit_direct\<close>(, 1)",
        "syntax error"),
       ("\<epsilon>\<open>antiquotation_call_audit_direct\<close>(1,, 2)",
        "syntax error"),
       ("\<epsilon>\<open>antiquotation_call_audit_direct\<close>(1",
        "syntax error found at end of input")]
    val _ =
      List.app
        (fn (text, expected) =>
          (expect_rejection text expected;
           audit_assert "parser state leaked after malformed call"
             (case parse_text "()" of
                UE_Unit _ => true
              | _ => false)))
        malformed

    fun find_from text needle offset =
      if offset + size needle > size text
      then error
        ("expression-antiquotation callee audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    val markup_text =
      "let h = \<llangle>antiquotation_call_audit_direct\<rrangle>; " ^
      "\<epsilon>\<open>h\<close>(" ^
      "\<llangle>antiquotation_call_audit_first\<rrangle>, " ^
      "\<llangle>antiquotation_call_audit_second\<rrangle>)"
    val markup_start =
      Position.make0 11 50 500 "" "" "antiquotation-call-markup-audit"
    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source
                      markup_text markup_start))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, tree)) result =
          fold collect_markup tree (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun entity_id property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               "expression-antiquotation callee audit: binder entity markup changed")
      end
    val (definition_offset, definition_position) =
      token_position markup_text markup_start "h" 0
    val (_, reference_position) =
      token_position markup_text markup_start "h"
        (definition_offset + size "h")
    val (_, opener_position) =
      token_position markup_text markup_start "\<epsilon>" 0
    val _ =
      audit_assert "antiquotation opener lost literal markup"
        (has_markup Markup.literalN opener_position)
    val _ =
      audit_assert "antiquotation callee binder definition lost bound markup"
        (has_markup Markup.boundN definition_position)
    val _ =
      audit_assert "antiquotation callee binder reference lost bound markup"
        (has_markup Markup.boundN reference_position)
    val _ =
      audit_assert "antiquotation callee binder navigation changed"
        (entity_id Markup.defN definition_position =
          entity_id Markup.refN reference_position)
  in
    val _ =
      writeln
        "Expression-antiquotation callee AST, lowering, recovery, and markup regressions passed"
  end
\<close>

section\<open> Arity-indexed function-literal callee audit \<close>

text\<open>
These checks pin the function-literal boundary independently of same-source conformance: exact HOL and
suffix ranges, complete call spans, lift-before-parameter-before-call lowering, argument order,
dispatch/literal bypass, failure recovery, suffix token markup, and captured-binder navigation.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("function-literal callee audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "function-literal callee audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)
      |> Term_Position.strip_positions

    fun same_start actual expected =
      Position.offset_of actual = Position.offset_of expected

    fun same_stop actual expected =
      Position.end_offset_of actual = Position.offset_of expected

    fun is_path name (UE_Path path) = render_path path = name
      | is_path _ _ = false

    val opener = "\<llangle>"
    val body = "  (\<lambda>x. x)\n"
    val closer = "\<rrangle>"
    val suffix14 = "\<^sub>1\<^sub>4"
    val generic = "::<function_literal_parameter_a>"
    val arguments = "(first, second)"
    val ast_text =
      opener ^ body ^ closer ^ suffix14 ^ generic ^ arguments
    val ast_start =
      Position.make0 7 30 300 "" "" "function-literal-ast-audit"
    val body_start = Position.symbol_explode opener ast_start
    val body_stop = Position.symbol_explode (opener ^ body) ast_start
    val suffix_start =
      Position.symbol_explode (opener ^ body ^ closer) ast_start
    val suffix_stop =
      Position.symbol_explode
        (opener ^ body ^ closer ^ suffix14) ast_start
    val generic_start =
      Position.symbol_explode
        (opener ^ body ^ closer ^ suffix14 ^ "::<") ast_start
    val generic_stop =
      Position.symbol_explode
        (opener ^ body ^ closer ^ suffix14 ^
          "::<function_literal_parameter_a") ast_start
    val call_stop = Position.symbol_explode ast_text ast_start
    val ast =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          ast_text ast_start)
    val _ =
      (case ast of
         UE_Call
           (UC_FunLiteral
              (source, 14, suffix_pos,
               SOME
                 (Generic_Args
                   ([Generic_Arg (canonical, generic_source)], _))),
            [first, second], call_pos) =>
           (audit_assert "runtime argument order changed"
              (is_path "first" first andalso is_path "second" second);
            audit_assert "retained HOL body text changed"
              (Input.string_of source = body);
            audit_assert "retained HOL body range start moved"
              (same_start (#1 (Input.range_of source)) body_start);
            audit_assert "retained HOL body range end moved"
              (Position.offset_of (#2 (Input.range_of source)) =
                Position.offset_of body_stop);
            audit_assert "two-digit suffix range start moved"
              (same_start suffix_pos suffix_start);
            audit_assert "two-digit suffix range end moved"
              (same_stop suffix_pos suffix_stop);
            audit_assert "generic canonical fragment changed"
              (canonical = "function_literal_parameter_a");
            audit_assert "generic source range start moved"
              (same_start (#1 (Input.range_of generic_source)) generic_start);
            audit_assert "generic source range end moved"
              (Position.offset_of (#2 (Input.range_of generic_source)) =
                Position.offset_of generic_stop);
            audit_assert "call span no longer starts at the value opener"
              (same_start call_pos ast_start);
            audit_assert "call span no longer includes the closing parenthesis"
              (same_stop call_pos call_stop);
            audit_assert "expression_position lost the complete call span"
              (same_start (expression_position ast) ast_start andalso
               same_stop (expression_position ast) call_stop))
       | _ => error "function-literal callee audit: call AST changed")

    val suffix9_text = "\<llangle>id\<rrangle>\<^sub>9(0)"
    val suffix9_start =
      Position.make0 13 70 700 "" "" "function-literal-suffix9-audit"
    val suffix9_expected_start =
      Position.symbol_explode "\<llangle>id\<rrangle>" suffix9_start
    val suffix9_expected_stop =
      Position.symbol_explode
        "\<llangle>id\<rrangle>\<^sub>9" suffix9_start
    val _ =
      (case
         parse_source
           (Parser_Lex_Util.positioned_content_source
             suffix9_text suffix9_start) of
         UE_Call
           (UC_FunLiteral (_, 9, suffix_pos, NONE), [_], _) =>
           (audit_assert "one-digit suffix range start moved"
              (same_start suffix_pos suffix9_expected_start);
            audit_assert "one-digit suffix range end moved"
              (same_stop suffix_pos suffix9_expected_stop))
       | _ => error "function-literal callee audit: one-digit suffix AST changed")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun constant_name (Const (name, _)) = SOME name
      | constant_name _ = NONE

    fun literal_constant expected argument =
      (case argument of
         Const (literal_name, _) $ Const (actual, _) =>
           literal_name = \<^const_name>\<open>literal\<close> andalso
           actual = expected
       | _ => false)

    val direct =
      checked
        ("\<llangle>function_literal_collision\<rrangle>\<^sub>1(" ^
          "\<llangle>antiquotation_call_audit_first\<rrangle>)")
    val _ =
      (case Term.strip_comb direct of
         (Const (call_name, _), [lifted, runtime_argument]) =>
           (audit_assert "direct function literal did not use funcall1"
              (call_name = \<^const_name>\<open>funcall1\<close>);
            audit_assert "direct runtime argument changed"
              (literal_constant
                \<^const_name>\<open>antiquotation_call_audit_first\<close>
                runtime_argument);
            case Term.strip_comb lifted of
              (Const (lift_name, _), [Const (body_name, _)]) =>
                (audit_assert "direct function literal did not use lift_fun1"
                   (lift_name = \<^const_name>\<open>lift_fun1\<close>);
                 audit_assert "HOL body changed or gained a wrapper"
                   (body_name =
                     \<^const_name>\<open>function_literal_collision\<close>))
            | _ =>
                error
                  "function-literal callee audit: direct lifted term changed")
       | _ => error "function-literal callee audit: direct call term changed")
    val _ =
      audit_assert "HOL body was duplicated"
        (count_constant
          \<^const_name>\<open>function_literal_collision\<close> direct = 1)
    val _ =
      audit_assert "HOL body or lifted function received a literal wrapper"
        (count_constant \<^const_name>\<open>literal\<close> direct = 1)
    val _ =
      audit_assert "HOL body entered notation dispatch"
        (count_constant \<^const_name>\<open>urust_dispatch\<close> direct = 0)

    val parameterized =
      checked
        ("\<llangle>\<lambda>a b c. (a + b + c :: nat)\<rrangle>\<^sub>3" ^
         "::<function_literal_parameter_a>(" ^
         "\<llangle>antiquotation_call_audit_first\<rrangle>, " ^
         "\<llangle>antiquotation_call_audit_second\<rrangle>)")
    val _ =
      (case Term.strip_comb parameterized of
         (Const (call_name, _),
          [function, first_argument, second_argument]) =>
           let
             val (lift_head, lift_arguments) =
               Term.strip_comb function
           in
             audit_assert "parameterized function literal did not use funcall2"
               (call_name = \<^const_name>\<open>funcall2\<close>);
             audit_assert "generic parameter was not applied after lift_fun3"
               (constant_name lift_head =
                  SOME \<^const_name>\<open>lift_fun3\<close> andalso
                length lift_arguments = 2 andalso
                constant_name (List.last lift_arguments) =
                  SOME
                    \<^const_name>\<open>function_literal_parameter_a\<close>);
             audit_assert "parameterized runtime argument order changed"
               (literal_constant
                  \<^const_name>\<open>antiquotation_call_audit_first\<close>
                  first_argument andalso
                literal_constant
                  \<^const_name>\<open>antiquotation_call_audit_second\<close>
                  second_argument)
           end
       | _ =>
           error
             "function-literal callee audit: parameterized call term changed")

    fun expect_rejection text expected =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source text)) () of
         Exn.Res _ =>
           error
             ("function-literal callee audit: unexpectedly accepted " ^
               quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (Runtime.exn_message exn)))

    val malformed =
      [("\<llangle>id\<rrangle>\<^sub>0()", "unexpected input"),
       ("\<llangle>id\<rrangle>\<^sub>1(,0)", "syntax error"),
       ("\<llangle>id\<rrangle>\<^sub>1::<-1>()", "unexpected input"),
       ("\<llangle>id\<rrangle>\<^sub>1::<1(0)", "unterminated turbofish"),
       ("\<llangle>\<lambda>x. x\<rrangle>\<^sub>1()",
        "Type unification failed")]
    val _ =
      List.app
        (fn (text, expected) =>
          (expect_rejection text expected;
           audit_assert "parser state leaked after failed function literal"
             (case parse "()" of
                UE_Unit _ => true
              | _ => false)))
        malformed

    fun find_from text needle offset =
      if offset + size needle > size text
      then error
        ("function-literal callee audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    val markup_text =
      "let captured = \<llangle>1 :: nat\<rrangle>; " ^
      "\<llangle>\<lambda>x. x + captured\<rrangle>\<^sub>1(0)"
    val markup_start =
      Position.make0 11 50 500 "" "" "function-literal-markup-audit"
    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source
                      markup_text markup_start))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, tree)) result =
          fold collect_markup tree (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun entity_id property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               "function-literal callee audit: binder entity markup changed")
      end
    val (definition_offset, definition_position) =
      token_position markup_text markup_start "captured" 0
    val (_, reference_position) =
      token_position markup_text markup_start "captured"
        (definition_offset + size "captured")
    val (_, suffix_position) =
      token_position markup_text markup_start "\<^sub>1" 0
    val _ =
      audit_assert "function-literal suffix lost delimiter markup"
        (has_markup Markup.delimiterN suffix_position)
    val _ =
      audit_assert "function-literal suffix lost typing markup"
        (has_markup Markup.typingN suffix_position)
    val _ =
      audit_assert "captured binder definition lost bound markup"
        (has_markup Markup.boundN definition_position)
    val _ =
      audit_assert "function-literal body reference lost bound markup"
        (has_markup Markup.boundN reference_position)
    val _ =
      audit_assert "function-literal binder navigation changed"
        (entity_id Markup.defN definition_position =
          entity_id Markup.refN reference_position)
  in
    val _ =
      writeln
        "Function-literal AST, lowering, recovery, and markup regressions passed"
  end
\<close>

section\<open> Closure AST, lowering, and binder-navigation audit \<close>

consts
  closure_audit_marker ::
    \<open>(unit, nat, nat, unit, unit, unit) expression\<close>

text\<open>
These checks pin the second-class closure boundary below the source-level examples. They retain
ordered pattern-shaped formals and the complete closure span, prove that grouping alone re-enters
ordinary expression positions, and inspect the checked shallow term for the exact frontend shape.
The markup checks lock definition/reference navigation across ordinary, duplicate, nested, and
shadowed formals.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("closure regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "closure regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_abstractions (Abs (_, _, body)) =
          1 + count_abstractions body
      | count_abstractions (left $ right) =
          count_abstractions left + count_abstractions right
      | count_abstractions _ = 0

    fun is_grouped_closure (UE_Group (UE_Closure _, _)) = true
      | is_grouped_closure _ = false

    val ast_text = "|first, second| second"
    val ast_start =
      Position.make0 5 20 100 "" "" "closure-ast-audit"
    val ast_stop =
      Position.symbol_explode ast_text ast_start
    val ast =
      parse
        (Parser_Lex_Util.positioned_content_source
          ast_text ast_start)
    val _ =
      (case ast of
         UE_Closure
           ([P_Ident ("first", _), P_Ident ("second", _)],
            UE_Path body_path, closure_pos) =>
           (audit_assert "closure body path changed"
              (render_path body_path = "second");
            audit_assert "full closure span start moved"
              (Position.offset_of closure_pos =
                Position.offset_of ast_start);
            audit_assert "full closure span end moved"
              (Position.end_offset_of closure_pos =
                Position.offset_of ast_stop);
            audit_assert "expression_position lost the closure span"
              (Position.offset_of (expression_position ast) =
                 Position.offset_of closure_pos andalso
               Position.end_offset_of (expression_position ast) =
                 Position.end_offset_of closure_pos))
       | _ =>
           error "closure regression audit: closure AST changed")

    val _ =
      (case parse_text "let f = (|| 1); ()" of
         UE_Let (_, initializer, _) =>
           audit_assert "grouped closure initializer stopped parsing"
             (is_grouped_closure initializer)
       | _ =>
           error "closure regression audit: grouped initializer AST changed")
    val _ =
      (case parse_text "target = (|| 1)" of
         UE_Assign (_, _, rhs, _) =>
           audit_assert "grouped closure assignment RHS stopped parsing"
             (is_grouped_closure rhs)
       | _ =>
           error "closure regression audit: grouped assignment AST changed")
    val _ =
      (case parse_text "1 + (|| 2)" of
         UE_Bin (_, _, rhs, _) =>
           audit_assert "grouped closure binary operand stopped parsing"
             (is_grouped_closure rhs)
       | _ =>
           error "closure regression audit: grouped binary AST changed")
    val _ =
      (case parse_text "if (|| true) { () }" of
         UE_If (condition, _, _, _) =>
           audit_assert "grouped closure condition stopped parsing"
             (is_grouped_closure condition)
       | _ =>
           error "closure regression audit: grouped condition AST changed")
    val _ =
      (case parse_text "match (|| true) { _ \<Rightarrow> () }" of
         UE_Match (_, scrutinee, _, _) =>
           audit_assert "grouped closure scrutinee stopped parsing"
             (is_grouped_closure scrutinee)
       | _ =>
           error "closure regression audit: grouped scrutinee AST changed")
    val _ =
      (case parse_text "for item in (|| []) { () }" of
         UE_For (_, iterable, _, _) =>
           audit_assert "grouped closure iterable stopped parsing"
             (is_grouped_closure iterable)
       | _ =>
           error "closure regression audit: grouped iterable AST changed")
    val _ =
      (case
          parse_text
            "match true { true \<Rightarrow> (|| true), false \<Rightarrow> (|| false) }" of
         UE_Match
           (_, _, [UR_Arm (_, _, first), UR_Arm (_, _, second)], _) =>
           (audit_assert "first grouped closure arm stopped parsing"
              (is_grouped_closure first);
            audit_assert "second grouped closure arm stopped parsing"
              (is_grouped_closure second))
       | _ =>
           error "closure regression audit: grouped arm AST changed")
    val _ =
      (case parse_text "(|| 1); ()" of
         UE_Seq (left, _) =>
           audit_assert "grouped closure sequencing-left stopped parsing"
             (is_grouped_closure left)
       | _ =>
           error "closure regression audit: grouped sequence AST changed")
    val _ =
      (case parse_text "|| (|| 1)" of
         UE_Closure (_, body, _) =>
           audit_assert "grouped nested closure body stopped parsing"
             (is_grouped_closure body)
       | _ =>
           error "closure regression audit: grouped nested closure AST changed")

    val guard =
      parse_text
        "match_case Some(()) { Some(_) if || true \<Rightarrow> (), None \<Rightarrow> () }"
    val _ =
      (case guard of
         UE_Match
           (_, _,
            UR_Arm
              (_, SOME (UE_Closure ([], UE_Literal (LP_Bool (true, _)), _), _), _) :: _,
            _) =>
           ()
       | _ =>
           error
             "closure regression audit: a closure stopped parsing as a complete guard body")

    val shape =
      checked
        "|first, second| \<epsilon>\<open>closure_audit_marker\<close>"
    val _ =
      audit_assert "closure did not lower to exactly one literal"
        (count_constant \<^const_name>\<open>literal\<close> shape = 1)
    val _ =
      audit_assert "closure did not lower to exactly one FunctionBody"
        (count_constant \<^const_name>\<open>FunctionBody\<close> shape = 1)
    val _ =
      audit_assert "closure did not lower to one abstraction per formal"
        (count_abstractions shape = 2)
    val _ =
      audit_assert "closure body was lowered more than once"
        (count_constant
          \<^const_name>\<open>closure_audit_marker\<close> shape = 1)

    fun closure_payload
        (Const (name, _) $ payload) =
          if name = \<^const_name>\<open>literal\<close>
          then payload
          else error
            "closure regression audit: closure wrapper stopped using literal"
      | closure_payload _ =
          error "closure regression audit: closure wrapper shape changed"

    val ordered =
      checked
        "|first, second| \<llangle>(first :: nat, second :: bool)\<rrangle>"
    val (ordered_formals, _) =
      Term.strip_abs (closure_payload ordered)
    val _ =
      audit_assert "closure abstraction order changed"
        (map #2 ordered_formals = [HOLogic.natT, HOLogic.boolT])

    val duplicate =
      checked "|same, same, same| same"
    val (duplicate_formals, duplicate_body) =
      Term.strip_abs (closure_payload duplicate)
    val _ =
      audit_assert "duplicate closure formals stopped producing abstractions"
        (length duplicate_formals = 3)
    val _ =
      (case duplicate_body of
         Const (function_body_name, _) $
           (Const (literal_name, _) $ Bound 0) =>
           (audit_assert "duplicate closure body lost FunctionBody"
              (function_body_name =
                \<^const_name>\<open>FunctionBody\<close>);
            audit_assert "duplicate closure body lost literal lowering"
              (literal_name = \<^const_name>\<open>literal\<close>))
       | _ =>
           error
             "closure regression audit: innermost duplicate no longer shadows earlier formals")

    val allocator_start =
      Position.make0 9 30 300 "" "" "closure-allocator-audit"
    val allocator_positions =
      [allocator_start,
       Position.symbol_explode "first " allocator_start,
       Position.symbol_explode "first second " allocator_start]
    val (allocated, allocated_environment) =
      URust_Resolution.allocate_closure_formals ctxt
        URust_Resolution.empty_environment
        (map2 pair ["first", "second", "first"] allocator_positions)
    val allocated_names =
      map
        (fn Free (name, _) => name
          | _ =>
              error
                "closure regression audit: allocator returned a non-Free formal")
        allocated
    val _ =
      audit_assert "closure allocator reused a formal identity"
        (length (distinct (op =) allocated_names) = 3)
    val _ =
      audit_assert "closure allocator did not preserve source order"
        (length allocated = 3)
    val _ =
      audit_assert "later duplicate did not win in the final environment"
        (case URust_Resolution.lookup_local
            allocated_environment "first" of
           SOME selected => Term.aconv (selected, List.last allocated)
         | NONE => false)

    val resolved_dispatch =
      checked "|closureRole| closureRole(closureRole)"
    val _ =
      audit_assert "checked closure retained an unresolved dispatch marker"
        (count_constant
          \<^const_name>\<open>urust_dispatch\<close>
          resolved_dispatch = 0)

    fun find_from text needle offset =
      if offset + size needle > size text
      then error
        ("closure regression audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    val ordinary_text = "|alpha| alpha"
    val ordinary_start =
      Position.make0 11 40 400 "" "" "closure-markup-ordinary"
    val duplicate_text = "|dup, dup| dup"
    val duplicate_start =
      Position.make0 13 50 500 "" "" "closure-markup-duplicate"
    val nested_text =
      "|outer| (|inner| if true { outer } else { inner })"
    val nested_start =
      Position.make0 17 60 600 "" "" "closure-markup-nested"
    val shadow_text =
      "|shadow| { let shadow = shadow; shadow }"
    val shadow_start =
      Position.make0 19 70 700 "" "" "closure-markup-shadow"

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Parser_Test_Elaboration.expression ctxt
                  (Parser_Lex_Util.positioned_content_source
                    text start)) ())
          ())
    val _ = capture_elaboration ordinary_text ordinary_start
    val _ = capture_elaboration duplicate_text duplicate_start
    val _ = capture_elaboration nested_text nested_start
    val _ = capture_elaboration shadow_text shadow_start

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_bound position =
      exists
        (fn (name, properties) =>
          name = Markup.boundN andalso
            has_position properties position)
        markup
    fun entity_id property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               "closure regression audit: binder entity markup changed")
      end
    fun audit_navigation label definition reference =
      (audit_assert (label ^ " definition lost bound markup")
         (has_bound definition);
       audit_assert (label ^ " reference lost bound markup")
         (has_bound reference);
       audit_assert (label ^ " reference stopped targeting its formal")
         (entity_id Markup.defN definition =
          entity_id Markup.refN reference))

    val (ordinary_def_offset, ordinary_definition) =
      token_position ordinary_text ordinary_start "alpha" 0
    val (_, ordinary_reference) =
      token_position ordinary_text ordinary_start "alpha"
        (ordinary_def_offset + size "alpha")
    val _ =
      audit_navigation
        "ordinary closure formal"
        ordinary_definition ordinary_reference

    val (duplicate_first_offset, duplicate_first_definition) =
      token_position duplicate_text duplicate_start "dup" 0
    val (duplicate_second_offset, duplicate_second_definition) =
      token_position duplicate_text duplicate_start "dup"
        (duplicate_first_offset + size "dup")
    val (_, duplicate_reference) =
      token_position duplicate_text duplicate_start "dup"
        (duplicate_second_offset + size "dup")
    val duplicate_first_id =
      entity_id Markup.defN duplicate_first_definition
    val duplicate_second_id =
      entity_id Markup.defN duplicate_second_definition
    val _ =
      audit_assert "duplicate formal definitions reused an entity ID"
        (duplicate_first_id <> duplicate_second_id)
    val _ =
      audit_navigation
        "duplicate closure formal"
        duplicate_second_definition duplicate_reference
    val _ =
      audit_assert "duplicate body reference targeted the first formal"
        (entity_id Markup.refN duplicate_reference <>
          duplicate_first_id)

    val (nested_outer_offset, nested_outer_definition) =
      token_position nested_text nested_start "outer" 0
    val (nested_inner_offset, nested_inner_definition) =
      token_position nested_text nested_start "inner" 0
    val (_, nested_outer_reference) =
      token_position nested_text nested_start "outer"
        (nested_outer_offset + size "outer")
    val (_, nested_inner_reference) =
      token_position nested_text nested_start "inner"
        (nested_inner_offset + size "inner")
    val _ =
      audit_navigation
        "nested outer closure formal"
        nested_outer_definition nested_outer_reference
    val _ =
      audit_navigation
        "nested inner closure formal"
        nested_inner_definition nested_inner_reference
    val _ =
      audit_assert "nested closure formals reused an entity ID"
        (entity_id Markup.defN nested_outer_definition <>
          entity_id Markup.defN nested_inner_definition)

    val (shadow_outer_offset, shadow_outer_definition) =
      token_position shadow_text shadow_start "shadow" 0
    val (shadow_inner_offset, shadow_inner_definition) =
      token_position shadow_text shadow_start "shadow"
        (shadow_outer_offset + size "shadow")
    val (shadow_outer_reference_offset, shadow_outer_reference) =
      token_position shadow_text shadow_start "shadow"
        (shadow_inner_offset + size "shadow")
    val (_, shadow_inner_reference) =
      token_position shadow_text shadow_start "shadow"
        (shadow_outer_reference_offset + size "shadow")
    val _ =
      audit_navigation
        "shadowed closure formal"
        shadow_outer_definition shadow_outer_reference
    val _ =
      audit_navigation
        "shadowing let binder"
        shadow_inner_definition shadow_inner_reference
    val _ =
      audit_assert "shadowing let binder reused the closure formal entity ID"
        (entity_id Markup.defN shadow_outer_definition <>
          entity_id Markup.defN shadow_inner_definition)
  in
    val _ =
      writeln
        "Closure AST, lowering, allocator, dispatch, and markup regressions passed"
end
\<close>


section\<open> Cast AST, lowering, markup, and recovery \<close>

text\<open>
The cast audit pins the closed target representation, left association,
cast-before-prefix precedence, source position, exact lowering table, semantic
collapses, reserved-word markup, and parser-state recovery after malformed
targets.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("cast regression audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "cast regression audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun path_named expected (UE_Path path) =
          render_path path = expected
      | path_named _ _ = false

    fun target_is expected actual = expected = actual

    val positioned_text = "operand as *mut usize"
    val positioned_start =
      Position.make0 9 14 0 "" "" ""
    val positioned_ast =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          positioned_text positioned_start)
    val as_offset = size "operand "
    val expected_as =
      Position.symbol_explode
        (String.substring (positioned_text, 0, as_offset))
        positioned_start
    val _ =
      (case positioned_ast of
         UE_Cast
           (operand,
            CT_RawPointer (RPM_Mut, UT_Usize),
            as_position) =>
           (audit_assert "cast operand changed"
              (path_named "operand" operand);
            audit_assert "as position moved"
              (Position.offset_of as_position =
                Position.offset_of expected_as))
       | _ => error "cast regression audit: positioned cast AST changed")

    val _ =
      (case parse "source.field.method()[0]? as i64" of
         UE_Cast
           (UE_Unary
             (U_Propagate,
              UE_Index
                (UE_Call
                  (UC_Method
                    (UE_Field (source, "field", _),
                     Path_Segment ("method", _, NONE)),
                   [], _),
                 UE_Literal (LP_Integer ("0", _)), _),
              _),
            CT_Signed ST_I64, _) =>
           audit_assert "cast lost its complete postfix operand"
             (path_named "source" source)
       | _ =>
           error
             "cast regression audit: postfix operand AST changed")

    val _ =
      (case parse "value as u8 as u16 as i32" of
         UE_Cast
           (UE_Cast
             (UE_Cast
               (value, first, _),
              second, _),
            third, _) =>
           (audit_assert "cast chain lost its operand"
              (path_named "value" value);
            audit_assert "first cast target changed"
              (target_is (CT_Unsigned UT_U8) first);
            audit_assert "second cast target changed"
              (target_is (CT_Unsigned UT_U16) second);
            audit_assert "third cast target changed"
              (target_is (CT_Signed ST_I32) third))
       | _ =>
           error "cast regression audit: cast chain is not left-associated")

    val _ =
      (case parse "!value as u8" of
         UE_Unary
           (U_Not,
            UE_Cast
              (value, CT_Unsigned UT_U8, _),
            _) =>
           audit_assert "not/cast operand changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: cast-before-not precedence changed")

    val _ =
      (case parse "*raw as *const u8" of
         UE_Unary
           (U_Deref,
            UE_Cast
              (raw,
               CT_RawPointer (RPM_Const, UT_U8), _),
            _) =>
           audit_assert "deref/cast operand changed"
             (path_named "raw" raw)
       | _ =>
           error "cast regression audit: cast-before-deref precedence changed")

    val _ =
      (case parse "(!value) as u8" of
         UE_Cast
           (UE_Group
             (UE_Unary (U_Not, value, _), _),
            CT_Unsigned UT_U8, _) =>
           audit_assert "grouped opposite interpretation changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: grouped prefix/cast AST changed")

    val _ =
      (case parse "(value as u32).field.method()[0]?" of
         UE_Unary
           (U_Propagate,
            UE_Index
              (UE_Call
                (UC_Method
                  (UE_Field
                    (UE_Group
                      (UE_Cast
                        (value, CT_Unsigned UT_U32, _), _),
                     "field", _),
                   Path_Segment ("method", _, NONE)),
                 [], _),
               UE_Literal (LP_Integer ("0", _)), _),
            _) =>
           audit_assert "grouped cast postfix chain changed"
             (path_named "value" value)
       | _ =>
           error "cast regression audit: grouped cast postfix AST changed")

    fun unchecked text =
      URust_Translate.mk_expression ctxt [] (parse text)

    datatype lowering_kind =
        Unsigned_Lowering
      | Signed_Lowering
      | Pointer_Lowering

    val lowering_cases =
      [("value as u8", Unsigned_Lowering,
        \<^term>\<open>ucastu8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as u16", Unsigned_Lowering,
        \<^term>\<open>ucastu16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as u32", Unsigned_Lowering,
        \<^term>\<open>ucastu32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as u64", Unsigned_Lowering,
        \<^term>\<open>ucastu64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as usize", Unsigned_Lowering,
        \<^term>\<open>ucastu64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as i32", Signed_Lowering,
        \<^term>\<open>ucasti32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as i64", Signed_Lowering,
        \<^term>\<open>ucasti64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *const u8", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as *const u16", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as *const u32", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as *const u64", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *const usize", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *mut u8", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u8\<close>, \<^typ>\<open>8 word\<close>),
       ("value as *mut u16", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u16\<close>, \<^typ>\<open>16 word\<close>),
       ("value as *mut u32", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u32\<close>, \<^typ>\<open>32 word\<close>),
       ("value as *mut u64", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>),
       ("value as *mut usize", Pointer_Lowering,
        \<^term>\<open>raw_ptr_cast_u64\<close>, \<^typ>\<open>64 word\<close>)]

    fun count_constant expected term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)
        term 0

    fun cast_count term =
      count_constant \<^const_name>\<open>bind1\<close> term +
      count_constant \<^const_name>\<open>raw_ptr_cast\<close> term

    fun cast_result_type typ =
      Term.map_atyps
        (fn TFree _ => dummyT
          | TVar _ => dummyT
          | atomic => atomic)
        typ

    fun expected_lowering target_function =
      Type.constraint
        (cast_result_type
          (Term.range_type (fastype_of target_function)))
        (Term.list_comb
          (Term.map_types (K dummyT) target_function,
           [unchecked "value"]))

    fun checked text =
      Syntax.check_term ctxt (unchecked text)

    val reference_type_name =
      (case \<^typ>\<open>('address, 'global, 'value) Global_Store.ref\<close> of
         Type (name, _) => name
       | _ => error "cast regression audit: reference type abbreviation changed")

    fun result_width Pointer_Lowering term =
          (case fastype_of term of
             Type (expression_name, [_, value_type, _, _, _, _]) =>
               if expression_name = \<^type_name>\<open>expression\<close>
               then
                 (case value_type of
                    Type (reference_name, [_, _, width]) =>
                      if reference_name = reference_type_name
                      then width
                      else error "cast regression audit: pointer cast result is not a reference"
                  | _ =>
                      error "cast regression audit: pointer cast result is not a reference")
               else error "cast regression audit: cast result is not an expression"
           | _ => error "cast regression audit: cast result type changed")
      | result_width _ term =
          (case fastype_of term of
             Type (expression_name, [_, value_type, _, _, _, _]) =>
               if expression_name = \<^type_name>\<open>expression\<close>
               then value_type
               else error "cast regression audit: cast result is not an expression"
           | _ => error "cast regression audit: cast result type changed")

    fun check_lowering
      (source, kind, target_function, expected_width) =
      let
        val term = unchecked source
        val checked_term = checked source
      in
        audit_assert
          ("wrong lowering for " ^ quote source)
          (Term.aconv (term, expected_lowering target_function));
        audit_assert
          ("source cast did not lower exactly once for " ^ quote source)
          (cast_count term = 1);
        audit_assert
          ("wrong result width for " ^ quote source)
          (result_width kind checked_term = expected_width)
      end

    val _ = List.app check_lowering lowering_cases

    val _ =
      audit_assert "usize stopped collapsing to u64"
        (Term.aconv
          (unchecked "value as usize",
           unchecked "value as u64"))

    val _ =
      audit_assert "pointer usize stopped collapsing to pointer u64"
        (Term.aconv
          (unchecked "value as *const usize",
           unchecked "value as *const u64"))

    val _ =
      List.app
        (fn target =>
          audit_assert
            ("pointer mutability changed lowering for " ^ target)
            (Term.aconv
              (unchecked ("value as *const " ^ target),
               unchecked ("value as *mut " ^ target))))
        ["u8", "u16", "u32", "u64", "usize"]

    val chain = unchecked "value as u8 as u32 as i64"
    val _ =
      audit_assert "three-stage chain did not lower three casts"
        (cast_count chain = 3)
    val _ =
      audit_assert "three-stage lowering lost left nesting"
        (count_constant \<^const_name>\<open>bind1\<close> chain = 3 andalso
         result_width Signed_Lowering
           (checked "value as u8 as u32 as i64") =
             \<^typ>\<open>64 word\<close>)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("cast regression audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    val markup_text =
      "value as u8; value as u16; value as u32; " ^
      "value as u64; value as usize; value as i32; " ^
      "value as i64; raw as *const u8; raw as *mut usize"
    val markup_start =
      Position.make0 11 3 0 "" "" "cast-markup-audit"
    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                parse_source
                  (Parser_Lex_Util.positioned_content_source
                    markup_text markup_start)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun has_entity_markup position =
      has_markup Markup.defN position orelse
      has_markup Markup.refN position

    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size markup_text then rev positions
          else
            (case try (find_from markup_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position markup_text markup_start needle raw
                 in collect (raw + size needle) (position :: positions) end
             | NONE => rev positions)
      in collect 0 [] end

    val keyword_spellings =
      ["as", "u8", "u16", "u32", "u64", "usize", "i32", "i64",
       "const", "mut"]
    val type_spellings =
      ["u8", "u16", "u32", "u64", "usize", "i32", "i64"]
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              (audit_assert
                 (spelling ^ " lost keyword markup")
                 (has_markup Markup.keyword1N position);
               audit_assert
                 (spelling ^ " lost typing markup")
                 (has_markup Markup.typingN position)))
            (all_token_positions spelling))
        keyword_spellings
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                (spelling ^ " received identifier entity markup")
                (not (has_entity_markup position)))
            (all_token_positions spelling))
        type_spellings
    val _ =
      List.app
        (fn position =>
          audit_assert "* stopped being operator markup in cast targets"
            (has_markup Markup.operatorN position))
        (all_token_positions "*")

    val malformed =
      ["as u8",
       "value as",
       "value as *",
       "value as *const",
       "value as *mut",
       "value as u128",
       "value as i8",
       "value as i16",
       "value as i128",
       "value as isize",
       "value as f32",
       "value as f64",
       "value as char",
       "value as bool",
       "value as Target",
       "value as Target::Word",
       "value as Vec::<u8>",
       "value as *const i32",
       "value as *mut i64",
       "value as *const bool",
       "value as *mut Target",
       "value as *mut u128",
       "value as **const u8",
       "value as *const *const u8",
       "value as *const const u8",
       "value as *mut mut u8",
       "value as &u8",
       "value as as u8",
       "value as u8 as",
       "value as u8 as *const",
       "value as ()",
       "value as [u8]",
       "value as u8,",
       "value as u8 trailing",
       "value asu8",
       "value as U8",
       "value as u8_u16",
       "value as u32.field",
       "value as u32.method()",
       "value as u32[0]",
       "value as u32?",
       "value as u32()",
       "value as u8 as u32.field"]

    fun reject_then_recover bad =
      let
        val _ =
          (case Exn.result parse bad of
             Exn.Res _ =>
               error
                 ("cast regression audit: malformed cast accepted: " ^
                   quote bad)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn else ())
        val _ =
          (case parse "value as u8" of
             UE_Cast (_, CT_Unsigned UT_U8, _) => ()
           | _ =>
               error
                 ("cast regression audit: parser did not recover after " ^
                   quote bad))
      in () end

    val _ = List.app reject_then_recover malformed
  in
    val _ =
      writeln "Cast AST, lowering, markup, and recovery regressions passed"
  end
\<close>


section\<open> Struct-expression AST, lowering, markup, and recovery \<close>

definition d21_audit_identity1 ::
    \<open>'a \<Rightarrow> (unit, 'a, unit, unit, unit) function_body\<close>
  where \<open> d21_audit_identity1 \<equiv> lift_fun1 (\<lambda>value. value) \<close>

definition d21_audit_first2 ::
    \<open>nat \<Rightarrow> nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where \<open> d21_audit_first2 \<equiv> lift_fun2 (\<lambda>first second. first) \<close>

definition d21_audit_truth :: bool
  where \<open> d21_audit_truth \<equiv> True \<close>

consts
  d21_audit_marker_a :: nat
  d21_audit_marker_b :: nat
  d21_audit_marker_c :: nat

micro_rust_notation (call) d21_audit_identity1 ("D21AuditOne")
micro_rust_notation (call) d21_audit_first2 ("D21AuditPair")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("struct-expression regression audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "struct-expression regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source text)

    fun frontend text =
      Syntax.read_term ctxt ("\<lbrakk> " ^ text ^ " \<rbrakk>")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun count_named_atom name term =
      Term.fold_aterms
        (fn Free (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | Const (candidate, _) =>
              if Long_Name.base_name candidate = name
              then Integer.add 1
              else I
          | _ => I)
        term 0

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("struct-expression regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    val structural_text =
      "D21AuditPair {\n" ^
      "  alpha: \<llangle>d21_audit_marker_a\<rrangle>, // retained comment\n" ^
      "  beta: D21AuditPair { gamma: \<llangle>d21_audit_marker_b\<rrangle>, " ^
        "delta: \<llangle>d21_audit_marker_c\<rrangle> }\n" ^
      "}"
    val structural_start =
      Position.make0 31 700 0 "" "" "struct-expression-audit"
    val structural_stop =
      Position.symbol_explode structural_text structural_start
    val structural_source =
      Parser_Lex_Util.positioned_content_source
        structural_text structural_start
    val structural_ast = parse structural_source

    val control_text =
      "match (D21AuditOne { value: Some(()) }) {\n" ^
      "  Some(_) \<Rightarrow> (),\n" ^
      "  None \<Rightarrow> ()\n" ^
      "}"
    val control_start =
      Position.make0 41 900 0 "" "" "struct-control-head-audit"
    val control_stop =
      Position.symbol_explode control_text control_start
    val control_source =
      Parser_Lex_Util.positioned_content_source
        control_text control_start
    val control_ast = parse control_source

    val (outer_head_raw, outer_head_pos) =
      token_position structural_text structural_start "D21AuditPair" 0
    val (alpha_raw, alpha_pos) =
      token_position structural_text structural_start "alpha" 0
    val (_, marker_a_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_a" alpha_raw
    val (beta_raw, beta_pos) =
      token_position structural_text structural_start "beta" 0
    val (nested_head_raw, nested_head_pos) =
      token_position structural_text structural_start "D21AuditPair"
        (outer_head_raw + size "D21AuditPair")
    val (gamma_raw, gamma_pos) =
      token_position structural_text structural_start "gamma" nested_head_raw
    val (_, marker_b_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_b" gamma_raw
    val (delta_raw, delta_pos) =
      token_position structural_text structural_start "delta" gamma_raw
    val (_, marker_c_pos) =
      token_position structural_text structural_start
        "d21_audit_marker_c" delta_raw
    val (nested_close_raw, nested_close_pos) =
      token_position structural_text structural_start "}" delta_raw
    val (_, outer_close_pos) =
      token_position structural_text structural_start "}"
        (nested_close_raw + 1)
    val nested_span =
      Position.range_position
        (nested_head_pos,
         Position.symbol_explode "}" nested_close_pos)

    val (_, control_match_pos) =
      token_position control_text control_start "match" 0
    val (control_group_raw, control_group_left_pos) =
      token_position control_text control_start "(" 0
    val (control_head_raw, control_head_pos) =
      token_position control_text control_start "D21AuditOne"
        control_group_raw
    val (control_label_raw, control_label_pos) =
      token_position control_text control_start "value" control_head_raw
    val (control_struct_close_raw, control_struct_close_pos) =
      token_position control_text control_start "}" control_label_raw
    val (_, control_group_right_pos) =
      token_position control_text control_start ")"
        (control_struct_close_raw + 1)
    val control_struct_span =
      Position.range_position
        (control_head_pos,
         Position.symbol_explode "}" control_struct_close_pos)
    val control_group_span =
      Position.range_position
        (control_group_left_pos,
         Position.symbol_explode ")" control_group_right_pos)

    val _ =
      (case structural_ast of
         UE_Struct
           (head,
            [SE_Field
               ("alpha", first_label_pos,
                UE_Literal (LP_ValAntiq _)),
             SE_Field
               ("beta", second_label_pos,
                nested as
                  UE_Struct
                    (nested_head,
                     [SE_Field
                        ("gamma", third_label_pos,
                         UE_Literal (LP_ValAntiq _)),
                      SE_Field
                        ("delta", fourth_label_pos,
                         UE_Literal (LP_ValAntiq _))],
                     nested_pos))],
            outer_pos) =>
           (audit_assert "outer head changed"
              (render_path head = "D21AuditPair");
            audit_assert "nested head changed"
              (render_path nested_head = "D21AuditPair");
            audit_assert "outer label order or positions changed"
              (same_range first_label_pos alpha_pos andalso
               same_range second_label_pos beta_pos);
            audit_assert "nested label order or positions changed"
              (same_range third_label_pos gamma_pos andalso
               same_range fourth_label_pos delta_pos);
            audit_assert "outer span no longer covers head through closing brace"
              (Position.offset_of outer_pos =
                 Position.offset_of outer_head_pos andalso
               Position.end_offset_of outer_pos =
                 Position.offset_of structural_stop);
            audit_assert "nested struct span changed"
              (same_range nested_pos nested_span);
            audit_assert "expression_position lost the nested struct boundary"
              (same_range (expression_position nested) nested_span))
       | _ =>
           error "struct-expression regression audit: structural AST changed")

    val _ =
      (case control_ast of
         UE_Match
           (MF_Auto,
            UE_Group
              (nested as
                 UE_Struct
                   (head,
                    [SE_Field ("value", label_pos, _)],
                    struct_pos),
               group_pos),
            _, match_pos) =>
           (audit_assert "grouped control-head struct changed"
              (render_path head = "D21AuditOne");
            audit_assert "grouped control-head label position changed"
              (same_range label_pos control_label_pos);
            audit_assert "grouped control-head struct span changed"
              (same_range struct_pos control_struct_span andalso
               same_range
                 (expression_position nested) control_struct_span);
            audit_assert "grouped control-head span changed"
              (same_range group_pos control_group_span);
            audit_assert "grouped control-head match span changed"
              (Position.offset_of match_pos =
                 Position.offset_of control_match_pos andalso
               Position.end_offset_of match_pos =
                 Position.offset_of control_stop))
       | _ =>
           error
             "struct-expression regression audit: grouped control-head AST changed")

    fun dest_funcall2 term =
      (case Term_Position.strip_positions term of
         Const (name, _) $ function $ first $ second =>
           if name = \<^const_name>\<open>funcall2\<close>
           then (function, first, second)
           else
             error
               ("struct-expression regression audit: expected funcall2, found " ^
                 quote name)
       | _ =>
           error "struct-expression regression audit: funcall2 shape changed")

    val structural_term =
      Parser_Test_Elaboration.expression ctxt structural_source
    val (outer_function, outer_first, outer_second) =
      dest_funcall2 structural_term
    val (nested_function, nested_first, nested_second) =
      dest_funcall2 outer_second
    val _ =
      audit_assert "registered wrapper head was not retained"
        (count_constant
          \<^const_name>\<open>d21_audit_first2\<close>
          outer_function = 1 andalso
         count_constant
          \<^const_name>\<open>d21_audit_first2\<close>
          nested_function = 1)
    val _ =
      audit_assert "first initializer left the first call argument"
        (count_constant
           \<^const_name>\<open>d21_audit_marker_a\<close>
           outer_first = 1 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_b\<close>
           outer_first = 0)
    val _ =
      audit_assert "nested initializer order changed"
        (count_constant
           \<^const_name>\<open>d21_audit_marker_b\<close>
           nested_first = 1 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_c\<close>
           nested_first = 0 andalso
         count_constant
           \<^const_name>\<open>d21_audit_marker_c\<close>
           nested_second = 1)
    val _ =
      List.app
        (fn marker =>
          audit_assert
            ("initializer marker " ^ quote marker ^
              " was duplicated or dropped")
            (count_constant marker structural_term = 1))
        [\<^const_name>\<open>d21_audit_marker_a\<close>,
         \<^const_name>\<open>d21_audit_marker_b\<close>,
         \<^const_name>\<open>d21_audit_marker_c\<close>]
    val _ =
      List.app
        (fn label =>
          audit_assert
            ("label " ^ quote label ^ " leaked into the HOL term")
            (count_named_atom label structural_term = 0))
        ["alpha", "beta", "gamma", "delta"]

    val canonical =
      checked
        ("D21AuditPair { first: \<llangle>d21_audit_marker_a\<rrangle>, " ^
         "second: \<llangle>d21_audit_marker_b\<rrangle> }")
    val renamed =
      checked
        ("D21AuditPair { unknown: \<llangle>d21_audit_marker_a\<rrangle>, " ^
         "unknown: \<llangle>d21_audit_marker_b\<rrangle> }")
    val _ =
      audit_assert "labels stopped erasing completely"
        (Term.aconv (canonical, renamed))

    val parity_sources =
      ["let mut slot = 1_u64; " ^
         "D21AuditOne { value: slot = 2_u64 }",
       "D21AuditOne { value: " ^
         "[\<llangle>(\<lambda>left::nat. \<lambda>right::nat. " ^
           "FunctionBody (literal (left + right)))\<rrangle>, " ^
          "|left, right| \<llangle>left + right :: nat\<rrangle>] }",
       "for _ in (D21AuditOne { value: [1, 2] }) " ^
         "{ D21AuditOne { value: () }; () }",
       "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(_) = " ^
         "(D21AuditOne { value: Some(3) }) " ^
         "{ D21AuditOne { value: () }; () }",
       "match (D21AuditOne { value: Some(3) }) " ^
         "{ Some(_) \<Rightarrow> D21AuditOne { value: 1 }, None \<Rightarrow> 0 }",
       "match_case (D21AuditOne { value: Some(3) }) " ^
         "{ Some(_) \<Rightarrow> D21AuditOne { value: 1 }, None \<Rightarrow> 0 }",
       "match_switch (D21AuditOne { value: 42 }) " ^
         "{ 42 \<Rightarrow> D21AuditOne { value: () }, _ \<Rightarrow> () }"]
    val _ =
      List.app
        (fn source =>
          audit_assert
            ("direct frontend alpha parity failed for " ^ quote source)
            (Term.aconv (checked source, frontend source)))
        parity_sources

    val captured_reports = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                (ignore
                   (Parser_Test_Elaboration.expression ctxt structural_source);
                 ignore
                   (Parser_Test_Elaboration.expression ctxt control_source))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties pos =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of pos) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of pos)
    fun has_markup markup_name pos =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties pos)
        markup
    fun has_entity_markup kind pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            has_position properties pos)
        markup
    fun has_any_entity pos =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso has_position properties pos)
        markup
    fun all_token_positions needle =
      let
        fun collect offset positions =
          if offset + size needle > size structural_text then rev positions
          else
            (case try (find_from structural_text needle) offset of
               SOME raw =>
                 let
                   val (_, position) =
                     token_position structural_text structural_start
                       needle raw
                 in collect (raw + size needle) (position :: positions) end
             | NONE => rev positions)
      in collect 0 [] end

    val _ =
      List.app
        (fn head_pos =>
          (audit_assert "struct head lost function-role notation markup"
             (has_entity_markup
               Micro_Rust_Names.notationN head_pos);
           audit_assert "struct head lost registered-call styling"
             (has_markup Markup.keyword3N head_pos)))
        [outer_head_pos, nested_head_pos]
    val _ =
      (audit_assert
         "grouped control-head struct lost function-role notation markup"
         (has_entity_markup
           Micro_Rust_Names.notationN control_head_pos);
       audit_assert
         "grouped control-head struct lost registered-call styling"
         (has_markup Markup.keyword3N control_head_pos);
       audit_assert "grouped control-head label lost free markup"
         (has_markup Markup.freeN control_label_pos);
       audit_assert "grouped control-head label lost typing markup"
         (has_markup Markup.typingN control_label_pos);
       audit_assert "grouped control-head label received entity markup"
         (not (has_any_entity control_label_pos));
       audit_assert "grouped control-head opening parenthesis lost markup"
         (has_markup Markup.delimiterN control_group_left_pos);
       audit_assert "grouped control-head closing parenthesis lost markup"
         (has_markup Markup.delimiterN control_group_right_pos))
    val _ =
      List.app
        (fn (label, pos) =>
          (audit_assert
             ("label " ^ quote label ^ " lost free markup")
             (has_markup Markup.freeN pos);
           audit_assert
             ("label " ^ quote label ^ " lost typing markup")
             (has_markup Markup.typingN pos);
           audit_assert
             ("label " ^ quote label ^ " received entity/selector markup")
             (not (has_any_entity pos));
           audit_assert
             ("label " ^ quote label ^ " received call styling")
             (not (has_markup Markup.keyword3N pos))))
        [("alpha", alpha_pos), ("beta", beta_pos),
         ("gamma", gamma_pos), ("delta", delta_pos)]
    val _ =
      List.app
        (fn spelling =>
          List.app
            (fn position =>
              audit_assert
                ("delimiter " ^ quote spelling ^ " lost markup")
                (has_markup Markup.delimiterN position))
            (all_token_positions spelling))
        ["{", "}", ":", ","]
    val (_, comment_pos) =
      token_position structural_text structural_start
        "// retained comment" 0
    val _ =
      audit_assert "line comment lost comment markup"
        (has_markup Markup.comment1N comment_pos)
    val _ =
      List.app
        (fn position =>
          audit_assert "value-antiquotation opener lost delimiter markup"
            (has_markup Markup.delimiterN position))
        (all_token_positions "\<llangle>")
    val _ =
      List.app
        (fn (marker, position) =>
          audit_assert
            ("value-antiquotation body " ^ quote marker ^
              " lost constant entity markup")
            (has_entity_markup Markup.constantN position))
        [("d21_audit_marker_a", marker_a_pos),
         ("d21_audit_marker_b", marker_b_pos),
         ("d21_audit_marker_c", marker_c_pos)]

    val valid_struct =
      "D21AuditPair { first: \<llangle>d21_audit_marker_a\<rrangle>, " ^
      "second: \<llangle>d21_audit_marker_b\<rrangle> }"
    val ordinary_follower = "if d21_audit_truth { () }"
    val ordinary_arm_follower =
      "match d21_audit_truth { _ \<Rightarrow> () }"

    fun expect_failure operation source =
      (case Exn.result operation source of
         Exn.Res _ =>
           error
             ("struct-expression regression audit: expected rejection of " ^
               quote source)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ())

    fun assert_recovered () =
      let
        val _ = ignore (checked valid_struct)
        val _ =
          (case parse_text ordinary_follower of
             UE_If
               (UE_Path path, UE_Block (UE_Unit _, _), NONE, _) =>
               audit_assert "ordinary block-followed path changed after failure"
                 (render_path path = "d21_audit_truth")
           | _ =>
               error
                 "struct-expression regression audit: ordinary block follower did not recover")
        val _ =
          (case parse_text ordinary_arm_follower of
             UE_Match (MF_Auto, UE_Path path, _, _) =>
               audit_assert "ordinary match-followed path changed after failure"
                 (render_path path = "d21_audit_truth")
           | _ =>
               error
                 "struct-expression regression audit: ordinary arm follower did not recover")
      in () end

    val _ =
      (expect_failure parse_text
         "if D21AuditOne { value: true } { () }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: $, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: 1, second: }";
       assert_recovered ())
    val _ =
      (expect_failure parse_text
         "D21AuditPair { first: \<llangle>1, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure checked
         "D21AuditPair { first: 0 = rhs, second: 2 }";
       assert_recovered ())
    val _ =
      (expect_failure checked
         ("D21AuditPair { " ^
          "f00: 0, f01: 1, f02: 2, f03: 3, f04: 4, " ^
          "f05: 5, f06: 6, f07: 7, f08: 8, f09: 9, " ^
          "f10: 10, f11: 11, f12: 12, f13: 13, f14: 14 }");
       assert_recovered ())
  in
    val _ =
      writeln
        "Struct-expression AST, lowering, parity, markup, and recovery regressions passed"
  end
\<close>


section\<open> Structural call-arity preflight audit \<close>

consts
  arity_audit_marker_00 :: nat
  arity_audit_marker_01 :: nat
  arity_audit_marker_02 :: nat
  arity_audit_marker_03 :: nat
  arity_audit_marker_04 :: nat
  arity_audit_marker_05 :: nat
  arity_audit_marker_06 :: nat
  arity_audit_marker_07 :: nat
  arity_audit_marker_08 :: nat
  arity_audit_marker_09 :: nat
  arity_audit_marker_10 :: nat
  arity_audit_marker_11 :: nat
  arity_audit_marker_12 :: nat
  arity_audit_marker_13 :: nat

definition arity_audit_backend14 ::
  \<open>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body
  \<close>
  where
    \<open>
      arity_audit_backend14 \<equiv>
        lift_fun14 (\<lambda>a b c d e f g h i j k l m n. a)
    \<close>

definition arity_audit_registered_value :: nat
  where \<open> arity_audit_registered_value = 0 \<close>

micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Call14")
micro_rust_notation (call) arity_audit_backend14 ("arity_audit_method14")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Struct14")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::Over")
micro_rust_notation (call) arity_audit_backend14 ("arity_audit_over_method")
micro_rust_notation (call) arity_audit_backend14 ("ArityAudit::StructOver")
micro_rust_notation (literal) arity_audit_registered_value ("ArityAudit::Value")

text\<open>
The shallow-term layer owns the single \<open>funcall0\<close>-through-\<open>funcall14\<close> table. Translation
preflights the AST's total runtime arity before resolving a callee, applying generic arguments,
parsing embedded HOL, reporting struct labels, or lowering a receiver, argument, or initializer.
The ordinary call constructor still checks the same private table defensively.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("structural call-arity preflight audit: " ^ message)

    fun comma arguments = space_implode ", " arguments
    fun integers first count =
      map string_of_int (first upto (first + count - 1))
    fun call head arguments =
      head ^ "(" ^ comma arguments ^ ")"
    fun method receiver head arguments =
      receiver ^ "." ^ head ^ "(" ^ comma arguments ^ ")"

    val marker_sources =
      ["arity_audit_marker_00", "arity_audit_marker_01",
       "arity_audit_marker_02", "arity_audit_marker_03",
       "arity_audit_marker_04", "arity_audit_marker_05",
       "arity_audit_marker_06", "arity_audit_marker_07",
       "arity_audit_marker_08", "arity_audit_marker_09",
       "arity_audit_marker_10", "arity_audit_marker_11",
       "arity_audit_marker_12", "arity_audit_marker_13"]
    val marker_constants =
      [\<^const_name>\<open>arity_audit_marker_00\<close>,
       \<^const_name>\<open>arity_audit_marker_01\<close>,
       \<^const_name>\<open>arity_audit_marker_02\<close>,
       \<^const_name>\<open>arity_audit_marker_03\<close>,
       \<^const_name>\<open>arity_audit_marker_04\<close>,
       \<^const_name>\<open>arity_audit_marker_05\<close>,
       \<^const_name>\<open>arity_audit_marker_06\<close>,
       \<^const_name>\<open>arity_audit_marker_07\<close>,
       \<^const_name>\<open>arity_audit_marker_08\<close>,
       \<^const_name>\<open>arity_audit_marker_09\<close>,
       \<^const_name>\<open>arity_audit_marker_10\<close>,
       \<^const_name>\<open>arity_audit_marker_11\<close>,
       \<^const_name>\<open>arity_audit_marker_12\<close>,
       \<^const_name>\<open>arity_audit_marker_13\<close>]

    fun checked elaboration_ctxt text =
      Parser_Test_Elaboration.expression elaboration_ctxt
        (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun marker_sequence term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if member (op =) marker_constants name
              then fn names => names @ [name]
              else I
          | _ => I)
        term []

    val valid_direct =
      call "ArityAudit::Call14" marker_sources
    val valid_method =
      method (hd marker_sources) "arity_audit_method14"
        (tl marker_sources)
    val valid_struct =
      "ArityAudit::Struct14 { " ^
      comma
        (map_index
          (fn (index, marker) =>
            "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
            ": " ^ marker)
          marker_sources) ^
      " }"

    fun check_supported_boundary label text =
      let
        val term = checked ctxt text
      in
        audit_assert (label ^ " selected the backend more than once")
          (count_constant
            \<^const_name>\<open>arity_audit_backend14\<close> term = 1);
        audit_assert (label ^ " changed source order or single evaluation")
          (marker_sequence term = marker_constants)
      end

    fun recovery () =
      (check_supported_boundary "direct arity-14 recovery" valid_direct;
       check_supported_boundary "method total-14 recovery" valid_method;
       check_supported_boundary "struct arity-14 recovery" valid_struct;
       ignore (checked ctxt "()"))

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("structural call-arity preflight audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun complete_position text start =
      Position.range_position
        (start, Position.symbol_explode text start)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup

    fun has_entity markup kind identity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            Properties.get properties Markup.nameN = SOME identity andalso
            has_position properties position)
        markup

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun arity_message arity position =
      "urust_expr: unsupported call arity " ^ string_of_int arity ^
      " (max 14; the frontend's surface lowering caps here)" ^
      Position.here position

    fun capture_expression elaboration_ctxt source =
      let
        val captured =
          Synchronized.var "structural_call_arity_reports" ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        Parser_Test_Elaboration.expression
                          elaboration_ctxt source) ()) ())
              ())
      in
        (result,
         fold collect_markup
           (maps YXML.parse_body (Synchronized.value captured)) [])
      end

    fun expect_rejection elaboration_ctxt serial label text arity inspect =
      let
        val start =
          Position.make0 (130 + serial) (9000 + serial * 500) 0 "" ""
            ("structural-call-arity-" ^ label ^ "-audit")
        val position = complete_position text start
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (result, markup) =
          capture_expression elaboration_ctxt source
        val body =
          (case result of
             Exn.Res term =>
               error
                 (label ^ " unexpectedly elaborated to " ^
                   Syntax.string_of_term elaboration_ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = arity_message arity position);
                   YXML.parse_body actual
                 end)
        val expected_range =
          [(Value.print_int (the (Position.offset_of position)),
            Value.print_int (the (Position.end_offset_of position)))]
        val _ =
          audit_assert (label ^ " diagnostic range changed")
            (diagnostic_ranges body = expected_range)
        val _ = inspect text start markup
        val _ = recovery ()
      in () end

    fun no_inspection _ _ _ = ()

    fun assert_no_notation label key position markup =
      (audit_assert (label ^ " resolved notation before arity rejection")
         (not
           (has_entity markup Micro_Rust_Names.notationN key position));
       audit_assert (label ^ " emitted registered-call styling before rejection")
         (not (has_markup markup Markup.keyword3N position)))

    fun inspect_direct text start markup =
      let
        val (head_offset, _) =
          token_position text start "ArityAudit::Over" 0
        val (_, head_position) =
          token_position text start "Over"
            (head_offset + size "ArityAudit::")
        val (value_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, value_position) =
          token_position text start "Value"
            (value_offset + size "ArityAudit::")
      in
        assert_no_notation "direct head" "ArityAudit::Over"
          head_position markup;
        assert_no_notation "direct argument" "ArityAudit::Value"
          value_position markup
      end

    fun inspect_method text start markup =
      let
        val (receiver_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, receiver_position) =
          token_position text start "Value"
            (receiver_offset + size "ArityAudit::")
        val (_, method_position) =
          token_position text start "arity_audit_over_method" 0
      in
        assert_no_notation "method receiver" "ArityAudit::Value"
          receiver_position markup;
        assert_no_notation "method head" "arity_audit_over_method"
          method_position markup
      end

    fun inspect_struct text start markup =
      let
        val (head_offset, _) =
          token_position text start "ArityAudit::StructOver" 0
        val (_, head_position) =
          token_position text start "StructOver"
            (head_offset + size "ArityAudit::")
        val (_, label_position) =
          token_position text start "f00" 0
        val (value_offset, _) =
          token_position text start "ArityAudit::Value" 0
        val (_, value_position) =
          token_position text start "Value"
            (value_offset + size "ArityAudit::")
      in
        assert_no_notation "struct head" "ArityAudit::StructOver"
          head_position markup;
        assert_no_notation "struct initializer" "ArityAudit::Value"
          value_position markup;
        audit_assert "struct label was semantically reported before arity rejection"
          (not (has_markup markup Markup.freeN label_position))
      end

    val fifteen = integers 0 15
    val method_fifteen = integers 1 14
    val method_sixteen = integers 1 15
    val (fixed_names, fixed_ctxt) =
      Variable.add_fixes
        ["arity_audit_fixed", "arity_audit_fixed_method"] ctxt
    val (fixed_head, fixed_method) =
      (case fixed_names of
         [head, method_name] => (head, method_name)
       | _ => error "structural call-arity preflight audit: fixed-name allocation changed")

    val direct_report_text =
      call "ArityAudit::Over"
        ("ArityAudit::Value" :: integers 1 14)
    val method_report_text =
      method "ArityAudit::Value" "arity_audit_over_method"
        method_fifteen
    val struct_report_text =
      "ArityAudit::StructOver { " ^
      comma
        ("f00: ArityAudit::Value" ::
          map
            (fn index =>
              "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
              ": " ^ string_of_int index)
            (1 upto 14)) ^
      " }"

    val _ =
      expect_rejection ctxt 0 "direct-registered-reports"
        direct_report_text 15 inspect_direct
    val _ =
      expect_rejection ctxt 1 "direct-unregistered"
        (call "arity_audit_missing_direct" fifteen) 15 no_inspection
    val _ =
      expect_rejection fixed_ctxt 2 "direct-fixed"
        (call fixed_head fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 3 "direct-shallow"
        (call "cf1" fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 4 "direct-pure"
        (call "Suc" fifteen) 15 no_inspection
    val _ =
      expect_rejection ctxt 5 "direct-antiquotation"
        (call "\<epsilon>\<open>arity_audit_missing_antiquotation\<close>" fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 6 "direct-function-literal"
        (call
          "\<llangle>arity_audit_missing_function_literal\<rrangle>\<^sub>1::<arity_audit_missing_generic>"
          fifteen)
        15 no_inspection

    val _ =
      expect_rejection ctxt 7 "method-registered-reports"
        method_report_text 15 inspect_method
    val _ =
      expect_rejection ctxt 8 "method-registered-16"
        (method "0" "arity_audit_over_method" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 9 "method-unregistered-15"
        (method "0" "arity_audit_missing_method" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 10 "method-unregistered-16"
        (method "0" "arity_audit_missing_method" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection fixed_ctxt 11 "method-fixed-15"
        (method "0" fixed_method method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection fixed_ctxt 12 "method-fixed-16"
        (method "0" fixed_method method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 13 "method-shallow-15"
        (method "0" "cf1" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 14 "method-shallow-16"
        (method "0" "cf1" method_sixteen)
        16 no_inspection
    val _ =
      expect_rejection ctxt 15 "method-pure-15"
        (method "0" "Suc" method_fifteen)
        15 no_inspection
    val _ =
      expect_rejection ctxt 16 "method-pure-16"
        (method "0" "Suc" method_sixteen)
        16 no_inspection

    val _ =
      expect_rejection ctxt 17 "struct-reports"
        struct_report_text 15 inspect_struct
    val _ =
      expect_rejection ctxt 18 "callee-and-argument-precedence"
        (call "Suc"
          ("unknown_arity_argument!()" :: integers 1 14))
        15 no_inspection
    val _ =
      expect_rejection ctxt 19 "receiver-and-method-precedence"
        (method "unknown_arity_receiver!()" "arity_audit_missing_method"
          ("unknown_arity_argument!()" :: integers 2 13))
        15 no_inspection
    val _ =
      expect_rejection ctxt 20 "struct-head-and-initializer-precedence"
        ("UnknownArityStruct { " ^
         comma
           ("f00: unknown_arity_initializer!()" ::
             map
               (fn index =>
                 "f" ^ StringCvt.padLeft #"0" 2 (string_of_int index) ^
                 ": " ^ string_of_int index)
               (1 upto 14)) ^
         " }")
        15 no_inspection

    val _ =
      URust_Shallow_Terms.check_function_call_arity Position.none 14
    val _ =
      (case Exn.result
          (fn () =>
            URust_Shallow_Terms.function_call Position.none HOLogic.unit
              (replicate 15 HOLogic.unit)) () of
         Exn.Res _ =>
           error "structural call-arity preflight audit: defensive function_call accepted arity 15"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "defensive function_call diagnostic changed"
               (Runtime.exn_message exn =
                 arity_message 15 Position.none))
  in
    val _ =
      writeln
        "Structural call-arity preflight, precedence, reports, ranges, recovery, order, and single-evaluation regressions passed"
  end
\<close>


section\<open> Method resolution boundary audit \<close>

definition method_audit_pure :: \<open>nat option \<Rightarrow> bool\<close>
  where \<open> method_audit_pure \<equiv> Option.is_none \<close>

definition method_audit_registered ::
  \<open>nat option \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where \<open> method_audit_registered \<equiv> lift_fun1 Option.is_none \<close>

definition method_audit_shallow ::
  \<open>nat option \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where \<open> method_audit_shallow \<equiv> lift_fun1 Option.is_none \<close>

micro_rust_notation (literal) method_audit_pure ("is_none")
micro_rust_notation (call) method_audit_registered ("method_registered")

text\<open>
Method parsing retains the receiver, method identifier, and call span before resolution. Method
resolution rejects an unresolved call spelling at the exact method range; a literal-only registration
does not alter that call-role boundary. The general positioned call-head constraint also rejects a
known pure HOL constant whose terminal result cannot be a shallow \<open>function_body\<close>. Registered,
ordinary shallow-HOL, direct-call, and unit expressions then elaborate normally.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("method resolution boundary audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("method resolution boundary audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start,
            Position.symbol_explode needle token_start))
      end

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "method resolution boundary audit: empty parse")

    val unregistered_ctxt =
      ctxt
      |> Context.Proof
      |> Micro_Rust_Names.Data.map
          (Symtab.delete_safe
            (Micro_Rust_Names.mk_key
              Micro_Rust_Names.NFunction "is_none"))
      |> Context.proof_of
    val _ =
      audit_assert "literal-only fixture lost its literal registration"
        (not (null
          (Micro_Rust_Names.lookups unregistered_ctxt
            Micro_Rust_Names.NLiteral "is_none")))
    val _ =
      audit_assert "isolated fixture retained a call registration"
        (null
          (Micro_Rust_Names.lookups unregistered_ctxt
            Micro_Rust_Names.NFunction "is_none"))

    val text =
      "assert!(!o.is_none())"
    val start =
      Position.make0 17 200 0 "" "" "method-resolution-boundary-audit"
    val source =
      Parser_Lex_Util.positioned_content_source text start
    val (call_offset, expected_call) =
      token_position text start "o.is_none()" 0
    val (_, expected_method) =
      token_position text start "is_none"
        (call_offset + size "o.")
    val ast = parse source
    val method_position =
      (case ast of
         UE_Macro
           (macro_path, _, MP_Arguments
             [UE_Unary
               (U_Not,
                UE_Call
                  (UC_Method
                    (UE_Path receiver_path,
                     Path_Segment
                       ("is_none", method_pos, NONE)),
                   [], call_pos),
                _)],
            _) =>
           (audit_assert "assert macro wrapper changed"
              (render_path macro_path = "assert");
            audit_assert "method receiver changed"
              (render_path receiver_path = "o");
            audit_assert "method identifier range moved"
              (same_range method_pos expected_method);
            audit_assert "method call span moved"
              (same_range call_pos expected_call);
            method_pos)
       | _ => error "method resolution boundary audit: method AST changed")

    val captured_reports =
      Synchronized.var "method_resolution_boundary_reports" ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    fun capture_elaboration elaboration_ctxt elaboration_source =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                Exn.result
                  (fn () =>
                    Parser_Test_Elaboration.expression
                      elaboration_ctxt elaboration_source) ()) ())
          ())

    val unregistered_result =
      capture_elaboration unregistered_ctxt source
    val diagnostic_markup =
      (case unregistered_result of
         Exn.Res term =>
           error
             ("method resolution boundary audit: unresolved method unexpectedly " ^
              "elaborated to " ^ Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
             in
               audit_assert "unresolved method diagnostic changed"
                 (String.isSubstring "Type unification failed" message);
               body
             end)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val diagnostic_markup =
      fold collect_markup diagnostic_markup []
    val semantic_markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_diagnostic_position_in markup position =
      exists (fn (_, properties) => has_position properties position)
        markup
    fun has_markup_in markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup
    fun has_entity_in markup kind identity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            Properties.get properties Markup.nameN = SOME identity andalso
            has_position properties position)
        markup
    fun urust_entity_id_in markup property position =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               ("method resolution boundary audit: receiver entity markup changed" ^
                 Position.here position))
      end

    val _ =
      audit_assert "method-resolution diagnostic lost the identifier range"
        (has_diagnostic_position_in diagnostic_markup method_position)
    val _ =
      audit_assert "unregistered method lost ordinary free-name styling"
        (has_markup_in semantic_markup Markup.freeN method_position)
    val _ =
      audit_assert "unregistered method acquired constant identity markup"
        (not
          (has_entity_in semantic_markup Markup.constantN
            \<^const_name>\<open>Option.is_none\<close> method_position))
    val _ =
      audit_assert "unregistered method acquired constant styling"
        (not (has_markup_in semantic_markup Markup.constN method_position))
    val _ =
      audit_assert "unregistered fallback lost typing markup"
        (has_markup_in semantic_markup Markup.typingN method_position)
    val _ =
      audit_assert "literal-only registration leaked call-notation markup"
        (not
          (has_entity_in semantic_markup
            Micro_Rust_Names.notationN "is_none" method_position))
    val _ =
      audit_assert "literal-only registration leaked registered-call styling"
        (not
          (has_markup_in semantic_markup Markup.keyword3N method_position))

    val pure_text =
      "let o = \<llangle>None :: nat option\<rrangle>; " ^
      "o.method_audit_pure()"
    val pure_start =
      Position.make0 19 250 0 "" "" "method-pure-hol-boundary-audit"
    val pure_source =
      Parser_Lex_Util.positioned_content_source pure_text pure_start
    val (_, pure_method_position) =
      token_position pure_text pure_start "method_audit_pure" 0
    val pure_result =
      capture_elaboration ctxt pure_source
    val pure_diagnostic_markup =
      (case pure_result of
         Exn.Res term =>
           error
             ("method resolution boundary audit: known pure HOL method " ^
              "unexpectedly elaborated to " ^ Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val body = YXML.parse_body (Runtime.exn_message exn)
               val message = XML.content_of body
             in
               audit_assert "known pure HOL method diagnostic changed"
                 (String.isSubstring
                   "whose result is not a shallow function_body" message);
               body
             end)
      |> (fn body => fold collect_markup body [])
    val pure_semantic_markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    val _ =
      audit_assert "pure HOL diagnostic lost the method identifier range"
        (has_diagnostic_position_in
          pure_diagnostic_markup pure_method_position)
    val _ =
      audit_assert "pure HOL method lost constant identity markup"
        (has_entity_in pure_semantic_markup Markup.constantN
          \<^const_name>\<open>method_audit_pure\<close> pure_method_position)
    val _ =
      audit_assert "pure HOL method lost constant styling"
        (has_markup_in pure_semantic_markup
          Markup.constN pure_method_position)
    val _ =
      audit_assert "pure HOL method lost typing markup"
        (has_markup_in pure_semantic_markup
          Markup.typingN pure_method_position)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    val registered_text =
      "let o = \<llangle>None :: nat option\<rrangle>; " ^
      "assert!(!o.method_registered())"
    val registered_start =
      Position.make0 23 300 0 "" "" "method-registered-markup-audit"
    val registered_source =
      Parser_Lex_Util.positioned_content_source
        registered_text registered_start
    val (_, registered_method_position) =
      token_position registered_text registered_start
        "method_registered" 0
    val (_, registered_receiver_definition) =
      token_position registered_text registered_start "o" 0
    val (registered_call_offset, _) =
      token_position registered_text registered_start
        "o.method_registered()" 0
    val (_, registered_receiver_reference) =
      token_position registered_text registered_start
        "o" registered_call_offset
    val registered =
      (case capture_elaboration ctxt registered_source of
         Exn.Res term => term
       | Exn.Exn exn => Exn.reraise exn)
    val _ =
      audit_assert "registered lifted backend was not selected exactly once"
        (count_constant
          \<^const_name>\<open>method_audit_registered\<close> registered = 1)
    val _ =
      audit_assert "registered method duplicated or dropped its receiver"
        (count_constant \<^const_name>\<open>Option.None\<close> registered = 1)
    val semantic_markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured_reports)) []
    val _ =
      audit_assert "registered method lost notation entity markup"
        (has_entity_in semantic_markup Micro_Rust_Names.notationN
          "method_registered" registered_method_position)
    val _ =
      audit_assert "registered method lost registered-call styling"
        (has_markup_in semantic_markup
          Markup.keyword3N registered_method_position)
    val _ =
      audit_assert "registered method lost typing markup"
        (has_markup_in semantic_markup
          Markup.typingN registered_method_position)
    val _ =
      audit_assert "receiver definition/reference navigation changed"
        (urust_entity_id_in semantic_markup
            Markup.defN registered_receiver_definition =
          urust_entity_id_in semantic_markup
            Markup.refN registered_receiver_reference)

    val ordinary =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          ("let o = \<llangle>None :: nat option\<rrangle>; " ^
           "o.method_audit_shallow()"))
    val _ =
      audit_assert "ordinary shallow HOL fallback was not selected once"
        (count_constant \<^const_name>\<open>method_audit_shallow\<close> ordinary = 1)
    val _ =
      audit_assert "ordinary shallow method duplicated or dropped its receiver"
        (count_constant \<^const_name>\<open>Option.None\<close> ordinary = 1)

    val direct_registered =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          ("let o = \<llangle>None :: nat option\<rrangle>; " ^
           "method_registered(o)"))
    val _ =
      audit_assert "direct registered call selected a different backend"
        (count_constant
          \<^const_name>\<open>method_audit_registered\<close>
          direct_registered = 1)
    val _ =
      audit_assert "direct registered call duplicated or dropped its argument"
        (count_constant \<^const_name>\<open>Option.None\<close>
          direct_registered = 1)

    val _ =
      (case Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.text_source "()") of
         Const (\<^const_name>\<open>literal\<close>, _) $
             Const (\<^const_name>\<open>Product_Type.Unity\<close>, _) => ()
       | term =>
           error
             ("method resolution boundary audit: elaboration recovery failed: " ^
               Syntax.string_of_term ctxt term))
  in
    val _ =
      writeln
        "Method AST, exact diagnostic, semantic markup, resolution, and recovery regressions passed"
  end
\<close>


definition integration_registered_value_audit :: nat
  where \<open> integration_registered_value_audit = 42 \<close>

micro_rust_notation (literal)
  integration_registered_value_audit
  ("IntegrationAudit::Value")


section\<open> Concealed registered-constructor lookup boundary \<close>

experiment
begin

datatype concealed_constructor_audit =
    ConcealedRegistered
  | ConcealedUnregistered

micro_rust_notation (literal)
  concealed_constructor_audit.ConcealedRegistered
  ("ConcealedAudit::Registered")
micro_rust_notation (literal)
  concealed_constructor_audit.ConcealedUnregistered
  ("ConcealedAudit::Unregistered")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("concealed constructor lookup audit: " ^ message)

    fun parse source =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source source) of
         SOME expression => expression
       | NONE => error "concealed constructor lookup audit: empty parse")

    fun path_of source =
      (case parse source of
         UE_Path path => path
       | _ => error ("expected path " ^ quote source))

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked source =
      checked_source (Parser_Lex_Util.text_source source)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex = Const (name, _), ...} => name
         | _ =>
             error
               ("concealed constructor lookup audit: missing case metadata for " ^
                 quote type_name))
      end

    val theory = Proof_Context.theory_of ctxt
    val registered_name =
      \<^const_name>\<open>ConcealedRegistered\<close>
    val unregistered_name =
      \<^const_name>\<open>ConcealedUnregistered\<close>
    val concealed_case_name =
      case_constant_name \<^term>\<open>ConcealedRegistered\<close>
    val _ =
      audit_assert "fixture constructor unexpectedly entered Code.is_constr"
        (not (Code.is_constr theory registered_name) andalso
         not (Code.is_constr theory unregistered_name))

    val resolver =
      URust_Resolution.make_constructor_resolver ctxt Position.none
    val registered_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "ConcealedAudit::Registered"))
    val _ =
      (case URust_Resolution.classify_registered_literal ctxt resolver
          (path_of "ConcealedAudit::Registered") of
         URust_Resolution.Registered_Constructor_Literal => ()
       | _ =>
           error
             "concealed constructor lookup audit: registered concealed literal was not classified as a constructor")
    val _ =
      audit_assert "registered concealed identity was not recovered"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term registered_info,
           \<^term>\<open>ConcealedRegistered\<close>))
    val _ =
      audit_assert "registered concealed constructor leaked into basename lookup"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "ConcealedRegistered")))
    val _ =
      audit_assert "second concealed constructor leaked into basename lookup"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "ConcealedUnregistered")))

    val registered_match =
      checked
        ("match_case \<llangle>ConcealedRegistered\<rrangle> { " ^
         "ConcealedAudit::Registered \<Rightarrow> 0, " ^
         "ConcealedAudit::Unregistered \<Rightarrow> 1 }")
    val _ =
      audit_assert "registered concealed match lost its authentic case combinator"
        (count_constant concealed_case_name registered_match = 1)
    val _ =
      audit_assert "registered concealed exhaustive match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          registered_match = 0)

    val unregistered_binder =
      checked
        ("match_case \<llangle>ConcealedUnregistered\<rrangle> { " ^
         "ConcealedUnregistered \<Rightarrow> 0 }")
    val _ =
      audit_assert "unregistered concealed basename stopped being a binder"
        (count_constant unregistered_name unregistered_binder = 1)

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    val concealed_mixed_text =
      "match \<llangle>ConcealedRegistered\<rrangle> { " ^
      "0 \<Rightarrow> (), ConcealedAudit::Registered \<Rightarrow> () }"
    val concealed_mixed_start =
      Position.make0 64 900 0 "" ""
        "concealed-constructor-mixed-match-audit"
    val concealed_mixed_position =
      Position.range_position
        (concealed_mixed_start,
         Position.symbol_explode concealed_mixed_text concealed_mixed_start)
    val concealed_mixed_source =
      Parser_Lex_Util.positioned_content_source
        concealed_mixed_text concealed_mixed_start
    val concealed_mixed_expected =
      "urust_expr: mixed numeral and constructor patterns in bare `match`" ^
      Position.here concealed_mixed_position
    val concealed_mixed_range =
      (Value.print_int
        (the (Position.offset_of concealed_mixed_position)),
       Value.print_int
        (the (Position.end_offset_of concealed_mixed_position)))
    val concealed_mixed_body =
      (case Exn.result (fn () => checked_source concealed_mixed_source) () of
         Exn.Res term =>
           error
             ("concealed constructor lookup audit: mixed numeral match " ^
              "unexpectedly elaborated to " ^
              Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val actual = Runtime.exn_message exn
             in
               audit_assert
                 "concealed constructor mixed-match diagnostic changed"
                 (actual = concealed_mixed_expected);
               YXML.parse_body actual
             end)
    val _ =
      audit_assert
        "concealed constructor mixed-match range changed"
        (diagnostic_ranges concealed_mixed_body =
          [concealed_mixed_range])

    val recovered_switch =
      checked
        ("match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, " ^
         "_ \<Rightarrow> 2 }")
    val recovered_case =
      checked
        ("match_case \<llangle>ConcealedRegistered\<rrangle> { " ^
         "ConcealedAudit::Registered \<Rightarrow> 0, " ^
         "ConcealedAudit::Unregistered \<Rightarrow> 1 }")
    val recovered_unit = checked "()"
    val _ =
      audit_assert "concealed rejection lost switch recovery"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          recovered_switch = 1)
    val _ =
      audit_assert "concealed rejection lost constructor recovery"
        (count_constant concealed_case_name recovered_case = 1)
    val _ =
      audit_assert "concealed rejection lost unit recovery"
        (count_constant \<^const_name>\<open>Product_Type.Unity\<close>
          recovered_unit = 1)
  in
    val _ =
      writeln
        "Concealed registered identity, mixed-match rejection, recovery, and filtered unregistered lookup regressions passed"
  end
\<close>

end


section\<open> Registered constructor identity audit \<close>

consts
  registered_constructor_scrutinee :: registered_constructor_fixture
  registered_constructor_guard_marker :: bool
  registered_constructor_first_marker :: nat
  registered_constructor_second_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("registered constructor identity audit: " ^ message)

    fun checked source =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source source)

    fun parse source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "empty parse")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun constant_name term =
      (case Term.head_of term of
         Const (name, _) => name
       | _ => error "expected constant")

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex, ...} => constant_name casex
         | NONE =>
             error
               ("registered constructor identity audit: missing case metadata for " ^
                 quote type_name))
      end

    val nullary_name =
      constant_name \<^term>\<open>RegisteredNullary\<close>
    val unary_name =
      constant_name \<^term>\<open>RegisteredUnary\<close>
    val other_name =
      constant_name \<^term>\<open>RegisteredOther\<close>
    val phantom_a_name =
      constant_name
        \<^term>\<open>RegisteredPhantomA :: nat registered_phantom\<close>
    val phantom_b_name =
      constant_name
        \<^term>\<open>RegisteredPhantomB :: nat registered_phantom\<close>
    val negative_nullary_name =
      constant_name \<^term>\<open>NegativeRegisteredNullary\<close>
    val negative_other_name =
      constant_name \<^term>\<open>NegativeRegisteredOther\<close>
    val negative_phantom_name =
      constant_name
        \<^term>\<open>
          NegativeRegisteredPhantom ::
            nat negative_registered_phantom
        \<close>
    val registered_case_name =
      case_constant_name \<^term>\<open>RegisteredNullary\<close>
    val negative_case_name =
      case_constant_name \<^term>\<open>NegativeRegisteredNullary\<close>
    val negative_phantom_case_name =
      case_constant_name
        \<^term>\<open>
          NegativeRegisteredPhantom ::
            nat negative_registered_phantom
        \<close>

    val exhaustive =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Nullary \<Rightarrow> \<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "Registered::Unary(value) \<Rightarrow> value, " ^
         "Registered::Other \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val partial =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Unary(value) \<Rightarrow> value }")
    val guarded =
      checked
        ("match_case \<llangle>registered_constructor_scrutinee\<rrangle> { " ^
         "Registered::Unary(value) if " ^
         "\<llangle>registered_constructor_guard_marker\<rrangle> \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val nonconstructor =
      checked
        ("match_case IntegrationAudit::Value { IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val applied_nonconstructor =
      checked
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         "NegativeRegistered::Applied \<Rightarrow> " ^
         "\<llangle>registered_constructor_first_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>registered_constructor_second_marker\<rrangle> }")
    val duplicate_constructor =
      checked
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         "NegativeRegistered::Duplicate \<Rightarrow> 0, " ^
         "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
         "NegativeRegistered::Other \<Rightarrow> 1 }")
    val duplicate_phantom =
      checked
        ("match_case " ^
         "\<llangle>NegativeRegisteredPhantom :: " ^
         "nat negative_registered_phantom\<rrangle> { " ^
         "NegativeRegistered::Phantom \<Rightarrow> 0 }")

    val _ =
      audit_assert "exhaustive match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          exhaustive = 1)
    val _ =
      audit_assert "partial match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          partial = 1)
    val _ =
      audit_assert "guarded match duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>registered_constructor_scrutinee\<close>
          guarded = 1)
    val _ =
      audit_assert "exhaustive match lost its authentic case combinator"
        (count_constant registered_case_name exhaustive = 1)
    val _ =
      audit_assert "exhaustive constructor match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close> exhaustive = 0)
    val _ =
      audit_assert "exhaustive constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> exhaustive = 0)
    val _ =
      audit_assert "exhaustive constructor match used generated conditional"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close> exhaustive = 0)
    val _ =
      audit_assert "partial constructor match lost its case combinator"
        (count_constant registered_case_name partial = 1)
    val _ =
      audit_assert "partial constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> partial = 0)
    val _ =
      audit_assert "partial constructor match lost its unmatched fallback"
        (count_constant \<^const_name>\<open>undefined\<close> partial > 0)
    val _ =
      audit_assert "guard marker was duplicated or dropped"
        (count_constant
          \<^const_name>\<open>registered_constructor_guard_marker\<close>
          guarded = 1)
    val _ =
      audit_assert "guarded constructor match lost its authentic case combinator"
        (count_constant registered_case_name guarded = 1)
    val _ =
      audit_assert "guarded constructor match used generated equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> guarded = 0)
    val _ =
      audit_assert "guarded match with wildcard fallback retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close> guarded = 0)
    val _ =
      audit_assert "guarded false fall-through lost the next source arm"
        (count_constant
          \<^const_name>\<open>registered_constructor_second_marker\<close>
          guarded > 0)
    val _ =
      audit_assert "registered nonconstructor value-key count changed"
        (count_constant \<^const_name>\<open>integration_registered_value_audit\<close>
          nonconstructor = 2)
    val _ =
      audit_assert "registered nonconstructor lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          nonconstructor > 0)
    val _ =
      audit_assert "registered nonconstructor lost conditional lowering"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close>
          nonconstructor > 0)
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("registered nonconstructor acquired constructor classification " ^
              quote name)
            (count_constant name nonconstructor = 0))
        [nullary_name, unary_name, other_name]
    val _ =
      audit_assert "constructor-headed registered application lost its two values"
        (count_constant
          \<^const_name>\<open>NegativeRegisteredUnary\<close>
          applied_nonconstructor = 2)
    val _ =
      audit_assert "constructor-headed registered application lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          applied_nonconstructor > 0)
    val _ =
      audit_assert "constructor-headed registered application lost conditional lowering"
        (count_constant
          \<^const_name>\<open>two_armed_conditional\<close>
          applied_nonconstructor > 0)
    val _ =
      audit_assert "duplicate same-constructor registrations became ambiguous"
        (count_constant negative_case_name duplicate_constructor = 1)
    val _ =
      audit_assert "phantom type-instantiated registrations became ambiguous"
        (count_constant negative_phantom_case_name duplicate_phantom = 1)

    fun path_of source =
      (case parse (Parser_Lex_Util.text_source source) of
         UE_Path path => path
       | _ => error ("expected path " ^ quote source))

    val resolver =
      URust_Resolution.make_constructor_resolver
        ctxt Position.none
    val unary_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "Registered::Unary"))
    val phantom_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "RegisteredPhantom::A"))
    val duplicate_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "NegativeRegistered::Duplicate"))
    val duplicate_phantom_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "NegativeRegistered::Phantom"))
    val _ =
      audit_assert "registered nonconstructor became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "IntegrationAudit::Value")))
    val _ =
      audit_assert "constructor-equal definition became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "NegativeRegistered::Value")))
    val _ =
      audit_assert "constructor-headed application became a constructor"
        (is_none
          (URust_Resolution.resolve_constructor ctxt resolver
            (path_of "NegativeRegistered::Applied")))
    val _ =
      audit_assert "registered unary did not return catalogue identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term unary_info,
           \<^term>\<open>RegisteredUnary\<close>))
    val _ =
      (case URust_Resolution.constructor_family unary_info of
         SOME (_, members) =>
           audit_assert "registered constructor family is incomplete"
             (sort_strings (map constant_name members) =
              sort_strings [nullary_name, unary_name, other_name])
       | NONE => error "registered constructor lost family metadata")
    val _ =
      audit_assert "polymorphic phantom registration lost constructor identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term phantom_info,
           \<^term>\<open>RegisteredPhantomA :: bool registered_phantom\<close>))
    val _ =
      (case URust_Resolution.constructor_family phantom_info of
         SOME (_, members) =>
           audit_assert "phantom constructor family is incomplete"
             (sort_strings (map constant_name members) =
              sort_strings [phantom_a_name, phantom_b_name])
       | NONE => error "phantom constructor lost family metadata")
    val _ =
      audit_assert "duplicate identical registrations lost constructor identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term duplicate_info,
           \<^term>\<open>NegativeRegisteredNullary\<close>))
    val _ =
      audit_assert "phantom registrations did not deduplicate by untyped identity"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term duplicate_phantom_info,
           \<^term>\<open>
             NegativeRegisteredPhantom ::
               bool negative_registered_phantom
           \<close>))

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    val markup_text =
      "match_case \<llangle>RegisteredUnary 1\<rrangle> { " ^
      "Registered::Unary(value) \<Rightarrow> (), _ \<Rightarrow> () }"
    val markup_start =
      Position.make0 29 700 0 "" ""
        "registered-constructor-markup-audit"
    val markup_source =
      Parser_Lex_Util.positioned_content_source
        markup_text markup_start
    val (path_raw, expected_path) =
      token_position markup_text markup_start
        "Registered::Unary" 0
    val (_, expected_qualifier) =
      token_position markup_text markup_start
        "Registered" path_raw
    val (_, expected_terminal) =
      token_position markup_text markup_start
        "Unary" (path_raw + size "Registered::")
    val pattern_path =
      (case parse markup_source of
         UE_Match
           (_, _, UR_Arm (P_Constr (path, [_]), NONE, _) :: _, _) =>
           path
       | _ => error "registered constructor pattern AST changed")
    val (_, terminal_position) =
      segment_identifier (final_segment pattern_path)
    val _ =
      audit_assert "registered constructor path span changed"
        (same_range (path_position pattern_path) expected_path)
    val _ =
      audit_assert "registered constructor terminal range changed"
        (same_range terminal_position expected_terminal)

    val captured_reports =
      Synchronized.var "registered_constructor_reports"
        ([]: string list)
    fun capture_reports chunks =
      Synchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression
                    ctxt markup_source)) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body
          (Synchronized.value captured_reports)) []
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso
            has_position properties position)
        markup
    fun has_entity kind identity position =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME kind andalso
            Properties.get properties Markup.nameN = SOME identity andalso
            has_position properties position)
        markup

    val _ =
      audit_assert "constructor qualifier lost path/free markup"
        (has_markup Markup.freeN expected_qualifier)
    val _ =
      audit_assert "constructor terminal lost authentic constant markup"
        (has_entity Markup.constantN unary_name expected_terminal)
    val _ =
      audit_assert "constructor terminal was reported as a free binder"
        (not (has_markup Markup.freeN expected_terminal))
    val _ =
      audit_assert "constructor terminal retained notation dispatch markup"
        (not
          (has_entity Micro_Rust_Names.notationN
            "Registered::Unary" expected_terminal))
    val _ =
      audit_assert "constructor terminal retained registered-literal styling"
        (not (has_markup Markup.keyword3N expected_terminal))

    fun recovery_checks () =
      let
        val constructor_recovery =
          checked
            ("match_case \<llangle>NegativeRegisteredUnary 3\<rrangle> { " ^
             "NegativeRegistered::Nullary \<Rightarrow> 0, " ^
             "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
             "NegativeRegistered::Other \<Rightarrow> 1 }")
        val nonconstructor_recovery =
          checked
            ("match_case \<llangle>negative_registered_nonconstructor\<rrangle> { " ^
             "NegativeRegistered::Value \<Rightarrow> " ^
             "NegativeRegisteredNullary, " ^
             "_ \<Rightarrow> NegativeRegisteredOther }")
      in
        audit_assert "constructor recovery lost authentic identity"
          (count_constant
            \<^const_name>\<open>NegativeRegisteredUnary\<close>
            constructor_recovery > 0);
        audit_assert "nonconstructor recovery lost equality lowering"
          (count_constant \<^const_name>\<open>urust_eq\<close>
            nonconstructor_recovery > 0)
      end

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun expect_exact_rejection serial label text path terminal expected =
      let
        val start =
          Position.make0 (40 + serial) (900 + serial * 200) 0 "" ""
            ("registered-constructor-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (path_raw, _) =
          token_position text start path 0
        val terminal_raw =
          path_raw + size path - size terminal
        val (_, expected_position) =
          token_position text start terminal terminal_raw
        val expected_message =
          expected ^ Position.here expected_position
        val expected_range =
          (Value.print_int (the (Position.offset_of expected_position)),
           Value.print_int (the (Position.end_offset_of expected_position)))
        val body =
          (case Exn.result
              (fn () =>
                Parser_Test_Elaboration.expression ctxt source) () of
             Exn.Res term =>
               error
                 ("registered constructor identity audit: " ^ label ^
                  " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = expected_message);
                   YXML.parse_body actual
                 end)
        val _ =
          audit_assert (label ^ " YXML offset/end_offset changed")
            (diagnostic_ranges body = [expected_range])
        val _ = recovery_checks ()
      in () end

    val unary_path = "NegativeRegistered::Unary"
    val value_path = "NegativeRegistered::Value"
    val ambiguous_path = "NegativeRegistered::Ambiguous"
    val applied_path = "NegativeRegistered::Applied"
    val _ =
      expect_exact_rejection 0 "zero-arity"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         unary_path ^ " \<Rightarrow> 0, _ \<Rightarrow> 1 }")
        unary_path "Unary"
        ("urust_expr: constructor " ^ quote "Unary" ^
         " expects 1 pattern argument(s), but got 0")
    val _ =
      expect_exact_rejection 1 "excess-arity"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         unary_path ^ "(left, right) \<Rightarrow> left, _ \<Rightarrow> 0 }")
        unary_path "Unary"
        ("urust_expr: constructor " ^ quote unary_path ^
         " expects 1 pattern argument(s), but got 2")
    val _ =
      expect_exact_rejection 2 "nonconstructor-application"
        ("match_case \<llangle>negative_registered_nonconstructor\<rrangle> { " ^
         value_path ^ "(value) \<Rightarrow> value, _ \<Rightarrow> " ^
         "NegativeRegisteredNullary }")
        value_path "Value"
        ("urust_expr: `" ^ value_path ^ "` is not a known constructor")
    val _ =
      expect_exact_rejection 3 "distinct-constructor-ambiguity"
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         ambiguous_path ^ " \<Rightarrow> 0, _ \<Rightarrow> 1 }")
        ambiguous_path "Ambiguous"
        ("urust_expr: constructor pattern " ^ quote ambiguous_path ^
         " is ambiguous; candidates: " ^
         space_implode ", "
           (sort_strings [negative_nullary_name, negative_other_name]))
    val _ =
      expect_exact_rejection 4 "constructor-headed-application"
        ("match_case \<llangle>NegativeRegisteredUnary 0\<rrangle> { " ^
         applied_path ^ "(value) \<Rightarrow> value, _ \<Rightarrow> 0 }")
        applied_path "Applied"
        ("urust_expr: `" ^ applied_path ^ "` is not a known constructor")
  in
    val _ =
      writeln
        "Registered constructor identity, diagnostics, recovery, lowering, range, markup, and single-evaluation regressions passed"
  end
\<close>


section\<open> Contextual bare-match classification audit \<close>

consts
  mixed_match_scrutinee_marker :: nat
  mixed_match_first_body_marker :: nat
  mixed_match_second_body_marker :: nat
  mixed_match_fallback_marker :: nat

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("contextual bare-match classification audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE =>
           error "contextual bare-match classification audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked text =
      checked_source (Parser_Lex_Util.text_source text)

    fun path_of_source source =
      (case parse_source source of
         UE_Path path => path
       | _ => error "contextual bare-match classification audit: expected path")

    fun path_of text =
      path_of_source (Parser_Lex_Util.text_source text)

    fun class_matches expected actual =
      (case (expected, actual) of
         (URust_Resolution.Unregistered_Literal,
          URust_Resolution.Unregistered_Literal) => true
       | (URust_Resolution.Registered_Value_Literal,
          URust_Resolution.Registered_Value_Literal) => true
       | (URust_Resolution.Registered_Constructor_Literal,
          URust_Resolution.Registered_Constructor_Literal) => true
       | _ => false)

    fun class_name URust_Resolution.Unregistered_Literal = "unregistered"
      | class_name URust_Resolution.Registered_Value_Literal = "value"
      | class_name URust_Resolution.Registered_Constructor_Literal =
          "constructor"

    fun expect_class label expected path =
      let
        val resolver =
          URust_Resolution.make_constructor_resolver
            ctxt (path_position path)
        val actual =
          URust_Resolution.classify_registered_literal
            ctxt resolver path
      in
        if class_matches expected actual
        then ()
        else
          error
            ("contextual bare-match classification audit: " ^ label ^
              " classification changed from " ^ class_name expected ^
              " to " ^ class_name actual)
      end

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun expect_report_free_class serial label expected text =
      let
        val start =
          Position.make0 (96 + serial) (33000 + serial * 500) 0 "" ""
            ("contextual-match-" ^ label ^ "-classification-audit")
        val path =
          path_of_source
            (Parser_Lex_Util.positioned_content_source text start)
        val resolver =
          URust_Resolution.make_constructor_resolver
            ctxt (path_position path)
        val captured =
          Synchronized.var
            ("contextual_match_" ^ label ^ "_classification_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val actual =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    URust_Resolution.classify_registered_literal
                      ctxt resolver path) ())
              ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
        val segment_positions =
          map (#2 o segment_identifier) (path_segments path)
        val reported_at_path =
          exists
            (fn (_, properties) =>
              exists (has_position properties) segment_positions)
            markup
      in
        audit_assert (label ^ " classification changed")
          (class_matches expected actual);
        audit_assert (label ^ " classification emitted path reports")
          (not reported_at_path)
      end

    val _ =
      expect_class "qualified registered value"
        URust_Resolution.Registered_Value_Literal
        (path_of "IntegrationAudit::Value")
    val _ =
      expect_class "single-segment registered value"
        URust_Resolution.Registered_Value_Literal
        (path_of "registered_seven")
    val _ =
      expect_report_free_class 0 "merged constructor/value exact key"
        URust_Resolution.Registered_Constructor_Literal
        "Color::Red"
    val _ =
      expect_class "registered constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "Registered::Nullary")
    val _ =
      expect_class "registered phantom constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "RegisteredPhantom::A")
    val _ =
      expect_class "duplicate registered constructor"
        URust_Resolution.Registered_Constructor_Literal
        (path_of "NegativeRegistered::Duplicate")
    val _ =
      expect_report_free_class 1 "constructor-wins exact key"
        URust_Resolution.Registered_Constructor_Literal
        "NegativeRegistered::ConstructorWins"
    val _ =
      expect_report_free_class 2 "two-constructor exact key"
        URust_Resolution.Registered_Constructor_Literal
        "NegativeRegistered::Ambiguous"
    val _ =
      expect_class "constructor-equal definition"
        URust_Resolution.Registered_Value_Literal
        (path_of "NegativeRegistered::Value")
    val _ =
      expect_class "constructor-headed application"
        URust_Resolution.Registered_Value_Literal
        (path_of "NegativeRegistered::Applied")
    val _ =
      expect_class "unregistered qualified path"
        URust_Resolution.Unregistered_Literal
        (path_of "Unregistered::Value")

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun token_position text start needle offset =
      let
        val raw = find_from text needle offset
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        (raw,
         Position.range_position
           (token_start, Position.symbol_explode needle token_start))
      end

    fun same_range left right =
      Position.offset_of left = Position.offset_of right andalso
      Position.end_offset_of left = Position.end_offset_of right

    val ast_text =
      "match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, 7 \<Rightarrow> 2, _ \<Rightarrow> 3 }"
    val ast_start =
      Position.make0 71 1700 0 "" ""
        "contextual-match-ast-audit"
    val ast_source =
      Parser_Lex_Util.positioned_content_source ast_text ast_start
    val ast_stop = Position.symbol_explode ast_text ast_start
    val expected_match =
      Position.range_position (ast_start, ast_stop)
    val (first_numeral_raw, expected_first_numeral) =
      token_position ast_text ast_start "0" (size "match 42 { ")
    val (_, expected_value_path) =
      token_position ast_text ast_start "IntegrationAudit::Value"
        (first_numeral_raw + 1)
    val (value_raw, expected_qualifier) =
      token_position ast_text ast_start "IntegrationAudit"
        (first_numeral_raw + 1)
    val (_, expected_terminal) =
      token_position ast_text ast_start "Value"
        (value_raw + size "IntegrationAudit::")
    val (_, expected_second_numeral) =
      token_position ast_text ast_start "7"
        (value_raw + size "IntegrationAudit::Value")
    val _ =
      (case parse_source ast_source of
         UE_Match
           (MF_Auto, _,
            [UR_Arm (P_Literal (LP_Integer (_, first_pos)), NONE, _),
             UR_Arm (P_Path path, NONE, _),
             UR_Arm (P_Literal (LP_Integer (_, second_pos)), NONE, _),
             UR_Arm (P_Wild _, NONE, _)],
            match_pos) =>
           let
             val (_, terminal_pos) =
               segment_identifier (final_segment path)
             val qualifier_pos =
               #2
                 (segment_identifier
                   (hd (path_segments path)))
           in
             audit_assert "contextual classification rewrote MF_Auto"
               true;
             audit_assert "bare match span changed"
               (same_range match_pos expected_match);
             audit_assert "first numeral range changed"
               (same_range first_pos expected_first_numeral);
             audit_assert "second numeral range changed"
               (same_range second_pos expected_second_numeral);
             audit_assert "registered path range changed"
               (same_range (path_position path) expected_value_path);
             audit_assert "registered qualifier range changed"
               (same_range qualifier_pos expected_qualifier);
             audit_assert "registered terminal range changed"
               (same_range terminal_pos expected_terminal)
           end
       | _ => error "contextual bare-match classification audit: AST changed")

    val identifier_text =
      "match 7 { 0 \<Rightarrow> 0, registered_seven \<Rightarrow> 1, _ \<Rightarrow> 2 }"
    val identifier_start =
      Position.make0 72 1900 0 "" ""
        "contextual-match-identifier-ast-audit"
    val (_, expected_identifier) =
      token_position identifier_text identifier_start
        "registered_seven" 0
    val _ =
      (case parse_source
          (Parser_Lex_Util.positioned_content_source
            identifier_text identifier_start) of
         UE_Match
           (_, _,
            [_,
             UR_Arm (P_Ident (_, identifier_pos), NONE, _),
             _],
            _) =>
           audit_assert "single-segment registered key range changed"
             (same_range identifier_pos expected_identifier)
       | _ =>
           error
             "contextual bare-match classification audit: identifier AST changed")

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun case_constant_name constructor =
      let
        val (type_name, _) =
          dest_Type (body_type (fastype_of constructor))
      in
        (case Ctr_Sugar.ctr_sugar_of ctxt type_name of
           SOME {casex = Const (name, _), ...} => name
         | _ =>
             error
               ("contextual bare-match classification audit: missing case metadata for " ^
                 quote type_name))
      end

    val registered_case_name =
      case_constant_name \<^term>\<open>RegisteredNullary\<close>
    val negative_case_name =
      case_constant_name \<^term>\<open>NegativeRegisteredNullary\<close>

    val auto =
      checked
        ("match \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "0 \<Rightarrow> \<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_second_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val explicit =
      checked
        ("match_switch \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "0 \<Rightarrow> \<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_second_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "auto registered-value mixture differs from explicit switch"
        (Term.aconv (auto, explicit))
    val _ =
      audit_assert "auto registered-value mixture lost ncase_selector"
        (count_constant \<^const_name>\<open>ncase_selector\<close> auto = 1)
    val _ =
      audit_assert "auto registered-value mixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>mixed_match_scrutinee_marker\<close>
          auto = 1)
    val _ =
      audit_assert "registered backend was duplicated or dropped"
        (count_constant
          \<^const_name>\<open>integration_registered_value_audit\<close>
          auto = 1)
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("switch body marker was duplicated or dropped: " ^ name)
            (count_constant name auto = 1))
        [\<^const_name>\<open>mixed_match_first_body_marker\<close>,
         \<^const_name>\<open>mixed_match_second_body_marker\<close>,
         \<^const_name>\<open>mixed_match_fallback_marker\<close>]
    val _ =
      List.app
        (fn name =>
          audit_assert
            ("switch lowering introduced " ^ quote name)
            (count_constant name auto = 0))
        [\<^const_name>\<open>case_guard\<close>,
         \<^const_name>\<open>urust_eq\<close>,
         \<^const_name>\<open>two_armed_conditional\<close>,
         \<^const_name>\<open>undefined\<close>,
         \<^const_name>\<open>RegisteredNullary\<close>]

    val case_preferred =
      checked
        ("match \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "registered value without numeral selected switch"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          case_preferred = 0)
    val _ =
      audit_assert "registered value without numeral lost case equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          case_preferred > 0)
    val _ =
      audit_assert "registered value without numeral lost case conditional"
        (count_constant \<^const_name>\<open>two_armed_conditional\<close>
          case_preferred > 0)

    val constructor_wins =
      checked
        ("match_case \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         "NegativeRegistered::ConstructorWins \<Rightarrow> 0, " ^
         "NegativeRegistered::Unary(value) \<Rightarrow> value, " ^
         "NegativeRegistered::Other \<Rightarrow> 1 }")
    val _ =
      audit_assert "constructor/nonconstructor exact key did not select the constructor"
        (count_constant negative_case_name constructor_wins = 1)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_markup label source =
      let
        val captured =
          Synchronized.var
            ("contextual_match_" ^ label ^ "_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () => ignore (checked_source source)) ())
              ())
      in
        fold collect_markup
          (maps YXML.parse_body (Synchronized.value captured)) []
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun count_markup markup_name position markup =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)

    fun count_entity kind identity position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    val qualified_markup = capture_markup "qualified" ast_source
    val _ =
      audit_assert "first numeral markup duplicated or disappeared"
        (count_markup Markup.numeralN expected_first_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "second numeral markup duplicated or disappeared"
        (count_markup Markup.numeralN expected_second_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "first numeral typing markup duplicated or disappeared"
        (count_markup Markup.typingN expected_first_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "second numeral typing markup duplicated or disappeared"
        (count_markup Markup.typingN expected_second_numeral
          qualified_markup = 1)
    val _ =
      audit_assert "registered qualifier free markup duplicated or disappeared"
        (count_markup Markup.freeN expected_qualifier
          qualified_markup = 1)
    val _ =
      audit_assert "registered terminal notation report duplicated"
        (count_entity Micro_Rust_Names.notationN "IntegrationAudit::Value"
          expected_terminal qualified_markup = 1)
    val _ =
      audit_assert "registered terminal keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_terminal
          qualified_markup = 1)
    val _ =
      audit_assert "registered terminal acquired typing markup"
        (count_markup Markup.typingN expected_terminal
          qualified_markup = 0)
    val _ =
      audit_assert "registered nonconstructor constant entity count changed"
        (count_entity Markup.constantN
          \<^const_name>\<open>integration_registered_value_audit\<close>
          expected_terminal qualified_markup = 1)

    val identifier_source =
      Parser_Lex_Util.positioned_content_source
        identifier_text identifier_start
    val identifier_markup =
      capture_markup "identifier" identifier_source
    val _ =
      audit_assert "single-segment notation report duplicated"
        (count_entity Micro_Rust_Names.notationN "registered_seven"
          expected_identifier identifier_markup = 1)
    val _ =
      audit_assert "single-segment keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_identifier
          identifier_markup = 1)
    val _ =
      audit_assert "single-segment registration acquired typing markup"
        (count_markup Markup.typingN expected_identifier
          identifier_markup = 0)

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun recovery_checks () =
      let
        val recovered_switch =
          checked
            ("match 42 { 0 \<Rightarrow> 0, IntegrationAudit::Value \<Rightarrow> 1, " ^
             "_ \<Rightarrow> 2 }")
        val recovered_case =
          checked
            ("match \<llangle>RegisteredNullary\<rrangle> { " ^
             "Registered::Nullary \<Rightarrow> 0, " ^
             "Registered::Unary(value) \<Rightarrow> value, " ^
             "Registered::Other \<Rightarrow> 1 }")
        val recovered_unit = checked "()"
      in
        audit_assert "registered-value switch recovery failed"
          (count_constant \<^const_name>\<open>ncase_selector\<close>
            recovered_switch = 1);
        audit_assert "registered-constructor case recovery failed"
          (count_constant registered_case_name recovered_case = 1);
        audit_assert "unit recovery failed"
          (count_constant \<^const_name>\<open>Product_Type.Unity\<close>
            recovered_unit = 1)
      end

    fun expect_exact_rejection serial label text expected_position expected =
      let
        val start =
          Position.make0 (80 + serial) (2300 + serial * 300) 0 "" ""
            ("contextual-match-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val position = expected_position text start
        val expected_message = expected ^ Position.here position
        val expected_range =
          (Value.print_int (the (Position.offset_of position)),
           Value.print_int (the (Position.end_offset_of position)))
        val body =
          (case Exn.result (fn () => checked_source source) () of
             Exn.Res term =>
               error
                 ("contextual bare-match classification audit: " ^
                  label ^ " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let val actual = Runtime.exn_message exn
                 in
                   audit_assert (label ^ " exact diagnostic changed")
                     (actual = expected_message);
                   YXML.parse_body actual
                 end)
        val _ =
          audit_assert (label ^ " YXML offset/end_offset changed")
            (diagnostic_ranges body = [expected_range])
        val _ = recovery_checks ()
      in () end

    fun complete_range text start =
      Position.range_position
        (start, Position.symbol_explode text start)

    fun token_range needle offset text start =
      #2 (token_position text start needle offset)

    val constructor_mixed_text =
      "match \<llangle>RegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), Registered::Nullary \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 0 "registered-constructor-mix"
        constructor_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"

    val guarded_text =
      "match 42 { 0 if True \<Rightarrow> (), IntegrationAudit::Value \<Rightarrow> (), " ^
      "_ \<Rightarrow> () }"
    val guarded_numeral_offset =
      find_from guarded_text "0" (size "match 42 { ")
    val _ =
      expect_exact_rejection 1 "guard-forced-case"
        guarded_text (token_range "0" guarded_numeral_offset)
        "urust_expr: numeric patterns are not supported in case patterns"

    val switch_guard_text =
      "match_switch 42 { IntegrationAudit::Value if True \<Rightarrow> (), _ \<Rightarrow> () }"
    val switch_guard_offset =
      find_from switch_guard_text "if" 0
    val _ =
      expect_exact_rejection 2 "explicit-switch-guard"
        switch_guard_text (token_range "if" switch_guard_offset)
        "urust_expr: guards are not supported in explicit `match_switch`"

    val identifier_failure_text =
      "match 0 { 0 \<Rightarrow> (), unregistered_key \<Rightarrow> () }"
    val identifier_failure_offset =
      find_from identifier_failure_text "unregistered_key" 0
    val _ =
      expect_exact_rejection 3 "unregistered-identifier"
        identifier_failure_text
        (token_range "unregistered_key" identifier_failure_offset)
        ("urust_expr: unsupported match_switch key " ^
         quote "unregistered_key" ^
         " (numeral or `_` only; const-id / path keys not yet supported)")

    val constructor_wins_mixed_text =
      "match \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), NegativeRegistered::ConstructorWins \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 4 "constructor-wins-mix"
        constructor_wins_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"

    val ambiguous_mixed_text =
      "match \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), NegativeRegistered::Ambiguous \<Rightarrow> () }"
    val _ =
      expect_exact_rejection 5 "two-constructor-mix"
        ambiguous_mixed_text complete_range
        "urust_expr: mixed numeral and constructor patterns in bare `match`"
  in
    val _ =
      writeln
        "Contextual bare-match classification, lowering, range, markup, diagnostics, recovery, and single-evaluation regressions passed"
  end
\<close>


section\<open> Or-pattern binder-set validation \<close>

datatype binder_or_audit_fixture =
    BinderAuditA nat nat
  | BinderAuditB nat nat
  | BinderAuditC nat nat
  | BinderAuditSliceA \<open>nat list\<close>
  | BinderAuditSliceB \<open>nat list\<close>

text\<open>
The first alternative is the canonical binder signature. Every alternative is recursively checked
for duplicates before the name sets are compared; rejection precedes local allocation and guard/body
lowering. Successful alternatives share the first signature's entity identities even when source
order and structural positions differ.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("or-pattern binder audit: " ^ message)

    fun checked_source source =
      Parser_Test_Elaboration.expression ctxt source

    fun checked text =
      checked_source (Parser_Lex_Util.text_source text)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("or-pattern binder audit: missing " ^ quote needle)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun nth_raw text needle index =
      let
        fun seek 0 offset = find_from text needle offset
          | seek remaining offset =
              let val found = find_from text needle offset
              in seek (remaining - 1) (found + size needle) end
      in seek index 0 end

    fun token_position text start needle index =
      let
        val raw = nth_raw text needle index
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (token_start, Position.symbol_explode needle token_start)
      end

    fun position_range position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))

    fun diagnostic_ranges body =
      let
        fun collect (XML.Text _) ranges = ranges
          | collect (XML.Elem ((_, properties), children)) ranges =
              let
                val ranges' =
                  (case
                    (Properties.get properties Markup.offsetN,
                     Properties.get properties Markup.end_offsetN) of
                     (SOME offset, SOME end_offset) =>
                       (offset, end_offset) :: ranges
                   | _ => ranges)
              in fold collect children ranges' end
      in distinct (op =) (fold collect body []) end

    fun same_ranges left right =
      length left = length right andalso
        List.all (fn range => member (op =) right range) left

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun markup_of reports =
      fold collect_markup (maps YXML.parse_body reports) []

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

    fun has_markup markup_name position markup =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup

    fun has_urust_entity position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            has_position properties position)
        markup

    fun entity_id property position markup =
      let
        val ids =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                   Properties.get properties Markup.kindN =
                     SOME "urust_var" andalso
                   has_position properties position
                then Properties.get properties property
                else NONE)
          |> distinct (op =)
      in
        (case ids of
           [id] => id
         | _ =>
             error
               ("or-pattern binder audit: entity markup changed" ^
                 Position.here position))
      end

    fun has_entity_property property position markup =
      exists
        (fn (name, properties) =>
          name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            is_some (Properties.get properties property) andalso
            has_position properties position)
        markup

    fun capture_expression text start =
      let
        val captured =
          Synchronized.var "or_pattern_binder_reports" ([]: string list)
        fun capture_reports chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture_reports
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        checked_source
                          (Parser_Lex_Util.positioned_content_source
                            text start)) ()) ())
              ())
      in (result, markup_of (Synchronized.value captured)) end

    val recovery_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | " ^
      "BinderAuditC(x, y) \<Rightarrow> x }"

    fun recover label =
      (ignore (checked recovery_text);
       ignore (checked "()");
       writeln ("or-pattern recovery passed after " ^ label))

    fun expect_rejection serial label text expected positions forbidden =
      let
        val start =
          Position.make0 (110 + serial) (7000 + serial * 400) 0 "" ""
            ("or-pattern-" ^ label ^ "-audit")
        val (result, markup) = capture_expression text start
        val actual =
          (case result of
             Exn.Res term =>
               error
                 ("or-pattern binder audit: " ^ label ^
                  " unexpectedly elaborated to " ^
                  Syntax.string_of_term ctxt term)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else Runtime.exn_message exn)
        val _ =
          audit_assert (label ^ " exact diagnostic changed")
            (actual = expected start)
        val actual_ranges = diagnostic_ranges (YXML.parse_body actual)
        val expected_ranges =
          map (position_range o (fn position => position start)) positions
        val _ =
          audit_assert (label ^ " diagnostic ranges changed")
            (same_ranges actual_ranges expected_ranges)
        val _ =
          List.app
            (fn unexpected =>
              audit_assert
                (label ^ " elaborated " ^ quote unexpected)
                (not (String.isSubstring unexpected actual)))
            forbidden
        val _ = recover label
      in (start, markup) end

    fun missing_message name primary secondary start =
      "urust_expr: or-pattern alternative is missing binder " ^ quote name ^
      Position.here (primary start) ^
      "\nThe first alternative binds it here" ^
      Position.here (secondary start)

    fun extra_message name primary start =
      "urust_expr: or-pattern alternative has extra binder " ^ quote name ^
      Position.here (primary start)

    fun duplicate_message name repeated original start =
      "urust_expr: duplicate pattern binder " ^ quote name ^
      Position.here (repeated start) ^
      "\nThe original binder is here" ^
      Position.here (original start)

    val missing_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { Some(x) | None \<Rightarrow> x }"
    fun missing_bar start = token_position missing_text start "|" 0
    fun missing_first_x start = token_position missing_text start "x" 0
    fun missing_body_x start = token_position missing_text start "x" 1
    val (missing_start, missing_markup) =
      expect_rejection 0 "missing" missing_text
        (missing_message "x" missing_bar missing_first_x)
        [missing_bar, missing_first_x] []
    val _ =
      audit_assert "missing-binder bar lost operator markup"
        (has_markup Markup.operatorN
          (missing_bar missing_start) missing_markup)
    val _ =
      audit_assert "missing-binder bar lost typing markup"
        (has_markup Markup.typingN
          (missing_bar missing_start) missing_markup)
    val _ =
      List.app
        (fn position =>
          (audit_assert "rejected binder acquired bound markup"
             (not (has_markup Markup.boundN position missing_markup));
           audit_assert "rejected binder acquired an entity"
             (not (has_urust_entity position missing_markup))))
        [missing_first_x missing_start, missing_body_x missing_start]

    val extra_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { None | Some(x) \<Rightarrow> 0 }"
    fun extra_x start = token_position extra_text start "x" 0
    val (extra_start, extra_markup) =
      expect_rejection 1 "extra" extra_text
        (extra_message "x" extra_x) [extra_x] []
    val _ =
      audit_assert "extra rejected binder acquired bound markup"
        (not (has_markup Markup.boundN (extra_x extra_start) extra_markup))
    val _ =
      audit_assert "extra rejected binder acquired an entity"
        (not (has_urust_entity (extra_x extra_start) extra_markup))

    val deterministic_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(z, x) | BinderAuditB(_, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun deterministic_bar start =
      token_position deterministic_text start "|" 0
    fun deterministic_x start =
      token_position deterministic_text start "x" 0
    val _ =
      expect_rejection 2 "deterministic-missing" deterministic_text
        (missing_message "x" deterministic_bar deterministic_x)
        [deterministic_bar, deterministic_x] []

    val third_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, _) | BinderAuditB(x, _) | " ^
      "BinderAuditC(_, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun third_first_bar start = token_position third_text start "|" 0
    fun third_first_x start = token_position third_text start "x" 0
    val _ =
      expect_rejection 3 "third-alternative" third_text
        (missing_message "x" third_first_bar third_first_x)
        [third_first_bar, third_first_x] []

    val nested_missing_text =
      "match_case \<llangle>Some (Ok (1 :: nat))\<rrangle> { " ^
      "Some(Ok(x) | Err(y)) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun nested_missing_bar start =
      token_position nested_missing_text start "|" 0
    fun nested_missing_x start =
      token_position nested_missing_text start "x" 0
    val _ =
      expect_rejection 4 "nested-missing-before-extra" nested_missing_text
        (missing_message "x" nested_missing_bar nested_missing_x)
        [nested_missing_bar, nested_missing_x] []

    val nested_extra_text =
      "match_case \<llangle>Some (Some (1 :: nat))\<rrangle> { " ^
      "Some(None | Some(x)) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun nested_extra_x start =
      token_position nested_extra_text start "x" 0
    val _ =
      expect_rejection 5 "nested-extra" nested_extra_text
        (extra_message "x" nested_extra_x) [nested_extra_x] []

    val guarded_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { " ^
      "Some(x) | None if unknown_binder_guard!() \<Rightarrow> " ^
      "unknown_binder_body!(), _ \<Rightarrow> 0 }"
    fun guarded_bar start = token_position guarded_text start "|" 0
    fun guarded_x start = token_position guarded_text start "x" 0
    val _ =
      expect_rejection 6 "guarded" guarded_text
        (missing_message "x" guarded_bar guarded_x)
        [guarded_bar, guarded_x]
        ["unknown_binder_guard", "unknown_binder_body"]

    val slice_missing_text =
      "match_case \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
      "BinderAuditSliceA([x, ..]) | BinderAuditSliceB([]) \<Rightarrow> 0, " ^
      "_ \<Rightarrow> 0 }"
    fun slice_missing_bar start =
      token_position slice_missing_text start "|" 0
    fun slice_missing_x start =
      token_position slice_missing_text start "x" 0
    val _ =
      expect_rejection 7 "slice-missing" slice_missing_text
        (missing_message "x" slice_missing_bar slice_missing_x)
        [slice_missing_bar, slice_missing_x] []

    val slice_extra_text =
      "match_case \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
      "BinderAuditSliceA([]) | BinderAuditSliceB([.., x]) \<Rightarrow> 0, " ^
      "_ \<Rightarrow> 0 }"
    fun slice_extra_x start =
      token_position slice_extra_text start "x" 0
    val _ =
      expect_rejection 8 "slice-extra" slice_extra_text
        (extra_message "x" slice_extra_x) [slice_extra_x] []

    val duplicate_first_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, x) | BinderAuditB(y, _) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun duplicate_first_original start =
      token_position duplicate_first_text start "x" 0
    fun duplicate_first_repeated start =
      token_position duplicate_first_text start "x" 1
    val _ =
      expect_rejection 9 "duplicate-first" duplicate_first_text
        (duplicate_message "x"
          duplicate_first_repeated duplicate_first_original)
        [duplicate_first_repeated, duplicate_first_original] []

    val duplicate_later_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, _) | BinderAuditB(y, y) \<Rightarrow> 0, _ \<Rightarrow> 0 }"
    fun duplicate_later_original start =
      token_position duplicate_later_text start "y" 0
    fun duplicate_later_repeated start =
      token_position duplicate_later_text start "y" 1
    val _ =
      expect_rejection 10 "duplicate-later" duplicate_later_text
        (duplicate_message "y"
          duplicate_later_repeated duplicate_later_original)
        [duplicate_later_repeated, duplicate_later_original] []

    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "or-pattern binder audit: empty parse")

    fun callback_trace text =
      let
        val calls = Unsynchronized.ref ([]: string list)
        fun lower _ expression =
          let
            val label =
              (case expression of
                 UE_Path path => render_path path
               | _ => "<non-path>")
            val _ = calls := label :: !calls
          in Free ("_" ^ label, dummyT) end
        val result =
          (case parse text of
             UE_Match arguments =>
               Exn.result
                 (fn () =>
                   URust_Matching.lower_match lower ctxt
                     URust_Resolution.empty_environment arguments) ()
           | _ => error "or-pattern binder audit: callback fixture changed")
      in (result, rev (!calls)) end

    val invalid_callback_text =
      "match_case binder_or_scrutinee_probe { " ^
      "BinderAuditA(x, _) | BinderAuditB(_, _) " ^
      "if binder_or_guard_probe \<Rightarrow> binder_or_body_probe, " ^
      "_ \<Rightarrow> binder_or_fallback_probe }"
    val (invalid_callback_result, invalid_callback_calls) =
      callback_trace invalid_callback_text
    val _ =
      (case invalid_callback_result of
         Exn.Res _ =>
           error "or-pattern binder audit: invalid callback fixture elaborated"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "callback rejection changed"
               (String.isSubstring
                 "or-pattern alternative is missing binder \"x\""
                 (Runtime.exn_message exn)))
    val _ =
      audit_assert "rejected arm lowered its guard or body"
        (invalid_callback_calls = ["binder_or_scrutinee_probe"])

    val valid_callback_text =
      "match_case binder_or_scrutinee_probe { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | BinderAuditC(x, y) " ^
      "if binder_or_guard_probe \<Rightarrow> binder_or_body_probe, " ^
      "_ \<Rightarrow> binder_or_fallback_probe }"
    val (valid_callback_result, valid_callback_calls) =
      callback_trace valid_callback_text
    val _ =
      (case valid_callback_result of
         Exn.Res _ => ()
       | Exn.Exn exn => Exn.reraise exn)
    val _ =
      audit_assert "valid arm source expressions were not lowered once"
        (valid_callback_calls =
          ["binder_or_scrutinee_probe", "binder_or_guard_probe",
           "binder_or_body_probe", "binder_or_fallback_probe"])

    val valid_markup_text =
      "match_case \<llangle>BinderAuditA 1 2\<rrangle> { " ^
      "BinderAuditA(x, y) | BinderAuditB(y, x) | BinderAuditC(x, y) " ^
      "if x < y \<Rightarrow> x, _ \<Rightarrow> 0 }"
    val valid_markup_start =
      Position.make0 140 14000 0 "" "" "or-pattern-valid-markup-audit"
    val (valid_markup_result, valid_markup) =
      capture_expression valid_markup_text valid_markup_start
    val _ =
      (case valid_markup_result of
         Exn.Res _ => ()
       | Exn.Exn exn => Exn.reraise exn)
    val x_positions =
      map (token_position valid_markup_text valid_markup_start "x")
        (0 upto 4)
    val y_positions =
      map (token_position valid_markup_text valid_markup_start "y")
        (0 upto 3)
    fun assert_shared name positions =
      let
        val definition = hd positions
        val references = tl positions
        val id = entity_id Markup.defN definition valid_markup
        val _ =
          audit_assert (name ^ " definition lost bound markup")
            (has_markup Markup.boundN definition valid_markup)
        val _ =
          List.app
            (fn position =>
              (audit_assert (name ^ " occurrence lost bound markup")
                 (has_markup Markup.boundN position valid_markup);
               audit_assert (name ^ " occurrence changed entity identity")
                 (entity_id Markup.refN position valid_markup = id)))
            references
        val _ =
          List.app
            (fn position =>
              audit_assert (name ^ " later alternative allocated a definition")
                (not
                  (has_entity_property Markup.defN
                    position valid_markup)))
            (tl positions)
      in () end
    val _ = assert_shared "x" x_positions
    val _ = assert_shared "y" y_positions

    val _ =
      ignore
        (checked
          ("match_case \<llangle>(Some (1 :: nat), " ^
           "(Some (2 :: nat), TNil))\<rrangle> { " ^
           "(Some(x), y) | (y, Some(x)) \<Rightarrow> x, _ \<Rightarrow> 0 }"))
    val _ =
      ignore
        (checked
          ("match \<llangle>BinderAuditSliceA [1 :: nat, 2]\<rrangle> { " ^
           "BinderAuditSliceA([x, ..]) | " ^
           "BinderAuditSliceB([.., x]) \<Rightarrow> x, _ \<Rightarrow> 0 }"))
  in
    val _ =
      writeln
        "Or-pattern binder diagnostics, ranges, precedence, markup, recovery, and shared-environment regressions passed"
  end
\<close>


section\<open> Standard code equations \<close>

urust_expr regression_code_literal
  \<open> 7_u32 \<close>

urust_expr regression_code_unit
  \<open> () \<close>

urust_expr regression_code_yield
  \<open> \<y>\<i>\<e>\<l>\<d> \<close>

urust_expr regression_code_primitive_log
  \<open> \<l>\<o>\<g> \<llangle>Info\<rrangle> \<llangle>[]\<rrangle> \<close>

urust_expr regression_code_log_data
  \<open> l\<llangle>True\<rrangle> \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt

    fun audit_assert message condition =
      if condition then ()
      else error ("parser code-equation audit: " ^ message)

    val generated =
      [\<^const_name>\<open>regression_code_literal\<close>,
       \<^const_name>\<open>regression_code_unit\<close>,
       \<^const_name>\<open>regression_code_yield\<close>,
       \<^const_name>\<open>regression_code_primitive_log\<close>,
       \<^const_name>\<open>regression_code_log_data\<close>]

    fun definition_theorem constant =
      Proof_Context.get_thm ctxt
        (Long_Name.base_name constant ^ "_def")

    fun executable_equations constant =
      let
        val certificate = Code.get_cert ctxt [] constant
        val (_, equations) =
          Code.equations_of_cert thy certificate
      in
        map_filter
          (fn (_, (SOME theorem, _)) => SOME theorem
            | _ => NONE)
          (the equations)
      end

    fun check_generated constant =
      let
        val definition = definition_theorem constant
        val equations = executable_equations constant
      in
        audit_assert
          ("expected one default equation for " ^ quote constant)
          (length equations = 1);
        audit_assert
          ("default equation differs from the definition for " ^
            quote constant)
          (Thm.equiv_thm thy
            (the_single equations,
             Axclass.unoverload ctxt definition))
      end

    val _ = List.app check_generated generated
  in
    val _ = writeln "Parser-generated default code equations passed"
  end
\<close>

end
