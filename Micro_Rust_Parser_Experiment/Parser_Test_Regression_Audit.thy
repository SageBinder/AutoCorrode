theory Parser_Test_Regression_Audit
  imports
    Parser_Test_Improvements
    Parser_Test_Negative_Conformance
begin

ML\<open>
structure Parser_Test_Report_Lock =
struct
  val lock = Synchronized.var "parser_test_report_lock" ()
  fun run action =
    Synchronized.change_result lock (fn () => (action (), ()))
end
\<close>

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
      URust_Command.elab_urust ctxt (Parser_Lex_Util.text_source source)

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
      (case URust_Diagnostics.parse_source ctxt source of
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
            URust_Command.elab_urust ctxt
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
      URust_Command.elab_urust ctxt (Parser_Lex_Util.text_source source)

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
      (case URust_Diagnostics.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "conditional-binding regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      URust_Command.elab_urust ctxt (Parser_Lex_Util.text_source text)

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

    val captured_reports = Unsynchronized.ref ([]: string list)
    fun capture_reports chunks =
      Unsynchronized.change captured_reports (append chunks)
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
        (maps YXML.parse_body (! captured_reports)) []
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

section\<open> Positions and pattern grammar \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("parser regression audit: " ^ message)

    fun parse text =
      (case URust_Diagnostics.parse_source ctxt
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

    val _ =
      audit_assert "exclusive range shape changed"
        (range RK_Exclusive "5" "7"
          (parse_pattern "5..7"))
    val _ =
      audit_assert "inclusive range shape changed"
        (range RK_Inclusive "5" "7"
          (parse_pattern "5..=7"))

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

    fun find_from text needle offset =
      if offset + size needle > size text then
        error
          ("parser regression audit: missing " ^ quote needle)
      else if
        String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

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
            URust_Command.elab_urust ctxt
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
              URust_Command.elab_urust ctxt
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
Same-source commands in \<open>Parser_Test_Conformance\<close> separately require the
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
      (case URust_Diagnostics.parse_source ctxt
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
      URust_Translate.mk_closed ctxt (parse text)

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

section\<open> Legacy macro structure, spans, and markup \<close>

consts
  macro_audit_scrutinee :: \<open>nat option\<close>
  macro_audit_ref :: \<open>('a, 'b, 'v) Global_Store.ref\<close>

text\<open>
These checks pin the unresolved macro payloads and the exact shallow term vocabulary.
They also prove that discarded arguments never enter lowering, \<open>vec!\<close> reuses
the array builder, address macros retain the exact legacy \<open>ref_address\<close> target,
registered bang-names win only when adjacent, and \<open>matches!\<close> uses the ordinary
case compiler with one scrutinee evaluation and false fallback.
\<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("legacy macro regression audit: " ^ message)

    fun parse source =
      (case URust_Diagnostics.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "legacy macro regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun unchecked text =
      URust_Translate.mk_closed ctxt (parse_text text)

    fun checked text =
      URust_Command.elab_urust ctxt (Parser_Lex_Util.text_source text)

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) =>
              if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

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

    val captured_reports = Unsynchronized.ref ([]: string list)
    fun capture_reports chunks =
      Unsynchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                URust_Command.elab_urust ctxt
                  (Parser_Lex_Util.positioned_content_source
                    text start)) ())
          ())
    val _ = capture_elaboration spaced_text spaced_start

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
        (maps YXML.parse_body (! captured_reports)) []
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
      (case URust_Diagnostics.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "closure regression audit: empty parse")

    fun parse_text text =
      parse (Parser_Lex_Util.text_source text)

    fun checked text =
      URust_Command.elab_urust ctxt
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

    val captured_reports = Unsynchronized.ref ([]: string list)
    fun capture_reports chunks =
      Unsynchronized.change captured_reports (append chunks)
    fun capture_elaboration text start =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                URust_Command.elab_urust ctxt
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
        (maps YXML.parse_body (! captured_reports)) []
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

section\<open> Structured paths and turbofish \<close>

definition path_audit_generic ::
  \<open>nat \<Rightarrow> nat \<Rightarrow>
    (unit, nat, unit, unit, unit) function_body\<close>
  where
  \<open> path_audit_generic parameter \<equiv>
      lift_fun1 (\<lambda>argument. parameter + argument) \<close>

micro_rust_notation (call) path_audit_generic ("Exact::f")
micro_rust_notation (call) cf0 ("Exact::<not valid HOL>::f")

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("structured-path regression audit: " ^ message)

    fun parse text =
      (case URust_Diagnostics.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME expression => expression
       | NONE => error "structured-path regression audit: empty parse")
      handle ERROR message =>
        error ("structured-path regression audit: source " ^ quote text ^
          " failed\n" ^ message)

    val structured_text = "Module :: f ::\n < a + 1, (b, c) >()"
    val structured_start =
      Position.make0 7 30 100 "" "" "structured-path-audit"
    val structured =
      (case URust_Diagnostics.parse_source ctxt
          (Parser_Lex_Util.positioned_content_source
            structured_text structured_start) of
         SOME expression => expression
       | NONE => error "structured-path regression audit: empty positioned parse")
    val _ =
      (case structured of
         UE_Call
           (UC_Path path, [], _) =>
           (audit_assert "canonical path rendering changed"
              (render_path path = "Module::f::<a + 1,(b, c)>");
            case path_segments path of
              [Path_Segment ("Module", _, NONE),
               Path_Segment ("f", _, NONE),
               Path_Segment
                 ("", _, _)] =>
                error "structured-path regression audit: impossible empty segment"
            | [Path_Segment ("Module", _, NONE),
               Path_Segment
                 ("f", _,
                  SOME (Generic_Args (arguments, generic_pos)))] =>
                let
                  val generic_start =
                    Position.symbol_explode "Module :: f " structured_start
                  val generic_stop =
                    Position.symbol_explode "Module :: f ::\n < a + 1, (b, c) >"
                      structured_start
                  val first_start =
                    Position.symbol_explode "Module :: f ::\n < " structured_start
                  val first_stop =
                    Position.symbol_explode "Module :: f ::\n < a + 1"
                      structured_start
                  val second_start =
                    Position.symbol_explode "Module :: f ::\n < a + 1, "
                      structured_start
                  val second_stop =
                    Position.symbol_explode "Module :: f ::\n < a + 1, (b, c)"
                      structured_start
                  val first_range = Input.range_of (nth arguments 0)
                  val second_range = Input.range_of (nth arguments 1)
                in
                 audit_assert "generic argument order changed"
                   (map Input.string_of arguments = ["a + 1", "(b, c)"]);
                 audit_assert "multiline generic span moved"
                   (Position.offset_of generic_pos =
                      Position.offset_of generic_start andalso
                    Position.end_offset_of generic_pos =
                      Position.offset_of generic_stop);
                 audit_assert "first multiline argument range moved"
                   (Position.offset_of (#1 first_range) =
                      Position.offset_of first_start andalso
                    Position.offset_of (#2 first_range) =
                      Position.offset_of first_stop);
                 audit_assert "second multiline argument range moved"
                   (Position.offset_of (#1 second_range) =
                      Position.offset_of second_start andalso
                    Position.offset_of (#2 second_range) =
                      Position.offset_of second_stop)
                end
            | _ =>
                error "structured-path regression audit: segment structure changed")
       | _ => error "structured-path regression audit: callee structure changed")

    val method = parse "receiver.method::<N>()"
    val _ =
      (case method of
         UE_Call
           (UC_Method
             (UE_Path receiver,
              Path_Segment
                ("method", _, SOME (Generic_Args ([argument], _)))),
            [], _) =>
           audit_assert "method callee structure changed"
             (render_path receiver = "receiver" andalso
              Input.string_of argument = "N")
       | _ => error "structured-path regression audit: method AST changed")

    val comparison_arguments = parse "f::<a > b, a >= b, a >> b>()"
    val _ =
      (case comparison_arguments of
         UE_Call
           (UC_Path
             (UR_Path
               ([Path_Segment
                  ("f", _,
                   SOME (Generic_Args (arguments, _)))], _)),
            [], _) =>
           audit_assert "top-level HOL comparison/shift operators split the generic group"
             (map Input.string_of arguments =
               ["a > b", "a >= b", "a >> b"])
       | _ =>
           error "structured-path regression audit: operator payload AST changed")

    fun expect_argument_sources label text expected =
      (case parse text of
         UE_Call
           (UC_Path
             (UR_Path
               ([Path_Segment
                  ("f", _,
                   SOME (Generic_Args (arguments, _)))], _)),
            [], _) =>
           audit_assert (label ^ " changed generic argument capture")
             (map Input.string_of arguments = expected)
       | _ =>
           error ("structured-path regression audit: " ^ label ^
             " changed call structure"))

    val _ =
      expect_argument_sources "double-quoted payload"
        "f::<\"quoted, > ) ] }\", second>()"
        ["\"quoted, > ) ] }\"", "second"]
    val _ =
      expect_argument_sources "HOL string payload"
        "f::<STR ''quoted, > ) ] }'', second>()"
        ["STR ''quoted, > ) ] }''", "second"]
    val _ =
      expect_argument_sources "cartouche payload"
        ("f::<" ^ Symbol.open_ ^ "opaque, > ) ] }" ^ Symbol.close ^
          ", second>()")
        [Symbol.open_ ^ "opaque, > ) ] }" ^ Symbol.close, "second"]
    val _ =
      expect_argument_sources "escaped-symbol final payload"
        "f::<first, \<clubsuit>>()"
        ["first", "\<clubsuit>"]
    val _ =
      expect_argument_sources "escaped-symbol payload before comma"
        "f::<\<clubsuit>, True>()"
        ["\<clubsuit>", "True"]
    val _ =
      expect_argument_sources "escaped-symbol payload before operator"
        "f::<\<clubsuit> + 1>()"
        ["\<clubsuit> + 1"]
    val _ =
      expect_argument_sources "escaped-symbol payload before application"
        "f::<\<spadesuit> (1)>()"
        ["\<spadesuit> (1)"]
    val physical_club =
      Byte.bytesToString
        (Word8Vector.fromList [0wxE2, 0wx99, 0wxA3])
    val _ =
      expect_argument_sources "physical-Unicode payload before comma"
        ("f::<" ^ physical_club ^ ", True>()")
        [physical_club, "True"]

    val escaped_text = "f::<\<clubsuit>, True>()"
    val escaped_start =
      Position.make0 19 60 400 "" "" "turbofish-escaped-range-audit"
    val escaped =
      (case URust_Diagnostics.parse_source ctxt
          (Parser_Lex_Util.positioned_content_source
            escaped_text escaped_start) of
         SOME expression => expression
       | NONE => error "structured-path regression audit: empty escaped-symbol parse")
    val _ =
      (case escaped of
         UE_Call
           (UC_Path
             (UR_Path
               ([Path_Segment
                  ("f", _,
                   SOME (Generic_Args ([first, second], generic_pos)))], _)),
            [], _) =>
           let
             val first_range = Input.range_of first
             val second_range = Input.range_of second
             val generic_start =
               Position.symbol_explode "f" escaped_start
             val first_start =
               Position.symbol_explode "f::<" escaped_start
             val first_stop =
               Position.symbol_explode "f::<\<clubsuit>" escaped_start
             val second_start =
               Position.symbol_explode "f::<\<clubsuit>, " escaped_start
             val second_stop =
               Position.symbol_explode "f::<\<clubsuit>, True" escaped_start
             val close_stop =
               Position.symbol_explode "f::<\<clubsuit>, True>" escaped_start
           in
             audit_assert "escaped symbol did not occupy one source position"
               (Position.offset_of (#1 first_range) =
                  Position.offset_of first_start andalso
                Position.offset_of (#2 first_range) =
                  Position.offset_of first_stop andalso
                Position.offset_of first_stop =
                  Option.map (fn offset => offset + 1)
                    (Position.offset_of first_start));
             audit_assert "second escaped-symbol argument range moved"
               (Position.offset_of (#1 second_range) =
                  Position.offset_of second_start andalso
                Position.offset_of (#2 second_range) =
                  Position.offset_of second_stop);
             audit_assert "escaped-symbol generic span moved"
               (Position.offset_of generic_pos =
                  Position.offset_of generic_start andalso
                Position.end_offset_of generic_pos =
                  Position.offset_of close_stop)
           end
       | _ =>
           error "structured-path regression audit: escaped-symbol AST changed")

    fun expect_parse_rejection label text expected =
      (case Exn.result
          (fn () =>
            URust_Diagnostics.parse_source ctxt
              (Parser_Lex_Util.text_source text)) () of
         Exn.Res _ =>
           error ("structured-path regression audit: " ^ label ^
             " was unexpectedly accepted")
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val message = Runtime.exn_message exn
             in
               if String.isSubstring expected message then ()
               else
                 error ("structured-path regression audit: " ^ label ^
                   " changed its diagnostic to " ^ quote message)
             end)

    val _ =
      expect_parse_rejection "unterminated double-quoted payload"
        "f::<\"unterminated>()"
        "unclosed string literal"
    val _ =
      expect_parse_rejection "unterminated HOL string payload"
        "f::<STR ''unterminated>()"
        "unclosed string literal"
    val _ =
      expect_parse_rejection "unterminated cartouche payload"
        ("f::<" ^ Symbol.open_ ^ "unterminated>()")
        "unclosed text cartouche"

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_reports action =
      let
        val captured = Unsynchronized.ref ([]: string list)
        fun capture chunks =
          Unsynchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE] action ()) ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (! captured)) []
      in (result, markup) end

    fun source_position start prefix text =
      let
        val token_start = Position.symbol_explode prefix start
        val token_stop = Position.symbol_explode text token_start
      in Position.range_position (Position.range (token_start, token_stop)) end

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

    val delimiter_text = "f::\n<\<clubsuit>, True>()"
    val delimiter_start =
      Position.make0 29 70 700 "" "" "turbofish-delimiter-markup-audit"
    val (_, delimiter_markup) =
      capture_reports
        (fn () =>
          ignore
            (URust_Diagnostics.parse_source ctxt
              (Parser_Lex_Util.positioned_content_source
                delimiter_text delimiter_start)))
    val colon_position =
      source_position delimiter_start "f" "::"
    val open_position =
      source_position delimiter_start "f::\n" "<"
    val comma_position =
      source_position delimiter_start "f::\n<\<clubsuit>" ","
    val close_position =
      source_position delimiter_start "f::\n<\<clubsuit>, True" ">"
    val _ =
      List.app
        (fn (label, position) =>
          (audit_assert (label ^ " delimiter markup moved")
             (has_markup delimiter_markup Markup.delimiterN position);
           audit_assert (label ^ " typing markup moved")
             (has_markup delimiter_markup Markup.typingN position)))
        [("multiline path separator", colon_position),
         ("multiline turbofish opener", open_position),
         ("escaped-symbol comma", comma_position),
         ("multiline turbofish closer", close_position)]

    val hol_markup_text =
      "path_audit_generic::<\<clubsuit> + 2>(3)"
    val hol_markup_start =
      Position.make0 31 90 900 "" "" "turbofish-hol-markup-audit"
    val (_, hol_markup) =
      capture_reports
        (fn () =>
          ignore
            (URust_Command.elab_urust ctxt
              (Parser_Lex_Util.positioned_content_source
                hol_markup_text hol_markup_start)))
    val hol_plus_position =
      source_position hol_markup_start
        "path_audit_generic::<\<clubsuit> " "+"
    val hol_numeral_position =
      source_position hol_markup_start
        "path_audit_generic::<\<clubsuit> + " "2"
    val _ =
      audit_assert "embedded HOL delimiter markup disappeared"
        (has_markup hol_markup Markup.delimiterN hol_plus_position)
    val _ =
      audit_assert "embedded HOL numeral markup disappeared"
        (has_markup hol_markup Markup.numeralN hol_numeral_position)

    val exact_markup_text = "Exact::<not valid HOL>::f()"
    val exact_markup_start =
      Position.make0 37 110 1100 "" "" "turbofish-exact-markup-audit"
    val (_, exact_markup) =
      capture_reports
        (fn () =>
          ignore
            (URust_Command.elab_urust ctxt
              (Parser_Lex_Util.positioned_content_source
                exact_markup_text exact_markup_start)))
    val exact_word_positions =
      [source_position exact_markup_start "Exact::<" "not",
       source_position exact_markup_start "Exact::<not " "valid",
       source_position exact_markup_start "Exact::<not valid " "HOL"]
    val _ =
      List.app
        (fn position =>
          audit_assert
            "exact malformed registration unexpectedly received HOL free markup"
            (not (has_markup exact_markup Markup.freeN position)))
        exact_word_positions

    fun message_markup message =
      fold collect_markup (YXML.parse_body message) []

    fun expect_positioned_rejection label text prefix expected =
      let
        val start =
          Position.make0 41 130 1300 "" ""
            ("turbofish-positioned-" ^ label)
        val expected_position =
          Position.symbol_explode prefix start
        val message =
          (case Exn.result
              (fn () =>
                URust_Diagnostics.parse_source ctxt
                  (Parser_Lex_Util.positioned_content_source
                    text start)) () of
             Exn.Res _ =>
               error ("structured-path regression audit: positioned " ^
                 label ^ " was unexpectedly accepted")
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else Runtime.exn_message exn)
        val plain = XML.content_of (YXML.parse_body message)
        val expected_offset =
          Option.map Value.print_int
            (Position.offset_of expected_position)
        val has_expected_offset =
          exists
            (fn (_, properties) =>
              Properties.get properties Markup.offsetN = expected_offset)
            (message_markup message)
      in
        audit_assert (label ^ " diagnostic text changed")
          (String.isSubstring expected plain);
        audit_assert (label ^ " diagnostic lost its source offset")
          has_expected_offset
      end

    val _ =
      expect_positioned_rejection "empty-argument"
        "f::<>()" "f::<" "empty turbofish argument"
    val _ =
      expect_positioned_rejection "mismatched-delimiter"
        "f::<(1]>()" "f::<(1" "mismatched delimiter in turbofish"
    val _ =
      expect_positioned_rejection "unterminated-group"
        "f::<1(" "f::" "unterminated turbofish"
    val _ =
      expect_positioned_rejection "native-string"
        "f::<\"unterminated>()" "f::<" "unclosed string literal"
    val _ =
      expect_positioned_rejection "native-HOL-string"
        "f::<STR ''unterminated>()" "f::<STR " "unclosed string literal"
    val _ =
      expect_positioned_rejection "native-cartouche"
        ("f::<" ^ Symbol.open_ ^ "unterminated>()")
        "f::<" "unclosed text cartouche"

    val semantic =
      Syntax.check_term ctxt
        (URust_Translate.mk_closed ctxt
          (parse "path_audit_generic::<1>(2)"))
    val _ =
      (case Term.strip_comb semantic of
         (Const (name, _), [function, _]) =>
           (audit_assert "semantic turbofish stopped using funcall1"
              (name = \<^const_name>\<open>funcall1\<close>);
            case Term.strip_comb (Term_Position.strip_positions function) of
              (Const (generic_name, _), [_]) =>
                audit_assert "semantic parameters were not applied to the callee"
                  (generic_name = \<^const_name>\<open>path_audit_generic\<close>)
            | _ =>
                error "structured-path regression audit: generic application shape changed")
       | _ => error "structured-path regression audit: call shape changed")

    val exact =
      URust_Command.elab_urust ctxt
        (Parser_Lex_Util.text_source
          "Exact::<not valid HOL>::f()")
    val _ =
      audit_assert "exact generic-path registration did not bypass HOL parsing"
        (Term.exists_subterm
          (fn Const (name, _) => name = \<^const_name>\<open>cf0\<close>
            | _ => false)
          exact)

    val _ =
      ((URust_Diagnostics.parse_source ctxt
          (Parser_Lex_Util.text_source "f::<1(");
        error "structured-path regression audit: unterminated turbofish accepted")
       handle ERROR _ => ())
    val _ =
      (case parse "cf0()" of
         UE_Call (UC_Path path, [], _) =>
           audit_assert "lexer state did not recover after turbofish failure"
             (render_path path = "cf0")
       | _ =>
           error "structured-path regression audit: recovery parse changed")
  in
    val _ = writeln "Structured path and turbofish regressions passed"
  end
\<close>

section\<open> Standard code equations \<close>

urust_expr regression_code_literal
  \<open> 7_u32 \<close>

urust_expr regression_code_unit
  \<open> () \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val thy = Proof_Context.theory_of ctxt

    fun audit_assert message condition =
      if condition then ()
      else error ("parser code-equation audit: " ^ message)

    val generated =
      [\<^const_name>\<open>regression_code_literal\<close>,
       \<^const_name>\<open>regression_code_unit\<close>]

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
