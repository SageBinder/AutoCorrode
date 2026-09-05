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
      (case URust_Diagnostics.parse_source ctxt
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
      (case URust_Diagnostics.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "expression-antiquotation callee audit: empty parse")

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
            URust_Command.elab_urust ctxt
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
    val captured_reports = Unsynchronized.ref ([]: string list)
    fun capture_reports chunks =
      Unsynchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (URust_Command.elab_urust ctxt
                    (Parser_Lex_Util.positioned_content_source
                      markup_text markup_start))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, tree)) result =
          fold collect_markup tree (markup :: result)
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
      (case URust_Diagnostics.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "function-literal callee audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun checked text =
      URust_Command.elab_urust ctxt
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
            URust_Command.elab_urust ctxt
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
    val captured_reports = Unsynchronized.ref ([]: string list)
    fun capture_reports chunks =
      Unsynchronized.change captured_reports (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture_reports
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (URust_Command.elab_urust ctxt
                    (Parser_Lex_Util.positioned_content_source
                      markup_text markup_start))) ())
          ())

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, tree)) result =
          fold collect_markup tree (markup :: result)
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
      (case URust_Diagnostics.parse_source ctxt source of
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
      URust_Translate.mk_closed ctxt (parse text)

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
    val captured_reports = Unsynchronized.ref ([]: string list)
    fun capture_reports chunks =
      Unsynchronized.change captured_reports (append chunks)
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
