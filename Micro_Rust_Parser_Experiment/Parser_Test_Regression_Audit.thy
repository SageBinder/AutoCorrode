theory Parser_Test_Regression_Audit
  imports
    Parser_Test_Improvements
    Parser_Test_Negative_Conformance
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
      elab_urust ctxt (Parser_Lex_Util.text_source source)

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
      elab_urust ctxt (Parser_Lex_Util.text_source source)

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
           P_Constr ("Some", _, [nested]), _) =>
             audit_assert "constructor alias lost its range argument"
               (range RK_Inclusive "5" "7" nested)
       | _ =>
           error
             "parser regression audit: constructor alias shape changed")

    val _ =
      (case parse_pattern "whole @ Head { field: 5..7 }" of
         P_Alias ("whole", _,
           P_Struct ("Head", _,
             [SF_Field ("field", _, nested)]), _) =>
             audit_assert "struct alias lost its range field"
               (range RK_Exclusive "5" "7" nested)
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
            elab_urust ctxt
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
              elab_urust ctxt
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

    fun identifier text (UE_Ident (actual, _)) = actual = text
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
            UP_Index (UP_Ident ("xs", _), index, _),
            rhs, _) =>
           audit_assert "indexed place conversion changed"
             (integer "0" index andalso integer "1" rhs)
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
