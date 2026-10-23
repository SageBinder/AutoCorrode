(* ML audits for pattern matching, name resolution and semantic navigation. The readable
   examples are in Parser_Pattern_Examples. *)

theory Parser_Pattern_ML_Tests
  imports
    Parser_Pattern_Examples
    Parser_Syntax_ML_Tests
begin

chapter\<open> Pattern matching \<close>

section\<open>Matcher mechanism regression audit\<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

ML_val\<open>
  local
    val ctxt = \<^context>

    fun assert message condition =
      if condition then ()
      else error ("matcher mechanism audit: " ^ message)

    fun count_constant expected term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)
        term 0

    fun rhs_of name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals
      |> snd

    fun outer_case_clauses rhs =
      let
        val (parameters, body) = Term.strip_abs rhs
        val names =
          Name.variants Name.context
            (map (fn (name, _) =>
              if name = "" then "parameter" else name)
              parameters)
        val frees = map Free (names ~~ map snd parameters)
        val body' = subst_bounds (rev frees, body)
        val selector =
          (case body' of
             Const (name, _) $ _ $ continuation =>
               if name = \<^const_name>\<open>bind\<close>
               then snd (Term.dest_abs_global continuation)
               else error "expected outer scrutinee bind"
           | _ => error "expected outer scrutinee bind")
      in
        (case Case_Translation.strip_case ctxt false selector of
           SOME (_, clauses) => clauses
         | NONE => error "expected outer structural case")
      end

    val direct_names =
      ["parser_four_axis_structural_matrix",
       "parser_small_structural_matrix",
       "parser_closed_structural_matrix",
       "parser_structural_or_matrix",
       "parser_partial_structural_matrix",
       "parser_explicit_fallback_structural_matrix",
       "parser_effectful_structural_matrix"]

    fun audit_direct name =
      let val rhs = rhs_of name
      in
        (assert (name ^ " duplicated its outer scrutinee bind")
          (count_constant \<^const_name>\<open>bind\<close> rhs = 1);
         assert (name ^ " generated a structural equality test")
          (count_constant \<^const_name>\<open>urust_eq\<close> rhs = 0);
         assert (name ^ " retained schematic variables")
          (null (Term.add_vars rhs []));
         assert (name ^ " retained local free binders")
          (null (Term.add_frees rhs [])))
      end

    val _ = List.app audit_direct direct_names
    val _ =
      assert "four-axis matrix changed its 16-clause source expansion"
        (length
          (outer_case_clauses
            (rhs_of "parser_four_axis_structural_matrix")) = 16)
    val _ =
      assert "small open matrix changed its clause count"
        (length
          (outer_case_clauses
            (rhs_of "parser_small_structural_matrix")) = 3)
    val _ =
      assert "small closed matrix changed its clause count"
        (length
          (outer_case_clauses
            (rhs_of "parser_closed_structural_matrix")) = 3)
    val _ =
      assert "structural or-pattern changed its normalized clause shape"
        (length
          (outer_case_clauses
            (rhs_of "parser_structural_or_matrix")) = 2)
    val _ =
      assert "explicit fallback matrix changed its clause count"
        (length
          (outer_case_clauses
            (rhs_of "parser_explicit_fallback_structural_matrix")) = 2)
    val _ =
      assert "complete structural matrices retained undefined fallbacks"
        (List.all
          (fn name =>
            count_constant \<^const_name>\<open>undefined\<close>
              (rhs_of name) = 0)
          ["parser_four_axis_structural_matrix",
           "parser_small_structural_matrix",
           "parser_closed_structural_matrix",
           "parser_structural_or_matrix",
           "parser_explicit_fallback_structural_matrix",
           "parser_effectful_structural_matrix"])
    val _ =
      assert "partial structural matrix lost its terminal fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          (rhs_of "parser_partial_structural_matrix") > 0)

    val open_b1 = rhs_of "parser_nested_registered_nullary_open"
    val SOME (nested_case, _) =
      Case_Translation.lookup_by_constr_permissive ctxt
        (dest_Const_name \<^term>\<open>ParserPrimaryStatus\<close>,
         fastype_of \<^term>\<open>ParserPrimaryStatus\<close>)
    val nested_case_name =
      (case Term.head_of nested_case of
         Const (name, _) => name
       | _ => error "expected nested constructor case constant")
    val _ =
      assert "open B1 fixture retained a constructor equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> open_b1 = 0)
    val _ =
      assert "open B1 fixture lost its nested constructor case"
        (count_constant nested_case_name open_b1 > 0)
    val _ =
      assert "open B1 fixture duplicated its scrutinee bind"
        (count_constant \<^const_name>\<open>bind\<close> open_b1 = 1)
    val _ =
      assert "open B1 fixture retained synthetic variables or frees"
        (null (Term.add_vars open_b1 []) andalso
         null (Term.add_frees open_b1 []))

    val metadata_free_switch =
      rhs_of "parser_metadata_free_switch"
    val metadata_free_case =
      rhs_of "parser_metadata_free_case"
    val literal_switch =
      rhs_of "parser_literal_switch"
    val _ =
      assert "metadata-free registered values lost switch lowering"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          metadata_free_switch = 1)
    val _ =
      assert "metadata-free registered values lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          metadata_free_case = 1)
    val _ =
      assert "integer literals lost switch lowering"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          literal_switch = 1)

    val registered_singleton =
      rhs_of "parser_nested_registered_singleton"
    val native_singleton =
      rhs_of "parser_nested_native_singleton"
    val _ =
      assert "registered singleton retained a redundant nested fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          registered_singleton = 0)
    val _ =
      assert "native singleton retained a redundant nested fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          native_singleton = 0)
    val _ =
      assert "singleton payloads were converted to equality tests"
        (count_constant \<^const_name>\<open>urust_eq\<close>
            registered_singleton = 0 andalso
         count_constant \<^const_name>\<open>urust_eq\<close>
            native_singleton = 0)

    val _ =
      assert "partial and rich nested patterns lost necessary fallbacks"
        (List.all
          (fn name =>
            count_constant \<^const_name>\<open>undefined\<close>
              (rhs_of name) > 0)
          ["parser_nested_partial_constructor_alias",
           "parser_nested_value_fallback",
           "parser_nested_range_fallback"])
  in
    val _ = ()
  end
\<close>

section\<open>Resolution and term-shape audit\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val theory = Proof_Context.theory_of ctxt

    fun assert message condition =
      if condition then () else error ("constructor matching audit: " ^ message)

    fun count_constant expected term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = expected then Integer.add 1 else I
          | _ => I)
        term 0

    fun equation_of name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of
      |> Logic.dest_equals

    fun rhs_of name = snd (equation_of name)

    fun constant_name term =
      (case Term.head_of term of
         Const (name, _) => name
       | _ => error "constructor matching audit: expected constant")

    fun make_path text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME (URust_AST.UE_Path path) => path
       | _ => error ("constructor matching audit: expected path " ^ quote text))

    fun resolve text =
      let
        val path = make_path text
        val resolver =
          URust_Resolution.make_constructor_resolver ctxt
            (URust_AST.path_position path)
      in
        the (URust_Resolution.resolve_constructor ctxt resolver path)
      end

    val native_payload = resolve "ParserNative::Payload"
    val native_family =
      the (URust_Resolution.constructor_family native_payload)
    val word_path = make_path "ParserWordFamily::Second"
    val word_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (URust_AST.path_position word_path)
    val word_second = resolve "ParserWordFamily::Second"
    val word_family =
      the (URust_Resolution.constructor_family word_second)
    val bare_word_second = resolve "ParserWordSecond"
    val bare_word_family =
      the (URust_Resolution.constructor_family bare_word_second)
    val single_word_only =
      resolve "ParserSingleWordFamily::ParserWordOnly"
    val single_word_family =
      the (URust_Resolution.constructor_family single_word_only)
    val (word_case, word_case_members) =
      the
        (Case_Translation.lookup_by_constr_permissive ctxt
          (dest_Const_name \<^term>\<open>ParserWordSecond\<close>,
           fastype_of \<^term>\<open>ParserWordSecond\<close>))
    val raw_path = make_path "ParserRaw::First"
    val raw_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (URust_AST.path_position raw_path)

    val (_, native_members) = native_family
    val (_, word_members) = word_family
    val (_, bare_word_members) = bare_word_family
    val (_, single_word_members) = single_word_family
    val word_case_name =
      dest_Const_name \<^term>\<open>case_parser_word_family\<close>
    val single_word_case_name =
      dest_Const_name \<^term>\<open>case_parser_single_word_family\<close>
    val _ =
      assert "custom enum positional arity was not recovered"
        (URust_Resolution.constructor_arity native_payload = 1)
    val _ =
      assert "custom enum unexpectedly acquired Ctr_Sugar metadata"
        (is_none
          (Ctr_Sugar.ctr_sugar_of ctxt
            (fst (dest_Type \<^typ>\<open>parser_native_case\<close>))))
    val _ =
      assert "custom enum is not an authentic Code constructor"
        (Code.is_constr theory
          (dest_Const_name \<^term>\<open>ParserNativePayload\<close>))
    val _ =
      assert "custom enum family order changed"
        (map constant_name native_members =
          map constant_name
            [\<^term>\<open>ParserNativeEmpty\<close>,
             \<^term>\<open>ParserNativePayload\<close>,
             \<^term>\<open>ParserNativeOther\<close>])
    val _ =
      assert "simple_word_enum family order changed"
        (map constant_name word_members =
          map constant_name
            [\<^term>\<open>ParserWordFirst\<close>,
             \<^term>\<open>ParserWordSecond\<close>,
             \<^term>\<open>ParserWordThird\<close>])
    val _ =
      assert "bare simple_word_enum constructor identity changed"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term bare_word_second,
           \<^term>\<open>ParserWordSecond\<close>))
    val _ =
      assert "bare simple_word_enum family order changed"
        (map constant_name bare_word_members =
          map constant_name word_members)
    val _ =
      assert "simple_word_enum native case registration changed"
        (constant_name word_case = word_case_name andalso
          map constant_name word_case_members =
            map constant_name
              [\<^term>\<open>ParserWordFirst\<close>,
               \<^term>\<open>ParserWordSecond\<close>,
               \<^term>\<open>ParserWordThird\<close>])
    val _ =
      assert "simple_word_enum was not classified as a registered constructor"
        (URust_Resolution.classify_registered_literal ctxt
          word_resolver word_path =
            URust_Resolution.Registered_Constructor_Literal)
    val _ =
      assert "simple_word_enum constructor arity changed"
        (URust_Resolution.constructor_arity word_second = 0)
    val _ =
      assert "simple_word_enum unexpectedly became a Code constructor"
        (not (Code.is_constr theory
          (dest_Const_name \<^term>\<open>ParserWordSecond\<close>)))
    val _ =
      assert "singleton simple_word_enum family changed"
        (map constant_name single_word_members =
          [constant_name \<^term>\<open>ParserWordOnly\<close>])
    val _ =
      assert "metadata-free value acquired constructor identity"
        (URust_Resolution.classify_registered_literal ctxt
          raw_resolver raw_path =
            URust_Resolution.Registered_Value_Literal)
    val _ =
      assert "metadata-free value unexpectedly acquired native case metadata"
        (is_none
          (Case_Translation.lookup_by_constr_permissive ctxt
            (dest_Const_name \<^term>\<open>ParserRawFirst\<close>,
             fastype_of \<^term>\<open>ParserRawFirst\<close>)))

    val metadata_free = rhs_of "parser_metadata_free_switch"
    val _ =
      assert "metadata-free values did not use switch lowering"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          metadata_free = 1)
    val _ =
      assert "metadata-free switch duplicated its scrutinee"
        (count_constant \<^const_name>\<open>parser_raw_scrutinee\<close>
          metadata_free = 1)

    val word_exhaustive =
      rhs_of "parser_word_family_exhaustive"
    val word_partial =
      rhs_of "parser_word_family_partial"
    val word_guarded =
      rhs_of "parser_word_family_guarded"
    val word_matches =
      rhs_of "parser_word_family_matches"
    val word_nested =
      rhs_of "parser_word_family_nested"
    val single_word_exhaustive =
      rhs_of "parser_single_word_family_exhaustive"
    val _ =
      assert "exhaustive simple_word_enum match lost its case combinator"
        (count_constant word_case_name word_exhaustive = 1)
    val _ =
      assert "exhaustive simple_word_enum match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          word_exhaustive = 0)
    val _ =
      assert "exhaustive simple_word_enum match used equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          word_exhaustive = 0)
    val _ =
      assert "partial simple_word_enum match lost its case combinator"
        (count_constant word_case_name word_partial = 1)
    val _ =
      assert "partial simple_word_enum match lost its unmatched fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          word_partial > 0)
    val _ =
      assert "partial simple_word_enum match used equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          word_partial = 0)
    val _ =
      assert "guarded simple_word_enum match lost structural lowering"
        (count_constant word_case_name word_guarded > 0)
    val _ =
      assert "guarded simple_word_enum match used equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          word_guarded = 0)
    val _ =
      assert "simple_word_enum matches! lost structural lowering"
        (count_constant word_case_name word_matches = 1)
    val _ =
      assert "simple_word_enum matches! retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          word_matches = 0)
    val _ =
      assert "nested simple_word_enum match lost its case combinator"
        (count_constant word_case_name word_nested = 1)
    val _ =
      assert "nested exhaustive simple_word_enum match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          word_nested = 0)
    val _ =
      assert "nested simple_word_enum match used equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          word_nested = 0)
    val _ =
      assert "singleton simple_word_enum match lost its case combinator"
        (count_constant single_word_case_name
          single_word_exhaustive = 1)
    val _ =
      assert "singleton simple_word_enum match retained undefined"
        (count_constant \<^const_name>\<open>undefined\<close>
          single_word_exhaustive = 0)

    val (nested_lhs, nested) =
      equation_of "parser_nested_registered_nullary"
    val (_, nested_lhs_arguments) = Term.strip_comb nested_lhs
    val _ =
      assert "nested fixture acquired an unintended definition argument"
        (null nested_lhs_arguments)
    val _ =
      assert "nested fixture acquired an unintended function type"
        (null (binder_types (fastype_of nested_lhs)))
    val _ =
      assert "nested fixture retained a schematic term variable"
        (null (Term.add_vars nested []))
    val _ =
      assert "nested fixture retained a local free binder"
        (null (Term.add_frees nested []))
    val SOME (inner_case, _) =
      Case_Translation.lookup_by_constr_permissive ctxt
        (dest_Const_name \<^term>\<open>ParserPrimaryStatus\<close>,
         fastype_of \<^term>\<open>ParserPrimaryStatus\<close>)
    val inner_case_name = constant_name inner_case
    val result_case_name =
      (case Ctr_Sugar.ctr_sugar_of ctxt
          (fst (dest_Type
            \<^typ>\<open>(unit, parser_nested_status) result\<close>)) of
         SOME {casex, ...} => constant_name casex
       | NONE => error "constructor matching audit: missing result case sugar")
    fun result_case_branches term =
      let
        fun seek candidate =
          (case Term.strip_comb candidate of
             (Const (name, _), [ok_branch, err_branch, _]) =>
               if name = result_case_name
               then SOME (ok_branch, err_branch)
               else seek_arguments candidate
           | _ => seek_arguments candidate)
        and seek_arguments (left $ right) =
              (case seek left of
                 SOME result => SOME result
               | NONE => seek right)
          | seek_arguments (Abs (_, _, body)) = seek body
          | seek_arguments _ = NONE
      in
        (case seek term of
           SOME branches => branches
         | NONE =>
             error
               "constructor matching audit: missing outer result case")
      end
    val _ =
      assert "nested normalization lost the enclosing authentic case"
        (count_constant result_case_name nested > 0)
    val _ =
      assert "nested exact nullary constructor lost its native inner case"
        (count_constant inner_case_name nested > 0)
    val _ =
      assert "nested exact nullary constructor retained an equality guard"
        (count_constant \<^const_name>\<open>urust_eq\<close> nested = 0)

    fun checked_structural_term name =
      let
        val rhs = rhs_of name
        val _ =
          assert (name ^ " retained a constructor equality")
            (count_constant \<^const_name>\<open>urust_eq\<close> rhs = 0)
        val _ =
          assert (name ^ " lost structural constructor matching")
            (count_constant inner_case_name rhs > 0)
        val _ =
          assert (name ^ " retained schematic variables")
            (null (Term.add_vars rhs []))
        val _ =
          assert (name ^ " retained local free binders")
            (null (Term.add_frees rhs []))
      in rhs end

    fun instantiate_definition rhs arguments =
      Envir.beta_eta_contract
        (Term.list_comb (rhs, arguments))

    fun outer_case_selector rhs =
      let
        val (parameters, body) = Term.strip_abs rhs
        val names =
          Name.variants Name.context
            (map (fn (name, _) =>
              if name = "" then "parameter" else name)
              parameters)
        val frees =
          map Free (names ~~ map snd parameters)
        val body' = subst_bounds (rev frees, body)
      in
        (case body' of
           Const (name, _) $ _ $ continuation =>
             if name = \<^const_name>\<open>bind\<close>
             then snd (Term.dest_abs_global continuation)
             else
               error
                 "constructor matching audit: expected outer scrutinee bind"
         | _ =>
             error
               "constructor matching audit: expected outer scrutinee bind")
      end

    fun outer_case_clauses rhs =
      (case Case_Translation.strip_case ctxt false
          (outer_case_selector rhs) of
         SOME (_, clauses) => clauses
       | NONE =>
           error
             "constructor matching audit: expected outer case")

    val status_constructor_names =
      map constant_name
        [\<^term>\<open>ParserPrimaryStatus\<close>,
         \<^term>\<open>ParserSecondaryStatus\<close>,
         \<^term>\<open>ParserTertiaryStatus\<close>]

    fun selected_constructors selected term =
      Term.fold_aterms
        (fn Const (name, _) =>
              if member (op =) selected name
              then cons name
              else I
          | _ => I)
        term []
      |> rev

    fun structural_constructor_rows selected rhs =
      map (selected_constructors selected o fst)
        (outer_case_clauses rhs)

    fun structural_status_rows rhs =
      structural_constructor_rows status_constructor_names rhs

    val ordered =
      checked_structural_term
        "parser_nested_registered_ordered"
    val ordered_or =
      checked_structural_term
        "parser_nested_registered_or_ordered"
    val guarded_order =
      checked_structural_term
        "parser_nested_registered_guard_order"
    val global_source_order =
      checked_structural_term
        "parser_nested_global_source_order"
    val overlapping_tuple =
      checked_structural_term
        "parser_nested_overlapping_tuple"
    val (overlapping_or_lhs, overlapping_or) =
      equation_of "parser_nested_overlapping_or_alternatives"
    val (guarded_or_lhs, guarded_or) =
      equation_of "parser_nested_guarded_or_alternatives"
    val (guarded_or_reversed_lhs, guarded_or_reversed) =
      equation_of "parser_nested_guarded_or_alternatives_reversed"
    val (guarded_or_binder_lhs, guarded_or_binder) =
      equation_of "parser_nested_guarded_or_binder"
    val (differing_binding_lhs, differing_binding) =
      equation_of "parser_nested_guarded_or_differing_binding"
    val (alias_source_guard_lhs, alias_source_guard) =
      equation_of "parser_nested_alias_source_guard_match"
    val (alias_binder_guard_lhs, alias_binder_guard) =
      equation_of "parser_nested_guarded_or_alias_binder"
    val (different_depth_lhs, different_depth) =
      equation_of "parser_nested_guarded_different_depth_alias"
    val (different_depth_reversed_lhs,
         different_depth_reversed) =
      equation_of
        "parser_nested_guarded_different_depth_alias_reversed"
    val (exhaustive_lhs, exhaustive) =
      equation_of "parser_nested_exhaustive_outer_shapes"
    val (exhaustive_guarded_lhs, exhaustive_guarded) =
      equation_of "parser_nested_exhaustive_outer_shapes_guarded"
    val (root_unguarded_left_lhs, root_unguarded_left) =
      equation_of "parser_root_suffix_unguarded_left"
    val (root_unguarded_right_lhs, root_unguarded_right) =
      equation_of "parser_root_suffix_unguarded_right"
    val (root_guarded_left_lhs, root_guarded_left) =
      equation_of "parser_root_suffix_guarded_left"
    val (root_guarded_right_lhs, root_guarded_right) =
      equation_of "parser_root_suffix_guarded_right"
    val (recursive_unguarded_left_lhs,
         recursive_unguarded_left) =
      equation_of "parser_recursive_coverage_unguarded_left"
    val (recursive_unguarded_right_lhs,
         recursive_unguarded_right) =
      equation_of "parser_recursive_coverage_unguarded_right"
    val (recursive_guarded_left_lhs,
         recursive_guarded_left) =
      equation_of "parser_recursive_coverage_guarded_left"
    val (recursive_guarded_right_lhs,
         recursive_guarded_right) =
      equation_of "parser_recursive_coverage_guarded_right"
    val guarded_or_instantiated =
      instantiate_definition guarded_or
        [\<^term>\<open>parser_nested_overlap_scrutinee\<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val guarded_or_reversed_instantiated =
      instantiate_definition guarded_or_reversed
        [\<^term>\<open>
            parser_nested_or_overlap_reversed_second_scrutinee
          \<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val guarded_or_binder_instantiated =
      instantiate_definition guarded_or_binder
        [\<^term>\<open>parser_nested_overlap_scrutinee\<close>]
    val alias_binder_guard_instantiated =
      instantiate_definition alias_binder_guard
        [\<^term>\<open>parser_nested_alias_binder_first_scrutinee\<close>,
         \<^term>\<open>Err ParserPrimaryStatus\<close>,
         \<^term>\<open>Err ParserTertiaryStatus\<close>]
    val different_depth_instantiated =
      instantiate_definition different_depth
        [\<^term>\<open>parser_nested_different_depth_both_scrutinee\<close>,
         \<^term>\<open>Err ParserSecondaryStatus\<close>,
         \<^term>\<open>Err ParserPrimaryStatus\<close>]
    val different_depth_reversed_instantiated =
      instantiate_definition different_depth_reversed
        [\<^term>\<open>parser_nested_different_depth_both_scrutinee\<close>,
         \<^term>\<open>Err ParserPrimaryStatus\<close>,
         \<^term>\<open>Err ParserSecondaryStatus\<close>]
    val exhaustive_guarded_instantiated =
      instantiate_definition exhaustive_guarded
        [\<^term>\<open>
            parser_nested_exhaustive_first_miss_scrutinee
          \<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val root_unguarded_left_instantiated =
      instantiate_definition root_unguarded_left
        [\<^term>\<open>parser_nested_or_overlap_reverse_scrutinee\<close>]
    val root_unguarded_right_instantiated =
      instantiate_definition root_unguarded_right
        [\<^term>\<open>parser_nested_or_overlap_later_scrutinee\<close>]
    val root_guarded_left_instantiated =
      instantiate_definition root_guarded_left
        [\<^term>\<open>parser_nested_or_overlap_reverse_scrutinee\<close>,
         \<^term>\<open>parser_nested_source_guard_false\<close>]
    val root_guarded_right_instantiated =
      instantiate_definition root_guarded_right
        [\<^term>\<open>parser_nested_or_overlap_later_scrutinee\<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val recursive_unguarded_left_instantiated =
      instantiate_definition recursive_unguarded_left
        [\<^term>\<open>parser_recursive_coverage_fallback\<close>]
    val recursive_unguarded_right_instantiated =
      instantiate_definition recursive_unguarded_right
        [\<^term>\<open>parser_recursive_coverage_fallback\<close>]
    val recursive_guarded_left_instantiated =
      instantiate_definition recursive_guarded_left
        [\<^term>\<open>parser_recursive_coverage_left_match\<close>,
         \<^term>\<open>parser_nested_source_guard_false\<close>]
    val recursive_guarded_right_instantiated =
      instantiate_definition recursive_guarded_right
        [\<^term>\<open>parser_recursive_coverage_right_match\<close>,
         \<^term>\<open>parser_nested_source_guard_true\<close>]
    val (global_ok_branch, global_err_branch) =
      result_case_branches global_source_order
    val alias_wildcard =
      checked_structural_term
        "parser_nested_alias_wildcard"
    val alias_binder =
      checked_structural_term
        "parser_nested_alias_binder"
    val (alias_wildcard_lhs, _) =
      equation_of "parser_nested_alias_wildcard"
    val (alias_binder_lhs, _) =
      equation_of "parser_nested_alias_binder"
    val (global_source_order_lhs, _) =
      equation_of "parser_nested_global_source_order"
    val (overlapping_tuple_lhs, _) =
      equation_of "parser_nested_overlapping_tuple"
    val (_, alias_wildcard_arguments) =
      Term.strip_comb alias_wildcard_lhs
    val (_, alias_binder_arguments) =
      Term.strip_comb alias_binder_lhs
    val (_, global_source_order_arguments) =
      Term.strip_comb global_source_order_lhs
    val (_, overlapping_tuple_arguments) =
      Term.strip_comb overlapping_tuple_lhs
    val (_, overlapping_or_arguments) =
      Term.strip_comb overlapping_or_lhs
    val (_, guarded_or_arguments) =
      Term.strip_comb guarded_or_lhs
    val (_, guarded_or_reversed_arguments) =
      Term.strip_comb guarded_or_reversed_lhs
    val (_, guarded_or_binder_arguments) =
      Term.strip_comb guarded_or_binder_lhs
    val (_, differing_binding_arguments) =
      Term.strip_comb differing_binding_lhs
    val (_, alias_source_guard_arguments) =
      Term.strip_comb alias_source_guard_lhs
    val (_, alias_binder_guard_arguments) =
      Term.strip_comb alias_binder_guard_lhs
    val (_, different_depth_arguments) =
      Term.strip_comb different_depth_lhs
    val (_, different_depth_reversed_arguments) =
      Term.strip_comb different_depth_reversed_lhs
    val (_, exhaustive_arguments) =
      Term.strip_comb exhaustive_lhs
    val (_, exhaustive_guarded_arguments) =
      Term.strip_comb exhaustive_guarded_lhs
    fun audit_product_case_closure name rhs =
      let
        fun is_product_type (Type (type_name, _)) =
              type_name = \<^type_name>\<open>prod\<close>
          | is_product_type _ = false
        fun is_wildcard_pattern (Free _) = true
          | is_wildcard_pattern (Var _) = true
          | is_wildcard_pattern _ = false
        fun close_bounds bound_types term =
          subst_bounds
            (map_index
              (fn (index, typ) =>
                Free
                  ("_case_audit_" ^ string_of_int index,
                   typ))
              bound_types,
             term)
        fun inspect bound_types term =
          let
            val closed_term =
              close_bounds bound_types term
            val _ =
              (case Case_Translation.strip_case ctxt false
                  closed_term of
                 SOME (scrutinee, clauses) =>
                   if is_product_type (fastype_of scrutinee)
                   then
                     let
                       val wildcard_clauses =
                         filter
                           (is_wildcard_pattern o fst)
                           clauses
                     in
                       assert
                         (name ^
                           " emitted a redundant product wildcard")
                         (null wildcard_clauses)
                     end
                   else ()
               | NONE => ())
          in
            (case term of
               left $ right =>
                 (inspect bound_types left;
                  inspect bound_types right)
             | Abs (_, typ, body) =>
                 inspect (typ :: bound_types) body
             | _ => ())
          end
      in inspect [] rhs end
    fun audit_total_root_suffix
        name lhs rhs expected_argument_types instantiated
        scrutinee_name source_guard_name =
      let
        val (_, arguments) = Term.strip_comb lhs
        val clauses = outer_case_clauses rhs
        val _ =
          assert (name ^ " changed its definition head")
            (null arguments)
        val _ =
          assert (name ^ " changed its argument types")
            (binder_types (fastype_of lhs) =
              expected_argument_types)
        val _ =
          assert (name ^ " retained schematic variables")
            (null (Term.add_vars rhs []))
        val _ =
          assert (name ^ " retained local free binders")
            (null (Term.add_frees rhs []))
        val _ =
          assert (name ^ " duplicated its outer scrutinee bind")
            (count_constant \<^const_name>\<open>bind\<close> rhs = 1)
        val _ =
          assert (name ^ " reevaluated its instantiated scrutinee")
            (count_constant scrutinee_name instantiated = 1)
        val _ =
          assert
            (name ^ " lost its outer structural clauses: " ^
              string_of_int (length clauses))
            (not (null clauses))
        val _ =
          assert (name ^ " retained an undefined fallback")
            (count_constant \<^const_name>\<open>undefined\<close>
              rhs = 0)
        val _ =
          (case source_guard_name of
             NONE => ()
           | SOME guard_name =>
               assert (name ^ " duplicated or lost its source guard")
                 (count_constant guard_name instantiated = 1))
      in () end
    val unguarded_root_argument_types =
      [\<^typ>\<open>parser_nested_overlap_input\<close>]
    val guarded_root_argument_types =
      [\<^typ>\<open>parser_nested_overlap_input\<close>,
       \<^typ>\<open>
         (nat, bool, unit, unit, unit, unit) expression
       \<close>]
    val recursive_unguarded_argument_types =
      [\<^typ>\<open>parser_recursive_coverage_input\<close>]
    val recursive_guarded_argument_types =
      [\<^typ>\<open>parser_recursive_coverage_input\<close>,
       \<^typ>\<open>
         (nat, bool, unit, unit, unit, unit) expression
       \<close>]
    val _ =
      audit_total_root_suffix
        "left unguarded total-root fallback"
        root_unguarded_left_lhs root_unguarded_left
        unguarded_root_argument_types
        root_unguarded_left_instantiated
        \<^const_name>\<open>parser_nested_or_overlap_reverse_scrutinee\<close>
        NONE
    val _ =
      audit_total_root_suffix
        "right unguarded total-root fallback"
        root_unguarded_right_lhs root_unguarded_right
        unguarded_root_argument_types
        root_unguarded_right_instantiated
        \<^const_name>\<open>parser_nested_or_overlap_later_scrutinee\<close>
        NONE
    val _ =
      audit_total_root_suffix
        "left guarded total-root fallback"
        root_guarded_left_lhs root_guarded_left
        guarded_root_argument_types
        root_guarded_left_instantiated
        \<^const_name>\<open>parser_nested_or_overlap_reverse_scrutinee\<close>
        (SOME
          \<^const_name>\<open>parser_nested_source_guard_false\<close>)
    val _ =
      audit_total_root_suffix
        "right guarded total-root fallback"
        root_guarded_right_lhs root_guarded_right
        guarded_root_argument_types
        root_guarded_right_instantiated
        \<^const_name>\<open>parser_nested_or_overlap_later_scrutinee\<close>
        (SOME
          \<^const_name>\<open>parser_nested_source_guard_true\<close>)
    val _ =
      audit_product_case_closure
        "left unguarded recursive total-root fallback"
        recursive_unguarded_left
    val _ =
      audit_product_case_closure
        "right unguarded recursive total-root fallback"
        recursive_unguarded_right
    val _ =
      audit_product_case_closure
        "left guarded recursive total-root fallback"
        recursive_guarded_left
    val _ =
      audit_product_case_closure
        "right guarded recursive total-root fallback"
        recursive_guarded_right
    val _ =
      audit_total_root_suffix
        "left unguarded recursive total-root fallback"
        recursive_unguarded_left_lhs
        recursive_unguarded_left
        recursive_unguarded_argument_types
        recursive_unguarded_left_instantiated
        \<^const_name>\<open>parser_recursive_coverage_fallback\<close>
        NONE
    val _ =
      audit_total_root_suffix
        "right unguarded recursive total-root fallback"
        recursive_unguarded_right_lhs
        recursive_unguarded_right
        recursive_unguarded_argument_types
        recursive_unguarded_right_instantiated
        \<^const_name>\<open>parser_recursive_coverage_fallback\<close>
        NONE
    val _ =
      audit_total_root_suffix
        "left guarded recursive total-root fallback"
        recursive_guarded_left_lhs
        recursive_guarded_left
        recursive_guarded_argument_types
        recursive_guarded_left_instantiated
        \<^const_name>\<open>parser_recursive_coverage_left_match\<close>
        (SOME
          \<^const_name>\<open>parser_nested_source_guard_false\<close>)
    val _ =
      audit_total_root_suffix
        "right guarded recursive total-root fallback"
        recursive_guarded_right_lhs
        recursive_guarded_right
        recursive_guarded_argument_types
        recursive_guarded_right_instantiated
        \<^const_name>\<open>parser_recursive_coverage_right_match\<close>
        (SOME
          \<^const_name>\<open>parser_nested_source_guard_true\<close>)
    val _ =
      assert "alias/wildcard fixture acquired an unintended definition argument"
        (null alias_wildcard_arguments)
    val _ =
      assert "alias/wildcard fixture acquired an unintended function type"
        (null (binder_types (fastype_of alias_wildcard_lhs)))
    val _ =
      assert "alias/binder fixture acquired an unintended definition argument"
        (null alias_binder_arguments)
    val _ =
      assert "alias/binder fixture acquired an unintended function type"
        (null (binder_types (fastype_of alias_binder_lhs)))
    val _ =
      assert "global source-order fixture acquired an unintended definition argument"
        (null global_source_order_arguments)
    val _ =
      assert "global source-order fixture acquired an unintended function type"
        (null (binder_types (fastype_of global_source_order_lhs)))
    val _ =
      assert "overlapping tuple fixture acquired an unintended definition argument"
        (null overlapping_tuple_arguments)
    val _ =
      assert "overlapping tuple fixture acquired an unintended function type"
        (null (binder_types (fastype_of overlapping_tuple_lhs)))
    val _ =
      assert "overlapping or-pattern fixture changed its definition head"
        (null overlapping_or_arguments)
    val _ =
      assert "overlapping or-pattern fixture acquired an unintended argument"
        (binder_types (fastype_of overlapping_or_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>])
    val _ =
      assert "overlapping or-pattern fixture retained schematic variables"
        (null (Term.add_vars overlapping_or []))
    val _ =
      assert "overlapping or-pattern fixture retained local free binders"
        (null (Term.add_frees overlapping_or []))
    val _ =
      assert "overlapping or-pattern fixture evaluated its scrutinee more than once"
        (count_constant \<^const_name>\<open>bind\<close>
          overlapping_or = 1)
    val _ =
      assert "guarded or-pattern fixture changed its definition head"
        (null guarded_or_arguments)
    val _ =
      assert "guarded or-pattern fixture changed its argument types"
        (binder_types (fastype_of guarded_or_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>,
           \<^typ>\<open>
             (nat, bool, unit, unit, unit, unit) expression
           \<close>])
    val _ =
      assert "guarded or-pattern fixture retained schematic variables"
        (null (Term.add_vars guarded_or []))
    val _ =
      assert "guarded or-pattern fixture retained local free binders"
        (null (Term.add_frees guarded_or []))
    val _ =
      assert "guarded or-pattern fixture evaluated its scrutinee more than once"
        (count_constant \<^const_name>\<open>bind\<close>
          guarded_or = 1)
    val _ =
      assert "reversed guarded or-pattern fixture changed its definition head"
        (null guarded_or_reversed_arguments)
    val _ =
      assert "reversed guarded or-pattern fixture retained schematic variables"
        (null (Term.add_vars guarded_or_reversed []))
    val _ =
      assert "reversed guarded or-pattern fixture retained local free binders"
        (null (Term.add_frees guarded_or_reversed []))
    val _ =
      assert "reversed guarded or-pattern fixture evaluated its scrutinee more than once"
        (count_constant \<^const_name>\<open>bind\<close>
          guarded_or_reversed = 1)
    val _ =
      assert "binder-dependent guard fixture changed its definition head"
        (null guarded_or_binder_arguments)
    val _ =
      assert "binder-dependent guard fixture changed its argument type"
        (binder_types (fastype_of guarded_or_binder_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>])
    val _ =
      assert "binder-dependent guard fixture retained schematic variables"
        (null (Term.add_vars guarded_or_binder []))
    val _ =
      assert "binder-dependent guard fixture retained local free binders"
        (null (Term.add_frees guarded_or_binder []))
    val _ =
      assert "binder-dependent guard fixture evaluated its scrutinee more than once"
        (count_constant \<^const_name>\<open>bind\<close>
          guarded_or_binder = 1)
    val _ =
      assert "differing-binding guard fixture changed its definition head"
        (null differing_binding_arguments)
    val _ =
      assert "differing-binding guard fixture changed its argument type"
        (binder_types (fastype_of differing_binding_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>])
    val _ =
      assert "differing-binding guard fixture retained schematic variables"
        (null (Term.add_vars differing_binding []))
    val _ =
      assert "differing-binding guard fixture retained local free binders"
        (null (Term.add_frees differing_binding []))
    val _ =
      assert "differing-binding guard fixture lost its scoped guard"
        (count_constant
          \<^const_name>\<open>parser_nested_binder_source_guard_inhomogeneous\<close>
          differing_binding > 0)
    val _ =
      assert "alias source-guard fixture changed its definition head"
        (null alias_source_guard_arguments)
    val _ =
      assert "alias source-guard fixture changed its argument types"
        (binder_types (fastype_of alias_source_guard_lhs) =
          [\<^typ>\<open>(unit, parser_nested_status) result\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>])
    val _ =
      assert "alias source-guard fixture retained schematic variables"
        (null (Term.add_vars alias_source_guard []))
    val _ =
      assert "alias source-guard fixture retained local free binders"
        (null (Term.add_frees alias_source_guard []))
    val _ =
      assert "alias source-guard fixture lost its scoped alias use"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_source_guard\<close>
          alias_source_guard > 0)
    val _ =
      assert "alias/binder guard fixture changed its definition head"
        (null alias_binder_guard_arguments)
    val _ =
      assert "alias/binder guard fixture changed its argument types"
        (binder_types (fastype_of alias_binder_guard_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>])
    val _ =
      assert "alias/binder guard fixture retained schematic variables"
        (null (Term.add_vars alias_binder_guard []))
    val _ =
      assert "alias/binder guard fixture retained local free binders"
        (null (Term.add_frees alias_binder_guard []))
    val _ =
      assert "alias/binder guard fixture lost its scoped guard"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_source_guard\<close>
          alias_binder_guard > 0)
    val _ =
      assert "alias/binder guard fixture reevaluated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_first_scrutinee\<close>
          alias_binder_guard_instantiated = 1)
    val _ =
      assert "different-depth alias fixture changed its definition head"
        (null different_depth_arguments)
    val _ =
      assert "different-depth alias fixture changed its argument types"
        (binder_types (fastype_of different_depth_lhs) =
          [\<^typ>\<open>parser_nested_different_depth_input\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>])
    val _ =
      assert "different-depth alias fixture retained schematic variables"
        (null (Term.add_vars different_depth []))
    val _ =
      assert "different-depth alias fixture retained local free binders"
        (null (Term.add_frees different_depth []))
    val _ =
      assert "different-depth alias fixture lost its scoped guard"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_source_guard\<close>
          different_depth > 0)
    val _ =
      assert "different-depth alias fixture reevaluated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_different_depth_both_scrutinee\<close>
          different_depth_instantiated = 1)
    val _ =
      assert
        ("different-depth alias fixture lost its outer structural clauses: " ^
          string_of_int
            (length (outer_case_clauses different_depth)))
        (not (null (outer_case_clauses different_depth)))
    val _ =
      assert
        "reversed different-depth alias fixture changed its definition head"
        (null different_depth_reversed_arguments)
    val _ =
      assert
        "reversed different-depth alias fixture changed its argument types"
        (binder_types (fastype_of different_depth_reversed_lhs) =
          [\<^typ>\<open>parser_nested_different_depth_input\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>,
           \<^typ>\<open>(unit, parser_nested_status) result\<close>])
    val _ =
      assert
        "reversed different-depth alias fixture retained schematic variables"
        (null (Term.add_vars different_depth_reversed []))
    val _ =
      assert
        "reversed different-depth alias fixture retained local free binders"
        (null (Term.add_frees different_depth_reversed []))
    val _ =
      assert
        "reversed different-depth alias fixture lost its scoped guard"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_source_guard\<close>
          different_depth_reversed > 0)
    val _ =
      assert
        "reversed different-depth alias fixture reevaluated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_different_depth_both_scrutinee\<close>
          different_depth_reversed_instantiated = 1)
    val _ =
      assert
        ("reversed different-depth alias fixture lost its outer structural clauses: " ^
          string_of_int
            (length
              (outer_case_clauses different_depth_reversed)))
        (not (null
          (outer_case_clauses different_depth_reversed)))
    val _ =
      assert "exhaustive outer-shape fixture changed its definition head"
        (null exhaustive_arguments)
    val _ =
      assert "exhaustive outer-shape fixture changed its argument type"
        (binder_types (fastype_of exhaustive_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>])
    val _ =
      assert "exhaustive outer-shape fixture retained schematic variables"
        (null (Term.add_vars exhaustive []))
    val _ =
      assert "exhaustive outer-shape fixture retained local free binders"
        (null (Term.add_frees exhaustive []))
    val _ =
      assert "exhaustive outer-shape fixture duplicated its scrutinee"
        (count_constant \<^const_name>\<open>bind\<close>
          exhaustive = 1)
    val _ =
      assert
        ("exhaustive outer-shape fixture changed its structural clause expansion: " ^
          string_of_int (length (outer_case_clauses exhaustive)))
        (length (outer_case_clauses exhaustive) = 9)
    val _ =
      assert "guarded exhaustive outer-shape fixture changed its definition head"
        (null exhaustive_guarded_arguments)
    val _ =
      assert "guarded exhaustive outer-shape fixture changed its argument types"
        (binder_types (fastype_of exhaustive_guarded_lhs) =
          [\<^typ>\<open>parser_nested_overlap_input\<close>,
           \<^typ>\<open>
             (nat, bool, unit, unit, unit, unit) expression
           \<close>])
    val _ =
      assert "guarded exhaustive outer-shape fixture retained schematic variables"
        (null (Term.add_vars exhaustive_guarded []))
    val _ =
      assert "guarded exhaustive outer-shape fixture retained local free binders"
        (null (Term.add_frees exhaustive_guarded []))
    val _ =
      assert "guarded exhaustive outer-shape fixture duplicated its scrutinee"
        (count_constant \<^const_name>\<open>bind\<close>
          exhaustive_guarded = 1)
    val _ =
      assert
        ("guarded exhaustive outer-shape fixture changed its structural clause expansion: " ^
          string_of_int (length
            (outer_case_clauses exhaustive_guarded)))
        (length (outer_case_clauses exhaustive_guarded) = 9)
    val [primary_name, secondary_name, tertiary_name] =
      status_constructor_names
    val ordered_structural_rows =
      [[], [primary_name], [secondary_name], [tertiary_name]]
    val ordered_or_structural_rows =
      [[], [tertiary_name], []]
    val overlapping_tuple_structural_rows =
      [[], [secondary_name], [],
       [primary_name], [primary_name, primary_name],
       [primary_name], [], [secondary_name], []]
    val overlapping_or_structural_rows =
      [[], [secondary_name], [],
       [primary_name], [primary_name, primary_name],
       [primary_name], [secondary_name],
       [secondary_name, secondary_name], [secondary_name],
       [tertiary_name], [tertiary_name, secondary_name],
       [tertiary_name]]
    val exhaustive_structural_rows =
      [[], [secondary_name], [],
       [primary_name], [primary_name, primary_name],
       [primary_name], [], [secondary_name], []]
    val _ =
      assert "separate same-outer alternatives duplicated the outer case"
        (count_constant result_case_name ordered = 1)
    val _ =
      assert "separate same-outer alternatives retained equality guards"
        (count_constant \<^const_name>\<open>urust_eq\<close> ordered = 0)
    val _ =
      assert "separate same-outer structural clause order changed"
        (structural_status_rows ordered =
          ordered_structural_rows)
    val _ =
      assert "or-pattern same-outer alternatives duplicated the outer case"
        (count_constant result_case_name ordered_or = 1)
    val _ =
      assert "or-pattern same-outer alternatives retained equality guards"
        (count_constant \<^const_name>\<open>urust_eq\<close> ordered_or = 0)
    val _ =
      assert "or-pattern structural clause order changed"
        (structural_status_rows ordered_or =
          ordered_or_structural_rows)
    val _ =
      assert "guarded same-shape arm duplicated the outer case"
        (count_constant result_case_name guarded_order = 1)
    val _ =
      assert "guarded same-shape arm duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_guarded_scrutinee\<close>
          guarded_order = 1)
    val _ =
      assert "guarded same-shape arm duplicated its source guard"
        (count_constant
          \<^const_name>\<open>parser_nested_guard_marker\<close>
          guarded_order = 1)
    val _ =
      assert "guarded same-shape arm retained a constructor equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          guarded_order = 0)
    val _ =
      assert "guarded same-shape arm lost its nested constructor case"
        (count_constant inner_case_name guarded_order > 0)
    val _ =
      assert "global source-order fixture duplicated the outer case"
        (count_constant result_case_name global_source_order = 1)
    val _ =
      assert "global source-order fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_scrutinee\<close>
          global_source_order = 1)
    val _ =
      assert "global source-order fixture retained constructor equalities"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          global_source_order = 0)
    val _ =
      assert "global source-order structural clauses changed order"
        (structural_status_rows global_source_order =
          ordered_structural_rows)
    val _ =
      assert "global source-order fixture changed guard evaluation count"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_source_order = 3)
    val _ =
      assert "global source-order Ok branch duplicated its source guard"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_ok_branch = 1)
    val _ =
      assert "global source-order Err branch duplicated its source guard"
        (count_constant
          \<^const_name>\<open>parser_nested_interleaved_guard\<close>
          global_err_branch = 2)
    val _ =
      assert "overlapping tuple fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_overlap_scrutinee\<close>
          overlapping_tuple = 1)
    val _ =
      assert "overlapping tuple structural clauses changed order"
        (structural_status_rows overlapping_tuple =
          overlapping_tuple_structural_rows)
    val _ =
      assert "overlapping or-pattern structural clauses changed order"
        (structural_status_rows overlapping_or =
          overlapping_or_structural_rows)
    val _ =
      assert "exhaustive outer-shape structural clauses changed order"
        (structural_status_rows exhaustive =
          exhaustive_structural_rows)
    val _ =
      assert "guarded exhaustive structural clauses changed order"
        (structural_status_rows exhaustive_guarded =
          exhaustive_structural_rows)
    val _ =
      assert "exhaustive outer-shape fallback was removed from continuations"
        (Term.exists_subterm
          (fn term =>
            Term.aconv_untyped
              (term, \<^term>\<open>literal (3 :: nat)\<close>))
          exhaustive)
    val _ =
      assert "guarded exhaustive outer-shape fallback was removed from continuations"
        (Term.exists_subterm
          (fn term =>
            Term.aconv_untyped
              (term, \<^term>\<open>literal (3 :: nat)\<close>))
          exhaustive_guarded)
    val _ =
      assert "a later applicable source arm still terminates at undefined"
        (List.all
          (fn term =>
            count_constant \<^const_name>\<open>undefined\<close>
              term = 0)
          [nested, ordered, ordered_or, guarded_order,
           global_source_order, overlapping_tuple,
           overlapping_or, guarded_or,
           guarded_or_reversed, guarded_or_binder,
           differing_binding, alias_source_guard,
           exhaustive, exhaustive_guarded])
    val _ =
      assert "alias/wildcard fixture duplicated the outer case"
        (count_constant result_case_name alias_wildcard = 1)
    val _ =
      assert "alias/wildcard fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_wild_scrutinee\<close>
          alias_wildcard = 1)
    val _ =
      assert "alias/wildcard fixture retained constructor equalities"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          alias_wildcard = 0)
    val _ =
      assert "alias/wildcard fixture lost its matching alias arm"
        (count_constant \<^const_name>\<open>parser_nested_alias_tag\<close>
          alias_wildcard = 1)
    val _ =
      assert "alias/binder fixture duplicated the outer case"
        (count_constant result_case_name alias_binder = 1)
    val _ =
      assert "alias/binder fixture duplicated its scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_binder_scrutinee\<close>
          alias_binder = 1)
    val _ =
      assert "alias/binder fixture retained constructor equalities"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          alias_binder = 0)
    val _ =
      assert "alias/binder fixture lost its matching alias arm"
        (count_constant
          \<^const_name>\<open>parser_nested_alias_rewrite\<close>
          alias_binder = 1)

    val nested_payload = rhs_of "parser_nested_registered_payload"
    val SOME (native_case, _) =
      Case_Translation.lookup_by_constr_permissive ctxt
        (dest_Const_name \<^term>\<open>ParserNativePayload\<close>,
         fastype_of \<^term>\<open>ParserNativePayload\<close>)
    val native_case_name = constant_name native_case
    val native_payload_name =
      dest_Const_name \<^term>\<open>ParserNativePayload\<close>
    val nested_payload_clauses =
      outer_case_clauses nested_payload
    val option_case_name =
      (case Ctr_Sugar.ctr_sugar_of ctxt
          (fst (dest_Type \<^typ>\<open>parser_native_case option\<close>)) of
         SOME {casex, ...} => constant_name casex
       | NONE =>
           error "constructor matching audit: missing option case sugar")
    val _ =
      assert "argument-bearing registered constructor did not remain directly structural"
        (length nested_payload_clauses = 3 andalso
         List.exists
           (fn (pattern, _) =>
             count_constant native_payload_name pattern = 1)
           nested_payload_clauses)
    val _ =
      assert "argument-bearing nested constructor lost recursive case lowering"
        (count_constant native_case_name nested_payload > 0)
    val _ =
      assert "argument-bearing nested constructor was normalized as equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          nested_payload = 0)

    val mixed = rhs_of "parser_nested_registered_mixed"
    val _ =
      assert "mixed nested alternatives lost the outer option case"
        (count_constant option_case_name mixed > 0)
    val _ =
      assert "mixed nested alternatives lost the native payload case"
        (count_constant native_case_name mixed > 0)
    val _ =
      assert "mixed nested alternatives retained constructor equality"
        (count_constant \<^const_name>\<open>urust_eq\<close> mixed = 0)
    val _ =
      assert "mixed nested alternatives duplicated their scrutinee"
        (count_constant
          \<^const_name>\<open>parser_nested_mixed_scrutinee\<close>
          mixed = 1)
    val _ =
      assert "mixed nested alternatives retained schematic variables"
        (null (Term.add_vars mixed []))
    val _ =
      assert "mixed nested alternatives retained local free binders"
        (null (Term.add_frees mixed []))
    val native_empty_name =
      dest_Const_name \<^term>\<open>ParserNativeEmpty\<close>
    val native_other_name =
      dest_Const_name \<^term>\<open>ParserNativeOther\<close>
    val _ =
      assert "mixed nested structural constructor order changed"
        (structural_constructor_rows
          [native_empty_name, native_payload_name, native_other_name]
          mixed =
         [[], [native_empty_name], [native_payload_name],
          [native_other_name]])

    val ambiguity_path = make_path "Shared"
    val ambiguity_resolver =
      URust_Resolution.make_constructor_resolver ctxt
        (URust_AST.path_position ambiguity_path)
    val ambiguity =
      (URust_Resolution.resolve_constructor ctxt
         ambiguity_resolver ambiguity_path;
       NONE)
      handle ERROR message => SOME message
    val ambiguity_message =
      (case ambiguity of
         SOME message => message
       | NONE =>
           error "constructor matching audit: expected constructor ambiguity")
    val left_name =
      dest_Const_name
        \<^term>\<open>Parser_Test_Fixtures_Left.Shared\<close>
    val right_name =
      dest_Const_name
        \<^term>\<open>Parser_Test_Fixtures_Right.Shared\<close>
    val _ =
      assert "ambiguity diagnostic omitted the left qualified candidate"
        (String.isSubstring left_name ambiguity_message)
    val _ =
      assert "ambiguity diagnostic omitted the right qualified candidate"
        (String.isSubstring right_name ambiguity_message)

    val switch_constructor =
      (Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          "match_switch \<llangle>ParserNativeOther\<rrangle> { \
          \ParserNative::Other \<Rightarrow> (), _ \<Rightarrow> () }");
       NONE)
      handle ERROR message => SOME message
    val _ =
      assert "explicit switch accepted an authentic constructor"
        (case switch_constructor of
           SOME message =>
             String.isSubstring "requires case-pattern lowering" message
         | NONE => false)

    val markup_reports =
      Synchronized.var
        "constructor_matching_native_case_markup"
        ([]: string list)
    fun capture_reports chunks =
      Synchronized.change markup_reports (append chunks)
    val markup_start =
      Position.make0 70 4000 0 "" ""
        "constructor-matching-native-case-markup"
    val markup_source =
      Parser_Lex_Util.positioned_content_source
        ("match \<llangle>ParserNativeOther\<rrangle> { " ^
         "ParserNative::Other \<Rightarrow> (), _ \<Rightarrow> () }")
        markup_start
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
    val markup_text =
      String.concat (Synchronized.value markup_reports)
    val _ =
      assert "native case qualifier lost constructor markup"
        (String.isSubstring Markup.keyword3N markup_text)
    val _ =
      assert "native case markup lost its recovered family identity"
        (String.isSubstring (#1 native_family) markup_text)

    val recovered =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          "match_case \<llangle>ParserNativeOther\<rrangle> { \
          \ParserNative::Other \<Rightarrow> (), _ \<Rightarrow> () }")
    val _ =
      assert "constructor rejection did not recover"
        (count_constant
          (constant_name
            (fst (the
              (Case_Translation.lookup_by_constr_permissive ctxt
                (dest_Const_name \<^term>\<open>ParserNativeOther\<close>,
                 fastype_of \<^term>\<open>ParserNativeOther\<close>)))))
          recovered > 0)
  in
    val _ = ()
  end
\<close>

section\<open> Frontend-shape structural audit \<close>

text\<open>
Guarded case compilation must preserve the established expanded term directly. In
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
           (P_Constr
              (pattern_path, [P_Ident ("value", _)], _),
            call,
            UE_Block (body, _),
            SOME
              (UE_Block
                (UE_Literal
                  (LP_Integer
                    (Integer_Literal ("0", _, _))), _)),
            layout) =>
           (audit_assert "if-let path structure changed"
              (path_named "Some" pattern_path andalso
               call_named "Some" call andalso
               expression_named "value" body);
            audit_assert "if-let span start moved"
              (Position.offset_of (source_span layout) =
                Position.offset_of if_start);
            audit_assert "if-let span end moved"
              (Position.end_offset_of (source_span layout) =
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
           (P_Constr
              (first_pattern_path, [P_Ident ("first", _)], _),
            first_call,
            UE_Block (first_body, _),
            SOME
              (UE_If
                (UE_Literal (LP_Bool (false, _)),
                 UE_Block
                   (UE_Literal
                     (LP_Integer
                       (Integer_Literal ("2", _, _))), _),
                 SOME
                   (UE_IfLet
                     (P_Constr
                        (last_pattern_path, [P_Ident ("last", _)], _),
                      last_call,
                      UE_Block (last_body, _),
                      SOME
                        (UE_Block
                          (UE_Literal
                            (LP_Integer
                              (Integer_Literal ("4", _, _))), _)),
                      nested_layout)),
                 _)),
            layout) =>
           (audit_assert "mixed-chain path structure changed"
              (path_named "Some" first_pattern_path andalso
               call_named "Some" first_call andalso
               expression_named "first" first_body andalso
               path_named "Some" last_pattern_path andalso
               call_named "Some" last_call andalso
               expression_named "last" last_body);
            audit_assert "mixed-chain span start moved"
              (Position.offset_of (source_span layout) =
                Position.offset_of mixed_start);
            audit_assert "mixed-chain span stopped before the final arm"
              (Position.end_offset_of (source_span layout) =
                Position.offset_of mixed_stop);
            audit_assert "nested if-let span stopped before its fallback"
              (Position.end_offset_of (source_span nested_layout) =
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
           (P_Constr
              (pattern_path, [P_Ident ("value", _)], _),
            call,
            UE_Block
              (UE_Literal
                (LP_Integer
                  (Integer_Literal ("0", _, _))), _),
            body,
            layout) =>
           (audit_assert "let-else path structure changed"
              (path_named "Some" pattern_path andalso
               call_named "Some" call andalso
               expression_named "value" body);
            audit_assert "let-else span start moved"
              (Position.offset_of (source_span layout) =
                Position.offset_of let_start);
            audit_assert "let-else span end moved"
              (Position.end_offset_of (source_span layout) =
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
        val actual = checked (conditional_source pattern scrutinee)
        val explicit =
          checked (explicit_case_source pattern scrutinee false)
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
        val actual = checked (conditional_source pattern scrutinee)
        val explicit =
          checked (explicit_case_source pattern scrutinee true)
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
          "\<llangle>Some True\<rrangle>")]

    (* This matrix is deliberately ill-typed. Coverage remains conservative before checking,
       while the valid shape comparisons above run after pattern typing witnesses are erased. *)
    val incompatible_family_source =
      conditional_source "Some(_) | ConditionalLetA(_)" "\<llangle>Some (1 :: nat)\<rrangle>"
    val incompatible_family_term = unchecked incompatible_family_source
    val _ =
      audit_assert "different constructor families incorrectly certified total coverage"
        (count_constant
           \<^const_name>\<open>conditional_let_fallback_marker\<close>
           incompatible_family_term > 0)
    val _ =
      (case Exn.result checked incompatible_family_source of
         Exn.Res _ =>
           error "conditional-binding regression audit: incompatible constructor families accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "incompatible constructor families did not reach type checking"
               (String.isSubstring "type" (String.map Char.toLower (Runtime.exn_message exn))))

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
         UE_IfLet (pattern, scrutinee, success, fallback, layout) =>
             URust_Matching.lower_if_let callback_lower ctxt
               URust_Resolution.empty_environment
               (pattern, scrutinee, success, fallback, layout)
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
         UE_Match (_, _, [UR_Arm (result, NONE, _, _)], _) => result
       | _ => error "parser regression audit: unexpected pattern AST")

    fun integer text (P_Literal (LP_Integer actual)) =
          integer_literal_lexeme actual = text
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
                   P_Borrow
                     (BM_Imm, P_Ident ("value", _), inner_layout),
                   outer_layout),
                 NONE, _, _)],
              _)) =>
           (audit_assert "outer borrow-pattern mode or position changed"
              (Position.offset_of (source_span outer_layout) =
                Position.offset_of outer_borrow_position);
            audit_assert "inner borrow-pattern mode or position changed"
              (Position.offset_of (source_span inner_layout) =
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
           P_Constr (path, [nested], _), _) =>
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
             [SF_Field ("field", _, nested)], _), _) =>
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

section\<open> Concealed native-constructor lookup boundary \<close>

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
    val bare_registered_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "ConcealedRegistered"))
    val bare_unregistered_info =
      the
        (URust_Resolution.resolve_constructor ctxt resolver
          (path_of "ConcealedUnregistered"))
    val _ =
      audit_assert "registered concealed constructor lost bare lookup"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term bare_registered_info,
           \<^term>\<open>ConcealedRegistered\<close>))
    val _ =
      audit_assert "unregistered concealed constructor lost bare lookup"
        (Term.aconv_untyped
          (URust_Resolution.constructor_term bare_unregistered_info,
           \<^term>\<open>ConcealedUnregistered\<close>))

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

    val unregistered_match =
      checked
        ("match_case \<llangle>ConcealedUnregistered\<rrangle> { " ^
         "ConcealedUnregistered \<Rightarrow> 0 }")
    val _ =
      audit_assert "unregistered concealed basename lost native case lowering"
        (count_constant concealed_case_name unregistered_match = 1)
    val _ =
      audit_assert "partial concealed match lost its unmatched fallback"
        (count_constant \<^const_name>\<open>undefined\<close>
          unregistered_match > 0)

    val concealed_mixed_text =
      "match \<llangle>ConcealedRegistered\<rrangle> { " ^
      "0 \<Rightarrow> (), ConcealedAudit::Registered \<Rightarrow> () }"
    val concealed_mixed_start =
      Position.make0 64 900 0 "" ""
        "concealed-constructor-mixed-match-audit"
    val concealed_mixed_source =
      Parser_Lex_Util.positioned_content_source
        concealed_mixed_text concealed_mixed_start
    val _ =
      (case parse concealed_mixed_text of
         UE_Match (flavour, _, arms, layout) =>
           (case URust_Patterns.select_match_flavour ctxt flavour arms (source_span layout) of
              MF_Case => ()
            | _ => error "concealed constructor lookup audit: numeral mixture lost case lowering")
       | _ => error "concealed constructor lookup audit: numeral mixture lost match AST")
    val _ =
      (case Exn.result (fn () => checked_source concealed_mixed_source) () of
         Exn.Res term =>
           error
             ("concealed constructor lookup audit: mixed numeral match " ^
              "unexpectedly elaborated to " ^
              Syntax.string_of_term ctxt term)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let val actual = String.map Char.toLower (Runtime.exn_message exn)
             in
               audit_assert
                 "concealed constructor numeral mixture did not reach ordinary type checking"
                 (String.isSubstring "type" actual orelse String.isSubstring "sort" actual);
               audit_assert "concealed constructor numeral mixture retained the obsolete pattern gate"
                 (not (String.isSubstring "mixed numeral and constructor patterns" actual))
             end)

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
        "Concealed registered identity, native basename lookup, checked numeral incompatibility, and recovery regressions passed"
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
    val registered_type_name =
      fst (dest_Type \<^typ>\<open>registered_constructor_fixture\<close>)
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
           (_, _,
            UR_Arm (P_Constr (path, [_], _), NONE, _, _) :: _, _) =>
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
    fun count_markup markup_name position =
      length
        (filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
          markup)
    fun count_entity kind identity position =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              Properties.get properties Markup.nameN = SOME identity andalso
              has_position properties position)
          markup)

    val _ =
      audit_assert "constructor qualifier retained free markup"
        (count_markup Markup.freeN expected_qualifier = 0)
    val _ =
      audit_assert "constructor qualifier datatype entity duplicated or disappeared"
        (count_entity Markup.type_nameN registered_type_name
          expected_qualifier = 1)
    val _ =
      audit_assert "constructor qualifier keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_qualifier = 1)
    val _ =
      audit_assert "constructor qualifier retained obsolete tconst styling"
        (count_markup Markup.tconstN expected_qualifier = 0)
    val _ =
      audit_assert "constructor terminal constant entity duplicated or disappeared"
        (count_entity Markup.constantN unary_name expected_terminal = 1)
    val _ =
      audit_assert "constructor terminal was reported as a free binder"
        (count_markup Markup.freeN expected_terminal = 0)
    val _ =
      audit_assert "constructor terminal notation entity duplicated or disappeared"
        (count_entity Micro_Rust_Names.notationN
          "Registered::Unary" expected_terminal = 1)
    val _ =
      audit_assert "constructor terminal keyword3 styling duplicated or disappeared"
        (count_markup Markup.keyword3N expected_terminal = 1)

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
        val qualifier_length = find_from path "::" 0
        val qualifier =
          String.substring (path, 0, qualifier_length)
        val (_, expected_qualifier_position) =
          token_position text start qualifier path_raw
        val expected_message =
          expected ^ Position.here expected_position
        val expected_range =
          (Value.print_int (the (Position.offset_of expected_position)),
           Value.print_int (the (Position.end_offset_of expected_position)))
        val captured =
          Synchronized.var
            ("registered_constructor_" ^ label ^ "_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Exn.result
                  (fn () =>
                    Parser_Test_Elaboration.expression ctxt source) ())
              ())
        val body =
          (case result of
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
        val rejection_markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
        val _ =
          audit_assert (label ^ " YXML offset/end_offset changed")
            (diagnostic_ranges body = [expected_range])
        val _ =
          audit_assert (label ^ " emitted premature qualifier free markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.freeN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier keyword3 markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.keyword3N andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier type entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Markup.type_nameN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier notation entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Micro_Rust_Names.notationN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature qualifier typing markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.typingN andalso
                    has_position properties
                      expected_qualifier_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal free markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.freeN andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal keyword3 markup")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.keyword3N andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal notation entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Micro_Rust_Names.notationN andalso
                    has_position properties expected_position)
                rejection_markup))
        val _ =
          audit_assert (label ^ " emitted premature terminal constant entity")
            (not
              (exists
                (fn (name, properties) =>
                  name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Markup.constantN andalso
                    has_position properties expected_position)
                rejection_markup))
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
      expect_report_free_class 0 "value-only exact key"
        URust_Resolution.Registered_Value_Literal
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
      expect_report_free_class 1 "merged constructor/value exact key"
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
      (case Exn.result
          (fn () =>
            let
              val path = path_of "Unregistered::Value"
              val resolver =
                URust_Resolution.make_constructor_resolver
                  ctxt (path_position path)
            in
              URust_Resolution.classify_registered_literal
                ctxt resolver path
            end) () of
         Exn.Res _ =>
           error
             "contextual bare-match classification audit: unregistered qualified path was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert
               "unregistered qualified path diagnostic changed"
               (String.isSubstring
                 "qualified path \"Unregistered::Value\" requires an exact micro_rust_notation (literal) declaration"
                 (Runtime.exn_message exn)))

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
            [UR_Arm
               (P_Literal (LP_Integer first_integer), NONE, _, _),
             UR_Arm (P_Path path, NONE, _, _),
             UR_Arm
               (P_Literal (LP_Integer second_integer), NONE, _, _),
             UR_Arm (P_Wild _, NONE, _, _)],
            match_layout) =>
           let
             val first_pos =
               integer_literal_position first_integer
             val second_pos =
               integer_literal_position second_integer
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
               (same_range (source_span match_layout) expected_match);
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
             UR_Arm (P_Ident (_, identifier_pos), NONE, _, _),
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

    val switch_preferred =
      checked
        ("match \<llangle>mixed_match_scrutinee_marker\<rrangle> { " ^
         "IntegrationAudit::Value \<Rightarrow> " ^
         "\<llangle>mixed_match_first_body_marker\<rrangle>, " ^
         "_ \<Rightarrow> \<llangle>mixed_match_fallback_marker\<rrangle> }")
    val _ =
      audit_assert "registered value without numeral selected switch"
        (count_constant \<^const_name>\<open>ncase_selector\<close>
          switch_preferred = 1)
    val _ =
      audit_assert "registered value without numeral retained case equality"
        (count_constant \<^const_name>\<open>urust_eq\<close>
          switch_preferred = 0)
    val _ =
      audit_assert "registered value without numeral retained case conditional"
        (count_constant \<^const_name>\<open>two_armed_conditional\<close>
          switch_preferred = 0)

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
      audit_assert "registered qualifier retained free markup"
        (count_markup Markup.freeN expected_qualifier
          qualified_markup = 0)
    val _ =
      audit_assert "registered qualifier notation report duplicated"
        (count_entity Micro_Rust_Names.notationN
          "IntegrationAudit::Value"
          expected_qualifier qualified_markup = 1)
    val _ =
      audit_assert "registered qualifier typing tooltip duplicated or disappeared"
        (count_markup Markup.typingN expected_qualifier
          qualified_markup = 1)
    val _ =
      audit_assert "registered qualifier acquired terminal styling"
        (count_markup Markup.keyword3N expected_qualifier
          qualified_markup = 0)
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

    val guarded_text =
      "match 42 { 0 if True \<Rightarrow> (), IntegrationAudit::Value \<Rightarrow> (), " ^
      "_ \<Rightarrow> () }"
    val guarded = checked guarded_text
    val _ =
      audit_assert "guarded numeral match selected switch lowering"
        (count_constant \<^const_name>\<open>ncase_selector\<close> guarded = 0)
    val _ =
      audit_assert "guarded numeral match lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close> guarded > 0)

    val binder_text =
      "match \<llangle>7 :: nat\<rrangle> { 0 \<Rightarrow> 11, number \<Rightarrow> number }"
    val binder = checked binder_text
    val _ =
      audit_assert "numeral and binder match selected switch lowering"
        (count_constant \<^const_name>\<open>ncase_selector\<close> binder = 0)
    val _ =
      audit_assert "numeral and binder match lost equality lowering"
        (count_constant \<^const_name>\<open>urust_eq\<close> binder = 1)
    val _ =
      audit_assert "numeral and binder match leaked a local identity"
        (null (Term.add_frees binder []) andalso null (Term.add_vars binder []))

    fun expect_checked_type_failure label text =
      let
        val _ =
          (case parse text of
             UE_Match (flavour, _, arms, layout) =>
               (case URust_Patterns.select_match_flavour ctxt flavour arms (source_span layout) of
                  MF_Case => ()
                | _ => error ("contextual bare-match classification audit: " ^ label ^
                    " did not select case lowering"))
           | _ => error "contextual bare-match classification audit: expected match")
      in
        (case Exn.result checked text of
           Exn.Res _ =>
             error ("contextual bare-match classification audit: " ^ label ^
               " accepted an incompatible integer pattern")
         | Exn.Exn exn =>
             if Exn.is_interrupt exn then Exn.reraise exn
             else
               let val message = String.map Char.toLower (Runtime.exn_message exn)
               in
                 audit_assert (label ^ " did not reach checked elaboration")
                   (String.isSubstring "type" message orelse String.isSubstring "sort" message);
                 audit_assert (label ^ " retained the obsolete numeral-mix diagnostic")
                   (not (String.isSubstring "mixed numeral and constructor patterns" message))
               end);
        recovery_checks ()
      end

    val _ =
      expect_checked_type_failure "registered constructor and numeral"
        ("match \<llangle>RegisteredNullary\<rrangle> { " ^
         "0 \<Rightarrow> (), Registered::Nullary \<Rightarrow> (), _ \<Rightarrow> () }")
    val _ =
      expect_checked_type_failure "constructor wins registration and numeral"
        ("match \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
         "0 \<Rightarrow> (), NegativeRegistered::ConstructorWins \<Rightarrow> (), _ \<Rightarrow> () }")

    val switch_guard_text =
      "match_switch 42 { IntegrationAudit::Value if True \<Rightarrow> (), _ \<Rightarrow> () }"
    val switch_guard_offset =
      find_from switch_guard_text "if" 0
    val _ =
      expect_exact_rejection 2 "explicit-switch-guard"
        switch_guard_text (token_range "if" switch_guard_offset)
        "urust_expr: guards are not supported in explicit `match_switch`"

    val ambiguous_mixed_text =
      "match \<llangle>NegativeRegisteredNullary\<rrangle> { " ^
      "0 \<Rightarrow> (), NegativeRegistered::Ambiguous \<Rightarrow> () }"
    val _ =
      (case Exn.result checked ambiguous_mixed_text of
         Exn.Res _ => error "contextual bare-match classification audit: ambiguous constructor accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert "numeral mixture masked constructor ambiguity"
               (String.isSubstring "ambiguous" (Runtime.exn_message exn)))
    val _ = recovery_checks ()
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
             UE_Match (flavour, scrutinee, arms, layout) =>
               Exn.result
                 (fn () =>
                   URust_Matching.lower_match lower ctxt
                     URust_Resolution.empty_environment
                     (flavour, scrutinee, arms, layout)) ()
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

chapter\<open> Slice patterns \<close>

section\<open>Lowering controls and closed generated terms\<close>

declare [[urust_verbosity = 0]]

ML_val\<open>
  local
    val ctxt = \<^context>
    fun assert message condition =
      if condition then () else error ("slice pattern term audit: " ^ message)

    fun rhs_of name =
      Proof_Context.get_thm ctxt (name ^ "_def")
      |> Thm.prop_of |> Logic.dest_equals |> snd

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (candidate, _) => if candidate = name then Integer.add 1 else I
          | _ => I)
        term 0

    val list_case_name =
      (case Ctr_Sugar.ctr_sugar_of ctxt \<^type_name>\<open>list\<close> of
         SOME {casex = Const (name, _), ...} => name
       | _ => error "slice pattern term audit: missing list case metadata")

    val pattern_type_probe_prefix = "_urust_pattern_type_probe_"

    fun probe_abstraction (Abs (name, _, _)) =
          String.isPrefix pattern_type_probe_prefix name
      | probe_abstraction _ = false

    fun probe_marker (Abs (name, _, _)) =
          String.isSubstring pattern_type_probe_prefix name
      | probe_marker (Free (name, _)) =
          String.isSubstring pattern_type_probe_prefix name
      | probe_marker (Var ((name, _), _)) =
          String.isSubstring pattern_type_probe_prefix name
      | probe_marker (Const (name, _)) =
          String.isSubstring pattern_type_probe_prefix name
      | probe_marker _ = false

    fun erased_type_probes name =
      let val definition = Thm.prop_of (Proof_Context.get_thm ctxt (name ^ "_def"))
      in
        assert (name ^ " retained a pattern typing probe abstraction")
          (not (Term.exists_subterm probe_abstraction definition));
        assert (name ^ " retained a pattern typing probe marker")
          (not (Term.exists_subterm probe_marker definition))
      end

    fun closed name =
      let val rhs = rhs_of name
      in
        assert (name ^ " leaked generated free variables") (null (Term.add_frees rhs []));
        assert (name ^ " leaked schematic variables") (null (Term.add_vars rhs []));
        erased_type_probes name
      end

    val _ = List.app closed
      ["parser_slice_rest", "parser_slice_bare_rest", "parser_slice_polymorphic_rest",
       "parser_slice_polymorphic_let_rest", "parser_slice_prefix",
       "parser_slice_suffix", "parser_slice_middle", "parser_slice_asymmetric",
       "parser_slice_closed", "parser_slice_bare_suffix", "parser_slice_bare_middle",
       "parser_slice_nested_suffix", "parser_slice_nested_bare_suffix",
       "parser_slice_integer_middle", "parser_slice_integer_prefix", "parser_slice_integer_suffix",
       "parser_slice_integer_option", "parser_slice_integer_alias", "parser_slice_integer_nested",
       "parser_slice_integer_tuple", "parser_slice_integer_struct",
       "parser_slice_integer_u8", "parser_slice_integer_u16", "parser_slice_integer_u32",
       "parser_slice_integer_u64", "parser_slice_integer_usize", "parser_slice_integer_or",
       "parser_slice_let_rest", "parser_slice_let_chain", "parser_slice_let_tuple",
       "parser_slice_let_rhs_once", "parser_slice_for_chain", "parser_slice_for_tuple",
       "parser_slice_for_rhs_once", "parser_slice_scope", "parser_slice_sibling_scope",
       "parser_slice_alternative_positions", "parser_slice_constructor_collisions",
       "parser_slice_hol_collision", "parser_slice_alias_range_reference",
       "parser_slice_if_let", "parser_slice_let_else", "parser_slice_matches",
       "parser_slice_matches_guard", "parser_slice_while_let", "parser_slice_total_while_let",
       "parser_slice_effectful_match", "parser_slice_guarded_or_order",
       "parser_slice_effectful_if_let", "parser_slice_effectful_let_else",
       "parser_slice_effectful_matches", "parser_slice_effectful_matches_plain",
       "parser_slice_numeric_switch",
       "parser_slice_numeric_explicit_switch", "parser_slice_numeric_or_switch",
       "parser_slice_numeric_or_explicit_switch",
       "parser_slice_numeric_case", "parser_slice_numeric_binding",
       "parser_slice_numeric_guarded", "parser_slice_term_markers"]

    val automatic = rhs_of "parser_slice_numeric_switch"
    val explicit = rhs_of "parser_slice_numeric_explicit_switch"
    val _ = assert "numeral-only bare match changed its explicit-switch term shape"
      (Term.aconv (automatic, explicit))
    val _ = assert "numeral-only bare match lost its switch selector"
      (count_constant \<^const_name>\<open>ncase_selector\<close> automatic = 1)

    val automatic_or = rhs_of "parser_slice_numeric_or_switch"
    val explicit_or = rhs_of "parser_slice_numeric_or_explicit_switch"
    val _ = assert "numeral or-pattern changed its explicit-switch term shape"
      (Term.aconv (automatic_or, explicit_or))
    val _ = assert "numeral or-pattern lost its switch selector"
      (count_constant \<^const_name>\<open>ncase_selector\<close> automatic_or = 1)
    val _ = assert "numeral or-pattern retained case equality"
      (count_constant \<^const_name>\<open>urust_eq\<close> automatic_or = 0)
    val _ = assert "numeral or-pattern retained case conditional lowering"
      (count_constant \<^const_name>\<open>two_armed_conditional\<close> automatic_or = 0)

    val _ = List.app
      (fn name =>
        let val term = rhs_of name
        in
          assert (name ^ " selected switch lowering")
            (count_constant \<^const_name>\<open>ncase_selector\<close> term = 0);
          assert (name ^ " lost value-pattern equality")
            (count_constant \<^const_name>\<open>urust_eq\<close> term > 0)
        end)
      ["parser_slice_numeric_case", "parser_slice_numeric_binding", "parser_slice_numeric_guarded",
       "parser_slice_integer_option", "parser_slice_integer_middle"]

    val _ = List.app
      (fn name => assert (name ^ " retained an undefined fallback")
        (count_constant \<^const_name>\<open>undefined\<close> (rhs_of name) = 0))
      ["parser_slice_rest", "parser_slice_bare_rest", "parser_slice_let_rest",
       "parser_slice_let_chain", "parser_slice_let_tuple",
       "parser_slice_total_if_let", "parser_slice_total_let_else", "parser_slice_total_while_let"]

    val _ = List.app
      (fn name => assert (name ^ " lost its direct rest-only abstraction")
        (count_constant list_case_name (rhs_of name) = 0))
      ["parser_slice_rest", "parser_slice_bare_rest", "parser_slice_let_rest",
       "parser_slice_let_chain", "parser_slice_total_if_let", "parser_slice_total_let_else"]

    val _ = List.app
      (fn (name, term) =>
        assert ("duplicated or dropped " ^ name)
          (count_constant name term = 1))
      (map (fn name => (name, rhs_of "parser_slice_term_markers"))
        [\<^const_name>\<open>parser_slice_source_marker\<close>,
         \<^const_name>\<open>parser_slice_guard_marker\<close>,
         \<^const_name>\<open>parser_slice_body_marker\<close>])

    val unchanged_let =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          "let value = \<llangle>11 :: nat\<rrangle>; value")
    val reference_let = \<^term>\<open>
      bind (literal (11 :: nat)) (\<lambda>value. literal value)
        :: (unit, nat, unit, unit, unit, unit) expression
    \<close>
    val _ = assert "ordinary identifier let changed its checked term shape"
      (Term.aconv_untyped (unchanged_let, reference_let))
  in
    val _ = writeln "Slice capture, integer lowering, totality, hygiene, and evaluation-shape audits passed"
  end
\<close>

chapter\<open> Matcher stability \<close>

declare [[urust_pretty = false]]

ML_val\<open>
  local
    val ctxt = \<^context>
    (* Raw baseline HOL terms preserve every internal type and sort.
       Printing and reparsing can change native case terms or latent types. *)
    fun frozen payload = Term_XML.Decode.term_raw (YXML.parse_body payload)
    fun checked source =
      URust_Command.elaborate ctxt
        {kind = URust_Command.Expression,
         source = Parser_Lex_Util.text_source source,
         arguments = [], arguments_pos = Position.none,
         declared_type = SOME
           ("(unit, nat, unit, unit, unit, unit) expression", Position.none)}
    (* Every one of three elaborations must equal the frozen term, so no compiler state may carry
       over from one elaboration to the next. *)
    fun check source expected =
      List.app (fn _ =>
        let
          val actual = checked source
          val _ = if Term.aconv (actual, expected) then ()
            else error "repeated matcher output differs from frozen baseline"
          val _ = Goal.prove ctxt [] []
            (HOLogic.mk_Trueprop (HOLogic.mk_eq (actual, expected)))
            (fn _ => resolve_tac ctxt [@{thm refl}] 1)
        in () end) [1, 2, 3]
  in
    val _ = check "match \<llangle>Some (Some (3 :: nat))\<rrangle> { Some(Some(2..=4)) if False \<Rightarrow> 1, Some(_) \<Rightarrow> 2, _ \<Rightarrow> 0 }"
      (frozen "\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.bind\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.Some\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.Some\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit1\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.zero_class.zero\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.bind\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.False\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.bind\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.urust_conj\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.comp_ge\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.comp_le\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.True\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.False\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.bind\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.urust_conj\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.comp_ge\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.comp_le\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.True\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.undefined\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.False\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.bind\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.undefined\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.bind\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.urust_conj\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.comp_ge\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.comp_le\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.True\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.False\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.bind\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.urust_conj\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.comp_ge\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.comp_le\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.False\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.one_class.one\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.undefined\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.undefined\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.zero_class.zero\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E1\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E");
    val _ = check "match \<llangle>Some ([1, 2] :: nat list)\<rrangle> { Some([head, ..]) if False \<Rightarrow> head, Some([head, ..]) \<Rightarrow> head, _ \<Rightarrow> 0 }"
      (frozen "\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.bind\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.Some\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=List.list.Cons\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.one_class.one\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=List.list.Cons\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.numeral_class.numeral\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.Bit0\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Num.num.One\^E\^E\^F0\^F0=Num.num\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=List.list.Nil\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.zero_class.zero\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=List.list.case_list\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.zero_class.zero\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E1\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=List.list.case_list\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.zero_class.zero\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=List.list.case_list\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.zero_class.zero\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E1\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E1\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Bool_Type.two_armed_conditional\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=HOL.False\^E\^E\^F0\^F0=HOL.bool\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E1\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Option.option.case_option\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Option.option\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.zero_class.zero\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=List.list.case_list\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Groups.zero_class.zero\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F4\^F0=x\^E\^E\^F:\^E\^E\^F0\^F0=List.list\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F5\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.literal\^E\^E\^F0\^F0=fun\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Core_Expression.expression\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Nat.nat\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F0\^F0=Product_Type.unit\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E1\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E3\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F:\^E\^E\^F3\^E0\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E\^E\^F\^E");
    val _ = writeln "Each probe elaborated three times to its typed frozen term"
  end
\<close>

chapter\<open> Name resolution \<close>

section\<open> Antiquotation markup under HOL shadowing \<close>

declare [[urust_pretty = true, urust_verbosity = 2]]

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
           (UC_Antiq source, [first, second], call_layout) =>
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
              (Position.offset_of (source_span call_layout) =
                Position.offset_of ast_start);
            audit_assert "call span no longer includes the closing parenthesis"
              (Position.end_offset_of (source_span call_layout) =
                Position.offset_of call_stop);
            audit_assert "expression_position lost the complete call span"
              (Position.offset_of (expression_position ast) =
                 Position.offset_of (source_span call_layout) andalso
               Position.end_offset_of (expression_position ast) =
                 Position.end_offset_of (source_span call_layout)))
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
These checks pin the function-literal boundary directly: exact HOL and
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
              (antiquotation, 14, suffix_pos,
               SOME
                 (Generic_Args
                   ([Generic_Arg (canonical, generic_source)], _))),
            [first, second], call_layout) =>
           let
             val source =
               value_antiquotation_source antiquotation
           in
             audit_assert "runtime argument order changed"
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
              (same_start (source_span call_layout) ast_start);
            audit_assert "call span no longer includes the closing parenthesis"
              (same_stop (source_span call_layout) call_stop);
            audit_assert "expression_position lost the complete call span"
              (same_start (expression_position ast) ast_start andalso
               same_stop (expression_position ast) call_stop)
           end
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
            (Micro_Rust_Names.mk_key Micro_Rust_Names.NFunction "is_none"))
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
           (macro_path, MP_Arguments
             [UE_Unary
               (U_Not,
                UE_Call
                  (UC_Method
                    (UE_Path receiver_path,
                     Path_Segment
                       ("is_none", method_pos, NONE)),
                   [], call_layout),
                _)],
            _) =>
           (audit_assert "assert macro wrapper changed"
              (render_path macro_path = "assert");
            audit_assert "method receiver changed"
              (render_path receiver_path = "o");
            audit_assert "method identifier range moved"
              (same_range method_pos expected_method);
            audit_assert "method call span moved"
              (same_range
                (source_span call_layout) expected_call);
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

section\<open> Registered constructor qualifier markup audit \<close>

datatype constructor_qualifier_fixture =
    ConstructorQualifierVariant
  | ConstructorQualifierOther

micro_rust_notation (literal)
  constructor_qualifier_fixture.ConstructorQualifierVariant
  ("Type::Variant")

micro_rust_notation (literal)
  constructor_qualifier_fixture.ConstructorQualifierVariant
  ("Module::Type::Variant")

datatype constructor_qualifier_left =
  ConstructorQualifierLeft

datatype constructor_qualifier_right =
  ConstructorQualifierRight

micro_rust_notation (literal)
  constructor_qualifier_left.ConstructorQualifierLeft
  ("Families::Variant")

micro_rust_notation (literal)
  constructor_qualifier_right.ConstructorQualifierRight
  ("Families::Variant")

definition constructor_qualifier_value :: nat
  where \<open> constructor_qualifier_value = 17 \<close>

micro_rust_notation (literal)
  constructor_qualifier_value
  ("Module::Value::Item")

definition constructor_qualifier_call ::
    \<open>(unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      constructor_qualifier_call =
        FunctionBody (literal 23)
    \<close>

micro_rust_notation (call)
  constructor_qualifier_call
  ("Module::Call::invoke")

definition qualifier_struct_call ::
    \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      qualifier_struct_call =
        lift_fun1 (\<lambda>value. value)
    \<close>

micro_rust_notation (call)
  qualifier_struct_call
  ("StructModule::Builder::new")

definition qualifier_generic_call ::
    \<open>nat \<Rightarrow> nat \<Rightarrow>
      (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      qualifier_generic_call parameter =
        lift_fun1 (\<lambda>argument. parameter + argument)
    \<close>

micro_rust_notation (call)
  qualifier_generic_call
  ("GenericBase::invoke")

micro_rust_notation (call)
  constructor_qualifier_call
  ("GenericExact::<Token>::invoke")

definition qualifier_macro_call ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      qualifier_macro_call =
        lift_fun1 (\<lambda>value. value)
    \<close>

micro_rust_notation (call)
  qualifier_macro_call
  ("MacroModule::invoke!")

micro_rust_notation (call)
  qualifier_macro_call
  ("MacroGeneric::<Token>::invoke!")

micro_rust_notation (call)
  \<open>lift_fun1 (\<lambda>value :: bool. value)\<close>
  ("MacroModule::anonymous!")

definition qualifier_multi_nat :: nat
  where \<open> qualifier_multi_nat = 29 \<close>

definition qualifier_multi_bool :: bool
  where \<open> qualifier_multi_bool = True \<close>

micro_rust_notation (literal)
  qualifier_multi_nat
  ("Multi::Registered::Value")

micro_rust_notation (literal)
  qualifier_multi_bool
  ("Multi::Registered::Value")

micro_rust_notation (literal)
  qualifier_multi_nat
  ("Duplicate::Registered::Value")

micro_rust_notation (literal)
  qualifier_multi_nat
  ("Duplicate::Registered::Value")

micro_rust_notation (call)
  constructor_qualifier_call
  ("Wrong::Role::Item")

micro_rust_notation (literal)
  constructor_qualifier_left.ConstructorQualifierLeft
  ("Module::Families::Variant")

micro_rust_notation (literal)
  constructor_qualifier_right.ConstructorQualifierRight
  ("Module::Families::Variant")

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("registered constructor qualifier markup audit: " ^ message)

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

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_markup label start text declared_type =
      let
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val captured =
          Synchronized.var
            ("constructor_qualifier_" ^ label ^ "_reports")
            ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val _ =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    ignore
                      (URust_Command.elaborate ctxt
                        {kind = URust_Command.Expression,
                         source = source,
                         arguments = [],
                         arguments_pos = #2 (Input.range_of source),
                         declared_type =
                           Option.map
                             (fn typ => (typ, Position.none))
                             declared_type})) ())
              ())
      in
        fold collect_markup
          (maps YXML.parse_body (Synchronized.value captured)) []
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)

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

    fun count_entity_kind kind position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              has_position properties position)
          markup)

    fun type_name typ = fst (dest_Type typ)
    fun constant_name term =
      (case Term.head_of term of
         Const (name, _) => name
       | _ => error "expected constant")

    val fixture_type_name =
      type_name \<^typ>\<open>constructor_qualifier_fixture\<close>
    val fixture_constructor_name =
      constant_name \<^term>\<open>ConstructorQualifierVariant\<close>
    val left_type_name =
      type_name \<^typ>\<open>constructor_qualifier_left\<close>
    val right_type_name =
      type_name \<^typ>\<open>constructor_qualifier_right\<close>
    val left_constructor_name =
      constant_name \<^term>\<open>ConstructorQualifierLeft\<close>
    val right_constructor_name =
      constant_name \<^term>\<open>ConstructorQualifierRight\<close>
    val value_name =
      \<^const_name>\<open>constructor_qualifier_value\<close>
    val call_name =
      \<^const_name>\<open>constructor_qualifier_call\<close>

    fun assert_constructor_qualifier
        label notation expected_type expected_notations position markup =
      (audit_assert (label ^ " retained free markup")
         (count_markup Markup.freeN position markup = 0);
       audit_assert (label ^ " lost datatype navigation")
         (count_entity Markup.type_nameN expected_type position markup = 1);
       audit_assert (label ^ " lost constructor keyword3 styling")
         (count_markup Markup.keyword3N position markup = 1);
       audit_assert (label ^ " retained obsolete tconst styling")
         (count_markup Markup.tconstN position markup = 0);
       audit_assert (label ^ " acquired neutral typing markup")
         (count_markup Markup.typingN position markup = 0);
       audit_assert (label ^ " notation navigation count changed")
         (count_entity Micro_Rust_Names.notationN notation
           position markup = expected_notations);
       audit_assert (label ^ " acquired backend constant identity")
         (count_entity_kind Markup.constantN position markup = 0))

    fun assert_neutral_qualifier
        label notation expected_entities position markup =
      (audit_assert (label ^ " retained free markup")
         (count_markup Markup.freeN position markup = 0);
       audit_assert (label ^ " notation entity count changed")
         (count_entity Micro_Rust_Names.notationN notation
           position markup = expected_entities);
       audit_assert (label ^ " typing tooltip count changed")
         (count_markup Markup.typingN position markup = 1);
       audit_assert (label ^ " acquired keyword styling")
         (count_markup Markup.keyword3N position markup = 0);
       audit_assert (label ^ " acquired obsolete tconst styling")
         (count_markup Markup.tconstN position markup = 0);
       audit_assert (label ^ " acquired datatype identity")
         (count_entity_kind Markup.type_nameN position markup = 0);
       audit_assert (label ^ " acquired backend constant identity")
         (count_entity_kind Markup.constantN position markup = 0))

    fun assert_terminal label notation constructor position markup =
      (audit_assert (label ^ " notation entity count changed")
         (count_entity Micro_Rust_Names.notationN notation
           position markup = 1);
       audit_assert (label ^ " constructor entity count changed")
         (count_entity Markup.constantN constructor position markup = 1);
       audit_assert (label ^ " keyword3 styling count changed")
         (count_markup Markup.keyword3N position markup = 1);
       audit_assert (label ^ " acquired terminal free markup")
         (count_markup Markup.freeN position markup = 0))

    val direct_text =
      "match_case Type::Variant { " ^
      "Type::Variant \<Rightarrow> (), _ \<Rightarrow> () }"
    val direct_start =
      Position.make0 71 1400 0 "" ""
        "constructor-qualifier-direct-audit"
    val direct_markup =
      capture_markup "direct" direct_start direct_text NONE
    val (direct_value_raw, _) =
      token_position direct_text direct_start "Type::Variant" 0
    val (_, direct_value_qualifier) =
      token_position direct_text direct_start "Type" direct_value_raw
    val (_, direct_value_terminal) =
      token_position direct_text direct_start "Variant"
        (direct_value_raw + size "Type::")
    val (direct_pattern_raw, _) =
      token_position direct_text direct_start "Type::Variant"
        (direct_value_raw + size "Type::Variant")
    val (_, direct_pattern_qualifier) =
      token_position direct_text direct_start "Type" direct_pattern_raw
    val (_, direct_pattern_terminal) =
      token_position direct_text direct_start "Variant"
        (direct_pattern_raw + size "Type::")
    val _ =
      assert_constructor_qualifier "value qualifier"
        "Type::Variant" fixture_type_name 1
        direct_value_qualifier direct_markup
    val _ =
      assert_constructor_qualifier "pattern qualifier"
        "Type::Variant" fixture_type_name 1
        direct_pattern_qualifier direct_markup
    val _ =
      assert_terminal "value terminal" "Type::Variant"
        fixture_constructor_name direct_value_terminal direct_markup
    val _ =
      assert_terminal "pattern terminal" "Type::Variant"
        fixture_constructor_name direct_pattern_terminal direct_markup

    val module_text =
      "match_case Module::Type::Variant { " ^
      "Module::Type::Variant \<Rightarrow> (), _ \<Rightarrow> () }"
    val module_start =
      Position.make0 79 1800 0 "" ""
        "constructor-qualifier-module-audit"
    val module_markup =
      capture_markup "module" module_start module_text NONE
    val (module_value_raw, _) =
      token_position module_text module_start
        "Module::Type::Variant" 0
    val (_, module_value_outer) =
      token_position module_text module_start "Module" module_value_raw
    val (_, module_value_type) =
      token_position module_text module_start "Type"
        (module_value_raw + size "Module::")
    val (module_pattern_raw, _) =
      token_position module_text module_start
        "Module::Type::Variant"
        (module_value_raw + size "Module::Type::Variant")
    val (_, module_pattern_outer) =
      token_position module_text module_start "Module"
        module_pattern_raw
    val (_, module_pattern_type) =
      token_position module_text module_start "Type"
        (module_pattern_raw + size "Module::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral_qualifier label
            "Module::Type::Variant" 1
            position module_markup)
        [("value outer qualifier", module_value_outer),
         ("pattern outer qualifier", module_pattern_outer)]
    val _ =
      assert_constructor_qualifier "value nearest qualifier"
        "Module::Type::Variant" fixture_type_name 1
        module_value_type module_markup
    val _ =
      assert_constructor_qualifier "pattern nearest qualifier"
        "Module::Type::Variant" fixture_type_name 1
        module_pattern_type module_markup

    val value_text = "Module::Value::Item"
    val value_start =
      Position.make0 87 2200 0 "" ""
        "constructor-qualifier-value-audit"
    val value_markup =
      capture_markup "value" value_start value_text NONE
    val (value_raw, _) =
      token_position value_text value_start value_text 0
    val (_, value_outer) =
      token_position value_text value_start "Module" value_raw
    val (_, value_nearest) =
      token_position value_text value_start "Value"
        (value_raw + size "Module::")
    val (_, value_terminal) =
      token_position value_text value_start "Item"
        (value_raw + size "Module::Value::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral_qualifier label
            "Module::Value::Item" 1
            position value_markup)
        [("registered value outer qualifier", value_outer),
         ("registered value nearest qualifier", value_nearest)]
    val _ =
      assert_terminal "registered value terminal"
        "Module::Value::Item" value_name value_terminal value_markup

    val call_text = "Module::Call::invoke()"
    val call_start =
      Position.make0 95 2600 0 "" ""
        "constructor-qualifier-call-audit"
    val call_markup =
      capture_markup "call" call_start call_text NONE
    val (call_raw, _) =
      token_position call_text call_start call_text 0
    val (_, call_outer) =
      token_position call_text call_start "Module" call_raw
    val (_, call_nearest) =
      token_position call_text call_start "Call"
        (call_raw + size "Module::")
    val (_, call_terminal) =
      token_position call_text call_start "invoke"
        (call_raw + size "Module::Call::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral_qualifier label
            "Module::Call::invoke" 1
            position call_markup)
        [("registered call outer qualifier", call_outer),
         ("registered call nearest qualifier", call_nearest)]
    val _ =
      assert_terminal "registered call terminal"
        "Module::Call::invoke" call_name call_terminal call_markup

    val families_text = "Families::Variant"
    val families_start =
      Position.make0 103 3000 0 "" ""
        "constructor-qualifier-families-audit"
    val families_markup =
      capture_markup "families" families_start families_text
        (SOME
          "(unit, constructor_qualifier_left, unit, unit, unit, unit) expression")
    val (families_raw, _) =
      token_position families_text families_start families_text 0
    val (_, families_qualifier) =
      token_position families_text families_start "Families"
        families_raw
    val (_, families_terminal) =
      token_position families_text families_start "Variant"
        (families_raw + size "Families::")
    val _ =
      audit_assert "multi-backend qualifier retained free markup"
        (count_markup Markup.freeN families_qualifier
          families_markup = 0)
    val _ =
      audit_assert "left datatype family navigation count changed"
        (count_entity Markup.type_nameN left_type_name
          families_qualifier families_markup = 1)
    val _ =
      audit_assert "right datatype family navigation count changed"
        (count_entity Markup.type_nameN right_type_name
          families_qualifier families_markup = 1)
    val _ =
      audit_assert "multi-backend constructor styling did not cover both families"
        (count_markup Markup.keyword3N families_qualifier
          families_markup = 2)
    val _ =
      audit_assert "multi-backend qualifier retained obsolete tconst styling"
        (count_markup Markup.tconstN families_qualifier
          families_markup = 0)
    val _ =
      audit_assert "multi-backend qualifier notation count changed"
        (count_entity Micro_Rust_Names.notationN "Families::Variant"
          families_qualifier families_markup = 2)
    val _ =
      audit_assert "multi-backend notation entity count changed"
        (count_entity Micro_Rust_Names.notationN "Families::Variant"
          families_terminal families_markup = 2)
    val _ =
      audit_assert "multi-backend keyword3 count changed"
        (count_markup Markup.keyword3N families_terminal
          families_markup = 2)
    val _ =
      audit_assert "left constructor entity count changed"
        (count_entity Markup.constantN left_constructor_name
          families_terminal families_markup = 1)
    val _ =
      audit_assert "right constructor entity count changed"
        (count_entity Markup.constantN right_constructor_name
          families_terminal families_markup = 1)
  in
    val _ =
      writeln
        "Registered constructor qualifier datatype, module, value, call, and all-backend markup regressions passed"
  end
\<close>

section\<open> Neutral registered path qualifier markup audit \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>
    val color_ctxt =
      Proof_Context.init_global \<^theory>\<open>Parser_Expression_Examples\<close>

    fun audit_assert message condition =
      if condition then ()
      else error ("neutral registered path qualifier markup audit: " ^ message)

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

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture active_ctxt serial label text declared_type =
      let
        val start =
          Position.make0 (180 + serial) (40000 + serial * 500) 0 "" ""
            ("neutral-registered-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val captured =
          Synchronized.var
            ("neutral_registered_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        URust_Command.elaborate active_ctxt
                          {kind = URust_Command.Expression,
                           source = source,
                           arguments = [],
                           arguments_pos = #2 (Input.range_of source),
                           declared_type =
                             Option.map
                               (fn typ => (typ, Position.none))
                               declared_type}) ())
                  ())
              ())
        val trees =
          maps YXML.parse_body (Synchronized.value captured)
      in
        (start, result, trees, fold collect_markup trees [])
      end

    fun require_success label (Exn.Res term) = term
      | require_success label (Exn.Exn exn) =
          if Exn.is_interrupt exn then Exn.reraise exn
          else
            error
              ("neutral registered path qualifier markup audit: " ^
                label ^ " failed: " ^ Runtime.exn_message exn)

    fun require_failure label (Exn.Exn exn) =
          if Exn.is_interrupt exn then Exn.reraise exn else ()
      | require_failure label (Exn.Res term) =
          error
            ("neutral registered path qualifier markup audit: " ^
              label ^ " unexpectedly elaborated to " ^
              Syntax.string_of_term ctxt term)

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

    fun count_entity_kind kind position markup =
      length
        (filter
          (fn (name, properties) =>
            name = Markup.entityN andalso
              Properties.get properties Markup.kindN = SOME kind andalso
              has_position properties position)
          markup)

    fun entity_refs kind notation position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN = SOME kind andalso
                Properties.get properties Markup.nameN = SOME notation andalso
                has_position properties position
            then Properties.get properties Markup.refN
            else NONE)
      |> sort_strings

    fun registration_refs active_ctxt kind notation =
      Micro_Rust_Names.lookups active_ctxt kind notation
      |> map
          (fn ({serial, ...} : Micro_Rust_Names.entry) =>
            Value.print_int serial)
      |> sort_strings

    fun typing_texts position trees =
      let
        fun collect (XML.Text _) result = result
          | collect (XML.Elem ((name, properties), body)) result =
              let
                val result' =
                  if name = Markup.typingN andalso
                      has_position properties position
                  then XML.content_of body :: result
                  else result
              in fold collect body result' end
      in rev (fold collect trees []) end

    fun assert_neutral active_ctxt label role kind notation
        position trees markup =
      let
        val expected_refs =
          registration_refs active_ctxt kind notation
        val expected_tooltip =
          "registered " ^ role ^ " path qualifier for " ^
            quote notation
      in
        audit_assert (label ^ " retained free markup")
          (count_markup Markup.freeN position markup = 0);
        audit_assert (label ^ " notation navigation changed")
          (entity_refs Micro_Rust_Names.notationN notation
             position markup = expected_refs andalso
           not (null expected_refs));
        audit_assert (label ^ " typing tooltip count changed")
          (count_markup Markup.typingN position markup = 1);
        audit_assert (label ^ " typing tooltip text changed")
          (typing_texts position trees = [expected_tooltip]);
        audit_assert (label ^ " acquired terminal styling")
          (count_markup Markup.keyword3N position markup = 0);
        audit_assert (label ^ " acquired type styling")
          (count_markup Markup.tconstN position markup = 0);
        audit_assert (label ^ " acquired datatype identity")
          (count_entity_kind Markup.type_nameN position markup = 0);
        audit_assert (label ^ " acquired backend constant identity")
          (count_entity_kind Markup.constantN position markup = 0)
      end

    fun assert_terminal active_ctxt label kind notation position markup =
      let
        val expected_refs =
          registration_refs active_ctxt kind notation
        val backend_count = length expected_refs
        val actual_refs =
          entity_refs Micro_Rust_Names.notationN notation
            position markup
        val reported_ranges =
          markup
          |> map_filter
              (fn (name, properties) =>
                if name = Markup.entityN andalso
                    Properties.get properties Markup.kindN =
                      SOME Micro_Rust_Names.notationN andalso
                    Properties.get properties Markup.nameN =
                      SOME notation
                then
                  SOME
                    (the_default "?"
                       (Properties.get properties Markup.offsetN) ^
                     "-" ^
                     the_default "?"
                       (Properties.get properties Markup.end_offsetN))
                else NONE)
      in
        audit_assert
          (label ^ " notation navigation changed: expected refs " ^
            commas expected_refs ^ ", actual refs " ^
            commas actual_refs ^ ", reported ranges " ^
            commas reported_ranges ^ ", expected range " ^
            the_default "?"
              (Option.map Value.print_int
                (Position.offset_of position)) ^
            "-" ^
            the_default "?"
              (Option.map Value.print_int
                (Position.end_offset_of position)))
          (actual_refs = expected_refs);
        audit_assert (label ^ " keyword styling count changed")
          (count_markup Markup.keyword3N position markup =
            backend_count);
        audit_assert (label ^ " backend identity count changed")
          (count_entity_kind Markup.constantN position markup =
            backend_count);
        audit_assert (label ^ " acquired free markup")
          (count_markup Markup.freeN position markup = 0)
      end

    fun assert_no_semantic label position markup =
      (audit_assert (label ^ " acquired free markup")
         (count_markup Markup.freeN position markup = 0);
       audit_assert (label ^ " acquired typing markup")
         (count_markup Markup.typingN position markup = 0);
       audit_assert (label ^ " acquired notation identity")
         (count_entity_kind Micro_Rust_Names.notationN
           position markup = 0);
       audit_assert (label ^ " acquired backend identity")
         (count_entity_kind Markup.constantN position markup = 0);
       audit_assert (label ^ " acquired datatype identity")
         (count_entity_kind Markup.type_nameN position markup = 0);
       audit_assert (label ^ " acquired keyword styling")
         (count_markup Markup.keyword3N position markup = 0))

    val color_text =
      "match_switch Color::Red { Color::Red \<Rightarrow> 1, _ \<Rightarrow> 0 }"
    val (color_start, color_result, color_trees, color_markup) =
      capture color_ctxt 0 "color" color_text NONE
    val _ = ignore (require_success "Color::Red reproduction" color_result)
    val (color_value_raw, _) =
      token_position color_text color_start "Color::Red" 0
    val (_, color_value_qualifier) =
      token_position color_text color_start "Color" color_value_raw
    val (_, color_value_terminal) =
      token_position color_text color_start "Red"
        (color_value_raw + size "Color::")
    val (color_pattern_raw, _) =
      token_position color_text color_start "Color::Red"
        (color_value_raw + size "Color::Red")
    val (_, color_pattern_qualifier) =
      token_position color_text color_start "Color"
        color_pattern_raw
    val (_, color_pattern_terminal) =
      token_position color_text color_start "Red"
        (color_pattern_raw + size "Color::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral color_ctxt label "literal"
            Micro_Rust_Names.NLiteral "Color::Red"
            position color_trees color_markup)
        [("Color::Red scrutinee qualifier", color_value_qualifier),
         ("Color::Red pattern qualifier", color_pattern_qualifier)]
    val _ =
      List.app
        (fn (label, position) =>
          assert_terminal color_ctxt label
            Micro_Rust_Names.NLiteral "Color::Red"
            position color_markup)
        [("Color::Red scrutinee terminal", color_value_terminal),
         ("Color::Red pattern terminal", color_pattern_terminal)]

    val deep_text =
      "match_switch Module::Value::Item { " ^
      "Module::Value::Item \<Rightarrow> 1, _ \<Rightarrow> 0 }"
    val (deep_start, deep_result, deep_trees, deep_markup) =
      capture ctxt 1 "deep-literal" deep_text NONE
    val _ = ignore (require_success "deep literal path" deep_result)
    val (deep_value_raw, _) =
      token_position deep_text deep_start "Module::Value::Item" 0
    val (deep_value_module_raw, deep_value_module) =
      token_position deep_text deep_start "Module" deep_value_raw
    val (_, deep_value_value) =
      token_position deep_text deep_start "Value"
        (deep_value_module_raw + size "Module::")
    val (_, deep_value_terminal) =
      token_position deep_text deep_start "Item"
        (deep_value_raw + size "Module::Value::")
    val (deep_pattern_raw, _) =
      token_position deep_text deep_start "Module::Value::Item"
        (deep_value_raw + size "Module::Value::Item")
    val (deep_pattern_module_raw, deep_pattern_module) =
      token_position deep_text deep_start "Module" deep_pattern_raw
    val (_, deep_pattern_value) =
      token_position deep_text deep_start "Value"
        (deep_pattern_module_raw + size "Module::")
    val (_, deep_pattern_terminal) =
      token_position deep_text deep_start "Item"
        (deep_pattern_raw + size "Module::Value::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral ctxt label "literal"
            Micro_Rust_Names.NLiteral "Module::Value::Item"
            position deep_trees deep_markup)
        [("deep value outer qualifier", deep_value_module),
         ("deep value inner qualifier", deep_value_value),
         ("deep pattern outer qualifier", deep_pattern_module),
         ("deep pattern inner qualifier", deep_pattern_value)]
    val _ =
      List.app
        (fn (label, position) =>
          assert_terminal ctxt label
            Micro_Rust_Names.NLiteral "Module::Value::Item"
            position deep_markup)
        [("deep value terminal", deep_value_terminal),
         ("deep pattern terminal", deep_pattern_terminal)]

    fun audit_call serial label text notation terminal_name
        qualifier_spellings =
      let
        val (start, result, trees, markup) =
          capture ctxt serial label text NONE
        val _ = ignore (require_success label result)
        val _ =
          List.app
            (fn (spelling, offset) =>
              let
                val (_, position) =
                  token_position text start spelling offset
              in
                assert_neutral ctxt
                  (label ^ " qualifier " ^ quote spelling)
                  "call" Micro_Rust_Names.NFunction notation
                  position trees markup
              end)
            qualifier_spellings
        val terminal_offset =
          find_from text terminal_name 0
        val (_, terminal_position) =
          token_position text start terminal_name terminal_offset
        val _ =
          assert_terminal ctxt (label ^ " terminal")
            Micro_Rust_Names.NFunction notation
            terminal_position markup
      in () end

    val _ =
      audit_call 2 "qualified call"
        "Module::Call::invoke()" "Module::Call::invoke" "invoke"
        [("Module", 0), ("Call", size "Module::")]
    val _ =
      audit_call 3 "qualified struct head"
        "StructModule::Builder::new { value: 7 }"
        "StructModule::Builder::new" "new"
        [("StructModule", 0),
         ("Builder", size "StructModule::")]
    val _ =
      audit_call 4 "base registration with turbofish"
        "GenericBase::invoke::<1>(2)"
        "GenericBase::invoke" "invoke"
        [("GenericBase", 0)]
    val _ =
      audit_call 5 "exact generic registration"
        "GenericExact::<Token>::invoke()"
        "GenericExact::<Token>::invoke" "invoke"
        [("GenericExact", 0)]

    fun audit_macro serial label text notation qualifier terminal_name =
      let
        val (start, result, trees, markup) =
          capture ctxt serial label text NONE
        val _ = ignore (require_success label result)
        val (_, qualifier_position) =
          token_position text start qualifier 0
        val (_, terminal_position) =
          token_position text start terminal_name
            (find_from text terminal_name 0)
        val (_, bang_position) =
          token_position text start "!" 0
        val _ =
          assert_neutral ctxt (label ^ " qualifier") "call"
            Micro_Rust_Names.NFunction notation
            qualifier_position trees markup
        val _ =
          assert_terminal ctxt (label ^ " identifier terminal")
            Micro_Rust_Names.NFunction notation
            terminal_position markup
        val _ =
          audit_assert (label ^ " bang operator markup changed")
            (count_markup Markup.operatorN bang_position markup = 1)
        val _ =
          audit_assert (label ^ " bang acquired notation navigation")
            (count_entity_kind Micro_Rust_Names.notationN
              bang_position markup = 0)
        val _ =
          audit_assert (label ^ " bang selected-backend count changed")
            (count_entity_kind Markup.constantN
              bang_position markup = 1)
        val _ =
          audit_assert (label ^ " bang constant styling changed")
            (count_markup Markup.constN bang_position markup = 1)
      in () end

    val _ =
      audit_macro 6 "qualified macro"
        "MacroModule::invoke!(true)"
        "MacroModule::invoke!" "MacroModule" "invoke"
    val _ =
      audit_macro 7 "generic qualified macro"
        "MacroGeneric::<Token>::invoke!(true)"
        "MacroGeneric::<Token>::invoke!" "MacroGeneric" "invoke"

    val multi_text = "Multi::Registered::Value"
    val (multi_start, multi_result, multi_trees, multi_markup) =
      capture ctxt 8 "multi-backend" multi_text
        (SOME "(unit, nat, unit, unit, unit, unit) expression")
    val _ = ignore (require_success "multi-backend literal" multi_result)
    val (multi_outer_raw, multi_outer) =
      token_position multi_text multi_start "Multi" 0
    val (_, multi_inner) =
      token_position multi_text multi_start "Registered"
        (multi_outer_raw + size "Multi::")
    val (_, multi_terminal) =
      token_position multi_text multi_start "Value"
        (size "Multi::Registered::")
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral ctxt label "literal"
            Micro_Rust_Names.NLiteral "Multi::Registered::Value"
            position multi_trees multi_markup)
        [("multi-backend outer qualifier", multi_outer),
         ("multi-backend inner qualifier", multi_inner)]
    val _ =
      assert_terminal ctxt "multi-backend terminal"
        Micro_Rust_Names.NLiteral "Multi::Registered::Value"
        multi_terminal multi_markup
    val _ =
      audit_assert "multi-backend qualifier tooltip multiplied"
        (count_markup Markup.typingN multi_outer multi_markup = 1)

    val duplicate_text = "Duplicate::Registered::Value"
    val (duplicate_start, duplicate_result,
         duplicate_trees, duplicate_markup) =
      capture ctxt 9 "duplicate-registration" duplicate_text NONE
    val _ =
      ignore (require_success "duplicate registration" duplicate_result)
    val (duplicate_outer_raw, duplicate_outer) =
      token_position duplicate_text duplicate_start "Duplicate" 0
    val (_, duplicate_inner) =
      token_position duplicate_text duplicate_start "Registered"
        (duplicate_outer_raw + size "Duplicate::")
    val (_, duplicate_terminal) =
      token_position duplicate_text duplicate_start "Value"
        (size "Duplicate::Registered::")
    val _ =
      audit_assert "idempotent duplicate survived in registry"
        (length
          (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral
            "Duplicate::Registered::Value") = 1)
    val _ =
      List.app
        (fn (label, position) =>
          assert_neutral ctxt label "literal"
            Micro_Rust_Names.NLiteral
            "Duplicate::Registered::Value"
            position duplicate_trees duplicate_markup)
        [("duplicate outer qualifier", duplicate_outer),
         ("duplicate inner qualifier", duplicate_inner)]
    val _ =
      assert_terminal ctxt "duplicate terminal"
        Micro_Rust_Names.NLiteral "Duplicate::Registered::Value"
        duplicate_terminal duplicate_markup

    val families_text = "Module::Families::Variant"
    val (families_start, families_result,
         families_trees, families_markup) =
      capture ctxt 10 "constructor-families" families_text
        (SOME
          "(unit, constructor_qualifier_left, unit, unit, unit, unit) expression")
    val _ =
      ignore (require_success "constructor families" families_result)
    val (families_outer_raw, families_outer) =
      token_position families_text families_start "Module" 0
    val (_, families_nearest) =
      token_position families_text families_start "Families"
        (families_outer_raw + size "Module::")
    val (_, families_terminal) =
      token_position families_text families_start "Variant"
        (size "Module::Families::")
    val _ =
      assert_neutral ctxt "constructor outer module qualifier"
        "literal" Micro_Rust_Names.NLiteral
        "Module::Families::Variant"
        families_outer families_trees families_markup
    val _ =
      audit_assert "nearest constructor qualifier retained free markup"
        (count_markup Markup.freeN families_nearest families_markup = 0)
    val _ =
      audit_assert "nearest constructor qualifier lost family navigation"
        (count_entity_kind Markup.type_nameN
          families_nearest families_markup = 2)
    val _ =
      audit_assert "nearest constructor qualifier styling count changed"
        (count_markup Markup.keyword3N
          families_nearest families_markup = 2)
    val _ =
      audit_assert "nearest constructor qualifier notation count changed"
        (count_entity_kind Micro_Rust_Names.notationN
           families_nearest families_markup = 2)
    val _ =
      audit_assert "nearest constructor qualifier acquired neutral tooltip"
        (count_markup Markup.typingN
           families_nearest families_markup = 0)
    val _ =
      assert_terminal ctxt "multi-family constructor terminal"
        Micro_Rust_Names.NLiteral "Module::Families::Variant"
        families_terminal families_markup

    fun failure_case serial label text qualifier =
      let
        val (start, result, _, markup) =
          capture ctxt serial label text NONE
        val _ = require_failure label result
        val (_, qualifier_position) =
          token_position text start qualifier 0
        val _ =
          assert_no_semantic (label ^ " qualifier")
            qualifier_position markup
      in () end

    val _ =
      failure_case 11 "wrong role"
        "Wrong::Role::Item" "Wrong"
    val _ =
      failure_case 12 "unregistered path"
        "Missing::Path::Item" "Missing"
    val _ =
      failure_case 13 "nonadjacent registered macro"
        "MacroModule::invoke !(true)" "MacroModule"

    val malformed_text =
      "match_case Type::Variant { " ^
      "Type::Variant(value) \<Rightarrow> (), _ \<Rightarrow> () }"
    val (malformed_start, malformed_result, _, malformed_markup) =
      capture ctxt 14 "malformed-constructor" malformed_text NONE
    val _ =
      require_failure "malformed constructor pattern" malformed_result
    val first_variant =
      find_from malformed_text "Type::Variant" 0
    val second_variant =
      find_from malformed_text "Type::Variant"
        (first_variant + size "Type::Variant")
    val (_, malformed_qualifier) =
      token_position malformed_text malformed_start "Type"
        second_variant
    val (_, malformed_terminal) =
      token_position malformed_text malformed_start "Variant"
        (second_variant + size "Type::")
    val _ =
      assert_no_semantic "malformed constructor qualifier"
        malformed_qualifier malformed_markup
    val _ =
      assert_no_semantic "malformed constructor terminal"
        malformed_terminal malformed_markup

    val recovery_text = "Module::Value::Item"
    val (recovery_start, recovery_result,
         recovery_trees, recovery_markup) =
      capture ctxt 15 "recovery" recovery_text NONE
    val _ =
      ignore (require_success "post-failure recovery" recovery_result)
    val (_, recovery_qualifier) =
      token_position recovery_text recovery_start "Module" 0
    val _ =
      assert_neutral ctxt "post-failure recovery qualifier"
        "literal" Micro_Rust_Names.NLiteral
        "Module::Value::Item"
        recovery_qualifier recovery_trees recovery_markup

    val single_text = "registered_seven"
    val (single_start, single_result, _, single_markup) =
      capture ctxt 16 "single-segment" single_text NONE
    val _ =
      ignore (require_success "single-segment registration" single_result)
    val (_, single_position) =
      token_position single_text single_start single_text 0
    val _ =
      assert_terminal ctxt "single-segment registration"
        Micro_Rust_Names.NLiteral "registered_seven"
        single_position single_markup

    val unresolved_text = "actual_unresolved_identifier"
    val (unresolved_start, unresolved_result, _, unresolved_markup) =
      capture ctxt 17 "unresolved-control" unresolved_text NONE
    val _ =
      ignore (require_success "unresolved identifier control"
        unresolved_result)
    val (_, unresolved_position) =
      token_position unresolved_text unresolved_start unresolved_text 0
    val _ =
      audit_assert "genuine unresolved identifier lost free markup"
        (count_markup Markup.freeN
          unresolved_position unresolved_markup = 1)

    val lexical_text =
      "let lexical_control = 1; lexical_control"
    val (lexical_start, lexical_result, _, lexical_markup) =
      capture ctxt 18 "lexical-control" lexical_text NONE
    val _ =
      ignore (require_success "lexical binder control" lexical_result)
    val (lexical_definition_raw, lexical_definition) =
      token_position lexical_text lexical_start "lexical_control" 0
    val (_, lexical_reference) =
      token_position lexical_text lexical_start "lexical_control"
        (lexical_definition_raw + size "lexical_control")
    val _ =
      List.app
        (fn (label, position) =>
          (audit_assert (label ^ " lost bound markup")
             (count_markup Markup.boundN position lexical_markup = 1);
           audit_assert (label ^ " acquired free markup")
             (count_markup Markup.freeN position lexical_markup = 0)))
        [("lexical definition", lexical_definition),
         ("lexical reference", lexical_reference)]

    val (_, fixed_ctxt) =
      Proof_Context.add_fixes
        [(Binding.name "fixed_qualifier_control",
          SOME \<^typ>\<open>nat\<close>, NoSyn)]
        ctxt
    val fixed_text = "fixed_qualifier_control"
    val (fixed_start, fixed_result, _, fixed_markup) =
      capture fixed_ctxt 19 "fixed-control" fixed_text NONE
    val _ =
      ignore (require_success "fixed identifier control" fixed_result)
    val (_, fixed_position) =
      token_position fixed_text fixed_start fixed_text 0
    val _ =
      audit_assert "fixed parameter changed free-name markup"
        (count_markup Markup.freeN fixed_position fixed_markup = 1)
  in
    val _ =
      writeln
        "Neutral registered qualifier navigation, tooltip, styling, multiplicity, constructor, failure, recovery, and binder-boundary regressions passed"
  end
\<close>

section\<open> Lifted backend navigation audit \<close>

definition lifted_navigation_pure :: \<open>nat \<Rightarrow> nat\<close>
  where \<open> lifted_navigation_pure value = value + 1 \<close>

micro_rust_notation (call)
  \<open>lift_fun1 lifted_navigation_pure\<close>
  ("LiftedNavigation::named")

micro_rust_notation (call)
  \<open>lift_fun1 (\<lambda>value :: nat. value)\<close>
  ("LiftedNavigation::anonymous")

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("lifted backend navigation audit: " ^ message)

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

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture serial label text declared_type =
      let
        val start =
          Position.make0 (240 + serial) (60000 + serial * 600) 0 "" ""
            ("lifted-navigation-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val ast =
          (case URust_Parser.parse_source ctxt source of
             SOME expression => expression
           | NONE => error (label ^ " parsed as empty input"))
        val captured =
          Synchronized.var
            ("lifted_navigation_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        URust_Command.elaborate ctxt
                          {kind = URust_Command.Expression,
                           source = source,
                           arguments = [],
                           arguments_pos = #2 (Input.range_of source),
                           declared_type =
                             Option.map
                               (fn typ => (typ, Position.none))
                               declared_type}) ())
                  ())
              ())
        val term =
          (case result of
             Exn.Res checked => checked
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 error
                   (label ^ " failed: " ^ Runtime.exn_message exn))
        val trees =
          maps YXML.parse_body (Synchronized.value captured)
      in
        (start, ast, term, fold collect_markup trees [])
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

    fun entity_names kind position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN = SOME kind andalso
                has_position properties position
            then Properties.get properties Markup.nameN
            else NONE)

    fun count_entity kind name position markup =
      entity_names kind position markup
      |> filter (fn actual => actual = name)
      |> length

    fun distinct_entity_names kind position markup =
      entity_names kind position markup
      |> distinct (op =)
      |> sort_strings

    fun assert_registered_terminal
        label notation target position markup =
      (audit_assert (label ^ " notation navigation count changed")
         (count_entity Micro_Rust_Names.notationN notation
           position markup = 1);
       audit_assert (label ^ " lost keyword3 styling")
         (count_markup Markup.keyword3N position markup = 1);
       audit_assert (label ^ " did not link to wrapped target")
         (count_entity Markup.constantN target position markup >= 1);
       audit_assert (label ^ " retained lift_fun1 navigation")
         (count_entity Markup.constantN
           \<^const_name>\<open>lift_fun1\<close> position markup = 0);
       audit_assert (label ^ " linked to an unrelated constant")
         (distinct_entity_names Markup.constantN position markup =
           [target]))

    fun assert_pattern_terminal label target position markup =
      (audit_assert (label ^ " acquired notation navigation")
         (entity_names Micro_Rust_Names.notationN
           position markup = []);
       audit_assert (label ^ " acquired registered keyword styling")
         (count_markup Markup.keyword3N position markup = 0);
       audit_assert (label ^ " did not retain native constructor navigation")
         (distinct_entity_names Markup.constantN position markup =
           [target]);
       audit_assert (label ^ " linked to lift_fun1")
         (count_entity Markup.constantN
           \<^const_name>\<open>lift_fun1\<close> position markup = 0))

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun assert_call_ast label expected expected_arity ast =
      (case ast of
         UE_Call (UC_Path path, arguments, _) =>
           (audit_assert (label ^ " call path changed")
              (render_path path = expected);
            audit_assert (label ^ " call arity changed")
              (length arguments = expected_arity))
       | _ => error (label ^ " call AST changed"))

    fun assert_match_ast label value_name pattern_name ast =
      (case ast of
         UE_Match
           (_, UE_Call (UC_Path value_path, [_], _),
            UR_Arm
              (P_Constr (pattern_path, [_], _), _, _, _) :: _, _) =>
           (audit_assert (label ^ " value-call AST changed")
              (render_path value_path = value_name);
            audit_assert (label ^ " constructor-pattern AST changed")
              (render_path pattern_path = pattern_name))
       | _ => error (label ^ " match AST changed"))

    fun assert_wrapped_registration notation wrapped =
      (case
        Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NFunction notation of
         [{hol_term, ...}] =>
           (case Term.strip_comb
               (Term_Position.strip_positions hol_term) of
              (Const (wrapper, _), [argument]) =>
                (audit_assert (notation ^ " registration wrapper changed")
                   (wrapper = \<^const_name>\<open>lift_fun1\<close>);
                 audit_assert (notation ^ " wrapped backend changed")
                   (wrapped argument))
            | _ => error (notation ^ " registration term shape changed"))
       | _ => error (notation ^ " registration multiplicity changed"))

    val some_text =
      "match_case Some(\<llangle>1 :: nat\<rrangle>) { " ^
      "Some(value) \<Rightarrow> value, None \<Rightarrow> 0 }"
    val (some_start, some_ast, some_term, some_markup) =
      capture 0 "some" some_text NONE
    val (some_value_raw, some_value_position) =
      token_position some_text some_start "Some" 0
    val (_, some_pattern_position) =
      token_position some_text some_start "Some"
        (some_value_raw + size "Some")
    val _ =
      assert_registered_terminal "Some value" "Some"
        \<^const_name>\<open>Option.Some\<close>
        some_value_position some_markup
    val _ =
      assert_pattern_terminal "Some pattern"
        \<^const_name>\<open>Option.Some\<close>
        some_pattern_position some_markup
    val _ =
      assert_match_ast "Some" "Some" "Some" some_ast
    val _ =
      audit_assert "Some checked term lost lift_fun1"
        (count_constant \<^const_name>\<open>lift_fun1\<close> some_term = 1)
    val _ =
      audit_assert "Some checked term lost Option.Some"
        (count_constant \<^const_name>\<open>Option.Some\<close> some_term = 1)

    val ok_text =
      "match_case Ok(\<llangle>1 :: nat\<rrangle>) { " ^
      "Ok(value) \<Rightarrow> value, Err(error) \<Rightarrow> error }"
    val (ok_start, ok_ast, ok_term, ok_markup) =
      capture 1 "ok" ok_text NONE
    val (ok_value_raw, ok_value_position) =
      token_position ok_text ok_start "Ok" 0
    val (_, ok_pattern_position) =
      token_position ok_text ok_start "Ok"
        (ok_value_raw + size "Ok")
    val (_, err_pattern_position) =
      token_position ok_text ok_start "Err" 0
    val _ =
      assert_registered_terminal "Ok value" "Ok"
        \<^const_name>\<open>Ok\<close> ok_value_position ok_markup
    val _ =
      assert_pattern_terminal "Ok pattern"
        \<^const_name>\<open>Ok\<close> ok_pattern_position ok_markup
    val _ =
      assert_pattern_terminal "Err pattern"
        \<^const_name>\<open>Err\<close> err_pattern_position ok_markup
    val _ =
      assert_match_ast "Ok" "Ok" "Ok" ok_ast
    val _ =
      audit_assert "Ok checked term lost lift_fun1"
        (count_constant \<^const_name>\<open>lift_fun1\<close> ok_term = 1)
    val _ =
      audit_assert "Ok checked term lost result constructors"
        (count_constant \<^const_name>\<open>Ok\<close> ok_term = 1)

    val err_text = "Err(\<llangle>1 :: nat\<rrangle>)"
    val (err_start, err_ast, err_term, err_markup) =
      capture 2 "err" err_text NONE
    val (_, err_value_position) =
      token_position err_text err_start "Err" 0
    val _ =
      assert_registered_terminal "Err value" "Err"
        \<^const_name>\<open>Err\<close> err_value_position err_markup
    val _ = assert_call_ast "Err" "Err" 1 err_ast
    val _ =
      audit_assert "Err checked term shape changed"
        (count_constant \<^const_name>\<open>lift_fun1\<close> err_term = 1 andalso
         count_constant \<^const_name>\<open>Err\<close> err_term = 1)

    val named_text =
      "LiftedNavigation::named(\<llangle>4 :: nat\<rrangle>)"
    val (named_start, named_ast, named_term, named_markup) =
      capture 3 "named" named_text NONE
    val (named_outer_raw, named_qualifier) =
      token_position named_text named_start "LiftedNavigation" 0
    val (_, named_terminal) =
      token_position named_text named_start "named"
        (named_outer_raw + size "LiftedNavigation::")
    val _ =
      assert_registered_terminal "named lifted function"
        "LiftedNavigation::named"
        \<^const_name>\<open>lifted_navigation_pure\<close>
        named_terminal named_markup
    val _ =
      audit_assert "named lifted qualifier notation changed"
        (count_entity Micro_Rust_Names.notationN
           "LiftedNavigation::named"
           named_qualifier named_markup = 1)
    val _ =
      audit_assert "named lifted qualifier typing changed"
        (count_markup Markup.typingN
           named_qualifier named_markup = 1)
    val _ =
      audit_assert "named lifted qualifier acquired terminal identity"
        (entity_names Markup.constantN
           named_qualifier named_markup = [])
    val _ =
      assert_call_ast "named lifted function"
        "LiftedNavigation::named" 1 named_ast
    val _ =
      audit_assert "named lifted checked term changed"
        (count_constant \<^const_name>\<open>lift_fun1\<close> named_term = 1 andalso
         count_constant \<^const_name>\<open>lifted_navigation_pure\<close>
           named_term = 1)

    val anonymous_text =
      "LiftedNavigation::anonymous(\<llangle>5 :: nat\<rrangle>)"
    val (anonymous_start, anonymous_ast,
         anonymous_term, anonymous_markup) =
      capture 4 "anonymous" anonymous_text NONE
    val (_, anonymous_terminal) =
      token_position anonymous_text anonymous_start "anonymous"
        (size "LiftedNavigation::")
    val _ =
      audit_assert "lifted lambda notation navigation changed"
        (count_entity Micro_Rust_Names.notationN
           "LiftedNavigation::anonymous"
           anonymous_terminal anonymous_markup = 1)
    val _ =
      audit_assert "lifted lambda lost keyword3 styling"
        (count_markup Markup.keyword3N
           anonymous_terminal anonymous_markup = 1)
    val _ =
      audit_assert "lifted lambda acquired a constant target"
        (entity_names Markup.constantN
           anonymous_terminal anonymous_markup = [])
    val _ =
      assert_call_ast "lifted lambda"
        "LiftedNavigation::anonymous" 1 anonymous_ast
    val _ =
      audit_assert "lifted lambda checked term lost its wrapper"
        (count_constant \<^const_name>\<open>lift_fun1\<close>
           anonymous_term = 1)

    val ordinary_text = "Module::Call::invoke()"
    val (ordinary_start, ordinary_ast,
         ordinary_term, ordinary_markup) =
      capture 5 "ordinary" ordinary_text NONE
    val (_, ordinary_terminal) =
      token_position ordinary_text ordinary_start "invoke"
        (size "Module::Call::")
    val _ =
      audit_assert "ordinary registration navigation changed"
        (distinct_entity_names Markup.constantN
           ordinary_terminal ordinary_markup =
           [\<^const_name>\<open>constructor_qualifier_call\<close>])
    val _ =
      audit_assert "ordinary registration styling changed"
        (count_markup Markup.keyword3N
           ordinary_terminal ordinary_markup = 1)
    val _ =
      assert_call_ast "ordinary registration"
        "Module::Call::invoke" 0 ordinary_ast
    val _ =
      audit_assert "ordinary checked term changed"
        (count_constant \<^const_name>\<open>constructor_qualifier_call\<close>
           ordinary_term = 1)

    val multi_text = "Multi::Registered::Value"
    val (multi_start, multi_ast, multi_term, multi_markup) =
      capture 6 "multiplicity" multi_text
        (SOME "(unit, nat, unit, unit, unit, unit) expression")
    val (multi_outer_raw, multi_outer) =
      token_position multi_text multi_start "Multi" 0
    val (_, multi_inner) =
      token_position multi_text multi_start "Registered"
        (multi_outer_raw + size "Multi::")
    val (_, multi_terminal) =
      token_position multi_text multi_start "Value"
        (size "Multi::Registered::")
    val _ =
      audit_assert "multi-backend registration count changed"
        (length
          (Micro_Rust_Names.lookups ctxt Micro_Rust_Names.NLiteral
            "Multi::Registered::Value") = 2)
    val _ =
      List.app
        (fn position =>
          (audit_assert "multi-backend qualifier notation changed"
             (count_entity Micro_Rust_Names.notationN
                "Multi::Registered::Value"
                position multi_markup = 2);
           audit_assert "multi-backend qualifier tooltip multiplied"
             (count_markup Markup.typingN position multi_markup = 1);
           audit_assert "multi-backend qualifier acquired constant identity"
             (entity_names Markup.constantN position multi_markup = [])))
        [multi_outer, multi_inner]
    val _ =
      audit_assert "multi-backend terminal notation count changed"
        (count_entity Micro_Rust_Names.notationN
           "Multi::Registered::Value"
           multi_terminal multi_markup = 2)
    val _ =
      audit_assert "multi-backend terminal targets changed"
        (distinct_entity_names Markup.constantN
           multi_terminal multi_markup =
           sort_strings
             [\<^const_name>\<open>qualifier_multi_nat\<close>,
              \<^const_name>\<open>qualifier_multi_bool\<close>])
    val _ =
      (case multi_ast of
         UE_Path path =>
           audit_assert "multi-backend value AST changed"
             (render_path path = "Multi::Registered::Value")
       | _ => error "multi-backend value AST changed")
    val _ =
      audit_assert "multi-backend checked term selected a different backend"
        (count_constant \<^const_name>\<open>qualifier_multi_nat\<close>
           multi_term = 1 andalso
         count_constant \<^const_name>\<open>qualifier_multi_bool\<close>
           multi_term = 0)

    val _ =
      assert_wrapped_registration "Some"
        (fn argument =>
          (case Term.head_of argument of
             Const (name, _) => name = \<^const_name>\<open>Option.Some\<close>
           | _ => false))
    val _ =
      assert_wrapped_registration "Ok"
        (fn argument =>
          (case Term.head_of argument of
             Const (name, _) => name = \<^const_name>\<open>Ok\<close>
           | _ => false))
    val _ =
      assert_wrapped_registration "Err"
        (fn argument =>
          (case Term.head_of argument of
             Const (name, _) => name = \<^const_name>\<open>Err\<close>
           | _ => false))
    val _ =
      assert_wrapped_registration "LiftedNavigation::named"
        (fn argument =>
          (case Term.head_of argument of
             Const (name, _) =>
               name = \<^const_name>\<open>lifted_navigation_pure\<close>
           | _ => false))
    val _ =
      assert_wrapped_registration "LiftedNavigation::anonymous"
        (fn Abs _ => true | _ => false)
  in
    val _ =
      writeln
        "Lifted constructor/function navigation, neutral patterns, wrapper-free lambdas, registration shape, AST, term, qualifier, and multiplicity regressions passed"
  end
\<close>

section\<open> Selected notation declaration navigation audit \<close>

definition selected_navigation_call_nat ::
    \<open>nat \<Rightarrow> (unit, nat, unit, unit, unit) function_body\<close>
  where
    \<open>
      selected_navigation_call_nat =
        lift_fun1 (\<lambda>value. value)
    \<close>

definition selected_navigation_call_bool ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      selected_navigation_call_bool =
        lift_fun1 (\<lambda>value. value)
    \<close>

micro_rust_notation (call)
  selected_navigation_call_nat
  ("Selected::Call::invoke")

micro_rust_notation (call)
  selected_navigation_call_bool
  ("Selected::Call::invoke")

datatype_record selected_navigation_record =
  selected_navigation_member :: nat

micro_rust_record selected_navigation_record
  (selected_navigation_member = "selected_navigation_field")

definition selected_navigation_record_value :: selected_navigation_record
  where
    \<open>
      selected_navigation_record_value =
        make_selected_navigation_record 7
    \<close>

ML_val\<open>
  local
    open URust_AST

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else
        error
          ("selected notation declaration navigation audit: " ^
            message)

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

    fun collect_markup_order (XML.Text _) = []
      | collect_markup_order (XML.Elem (markup, body)) =
          markup :: maps collect_markup_order body

    fun capture active_ctxt serial label text declared_type =
      let
        val start =
          Position.make0 (300 + serial) (80000 + serial * 800) 0 "" ""
            ("selected-notation-" ^ label ^ "-audit")
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val ast =
          (case URust_Parser.parse_source active_ctxt source of
             SOME expression => expression
           | NONE => error (label ^ " parsed as empty input"))
        val captured =
          Synchronized.var
            ("selected_notation_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured
            (fn current => current @ chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE]
                  (fn () =>
                    Exn.result
                      (fn () =>
                        URust_Command.elaborate active_ctxt
                          {kind = URust_Command.Expression,
                           source = source,
                           arguments = [],
                           arguments_pos = #2 (Input.range_of source),
                           declared_type =
                             Option.map
                               (fn typ => (typ, Position.none))
                               declared_type}) ())
                  ())
              ())
        val term =
          (case result of
             Exn.Res checked => checked
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 error
                   (label ^ " failed: " ^
                     Runtime.exn_message exn))
        val markup =
          Synchronized.value captured
          |> maps YXML.parse_body
          |> maps collect_markup_order
      in
        (start, ast, term, markup)
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun entity_events position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                has_position properties position
            then
              SOME
                (Properties.get properties Markup.kindN,
                 Properties.get properties Markup.nameN,
                 Properties.get properties Markup.refN)
            else NONE)

    fun notation_ref_order notation position markup =
      entity_events position markup
      |> map_filter
          (fn (SOME kind, SOME name, ref_id) =>
                if kind = Micro_Rust_Names.notationN andalso
                    name = notation
                then ref_id
                else NONE
            | _ => NONE)

    fun entry_ref ({serial, ...} : Micro_Rust_Names.entry) =
      Value.print_int serial

    fun selected_last_refs active_ctxt kind notation selected =
      let
        val entries = Micro_Rust_Names.lookups active_ctxt kind notation
      in
        entries
        |> filter
            (fn (entry : Micro_Rust_Names.entry) =>
              #serial entry <> #serial selected)
        |> map entry_ref
        |> (fn refs => refs @ [entry_ref selected])
      end

    fun backend_head_name ({hol_term, ...} : Micro_Rust_Names.entry) =
      (case Term.head_of (Term_Position.strip_positions hol_term) of
         Const (name, _) => SOME name
       | _ => NONE)

    fun entry_for_constant active_ctxt kind notation constant =
      (case
        Micro_Rust_Names.lookups active_ctxt kind notation
        |> filter
            (fn entry =>
              backend_head_name entry = SOME constant)
       of
         [entry] => entry
       | entries =>
           error
             ("expected one " ^ quote notation ^
               " registration for " ^ quote constant ^
               ", got " ^ string_of_int (length entries)))

    fun only_entry active_ctxt kind notation =
      (case Micro_Rust_Names.lookups active_ctxt kind notation of
         [entry] => entry
       | entries =>
           error
             ("expected one registration for " ^ quote notation ^
               ", got " ^ string_of_int (length entries)))

    fun is_backend_kind (SOME kind) =
          kind = Markup.constantN orelse kind = Markup.type_nameN
      | is_backend_kind NONE = false

    fun backend_entities_precede_notations events =
      let
        fun check _ [] = true
          | check seen_notation ((kind, _, _) :: rest) =
              if kind = SOME Micro_Rust_Names.notationN
              then check true rest
              else if seen_notation andalso is_backend_kind kind
              then false
              else check seen_notation rest
      in check false events end

    fun assert_selected_token active_ctxt label kind notation selected
        position markup =
      let
        val expected =
          selected_last_refs active_ctxt kind notation selected
        val actual =
          notation_ref_order notation position markup
        val events = entity_events position markup
        val final_event =
          if null events then NONE else SOME (List.last events)
      in
        audit_assert (label ^ " notation references changed")
          (actual = expected);
        audit_assert (label ^ " selected declaration was not final")
          (final_event =
            SOME
              (SOME Micro_Rust_Names.notationN,
               SOME notation,
               SOME (entry_ref selected)));
        audit_assert (label ^ " backend/type entity followed notation")
          (backend_entities_precede_notations events)
      end

    fun count_entity_kind kind position markup =
      entity_events position markup
      |> filter
          (fn (SOME actual, _, _) => actual = kind
            | _ => false)
      |> length

    fun count_markup markup_name position markup =
      markup
      |> filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
      |> length

    fun count_constant name term =
      Term.fold_aterms
        (fn Const (actual, _) =>
              if actual = name then Integer.add 1 else I
          | _ => I)
        term 0

    fun assert_path_ast label expected ast =
      (case ast of
         UE_Path path =>
           audit_assert (label ^ " path AST changed")
             (render_path path = expected)
       | _ => error (label ^ " path AST changed"))

    fun assert_call_ast label expected ast =
      (case ast of
         UE_Call (UC_Path path, _, _) =>
           audit_assert (label ^ " call AST changed")
             (render_path path = expected)
       | _ => error (label ^ " call AST changed"))

    val literal_text = "Multi::Registered::Value"
    val (literal_nat_start, literal_nat_ast,
         literal_nat_term, literal_nat_markup) =
      capture ctxt 0 "literal-nat" literal_text
        (SOME "(unit, nat, unit, unit, unit, unit) expression")
    val (literal_nat_outer_raw, literal_nat_outer) =
      token_position literal_text literal_nat_start "Multi" 0
    val (_, literal_nat_inner) =
      token_position literal_text literal_nat_start "Registered"
        (literal_nat_outer_raw + size "Multi::")
    val (_, literal_nat_terminal) =
      token_position literal_text literal_nat_start "Value"
        (size "Multi::Registered::")
    val literal_nat_entry =
      entry_for_constant ctxt Micro_Rust_Names.NLiteral
        literal_text \<^const_name>\<open>qualifier_multi_nat\<close>
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NLiteral literal_text
            literal_nat_entry position literal_nat_markup)
        [("nat literal outer qualifier", literal_nat_outer),
         ("nat literal inner qualifier", literal_nat_inner),
         ("nat literal terminal", literal_nat_terminal)]
    val _ = assert_path_ast "nat literal" literal_text literal_nat_ast
    val _ =
      audit_assert "nat literal selected backend term changed"
        (count_constant \<^const_name>\<open>qualifier_multi_nat\<close>
           literal_nat_term = 1 andalso
         count_constant \<^const_name>\<open>qualifier_multi_bool\<close>
           literal_nat_term = 0)

    val (literal_bool_start, literal_bool_ast,
         literal_bool_term, literal_bool_markup) =
      capture ctxt 1 "literal-bool" literal_text
        (SOME "(unit, bool, unit, unit, unit, unit) expression")
    val (literal_bool_outer_raw, literal_bool_outer) =
      token_position literal_text literal_bool_start "Multi" 0
    val (_, literal_bool_inner) =
      token_position literal_text literal_bool_start "Registered"
        (literal_bool_outer_raw + size "Multi::")
    val (_, literal_bool_terminal) =
      token_position literal_text literal_bool_start "Value"
        (size "Multi::Registered::")
    val literal_bool_entry =
      entry_for_constant ctxt Micro_Rust_Names.NLiteral
        literal_text \<^const_name>\<open>qualifier_multi_bool\<close>
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NLiteral literal_text
            literal_bool_entry position literal_bool_markup)
        [("bool literal outer qualifier", literal_bool_outer),
         ("bool literal inner qualifier", literal_bool_inner),
         ("bool literal terminal", literal_bool_terminal)]
    val _ = assert_path_ast "bool literal" literal_text literal_bool_ast
    val _ =
      audit_assert "bool literal selected backend term changed"
        (count_constant \<^const_name>\<open>qualifier_multi_bool\<close>
           literal_bool_term = 1 andalso
         count_constant \<^const_name>\<open>qualifier_multi_nat\<close>
           literal_bool_term = 0)

    fun audit_overloaded_call serial label argument selected_constant =
      let
        val notation = "Selected::Call::invoke"
        val text = notation ^ "(" ^ argument ^ ")"
        val (start, ast, term, markup) =
          capture ctxt serial label text NONE
        val (outer_raw, outer) =
          token_position text start "Selected" 0
        val (_, inner) =
          token_position text start "Call"
            (outer_raw + size "Selected::")
        val (_, terminal) =
          token_position text start "invoke"
            (size "Selected::Call::")
        val selected =
          entry_for_constant ctxt Micro_Rust_Names.NFunction
            notation selected_constant
        val _ =
          List.app
            (fn (token_label, position) =>
              assert_selected_token ctxt
                (label ^ " " ^ token_label)
                Micro_Rust_Names.NFunction notation
                selected position markup)
            [("outer qualifier", outer),
             ("inner qualifier", inner),
             ("terminal", terminal)]
        val _ = assert_call_ast label notation ast
        val _ =
          audit_assert (label ^ " selected backend term changed")
            (count_constant selected_constant term = 1)
      in () end

    val _ =
      audit_overloaded_call 2 "nat call"
        "\<llangle>7 :: nat\<rrangle>"
        \<^const_name>\<open>selected_navigation_call_nat\<close>
    val _ =
      audit_overloaded_call 3 "bool call"
        "true"
        \<^const_name>\<open>selected_navigation_call_bool\<close>

    val field_text =
      "\<llangle>selected_navigation_record_value\<rrangle>." ^
      "selected_navigation_field"
    val (field_start, _, field_term, field_markup) =
      capture ctxt 4 "field" field_text NONE
    val (_, field_position) =
      token_position field_text field_start
        "selected_navigation_field" 0
    val field_entry =
      only_entry ctxt Micro_Rust_Names.NField
        "selected_navigation_field"
    val field_backend =
      the (backend_head_name field_entry)
    val _ =
      assert_selected_token ctxt "field"
        Micro_Rust_Names.NField "selected_navigation_field"
        field_entry field_position field_markup
    val _ =
      audit_assert "field backend term changed"
        (count_constant field_backend field_term = 1)

    val constructor_text =
      "match_case \<llangle>ConstructorQualifierVariant\<rrangle> { " ^
      "Module::Type::Variant \<Rightarrow> (), _ \<Rightarrow> () }"
    val (constructor_start, _, _, constructor_markup) =
      capture ctxt 5 "constructor-pattern" constructor_text NONE
    val (constructor_path_raw, _) =
      token_position constructor_text constructor_start
        "Module::Type::Variant" 0
    val (constructor_outer_raw, constructor_outer) =
      token_position constructor_text constructor_start "Module"
        constructor_path_raw
    val (_, constructor_nearest) =
      token_position constructor_text constructor_start "Type"
        (constructor_outer_raw + size "Module::")
    val (_, constructor_terminal) =
      token_position constructor_text constructor_start "Variant"
        (constructor_path_raw + size "Module::Type::")
    val constructor_entry =
      only_entry ctxt Micro_Rust_Names.NLiteral
        "Module::Type::Variant"
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NLiteral
            "Module::Type::Variant"
            constructor_entry position constructor_markup)
        [("constructor outer qualifier", constructor_outer),
         ("constructor datatype qualifier", constructor_nearest),
         ("constructor terminal", constructor_terminal)]
    val _ =
      audit_assert "constructor datatype hover disappeared"
        (count_entity_kind Markup.type_nameN
           constructor_nearest constructor_markup = 1)
    val _ =
      audit_assert "constructor terminal backend hover disappeared"
        (count_entity_kind Markup.constantN
           constructor_terminal constructor_markup = 1)

    fun audit_registered_call serial label text notation qualifier
        terminal_name expected_backend =
      let
        val (start, ast, term, markup) =
          capture ctxt serial label text NONE
        val (_, qualifier_position) =
          token_position text start qualifier 0
        val terminal_position =
          #2
            (token_position text start terminal_name
              (find_from text terminal_name 0))
        val entry =
          only_entry ctxt Micro_Rust_Names.NFunction notation
        val _ =
          List.app
            (fn (token_label, position) =>
              assert_selected_token ctxt
                (label ^ " " ^ token_label)
                Micro_Rust_Names.NFunction notation entry
                position markup)
            [("qualifier", qualifier_position),
             ("terminal", terminal_position)]
        val _ =
          audit_assert (label ^ " backend hover disappeared")
            (count_entity_kind Markup.constantN
              terminal_position markup >= 1)
        val _ =
          audit_assert (label ^ " checked backend changed")
            (count_constant expected_backend term = 1)
        val _ =
          if String.isSuffix "!" notation then
            let
              val (_, bang_position) =
                token_position text start "!" 0
              val bang_events =
                entity_events bang_position markup
            in
              audit_assert
                (label ^ " bang acquired notation navigation")
                (notation_ref_order notation bang_position markup = []);
              audit_assert
                (label ^ " bang target changed")
                (map
                  (fn (kind, name, _) => (kind, name))
                  bang_events =
                  [(SOME Markup.constantN,
                    SOME expected_backend)]);
              audit_assert
                (label ^ " bang constant styling changed")
                (count_markup Markup.constN bang_position markup = 1)
            end
          else assert_call_ast label notation ast
      in () end

    val _ =
      audit_registered_call 6 "registered macro"
        "MacroModule::invoke!(true)"
        "MacroModule::invoke!" "MacroModule" "invoke"
        \<^const_name>\<open>qualifier_macro_call\<close>

    val anonymous_macro_text =
      "MacroModule::anonymous!(true)"
    val (anonymous_macro_start, _, anonymous_macro_term,
         anonymous_macro_markup) =
      capture ctxt 13 "anonymous-registered-macro"
        anonymous_macro_text NONE
    val (_, anonymous_macro_qualifier) =
      token_position anonymous_macro_text anonymous_macro_start
        "MacroModule" 0
    val (_, anonymous_macro_terminal) =
      token_position anonymous_macro_text anonymous_macro_start
        "anonymous" (size "MacroModule::")
    val (_, anonymous_macro_bang) =
      token_position anonymous_macro_text anonymous_macro_start "!" 0
    val anonymous_macro_entry =
      only_entry ctxt Micro_Rust_Names.NFunction
        "MacroModule::anonymous!"
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NFunction
            "MacroModule::anonymous!"
            anonymous_macro_entry position
            anonymous_macro_markup)
        [("anonymous macro qualifier", anonymous_macro_qualifier),
         ("anonymous macro terminal", anonymous_macro_terminal)]
    val _ =
      audit_assert "anonymous macro bang acquired notation navigation"
        (notation_ref_order "MacroModule::anonymous!"
          anonymous_macro_bang anonymous_macro_markup = [])
    val _ =
      audit_assert "anonymous macro bang acquired a false backend target"
        (entity_events anonymous_macro_bang anonymous_macro_markup = [])
    val _ =
      audit_assert "anonymous macro bang acquired constant styling"
        (count_markup Markup.constN
          anonymous_macro_bang anonymous_macro_markup = 0)
    val _ =
      audit_assert "anonymous macro checked term changed"
        (count_constant \<^const_name>\<open>lift_fun1\<close>
          anonymous_macro_term = 1)
    val _ =
      audit_registered_call 7 "exact turbofish"
        "GenericExact::<Token>::invoke()"
        "GenericExact::<Token>::invoke"
        "GenericExact" "invoke"
        \<^const_name>\<open>constructor_qualifier_call\<close>
    val _ =
      audit_registered_call 8 "lifted named function"
        "LiftedNavigation::named(\<llangle>4 :: nat\<rrangle>)"
        "LiftedNavigation::named"
        "LiftedNavigation" "named"
        \<^const_name>\<open>lift_fun1\<close>

    val lifted_lambda_text =
      "LiftedNavigation::anonymous(\<llangle>5 :: nat\<rrangle>)"
    val (lifted_lambda_start, lifted_lambda_ast,
         lifted_lambda_term, lifted_lambda_markup) =
      capture ctxt 9 "lifted-lambda" lifted_lambda_text NONE
    val (_, lifted_lambda_qualifier) =
      token_position lifted_lambda_text lifted_lambda_start
        "LiftedNavigation" 0
    val (_, lifted_lambda_terminal) =
      token_position lifted_lambda_text lifted_lambda_start
        "anonymous" (size "LiftedNavigation::")
    val lifted_lambda_entry =
      only_entry ctxt Micro_Rust_Names.NFunction
        "LiftedNavigation::anonymous"
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token ctxt label
            Micro_Rust_Names.NFunction
            "LiftedNavigation::anonymous"
            lifted_lambda_entry position lifted_lambda_markup)
        [("lifted lambda qualifier", lifted_lambda_qualifier),
         ("lifted lambda terminal", lifted_lambda_terminal)]
    val _ =
      audit_assert "lifted lambda gained a false backend entity"
        (count_entity_kind Markup.constantN
           lifted_lambda_terminal lifted_lambda_markup = 0)
    val _ =
      audit_assert "lifted lambda lost terminal styling"
        (count_markup Markup.keyword3N
           lifted_lambda_terminal lifted_lambda_markup = 1)
    val _ =
      assert_call_ast "lifted lambda"
        "LiftedNavigation::anonymous" lifted_lambda_ast
    val _ =
      audit_assert "lifted lambda checked term changed"
        (count_constant \<^const_name>\<open>lift_fun1\<close>
           lifted_lambda_term = 1)

    val some_value_text = "Some(\<llangle>1 :: nat\<rrangle>)"
    val (some_value_start, _, _, some_value_markup) =
      capture ctxt 10 "some-value" some_value_text NONE
    val (_, some_value_position) =
      token_position some_value_text some_value_start "Some" 0
    val some_entry =
      only_entry ctxt Micro_Rust_Names.NFunction "Some"
    val _ =
      assert_selected_token ctxt "Some value"
        Micro_Rust_Names.NFunction "Some" some_entry
        some_value_position some_value_markup
    val _ =
      audit_assert "Some value lost constructor hover"
        (count_entity_kind Markup.constantN
           some_value_position some_value_markup = 1)

    val native_pattern_text =
      "match_case \<llangle>Some (1 :: nat)\<rrangle> { " ^
      "Some(value) \<Rightarrow> value, None \<Rightarrow> 0 }"
    val (native_pattern_start, _, _, native_pattern_markup) =
      capture ctxt 11 "native-pattern" native_pattern_text NONE
    val (native_pattern_raw, _) =
      token_position native_pattern_text native_pattern_start
        "Some" (size "match_case \<llangle>Some (1 :: nat)\<rrangle> { ")
    val (_, native_pattern_position) =
      token_position native_pattern_text native_pattern_start
        "Some" native_pattern_raw
    val _ =
      audit_assert "native Some pattern acquired notation navigation"
        (notation_ref_order "Some"
          native_pattern_position native_pattern_markup = [])
    val _ =
      audit_assert "native Some pattern lost constructor navigation"
        (count_entity_kind Markup.constantN
           native_pattern_position native_pattern_markup = 1)

    val synthetic_name = "Synthetic::Variant"
    val synthetic_constructor =
      \<^term>\<open>ConstructorQualifierVariant\<close>
    val low_serial = serial ()
    val high_serial = serial ()
    val low_entry : Micro_Rust_Names.entry =
      {hol_term = synthetic_constructor,
       source_const = SOME synthetic_constructor,
       reg_pos =
         Position.make0 390 93000 0 "" ""
           "synthetic-notation-low-declaration",
       serial = low_serial}
    val high_entry : Micro_Rust_Names.entry =
      {hol_term = synthetic_constructor,
       source_const = SOME synthetic_constructor,
       reg_pos =
         Position.make0 391 93100 0 "" ""
           "synthetic-notation-high-declaration",
       serial = high_serial}
    (* Two registrations of one constructor stay distinct in the registry view only as automatic
       registrations, each with its own identity; explicit duplicates are represented by one. *)
    val synthetic_ctxt =
      Context.Proof ctxt
      |> Micro_Rust_Names.mark_automatic low_serial
      |> Micro_Rust_Names.mark_automatic high_serial
      |> Micro_Rust_Names.Data.map
          (Symtab.update
            (Micro_Rust_Names.mk_key Micro_Rust_Names.NLiteral synthetic_name,
             [low_entry, high_entry]))
      |> Context.proof_of
    val synthetic_text =
      "match_case \<llangle>ConstructorQualifierVariant\<rrangle> { " ^
      synthetic_name ^ " \<Rightarrow> (), _ \<Rightarrow> () }"
    val (synthetic_start, _, _, synthetic_markup) =
      capture synthetic_ctxt 12 "same-constructor" synthetic_text NONE
    val (synthetic_path_raw, _) =
      token_position synthetic_text synthetic_start synthetic_name 0
    val (_, synthetic_qualifier) =
      token_position synthetic_text synthetic_start "Synthetic"
        synthetic_path_raw
    val (_, synthetic_terminal) =
      token_position synthetic_text synthetic_start "Variant"
        (synthetic_path_raw + size "Synthetic::")
    val _ =
      audit_assert "synthetic serial order precondition changed"
        (low_serial < high_serial)
    val _ =
      List.app
        (fn (label, position) =>
          assert_selected_token synthetic_ctxt label
            Micro_Rust_Names.NLiteral synthetic_name low_entry
            position synthetic_markup)
        [("same-constructor qualifier", synthetic_qualifier),
         ("same-constructor terminal", synthetic_terminal)]
    val _ =
      audit_assert "same-constructor references were not both preserved"
        (notation_ref_order synthetic_name synthetic_terminal
           synthetic_markup =
          [Value.print_int high_serial, Value.print_int low_serial])
  in
    val _ =
      writeln
        "Selected notation declarations are final on registered literal, call, field, constructor, macro, turbofish, lifted, and overloaded tokens while backend/type hover, native fallback, ASTs, terms, multiplicity, and deterministic constructor priority remain intact"
  end
\<close>

section\<open> Deferred semantic target navigation audit \<close>

ML_val\<open>
  local
    structure Navigation = Micro_Rust_Semantic_Navigation

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("deferred semantic target navigation audit: " ^ message)

    fun collect_markup_order (XML.Text _) = []
      | collect_markup_order (XML.Elem (markup, body)) =
          markup :: maps collect_markup_order body

    fun capture_markup label action =
      let
        val captured =
          Synchronized.var
            ("semantic_navigation_" ^ label ^ "_reports")
            ([]: string list)
        fun report chunks =
          Synchronized.change captured
            (fn current => current @ chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn report
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE] action ())
              ())
        val markup =
          Synchronized.value captured
          |> maps YXML.parse_body
          |> maps collect_markup_order
      in (result, markup) end

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
        Position.range_position
          (token_start, Position.symbol_explode needle token_start)
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun constant_targets position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN =
                  SOME Markup.constantN andalso
                has_position properties position
            then Properties.get properties Markup.nameN
            else NONE)

    fun count_markup markup_name position markup =
      markup
      |> filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
      |> length

    val source_text = "panic!()"
    val source_start =
      Position.make0 410 97000 0 "" ""
        "deferred-semantic-target-navigation-audit"
    val panic_position =
      token_position source_text source_start "panic" 0
    val bang_position =
      token_position source_text source_start "!" 0
    val source =
      Parser_Lex_Util.positioned_content_source
        source_text source_start

    val ((_, reports), during_markup) =
      capture_markup "capture" (fn () =>
        Navigation.capture (fn () =>
          (Navigation.defer_report ctxt bang_position Markup.keyword3;
           Parser_Test_Elaboration.expression ctxt source)))

    val _ =
      List.app
        (fn (label, position) =>
          (audit_assert
             (label ^ " emitted targets before replay")
             (constant_targets position during_markup = []);
           audit_assert
             (label ^ " emitted constant styling before replay")
             (count_markup Markup.constN
                position during_markup = 0)))
        [("panic token", panic_position),
         ("bang token", bang_position)]
    val _ =
      audit_assert "generic markup was not deferred"
        (count_markup Markup.keyword3N
          bang_position during_markup = 0)

    val ((), replay_markup) =
      capture_markup "replay" (fn () =>
        Navigation.replay ctxt reports)
    val expected_targets =
      [\<^const_name>\<open>abort\<close>,
       \<^const_name>\<open>Panic\<close>]
    val _ =
      List.app
        (fn (label, position) =>
          (audit_assert
             (label ^
              " target order, stable deduplication, or primary-last " ^
              "classification changed")
             (constant_targets position replay_markup =
               expected_targets);
           audit_assert
             (label ^ " native constant styling count changed")
             (count_markup Markup.constN
                position replay_markup = 2)))
        [("panic token", panic_position),
         ("bang token", bang_position)]
    val _ =
      audit_assert "generic deferred markup was not replayed"
        (count_markup Markup.keyword3N
          bang_position replay_markup = 1)

    val (failure_result, failure_markup) =
      capture_markup "failure" (fn () =>
        Exn.result
          (fn () =>
            Navigation.capture (fn () =>
              (ignore
                (Parser_Test_Elaboration.expression ctxt source);
               error "intentional semantic navigation failure")))
          ())
    val _ =
      (case failure_result of
         Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ()
       | Exn.Res _ =>
           error
             ("deferred semantic target navigation audit: " ^
              "intentional failure unexpectedly succeeded"))
    val _ =
      audit_assert "failed capture leaked semantic targets"
        (constant_targets panic_position failure_markup = [] andalso
         count_markup Markup.constN panic_position failure_markup = 0)
  in
    val _ =
      writeln
        "Deferred semantic navigation target order, exact ranges, stable deduplication, native entity/style markup, generic replay, and failure isolation passed"
  end
\<close>

chapter\<open>Turbofish\<close>

section\<open> Structural and semantic audit \<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("restricted turbofish audit: " ^ message)

    fun parse_source source =
      (case URust_Parser.parse_source ctxt source of
         SOME expression => expression
       | NONE => error "restricted turbofish audit: empty parse")

    fun parse text =
      parse_source (Parser_Lex_Util.text_source text)

    fun generic_arguments text =
      (case parse text of
         UE_Call (UC_Path path, [], _) =>
           (case path_segments path of
              [Path_Segment
                ("f", _, SOME (Generic_Args (arguments, _)))] =>
                  arguments
            | _ =>
                error
                  ("restricted turbofish audit: path shape changed for " ^
                    quote text))
       | _ =>
           error ("restricted turbofish audit: call shape changed for " ^
             quote text))

    fun one_generic text =
      (case generic_arguments text of
         [Generic_Arg (canonical, source)] => (canonical, source)
       | _ =>
           error ("restricted turbofish audit: expected one argument for " ^
             quote text))

    val canonical_cases =
      [("f::<a + b + c>()", "a+b+c"),
       ("f::<(a + b) + c>()", "(a+b)+c"),
       ("f::<Module::Value>()", "Module::Value"),
       ("f::<42>()", "42"),
       ("f::<0x2a>()", "0x2a")]
    val _ =
      List.app
        (fn (source, expected) =>
          audit_assert ("canonical fragment changed for " ^ quote source)
            (#1 (one_generic source) = expected))
        canonical_cases

    val spaced_text = "f::\n <  a +\n b + c  ,  (d) >()"
    val spaced_start =
      Position.make0 11 40 400 "" "" "restricted-turbofish-source-audit"
    val spaced =
      parse_source
        (Parser_Lex_Util.positioned_content_source
          spaced_text spaced_start)
    val _ =
      (case spaced of
         UE_Call (UC_Path path, [], _) =>
           (case path_segments path of
              [Path_Segment
                ("f", _,
                 SOME (Generic_Args
                   ([Generic_Arg (first_canonical, first_source),
                     Generic_Arg (second_canonical, second_source)],
                    generic_pos)))] =>
           let
             val expected_generic_start =
               Position.symbol_explode "f" spaced_start
             val first_start =
               Position.symbol_explode "f::\n <  " spaced_start
             val first_stop =
               Position.symbol_explode "f::\n <  a +\n b + c" spaced_start
             val second_start =
               Position.symbol_explode "f::\n <  a +\n b + c  ,  " spaced_start
             val second_stop =
               Position.symbol_explode "f::\n <  a +\n b + c  ,  (d)" spaced_start
           in
             audit_assert "canonical rendering retained trivia"
               (first_canonical = "a+b+c" andalso
                second_canonical = "(d)");
             audit_assert "first original source slice changed"
               (Input.string_of first_source = "a +\n b + c" andalso
                Position.offset_of (#1 (Input.range_of first_source)) =
                  Position.offset_of first_start andalso
                Position.offset_of (#2 (Input.range_of first_source)) =
                  Position.offset_of first_stop);
             audit_assert "second original source slice changed"
               (Input.string_of second_source = "(d)" andalso
                Position.offset_of (#1 (Input.range_of second_source)) =
                  Position.offset_of second_start andalso
                Position.offset_of (#2 (Input.range_of second_source)) =
                  Position.offset_of second_stop);
             audit_assert "generic span did not start at the path separator"
               (Position.offset_of generic_pos =
                  Position.offset_of expected_generic_start)
           end
            | _ =>
                error
                  "restricted turbofish audit: multiline path shape changed")
       | _ => error "restricted turbofish audit: multiline call shape changed")

    fun checked_generic_argument source =
      let
        val checked =
          Syntax.check_term ctxt
            (URust_Translate.mk_expression ctxt [] (parse source))
        val function =
          (case Term.strip_comb checked of
             (_, function :: _) => function
           | _ => error "restricted turbofish audit: checked call shape changed")
      in
        (case Term.strip_comb
            (Term_Position.strip_positions function) of
           (_, [argument]) => Term_Position.strip_positions argument
         | _ =>
             error "restricted turbofish audit: generic application shape changed")
      end

    fun check_semantic source expected =
      let
        val actual = checked_generic_argument source
        val wanted =
          Syntax.read_term ctxt expected
          |> Term_Position.strip_positions
      in
        audit_assert ("checked HOL shape changed for " ^ quote source)
          (actual aconv wanted)
      end

    val _ =
      List.app (fn (source, expected) => check_semantic source expected)
        [("turbofish_int_one::<1 + 2 + 3>(0)", "(1 + 2 + 3 :: int)"),
         ("turbofish_int_one::<(1 + 2) + 3>(0)", "((1 + 2) + 3 :: int)")]

    val exact_term =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "Exact::f::<N>()")
    val fallback_term =
      Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source "Exact::f::<1>(2)")
    val _ =
      audit_assert "complete exact registration did not win"
        (Term.exists_subterm
          (fn Const (name, _) => name = \<^const_name>\<open>cf0\<close>
            | _ => false)
          exact_term)
    val _ =
      audit_assert "final exact miss did not use semantic fallback"
        (Term.exists_subterm
          (fn Const (name, _) => name = \<^const_name>\<open>exact_fallback\<close>
            | _ => false)
          fallback_term)

    fun expect_rejection text expected =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source text)) () of
         Exn.Res _ =>
           error ("restricted turbofish audit: unexpectedly accepted " ^
             quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             audit_assert ("diagnostic changed for " ^ quote text)
               (String.isSubstring expected (Runtime.exn_message exn)))

    val _ =
      expect_rejection "GenericFactory::<Missing>::make()"
        "generic arguments on an intermediate path segment require an exact registration"
    val malformed =
      [("f::<>()", "syntax error"),
       ("f::<,1>()", "syntax error"),
       ("f::<1,,2>()", "syntax error"),
       ("f::<1,>()", "syntax error"),
       ("f::<1 a>()", "syntax error"),
       ("f::<1 +>()", "syntax error"),
       ("f::<-1>()", "unexpected input"),
       ("f::<1 - 2>()", "unexpected input"),
       ("f::<1 * 2>()", "unexpected input"),
       ("f::<1 / 2>()", "unexpected input"),
       ("f::<((1)>()", "syntax error"),
       ("f::<1)>()", "syntax error"),
       ("f::<1(", "unterminated turbofish"),
       ("f::<1>>()",
        "generic arguments on a bare value require an exact literal registration"),
       ("f::<1u8>()", "syntax error"),
       ("f::<Suc 4>()", "syntax error"),
       ("f::<a div b>()", "syntax error"),
       ("f::<a mod b>()", "syntax error"),
       ("f::<(1, 2)>()", "syntax error"),
       ("f::<[1, 2]>()", "unexpected input"),
       ("f::<\"text\">()", "unexpected input"),
       ("f::<STR ''text''>()", "unexpected input"),
       ("f::<1 :: nat>()", "syntax error"),
       ("f::<a < b>()", "unterminated turbofish"),
       ("f::<a << b>()", "syntax error"),
       ("f::<a & b>()", "unexpected input"),
       ("f::<a && b>()", "unexpected input"),
       ("f::<a % b>()", "unexpected input"),
       ("f::<a ^ b>()", "unexpected input"),
       ("f::<\<clubsuit>>()", "unexpected input"),
       ("f::<" ^ Symbol.open_ ^ "opaque" ^ Symbol.close ^ ">()",
        "unexpected input"),
       ("f::<\<epsilon>\<open>1\<close>>()", "unexpected input"),
       ("f::<1 // comment\n + 2>()", "unexpected input")]
    val _ =
      List.app
        (fn (source, expected) =>
          (expect_rejection source expected;
           case parse "cf0()" of
             UE_Call (UC_Path path, [], _) =>
               audit_assert "lexer state leaked after malformed generic input"
                 (render_path path = "cf0")
           | _ => error "restricted turbofish audit: recovery parse changed"))
        malformed
  in
    val _ = writeln "Restricted turbofish AST, semantics, lookup, and recovery passed"
  end
\<close>

section\<open> Markup and diagnostics \<close>

definition generic_markup_value :: int where
  \<open> generic_markup_value = 8 \<close>

definition generic_markup_call ::
  \<open>nat \<Rightarrow> int \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_markup_call _ _ \<equiv> cf1 \<close>

ML_val\<open>
  local
    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("restricted turbofish markup audit: " ^ message)

    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)

    fun capture_reports action =
      let
        val captured = Synchronized.var "parser_test_reports" ([]: string list)
        fun capture chunks =
          Synchronized.change captured (append chunks)
        val result =
          Parser_Test_Report_Lock.run (fn () =>
            Unsynchronized.setmp Private_Output.report_fn capture
              (fn () =>
                Print_Mode.with_modes [Print_Mode.PIDE] action ()) ())
        val markup =
          fold collect_markup
            (maps YXML.parse_body (Synchronized.value captured)) []
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

    val text = "generic_markup_call::\n <(1+2), generic_markup_value+2+1>(0)"
    val start =
      Position.make0 31 80 800 "" "" "restricted-turbofish-markup"
    val (_, markup) =
      capture_reports
        (fn () =>
          ignore
            (Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.positioned_content_source text start)))
    val delimiters =
      [source_position start "generic_markup_call" "::",
       source_position start "generic_markup_call::\n " "<",
       source_position start "generic_markup_call::\n <" "(",
       source_position start "generic_markup_call::\n <(1+2" ")",
       source_position start "generic_markup_call::\n <(1+2)" ",",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2+1" ">"]
    val operators =
      [source_position start "generic_markup_call::\n <(1" "+",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value" "+",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2" "+"]
    val numerals =
      [source_position start "generic_markup_call::\n <(" "1",
       source_position start "generic_markup_call::\n <(1+" "2",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+" "2",
       source_position start
         "generic_markup_call::\n <(1+2), generic_markup_value+2+" "1"]
    val _ =
      List.app
        (fn position =>
          audit_assert "generic delimiter markup moved"
            (has_markup markup Markup.delimiterN position))
        delimiters
    val _ =
      List.app
        (fn position =>
          audit_assert "generic operator markup moved"
            (has_markup markup Markup.operatorN position))
        operators
    val _ =
      List.app
        (fn position =>
          audit_assert "generic numeral markup moved"
            (has_markup markup Markup.numeralN position))
        numerals

    val operator_text = "f::<1+2+3>()"
    val operator_start =
      Position.make0 37 100 1000 "" "" "restricted-turbofish-all-operators"
    val (_, operator_markup) =
      capture_reports
        (fn () =>
          ignore
            (URust_Parser.parse_source ctxt
              (Parser_Lex_Util.positioned_content_source
                operator_text operator_start)))
    val all_operators =
      [source_position operator_start "f::<1" "+",
       source_position operator_start "f::<1+2" "+"]
    val _ =
      List.app
        (fn position =>
          audit_assert "arithmetic operator markup moved"
            (has_markup operator_markup Markup.operatorN position))
        all_operators

    val malformed_text = "// \<clubsuit>\nf::<1 + %>()"
    val malformed_start =
      Position.make0 41 120 1200 "" "" "restricted-turbofish-symbol-offset"
    val expected_position =
      Position.symbol_explode "// \<clubsuit>\nf::<1 + " malformed_start
    val message =
      (case Exn.result
          (fn () =>
            URust_Parser.parse_source ctxt
              (Parser_Lex_Util.positioned_content_source
                malformed_text malformed_start)) () of
         Exn.Res _ => error "restricted turbofish markup audit: malformed input accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else Runtime.exn_message exn)
    val plain = XML.content_of (YXML.parse_body message)
    val message_markup =
      fold collect_markup (YXML.parse_body message) []
    val _ =
      audit_assert "smallest offending generic token changed"
        (String.isSubstring "unexpected input \"%\"" plain)
    val _ =
      audit_assert "Isabelle-symbol-counted diagnostic offset changed"
        (exists
          (fn (_, properties) =>
            Properties.get properties Markup.offsetN =
              Option.map Value.print_int
                (Position.offset_of expected_position))
          message_markup)
  in
    val _ = writeln "Restricted turbofish markup and diagnostics passed"
  end
\<close>

definition generic_navigation_call ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> 64 word \<Rightarrow>
    (unit, 64 word, unit, unit, unit) function_body\<close>
  where \<open> generic_navigation_call _ _ \<equiv> cf1 \<close>

context
  fixes generic_free :: nat
begin

ML_val\<open>
  local
    val ctxt = \<^context>
    val text =
      "let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
      "generic_navigation_call::<generic_free, generic_bound>(0)"
    val start =
      Position.make0 47 140 1400 "" "" "restricted-turbofish-identifier-markup"
    val captured = Synchronized.var "parser_test_reports" ([]: string list)
    fun capture chunks =
      Synchronized.change captured (append chunks)
    val _ =
      Parser_Test_Report_Lock.run (fn () =>
        Unsynchronized.setmp Private_Output.report_fn capture
          (fn () =>
            Print_Mode.with_modes [Print_Mode.PIDE]
              (fn () =>
                ignore
                  (Parser_Test_Elaboration.expression ctxt
                    (Parser_Lex_Util.positioned_content_source text start))) ()) ())
    fun collect_markup (XML.Text _) result = result
      | collect_markup (XML.Elem (markup, body)) result =
          fold collect_markup body (markup :: result)
    val markup =
      fold collect_markup
        (maps YXML.parse_body (Synchronized.value captured)) []
    fun token_position prefix token =
      let
        val token_start = Position.symbol_explode prefix start
        val token_stop = Position.symbol_explode token token_start
      in Position.range_position (Position.range (token_start, token_stop)) end
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup markup_name position =
      exists
        (fn (name, properties) =>
          name = markup_name andalso has_position properties position)
        markup
    val free_position =
      token_position
        ("let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
          "generic_navigation_call::<")
        "generic_free"
    val bound_position =
      token_position
        ("let generic_bound = \<llangle>1 :: nat\<rrangle>; " ^
          "generic_navigation_call::<generic_free, ")
        "generic_bound"
    val _ =
      if has_markup Markup.freeN free_position then ()
      else error "restricted turbofish markup audit: context fix lost free markup"
    val _ =
      if has_markup Markup.boundN bound_position then ()
      else error "restricted turbofish markup audit: generic binder lost bound markup"
  in end
\<close>

end

section\<open> Canonical exact-key regressions \<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>

    fun parse_path text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.text_source text) of
         SOME (UE_Call (UC_Path path, [], _)) => path
       | _ => error ("canonical exact-key regression: unexpected AST for " ^ quote text))

    val identifier = render_path (parse_path "f::<adivb>()")
    val _ =
      if identifier = "f::<adivb>" then ()
      else error "canonical exact-key regression: identifier rendering changed"
    val _ =
      (case Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.text_source
                "f::<a div b>()")) () of
         Exn.Res _ =>
           error "canonical exact-key regression: a div b was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else ())
    val {suppress_warning, ...} =
      Micro_Rust_Names.shadow_opts ctxt Micro_Rust_Names.NFunction
        "AuditConfig::<a+b>::new"
    val _ =
      if suppress_warning then ()
      else error "urust_notation configuration did not canonicalize its name"
  in end
\<close>

section\<open>Shared iterator zip registration audit\<close>

ML\<open>
local
  fun assert message condition =
    if condition then () else error message

  fun theorem_term name =
    Thm.prop_of (Proof_Context.get_thm \<^context> name)

  fun contains_const name =
    Term.exists_subterm
      (fn Const (actual, _) => actual = name | _ => false)

  val iterator_zip_name = \<^const_name>\<open>iterator_zip\<close>
  val hol_zip_name = \<^const_name>\<open>List.zip\<close>
  val funcall1_name = \<^const_name>\<open>funcall1\<close>
  val funcall2_name = \<^const_name>\<open>funcall2\<close>

  val direct_terms =
    map theorem_term
      ["iterator_zip_expr_direct_def", "iterator_zip_direct_def"]
  val method_terms =
    map theorem_term
      ["iterator_zip_expr_method_def", "iterator_zip_method_def"]
  val chained_terms =
    map theorem_term
      ["iterator_zip_expr_chained_def", "iterator_zip_chained_def"]

  val _ =
    List.app
      (fn term =>
        assert "direct zip did not resolve through iterator_zip notation"
          (contains_const iterator_zip_name term))
      direct_terms
  val _ =
    List.app
      (fn term =>
        (assert "method zip did not resolve through iterator_zip notation"
           (contains_const iterator_zip_name term);
         assert "method zip did not use receiver-prepended binary arity"
           (contains_const funcall2_name term);
         assert "pure HOL List.zip leaked into method uRust lowering"
           (not (contains_const hol_zip_name term))))
      method_terms
  val _ =
    List.app
      (fn term =>
        (assert "chained zip did not resolve through iterator_zip notation"
           (contains_const iterator_zip_name term);
         assert "chained zip lost ordinary into_iter lowering"
           (contains_const funcall1_name term);
         assert "chained zip did not use receiver-prepended binary arity"
           (contains_const funcall2_name term)))
      chained_terms

  val registrations =
    Micro_Rust_Names.lookups \<^context> Micro_Rust_Names.NFunction "zip"
  val _ =
    assert "zip notation is not registered to iterator_zip"
      (exists
        (fn {hol_term, ...} => contains_const iterator_zip_name hol_term)
        registrations)
in
end
\<close>

chapter\<open> Semantic navigation \<close>

section\<open>Resolved navigation fixtures\<close>

consts
  semantic_navigation_ref ::
    \<open>(unit, unit, 32 word) Global_Store.ref\<close>
  semantic_navigation_word :: \<open>32 word\<close>
  semantic_navigation_shift :: \<open>64 word\<close>
  semantic_navigation_gref :: \<open>(unit, unit) gref\<close>

definition semantic_navigation_allocate ::
    \<open>32 word \<Rightarrow>
      (unit, (unit, unit, 32 word) Global_Store.ref,
       unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_allocate _ =
        FunctionBody (literal semantic_navigation_ref)
    \<close>

definition semantic_navigation_dereference ::
    \<open>(unit, unit, 32 word) Global_Store.ref \<Rightarrow>
      (unit, 32 word, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_dereference _ =
        FunctionBody (literal 0)
    \<close>

definition semantic_navigation_update ::
    \<open>(unit, unit, 32 word) Global_Store.ref \<Rightarrow> 32 word \<Rightarrow>
      (unit, unit, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_update _ _ =
        FunctionBody (literal ())
    \<close>

definition semantic_navigation_assign_add ::
    \<open>(unit, unit, 32 word) Global_Store.ref \<Rightarrow> 32 word \<Rightarrow>
      (unit, unit, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_assign_add _ _ =
        FunctionBody (literal ())
    \<close>

adhoc_overloading assign_add_const \<rightleftharpoons> semantic_navigation_assign_add
adhoc_overloading store_dereference_const \<rightleftharpoons> semantic_navigation_dereference
adhoc_overloading store_reference_const \<rightleftharpoons> semantic_navigation_allocate
adhoc_overloading store_update_const \<rightleftharpoons> semantic_navigation_update

definition semantic_navigation_field :: \<open>(nat, nat) lens\<close>
  where \<open>semantic_navigation_field = id\<^sub>L\<close>

definition semantic_navigation_focus ::
    \<open>(nat, nat) lens \<Rightarrow> nat \<Rightarrow> nat\<close>
  where
    \<open>semantic_navigation_focus field value = lens_view field value\<close>

adhoc_overloading focus_lens_const \<rightleftharpoons> semantic_navigation_focus

micro_rust_notation (field)
  semantic_navigation_field
  ("navigationField")

definition semantic_navigation_named_macro ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_named_macro =
        lift_fun1 (\<lambda>value. value)
    \<close>

abbreviation semantic_navigation_abbrev_macro ::
    \<open>bool \<Rightarrow> (unit, bool, unit, unit, unit) function_body\<close>
  where
    \<open>
      semantic_navigation_abbrev_macro \<equiv>
        semantic_navigation_named_macro
    \<close>

micro_rust_notation (call)
  semantic_navigation_named_macro
  ("NavigationMacro::named!")

micro_rust_notation (call)
  semantic_navigation_abbrev_macro
  ("NavigationMacro::abbrev!")

micro_rust_notation (call)
  \<open>lift_fun1 (\<lambda>value :: bool. value)\<close>
  ("NavigationMacro::anonymous!")

urust_datatype \<open>
  enum NavigationGeneratedValue { Empty, Payload(u32) }
\<close>

section\<open>Checked resolved denotations\<close>

ML_val\<open>
  local
    structure Navigation = Micro_Rust_Semantic_Navigation

    val ctxt = \<^context>

    fun audit_assert message condition =
      if condition then ()
      else error ("resolved semantic navigation audit: " ^ message)

    fun find_from text needle offset =
      if offset + size needle > size text then
        error ("missing " ^ quote needle ^ " in " ^ quote text)
      else if String.substring (text, offset, size needle) = needle
      then offset
      else find_from text needle (offset + 1)

    fun nth_from text needle occurrence =
      let
        fun seek index offset =
          let val found = find_from text needle offset
          in
            if index = occurrence then found
            else seek (index + 1) (found + size needle)
          end
      in seek 0 0 end

    fun token_position text start needle occurrence =
      let
        val raw = nth_from text needle occurrence
        val token_start =
          Position.symbol_explode
            (String.substring (text, 0, raw)) start
      in
        Position.range_position
          (token_start, Position.symbol_explode needle token_start)
      end

    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position) andalso
      Properties.get properties Markup.idN =
        Position.id_of position

    fun entity_names kind position markup =
      markup
      |> map_filter
          (fn (name, properties) =>
            if name = Markup.entityN andalso
                Properties.get properties Markup.kindN = SOME kind andalso
                has_position properties position
            then Properties.get properties Markup.nameN
            else NONE)

    fun constant_targets position markup =
      entity_names Markup.constantN position markup

    fun count_markup markup_name position markup =
      markup
      |> filter
          (fn (name, properties) =>
            name = markup_name andalso
              has_position properties position)
      |> length

    fun contains_navigation_marker term =
      Term.exists_subterm
        (fn Const (name, _) =>
              name =
                \<^const_name>\<open>semantic_navigation_target\<close> orelse
              name =
                \<^const_name>\<open>semantic_navigation_annotation\<close> orelse
              name =
                \<^const_name>\<open>semantic_navigation_probe\<close>
          | _ => false)
        term

    fun head_constant_name label term =
      (case Term.head_of (Term_Position.strip_positions term) of
         Const (name, _) => name
       | head =>
           error
             ("resolved semantic navigation audit: " ^
               label ^ " has non-constant head " ^
               Syntax.string_of_term ctxt head))

    val ucast_name =
      head_constant_name "ucast" \<^term>\<open>ucast\<close>
    val scast_name =
      head_constant_name "scast" \<^term>\<open>scast\<close>
    val word_type_name =
      (case \<^typ>\<open>64 word\<close> of
         Type (name, _) => name
       | _ =>
           error
             "resolved semantic navigation audit: word type is not a type constructor")
    val abbreviation_name =
      (case
          Proof_Context.read_const
            {proper = true, strict = false} ctxt
            "semantic_navigation_abbrev_macro" of
         Const (name, _) => name
       | _ =>
           error
             "resolved semantic navigation audit: abbreviation identity is not a constant")
    val info_name =
      (case
          Proof_Context.read_const
            {proper = true, strict = false} ctxt "info" of
         Const (name, _) => name
       | _ =>
           error
             "resolved semantic navigation audit: logger identity is not a constant")

    fun capture serial label text =
      let
        val start =
          Position.make0
            (500 + serial) (120000 + serial * 1000)
            0 "" ""
            ("resolved-semantic-navigation-" ^ label)
        val source =
          Parser_Lex_Util.positioned_content_source text start
        val (term, markup) =
          Parser_Test_Reports.markup (fn () =>
            Parser_Test_Elaboration.expression ctxt source)
        val _ =
          audit_assert
            (label ^ " returned an internal navigation marker")
            (not (contains_navigation_marker term))
      in
        {start = start, term = term, markup = markup}
      end

    fun audit_case serial label text specifications =
      let
        val {start, markup, ...} =
          capture serial label text
        fun check (needle, occurrence, expected) =
          let
            val position =
              token_position text start needle occurrence
            val actual = constant_targets position markup
          in
            audit_assert
              (label ^ " target changed at " ^
                quote needle ^ " occurrence " ^
                string_of_int occurrence ^
                ": expected " ^ commas_quote expected ^
                ", found " ^ commas_quote actual)
              (actual = expected);
            audit_assert
              (label ^ " native constant styling count changed")
              (count_markup Markup.constN position markup =
                length expected)
          end
      in List.app check specifications end

    fun audit_target_group serial label text specifications expected =
      let
        val {start, markup, ...} =
          capture serial label text
        fun targets (needle, occurrence) =
          constant_targets
            (token_position text start needle occurrence)
            markup
        val actual = map targets specifications
        val _ =
          List.app
            (fn (specification, found) =>
              let
                val (needle, occurrence) = specification
              in
                audit_assert
                  (label ^ " target changed at " ^
                    quote needle ^ " occurrence " ^
                    string_of_int occurrence ^
                    ": expected " ^ commas_quote expected ^
                    ", found " ^ commas_quote found)
                  (found = expected);
                audit_assert
                  (label ^ " native constant styling count changed")
                  (count_markup Markup.constN
                    (token_position text start
                      needle occurrence) markup =
                    length expected)
              end)
            (specifications ~~ actual)
        val _ =
          audit_assert
            (label ^ " paired or grouped tokens diverged")
            (case actual of
               [] => false
             | first :: rest =>
                 List.all (fn targets => targets = first) rest)
      in () end

    fun audit_markup_count serial label text needle occurrence
        markup_name expected =
      let
        val {start, markup, ...} =
          capture serial label text
        val position =
          token_position text start needle occurrence
      in
        audit_assert (label ^ " markup count changed")
          (count_markup markup_name position markup = expected)
      end

    fun audit_term_invariant serial label text =
      let
        val {term = positioned, ...} =
          capture serial label text
        val plain =
          Parser_Test_Elaboration.expression ctxt
            (Parser_Lex_Util.text_source text)
        val strip = Term_Position.strip_positions
      in
        audit_assert
          (label ^ " navigation changed the checked term")
          (Term.aconv (strip positioned, strip plain));
        audit_assert
          (label ^ " unpositioned term retained a marker")
          (not (contains_navigation_marker plain))
      end

    fun audit_type_token serial label text needle occurrence =
      let
        val {start, markup, ...} = capture serial label text
        val position = token_position text start needle occurrence
      in
        audit_assert (label ^ " type target changed")
          (entity_names Markup.type_nameN position markup =
            [word_type_name]);
        audit_assert (label ^ " type styling changed")
          (count_markup Markup.tconstN position markup = 1);
        audit_assert (label ^ " type token acquired a constant target")
          (constant_targets position markup = [])
      end

    val deferred_text = "panic!()"
    val deferred_start =
      Position.make0 450 100000 0 "" ""
        "resolved-semantic-navigation-deferred"
    val deferred_source =
      Parser_Lex_Util.positioned_content_source
        deferred_text deferred_start
    val ((deferred_term, deferred_reports), during_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.capture (fn () =>
          Parser_Test_Elaboration.expression ctxt deferred_source))
    val deferred_name =
      token_position deferred_text deferred_start "panic" 0
    val deferred_bang =
      token_position deferred_text deferred_start "!" 0
    val _ =
      audit_assert "checked capture leaked a target before replay"
        (constant_targets deferred_name during_markup = [] andalso
         constant_targets deferred_bang during_markup = [])
    val ((), replay_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.replay ctxt deferred_reports)
    val deferred_targets =
      [\<^const_name>\<open>abort\<close>,
       \<^const_name>\<open>Panic\<close>]
    val _ =
      List.app
        (fn position =>
          audit_assert
            "checked replay lost stable deduplication or primary-last order"
            (constant_targets position replay_markup =
              deferred_targets))
        [deferred_name, deferred_bang]
    val _ =
      audit_assert "checked deferred term retained an internal marker"
        (not (contains_navigation_marker deferred_term))

    val type_text = "0u64"
    val type_start =
      Position.make0 451 101000 0 "" ""
        "resolved-semantic-navigation-type"
    val type_source =
      Parser_Lex_Util.positioned_content_source
        type_text type_start
    val type_position =
      token_position type_text type_start "u64" 0
    val ((type_term, type_reports), during_type_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.capture (fn () =>
          Parser_Test_Elaboration.expression
            ctxt type_source))
    val _ =
      audit_assert "deferred type entity escaped before replay"
        (entity_names Markup.type_nameN
           type_position during_type_markup = [] andalso
         count_markup Markup.tconstN
           type_position during_type_markup = 0)
    val ((), replay_type_markup) =
      Parser_Test_Reports.markup (fn () =>
        Navigation.replay ctxt type_reports)
    val _ =
      audit_assert "deferred type entity target changed"
        (entity_names Markup.type_nameN
           type_position replay_type_markup =
             [word_type_name] andalso
         count_markup Markup.tconstN
           type_position replay_type_markup = 1)
    val _ =
      audit_assert "type-report elaboration retained a marker"
        (not (contains_navigation_marker type_term))

    val _ =
      audit_case 0 "addition" "1u32 + 2u32"
        [("+", 0,
          [\<^const_name>\<open>word_add_no_wrap\<close>])]
    val _ =
      audit_case 1 "boolean-negation" "!true"
        [("!", 0, [\<^const_name>\<open>negation\<close>])]
    val _ =
      audit_case 2 "word-negation" "!1u32"
        [("!", 0,
          [\<^const_name>\<open>Numeric_Types.word_bitwise_not\<close>])]
    val _ =
      audit_case 3 "iteration"
        "for item in [1u64] { let _ = item; () }"
        [("in", 0, [\<^const_name>\<open>list_into_iter\<close>])]
    val _ =
      audit_case 4 "scalar-index"
        "\<llangle>[1 :: nat]\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>list_index\<close>])]
    val _ =
      audit_case 5 "range-index"
        "\<llangle>[1 :: nat, 2]\<rrangle>[0usize..1usize]"
        [("[", 1, [\<^const_name>\<open>list_index_range\<close>])]
    val _ =
      audit_case 6 "field-focus"
        "\<llangle>1 :: nat\<rrangle>.navigationField"
        [(".", 0,
          [\<^const_name>\<open>semantic_navigation_focus\<close>])]
    val _ =
      audit_case 7 "option-propagation"
        "\<llangle>Some (1 :: nat)\<rrangle>?"
        [("?", 0, [\<^const_name>\<open>propagate_option\<close>])]
    val _ =
      audit_case 8 "result-propagation"
        "\<llangle>(Ok (1 :: nat) :: (nat, String.literal) result)\<rrangle>?"
        [("?", 0, [\<^const_name>\<open>propagate_result\<close>])]
    val _ =
      audit_case 9 "allocation"
        "let mut slot = 0u32; slot"
        [("mut", 0,
          [\<^const_name>\<open>semantic_navigation_allocate\<close>])]
    val _ =
      audit_case 10 "dereference"
        "*semantic_navigation_ref"
        [("*", 0,
          [\<^const_name>\<open>semantic_navigation_dereference\<close>])]
    val _ =
      audit_case 11 "update"
        "semantic_navigation_ref = semantic_navigation_word"
        [("=", 0,
          [\<^const_name>\<open>semantic_navigation_update\<close>])]
    val _ =
      audit_case 12 "additive-assignment"
        "semantic_navigation_ref += semantic_navigation_word"
        [("+=", 0,
          [\<^const_name>\<open>semantic_navigation_assign_add\<close>])]
    val _ =
      audit_case 13 "compound-assignment"
        "semantic_navigation_ref -= semantic_navigation_word"
        [("-=", 0,
          [\<^const_name>\<open>word_minus_no_wrap\<close>,
           \<^const_name>\<open>semantic_navigation_update\<close>])]

    val _ =
      audit_case 14 "unsigned-cast" "0u64 as u8"
        [("as", 0, [ucast_name])]
    val _ =
      audit_case 15 "signed-cast" "0u64 as i32"
        [("as", 0, [scast_name])]
    val _ =
      audit_case 16 "raw-pointer-cast"
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u8"
        [("as", 0, [\<^const_name>\<open>raw_ptr_cast\<close>])]

    val _ =
      audit_case 17 "switch-match"
        "match 1u64 { 1 => true, _ => false }"
        [("match", 0, [\<^const_name>\<open>ncase_selector\<close>])]
    val _ =
      audit_case 18 "constructor-match"
        "match \<llangle>Some (1 :: nat)\<rrangle> { Some(value) => value, None => 0 }"
        [("match", 0,
          [\<^const_name>\<open>case_nil\<close>,
           \<^const_name>\<open>case_cons\<close>,
           \<^const_name>\<open>case_elem\<close>,
           \<^const_name>\<open>case_abs\<close>,
           \<^const_name>\<open>case_guard\<close>,
           \<^const_name>\<open>case_option\<close>])]

    val binary_audits =
      [("subtraction", "3u32 - 2u32", "-",
        \<^const_name>\<open>word_minus_no_wrap\<close>),
       ("multiplication", "3u32 * 2u32", "*",
        \<^const_name>\<open>word_mul_no_wrap\<close>),
       ("division", "4u32 / 2u32", "/",
        \<^const_name>\<open>word_udiv\<close>),
       ("remainder", "4u32 % 3u32", "%",
        \<^const_name>\<open>word_umod\<close>),
       ("shift-left", "1u32 << 2u64", "<<",
        \<^const_name>\<open>word_shift_left_shift64\<close>),
       ("shift-right", "4u32 >> 1u64", ">>",
        \<^const_name>\<open>word_shift_right_shift64\<close>),
       ("bitwise-and", "3u32 & 1u32", "&",
        \<^const_name>\<open>word_bitwise_and\<close>),
       ("bitwise-or", "2u32 | 1u32", "|",
        \<^const_name>\<open>word_bitwise_or\<close>),
       ("bitwise-xor", "3u32 ^ 1u32", "^",
        \<^const_name>\<open>word_bitwise_xor\<close>),
       ("equality", "1u32 == 1u32", "==",
        \<^const_name>\<open>urust_eq\<close>),
       ("inequality", "1u32 != 2u32", "!=",
        \<^const_name>\<open>urust_neq\<close>),
       ("less-than", "1u32 < 2u32", "<",
        \<^const_name>\<open>comp_lt\<close>),
       ("less-equal", "1u32 <= 2u32", "<=",
        \<^const_name>\<open>comp_le\<close>),
       ("greater-than", "2u32 > 1u32", ">",
        \<^const_name>\<open>comp_gt\<close>),
       ("greater-equal", "2u32 >= 1u32", ">=",
        \<^const_name>\<open>comp_ge\<close>),
       ("conjunction", "true && false", "&&",
        \<^const_name>\<open>urust_conj\<close>),
       ("disjunction", "true || false", "||",
        \<^const_name>\<open>urust_disj\<close>)]
    val _ =
      binary_audits
      |> map_index
          (fn (index, (label, text, token, target)) =>
            audit_case (30 + index) label text
              [(token, 0, [target])])
      |> ignore

    val assignment_audits =
      [("subtract-assignment", "-=", "semantic_navigation_word",
        \<^const_name>\<open>word_minus_no_wrap\<close>),
       ("multiply-assignment", "*=", "semantic_navigation_word",
        \<^const_name>\<open>word_mul_no_wrap\<close>),
       ("remainder-assignment", "%=", "semantic_navigation_word",
        \<^const_name>\<open>word_umod\<close>),
       ("and-assignment", "&=", "semantic_navigation_word",
        \<^const_name>\<open>word_bitwise_and\<close>),
       ("or-assignment", "|=", "semantic_navigation_word",
        \<^const_name>\<open>word_bitwise_or\<close>),
       ("xor-assignment", "^=", "semantic_navigation_word",
        \<^const_name>\<open>word_bitwise_xor\<close>),
       ("shift-left-assignment", "<<=", "semantic_navigation_shift",
        \<^const_name>\<open>word_shift_left_shift64\<close>),
       ("shift-right-assignment", ">>=", "semantic_navigation_shift",
        \<^const_name>\<open>word_shift_right_shift64\<close>)]
    val _ =
      assignment_audits
      |> map_index
          (fn (index, (label, token, rhs, arithmetic)) =>
            audit_case (50 + index) label
              ("semantic_navigation_ref " ^ token ^
                " " ^ rhs)
              [(token, 0,
                [arithmetic,
                 \<^const_name>\<open>semantic_navigation_update\<close>])])
      |> ignore

    val _ =
      audit_case 60 "list-scalar-index-pair"
        "\<llangle>[1 :: nat]\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>list_index\<close>]),
         ("]", 1, [\<^const_name>\<open>list_index\<close>])]
    val _ =
      audit_case 61 "list-range-index-pair"
        "\<llangle>[1 :: nat, 2]\<rrangle>[0usize..1usize]"
        [("[", 1, [\<^const_name>\<open>list_index_range\<close>]),
         ("]", 1, [\<^const_name>\<open>list_index_range\<close>])]
    val _ =
      audit_case 62 "array-scalar-index-pair"
        "\<llangle>array_of_list [1 :: nat] :: (nat, 2) array\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>array_index\<close>]),
         ("]", 1, [\<^const_name>\<open>array_index\<close>])]
    val _ =
      audit_case 63 "array-range-index-pair"
        "\<llangle>array_of_list [1 :: nat, 2] :: (nat, 2) array\<rrangle>[0usize..1usize]"
        [("[", 1, [\<^const_name>\<open>array_index_range\<close>]),
         ("]", 1, [\<^const_name>\<open>array_index_range\<close>])]
    val _ =
      audit_case 64 "vector-scalar-index-pair"
        "\<llangle>vector_of_list [1 :: nat] :: (nat, 2) vector\<rrangle>[0usize]"
        [("[", 1, [\<^const_name>\<open>vector_index\<close>]),
         ("]", 1, [\<^const_name>\<open>vector_index\<close>])]
    val _ =
      audit_case 65 "vector-range-index-pair"
        "\<llangle>vector_of_list [1 :: nat, 2] :: (nat, 2) vector\<rrangle>[0usize..1usize]"
        [("[", 1, [\<^const_name>\<open>vector_index_range\<close>]),
         ("]", 1, [\<^const_name>\<open>vector_index_range\<close>])]

    val _ =
      audit_case 66 "array-iteration"
        "for item in \<llangle>array_of_list [1 :: nat] :: (nat, 2) array\<rrangle> { () }"
        [("in", 0, [\<^const_name>\<open>array_into_iter\<close>])]
    val _ =
      audit_case 67 "vector-iteration"
        "for item in \<llangle>vector_of_list [1 :: nat] :: (nat, 2) vector\<rrangle> { () }"
        [("in", 0, [\<^const_name>\<open>vector_into_iter\<close>])]
    val _ =
      audit_case 68 "range-iteration"
        "for item in 0u64..1u64 { () }"
        [("in", 0, [\<^const_name>\<open>range_into_iter\<close>])]
    val _ =
      audit_case 69 "iterator-iteration"
        "for item in \<llangle>make_iterator_from_list [1 :: nat]\<rrangle> { () }"
        [("in", 0, [\<^const_name>\<open>iterator_into_iter\<close>])]

    val literal_target =
      [\<^const_name>\<open>Core_Expression.literal\<close>]
    val literal_audits =
      [("decimal-literal", "17u32", "17"),
       ("binary-literal", "0b1010u8", "0b1010"),
       ("octal-literal", "0o17_u16", "0o17"),
       ("hex-literal", "0xFFusize", "0xFF")]
    val _ =
      literal_audits
      |> map_index
          (fn (index, (label, text, numeric)) =>
            audit_case (70 + index) label text
              [(numeric, 0, literal_target)])
      |> ignore
    val _ =
      audit_type_token 74 "decimal-suffix" "17u32" "u32" 0
    val _ =
      audit_type_token 75 "binary-suffix" "0b1010u8" "u8" 0
    val _ =
      audit_type_token 76 "octal-suffix" "0o17_u16" "_u16" 0
    val _ =
      audit_type_token 77 "hex-suffix" "0xFFusize" "usize" 0
    val _ =
      audit_case 78 "string-literal" "\"navigation\""
        [("\"navigation\"", 0, literal_target)]
    val _ =
      audit_case 79 "value-antiquotation"
        "\<llangle>1 :: nat\<rrangle>"
        [("\<llangle>", 0, literal_target),
         ("\<rrangle>", 0, literal_target)]

    val _ =
      audit_type_token 80 "unsigned-cast-type"
        "0u64 as u8" "u8" 0
    val _ =
      audit_type_token 81 "signed-cast-type"
        "0u64 as i32" "i32" 0
    val _ =
      audit_type_token 82 "raw-pointer-cast-type"
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u8"
        "u8" 0
    val complete_cast_audits =
      [("unsigned-u8", "0u64 as u8", ucast_name),
       ("unsigned-u16", "0u64 as u16", ucast_name),
       ("unsigned-u32", "0u64 as u32", ucast_name),
       ("unsigned-u64", "0u64 as u64", ucast_name),
       ("unsigned-usize", "0u64 as usize", ucast_name),
       ("signed-i32", "0u64 as i32", scast_name),
       ("signed-i64", "0u64 as i64", scast_name),
       ("raw-const-u8",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u8",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-const-u16",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u16",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-const-u32",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u32",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-const-u64",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const u64",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-const-usize",
        "\<llangle>semantic_navigation_gref\<rrangle> as *const usize",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-u8",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut u8",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-u16",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut u16",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-u32",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut u32",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-u64",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut u64",
        \<^const_name>\<open>raw_ptr_cast\<close>),
       ("raw-mut-usize",
        "\<llangle>semantic_navigation_gref\<rrangle> as *mut usize",
        \<^const_name>\<open>raw_ptr_cast\<close>)]
    val _ =
      complete_cast_audits
      |> map_index
          (fn (index, (label, text, target)) =>
            audit_case (110 + index) label text
              [("as", 0, [target])])
      |> ignore

    val _ =
      audit_case 83 "let-binding-sequence"
        "let value = 1u32; value"
        [(";", 0,
          [\<^const_name>\<open>Core_Expression.sequence\<close>])]
    val _ =
      audit_case 84 "const-binding-sequence"
        "const value = 1u32; value"
        [(";", 0,
          [\<^const_name>\<open>Core_Expression.sequence\<close>])]
    val _ =
      audit_case 85 "immutable-borrow"
        "&semantic_navigation_ref"
        [("&", 0, [\<^const_name>\<open>ro_ref_from_ref\<close>])]
    val _ =
      audit_case 86 "mutable-borrow"
        "& mut semantic_navigation_ref"
        [("&", 0, [\<^const_name>\<open>mut_ref_from_ref\<close>]),
         ("mut", 0, [\<^const_name>\<open>mut_ref_from_ref\<close>])]
    val _ =
      audit_case 87 "ordinary-repeat"
        "[1u32; 2usize]"
        [("[", 0, [\<^const_name>\<open>List.replicate\<close>]),
         (";", 0, [\<^const_name>\<open>List.replicate\<close>]),
         ("]", 0, [\<^const_name>\<open>List.replicate\<close>])]
    val _ =
      audit_case 88 "inline-const-repeat"
        "[const { 1u32 }; 2usize]"
        [("[", 0, [\<^const_name>\<open>List.replicate\<close>]),
         (";", 0, [\<^const_name>\<open>List.replicate\<close>]),
         ("const", 0, [\<^const_name>\<open>List.replicate\<close>]),
         ("]", 0, [\<^const_name>\<open>List.replicate\<close>])]
    val _ =
      audit_case 89 "primitive-log-antiquotations"
        "\<l>\<o>\<g> \<llangle>Error\<rrangle> \<llangle>[] :: log_data\<rrangle>"
        [("\<llangle>", 0, literal_target),
         ("\<rrangle>", 0, literal_target),
         ("\<llangle>", 1, literal_target),
         ("\<rrangle>", 1, literal_target)]
    val _ =
      audit_case 90 "log-data-antiquotation"
        "l\<llangle>\"left\", semantic_navigation_word\<rrangle>"
        [("l", 0, literal_target),
         ("\<llangle>", 0, literal_target),
         ("\<rrangle>", 0, literal_target),
         (",", 0, [])]
    val _ =
      audit_case 91 "macro-message-string"
        "panic!(\"navigation\")"
        [("\"navigation\"", 0, literal_target)]
    val _ =
      audit_case 92 "macro-message-antiquotation"
        "panic!(\<llangle>''navigation''\<rrangle>)"
        [("\<llangle>", 0, literal_target),
         ("\<rrangle>", 0, literal_target)]

    val _ =
      audit_case 93 "yield-link" "\<y>\<i>\<e>\<l>\<d>"
        [("\<y>\<i>\<e>\<l>\<d>", 0,
          [\<^const_name>\<open>pause\<close>])]
    val _ =
      audit_case 94 "erased-array-borrow" "&[1u32]"
        [("&", 0, [])]
    val _ =
      audit_case 100 "erased-mutable-array-borrow"
        "& mut [1u32]"
        [("&", 0, []), ("mut", 0, [])]
    val _ =
      audit_case 95 "method-dot"
        "\<llangle>[1 :: nat]\<rrangle>.into_iter()"
        [(".", 0, [])]
    val _ =
      audit_case 96 "group-and-block"
        "{ (1u32) }"
        [("{", 0, []), ("(", 0, []),
         (")", 0, []), ("}", 0, [])]
    val _ =
      audit_case 97 "match-alternative"
        "match \<llangle>Some (1 :: nat)\<rrangle> { Some(_) | None => () }"
        [("|", 0, [])]
    val _ =
      audit_case 98 "expression-antiquotation"
        "\<epsilon>\<open>literal (1 :: nat)\<close>"
        [("\<epsilon>", 0, []),
         ("\<open>", 0, []),
         ("\<close>", 0, [])]
    val _ =
      audit_case 101 "unsafe-erasure"
        "unsafe { 1u32 }"
        [("unsafe", 0, []), ("{", 0, []), ("}", 0, [])]
    val _ =
      audit_case 102 "switch-pattern-literal"
        "match 1u64 { 0x1 => true, _ => false }"
        [("0x1", 0, literal_target)]

    val bind_target =
      [\<^const_name>\<open>Core_Expression.bind\<close>]
    val sequence_target =
      [\<^const_name>\<open>Core_Expression.sequence\<close>]
    val funcall1_target =
      [\<^const_name>\<open>funcall1\<close>]
    val list_cons_target =
      [\<^const_name>\<open>List.Cons\<close>]
    val list_nil_target =
      [\<^const_name>\<open>List.Nil\<close>]
    val pair_target =
      [\<^const_name>\<open>Product_Type.Pair\<close>]
    val list_case_target =
      [\<^const_name>\<open>List.case_list\<close>]
    val bounded_while_target =
      [\<^const_name>\<open>bounded_while\<close>]
    val conditional_target =
      [\<^const_name>\<open>two_armed_conditional\<close>]
    val option_case_targets =
      [\<^const_name>\<open>case_nil\<close>,
       \<^const_name>\<open>case_cons\<close>,
       \<^const_name>\<open>case_elem\<close>,
       \<^const_name>\<open>case_abs\<close>,
       \<^const_name>\<open>case_guard\<close>,
       \<^const_name>\<open>case_option\<close>]

    val _ =
      audit_target_group 200 "empty-array-pair" "[]"
        [("[", 0), ("]", 0)] list_nil_target
    val _ =
      audit_target_group 201 "nonempty-array-pair" "[1u32]"
        [("[", 0), ("]", 0)] list_cons_target
    val _ =
      audit_target_group 202 "tuple-pair" "(1u32, 2u32)"
        [("(", 0), (")", 0)] pair_target
    val _ =
      audit_target_group 203 "struct-brace-pair"
        "semantic_navigation_allocate { value: 0u32 }"
        [("{", 0), ("}", 0)] funcall1_target
    val _ =
      audit_target_group 204 "ordinary-call-pair"
        "semantic_navigation_allocate(0u32)"
        [("(", 0), (")", 0)] funcall1_target
    val _ =
      audit_target_group 205 "method-call-pair"
        "\<llangle>[1 :: nat]\<rrangle>.into_iter()"
        [("(", 0), (")", 0)] funcall1_target
    val _ =
      audit_target_group 206 "erased-borrow-array-pair"
        "&[1u32]"
        [("[", 0), ("]", 0)] list_cons_target
    val _ =
      audit_case 207 "erased-borrow-array-prefix"
        "&[1u32]" [("&", 0, [])]
    val _ =
      audit_target_group 208 "erased-mutable-borrow-array-pair"
        "& mut [1u32]"
        [("[", 0), ("]", 0)] list_cons_target
    val _ =
      audit_case 209 "erased-mutable-borrow-array-prefix"
        "& mut [1u32]"
        [("&", 0, []), ("mut", 0, [])]

    val _ =
      audit_target_group 210 "let-binding-head"
        "let value = 1u32; value"
        [("let", 0), ("=", 0)] bind_target
    val _ =
      audit_case 211 "let-binding-separator"
        "let value = 1u32; value"
        [(";", 0, sequence_target)]
    val _ =
      audit_target_group 212 "mutable-binding-head"
        "let mut value = 1u32; value"
        [("let", 0), ("=", 0)] bind_target
    val _ =
      audit_case 213 "mutable-binding-roles"
        "let mut value = 1u32; value"
        [("mut", 0,
          [\<^const_name>\<open>semantic_navigation_allocate\<close>]),
         (";", 0, sequence_target)]
    val _ =
      audit_target_group 214 "const-binding-head"
        "const value = 1u32; value"
        [("const", 0), ("=", 0)] bind_target
    val _ =
      audit_case 215 "const-binding-separator"
        "const value = 1u32; value"
        [(";", 0, sequence_target)]

    val guarded_match_text =
      "match \<llangle>Some (1 :: nat)\<rrangle> { " ^
      "Some(value) if true => value, None => 0 }"
    val _ =
      audit_case 216 "guarded-match"
        guarded_match_text
        [("match", 0, option_case_targets),
         ("if", 0,
          [\<^const_name>\<open>two_armed_conditional\<close>])]

    val lhs_dereference_text =
      "*semantic_navigation_ref = semantic_navigation_word"
    val _ =
      audit_case 217 "lhs-dereference"
        lhs_dereference_text
        [("*", 0,
          [\<^const_name>\<open>semantic_navigation_dereference\<close>]),
         ("=", 0,
          [\<^const_name>\<open>semantic_navigation_update\<close>])]

    val boolean_pattern_text =
      "match \<llangle>Some True\<rrangle> { " ^
      "Some(true) => true, Some(false) => false, None => false }"
    val _ =
      audit_case 218 "boolean-patterns"
        boolean_pattern_text
        [("match", 0, option_case_targets),
         ("true", 0, literal_target),
         ("false", 0, literal_target)]
    val _ =
      audit_markup_count 219 "true-pattern-keyword-style"
        boolean_pattern_text "true" 0 Markup.keyword1N 1
    val _ =
      audit_markup_count 220 "false-pattern-keyword-style"
        boolean_pattern_text "false" 0 Markup.keyword1N 1

    val range_pattern_text =
      "match \<llangle>Some (2 :: nat)\<rrangle> { " ^
      "Some(1..=3) => true, _ => false }"
    val _ =
      audit_case 221 "range-pattern-match-scope"
        range_pattern_text
        [("match", 0, option_case_targets)]

    val _ =
      audit_case 227 "explicit-switch-match"
        "match_switch 1u64 { 1 => true, _ => false }"
        [("match_switch", 0,
          [\<^const_name>\<open>ncase_selector\<close>])]
    val string_match_text =
      "match_case \"ok\" { \"ok\" => true, _ => false }"
    val _ =
      audit_case 228 "string-match-case"
        string_match_text
        [("match_case", 0, conditional_target)]
    val antiquoted_value_match_text =
      "match \<llangle>2 :: nat\<rrangle> { " ^
      "\<llangle>2 :: nat\<rrangle> => true, _ => false }"
    val _ =
      audit_case 229 "antiquoted-value-match"
        antiquoted_value_match_text
        [("match", 0, conditional_target)]
    val boolean_disjunction_match_text =
      "match true { true | false => true }"
    val _ =
      audit_case 230 "boolean-disjunction-match"
        boolean_disjunction_match_text
        [("match", 0, conditional_target)]
    val top_level_range_match_text =
      "match_case \<llangle>2 :: nat\<rrangle> { " ^
      "1..=3 => true, _ => false }"
    val _ =
      audit_case 231 "top-level-range-match"
        top_level_range_match_text
        [("match_case", 0, conditional_target)]
    val guarded_value_match_text =
      "match_case \<llangle>2 :: nat\<rrangle> { " ^
      "\<llangle>2 :: nat\<rrangle> if true => true, _ => false }"
    val _ =
      audit_case 232 "guarded-value-match"
        guarded_value_match_text
        [("match_case", 0, conditional_target),
         ("if", 0, conditional_target)]
    val wildcard_match_text =
      "match_case 1u64 { _ => true }"
    val _ =
      audit_case 233 "irrefutable-wildcard-match"
        wildcard_match_text
        [("match_case", 0, bind_target)]
    val binder_match_text =
      "match_case \<llangle>1 :: nat\<rrangle> { value => value }"
    val _ =
      audit_case 234 "irrefutable-binder-match"
        binder_match_text
        [("match_case", 0, bind_target)]

    val top_slice_text =
      "match \<llangle>[1 :: nat, 2]\<rrangle> { " ^
      "[head, ..] => head, _ => 0 }"
    val _ =
      audit_target_group 222 "top-level-slice-navigation"
        top_slice_text
        [("[", 1), ("..", 0), ("]", 1)]
        list_case_target
    val nested_slice_text =
      "match \<llangle>Some [1 :: nat, 2]\<rrangle> { " ^
      "Some([head, ..]) => head, _ => 0 }"
    val _ =
      audit_target_group 223 "nested-slice-navigation"
        nested_slice_text
        [("[", 1), ("..", 0), ("]", 1)]
        list_case_target

    val _ =
      audit_target_group 260 "bound-rest-navigation"
        ("match \<llangle>[1 :: nat, 2, 3]\<rrangle> { " ^
         "[head, middle @ .., tail] => middle, _ => [] }")
        [("@", 0), ("..", 0), ("[", 1), ("]", 1)]
        list_case_target
    val _ =
      audit_target_group 261 "irrefutable-rest-navigation"
        ("let whole @ [rest @ ..] = \<llangle>[1 :: nat, 2]\<rrangle>; " ^
         "(whole, rest)")
        [("@", 0), ("@", 1), ("..", 0), ("[", 0), ("]", 0)]
        [\<^const_name>\<open>Core_Expression.bind\<close>]
    val _ =
      audit_type_token 262 "repeat-length-usize-navigation"
        "[0u64; 2u32 as usize]" "usize" 0
    val _ =
      audit_target_group 263 "irrefutable-for-rest-navigation"
        ("for whole @ [rest @ ..] in \<llangle>[[1 :: nat, 2]]\<rrangle> { () }")
        [("@", 0), ("@", 1), ("..", 0), ("[", 0), ("]", 0)]
        [\<^const_name>\<open>Core_Expression.bind\<close>]

    val refutable_alias_sources =
      [("match-alias",
        "match \<llangle>Some (1 :: nat)\<rrangle> { " ^
        "whole @ Some(item) => item, None => 0 }"),
       ("if-let-alias",
        "if let whole @ Some(item) = \<llangle>Some (1 :: nat)\<rrangle> " ^
        "{ item } else { 0 }"),
       ("while-let-alias",
        "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] " ^
        "while let whole @ Some(item) = \<llangle>Some (1 :: nat)\<rrangle> { () }"),
       ("let-else-alias",
        "let whole @ Some(item) = \<llangle>Some (1 :: nat)\<rrangle> " ^
        "else { 0 }; item"),
       ("matches-alias",
        "matches!(\<llangle>Some (1 :: nat)\<rrangle>, whole @ Some(item))")]
    val _ =
      List.app
        (fn (index, (label, text)) =>
          (audit_target_group (264 + index) label text
             [("@", 0)] [\<^const_name>\<open>Core_Expression.bind\<close>];
           audit_term_invariant (300 + index) label text))
        (map_index I refutable_alias_sources)

    val while_text =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] " ^
      "while (false) { () }"
    val _ =
      audit_target_group 224 "fuelled-while-navigation"
        while_text
        [("#[", 0), ("fuel", 0), ("]", 0), ("while", 0)]
        bounded_while_target
    val while_let_text =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] " ^
      "while let Some(_) = " ^
      "\<llangle>None :: unit option\<rrangle> { () }"
    val _ =
      audit_target_group 225 "fuelled-while-let-navigation"
        while_let_text
        [("#[", 0), ("fuel", 0), ("]", 0), ("while", 0)]
        bounded_while_target
    val loop_text =
      "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] loop { () }"
    val _ =
      audit_target_group 226 "fuelled-loop-navigation"
        loop_text
        [("#[", 0), ("fuel", 0), ("]", 0), ("loop", 0)]
        bounded_while_target

    val function_suffixes =
      ["\<^sub>1", "\<^sub>2", "\<^sub>3", "\<^sub>4",
       "\<^sub>5", "\<^sub>6", "\<^sub>7", "\<^sub>8",
       "\<^sub>9", "\<^sub>1\<^sub>0",
       "\<^sub>1\<^sub>1", "\<^sub>1\<^sub>2",
       "\<^sub>1\<^sub>3", "\<^sub>1\<^sub>4"]
    val lift_targets =
      [\<^const_name>\<open>lift_fun1\<close>,
       \<^const_name>\<open>lift_fun2\<close>,
       \<^const_name>\<open>lift_fun3\<close>,
       \<^const_name>\<open>lift_fun4\<close>,
       \<^const_name>\<open>lift_fun5\<close>,
       \<^const_name>\<open>lift_fun6\<close>,
       \<^const_name>\<open>lift_fun7\<close>,
       \<^const_name>\<open>lift_fun8\<close>,
       \<^const_name>\<open>lift_fun9\<close>,
       \<^const_name>\<open>lift_fun10\<close>,
       \<^const_name>\<open>lift_fun11\<close>,
       \<^const_name>\<open>lift_fun12\<close>,
       \<^const_name>\<open>lift_fun13\<close>,
       \<^const_name>\<open>lift_fun14\<close>]
    val function_parameters =
      ["a", "b", "c", "d", "e", "f", "g",
       "h", "i", "j", "k", "l", "m", "n"]

    fun function_literal_text arity suffix =
      let
        val parameters = take arity function_parameters
        val first = hd parameters
      in
        "\<llangle>\<lambda>" ^
        space_implode " " parameters ^
        ". (" ^ first ^ " :: nat)\<rrangle>" ^
        suffix ^ "(" ^
        space_implode ", " (replicate arity "0") ^ ")"
      end

    val _ =
      (function_suffixes ~~ lift_targets)
      |> map_index
          (fn (index, (suffix, target)) =>
            let
              val arity = index + 1
              val label =
                "function-literal-arity-" ^
                string_of_int arity
              val text =
                function_literal_text arity suffix
            in
              audit_target_group (240 + index)
                label text
                [("\<llangle>", 0), ("\<rrangle>", 0),
                 (suffix, 0)]
                [target];
              audit_term_invariant (260 + index)
                (label ^ "-term") text
            end)
      |> ignore

    val invariant_sources =
      [("empty-array", "[]"),
       ("bound-rest",
        "match \<llangle>[1 :: nat, 2, 3]\<rrangle> { " ^
        "[head, middle @ .., tail] => middle, _ => [] }"),
       ("irrefutable-rest",
        "let whole @ [rest @ ..] = \<llangle>[1 :: nat, 2]\<rrangle>; (whole, rest)"),
       ("recursive-irrefutable-rest",
        "let (whole @ [rest @ ..], other) = \<llangle>([1 :: nat], 2 :: nat, TNil)\<rrangle>; " ^
        "(whole, rest, other)"),
       ("irrefutable-for-rest",
        "for whole @ [rest @ ..] in \<llangle>[[1 :: nat, 2]]\<rrangle> { () }"),
       ("repeat-cast", "[0u64; 2u32 as usize]"),
       ("nonempty-array", "[1u32]"),
       ("tuple", "(1u32, 2u32)"),
       ("struct",
        "semantic_navigation_allocate { value: 0u32 }"),
       ("ordinary-call",
        "semantic_navigation_allocate(0u32)"),
       ("method-call",
        "\<llangle>[1 :: nat]\<rrangle>.into_iter()"),
       ("erased-array-borrow", "&[1u32]"),
       ("erased-mutable-array-borrow", "& mut [1u32]"),
       ("let-binding", "let value = 1u32; value"),
       ("mutable-binding", "let mut value = 1u32; value"),
       ("const-binding", "const value = 1u32; value"),
       ("guarded-match", guarded_match_text),
       ("lhs-dereference", lhs_dereference_text),
       ("boolean-patterns", boolean_pattern_text),
       ("range-pattern", range_pattern_text),
       ("explicit-switch-match",
        "match_switch 1u64 { 1 => true, _ => false }"),
       ("string-match-case", string_match_text),
       ("antiquoted-value-match",
        antiquoted_value_match_text),
       ("boolean-disjunction-match",
        boolean_disjunction_match_text),
       ("top-level-range-match",
        top_level_range_match_text),
       ("guarded-value-match",
        guarded_value_match_text),
       ("irrefutable-wildcard-match",
        wildcard_match_text),
       ("irrefutable-binder-match",
        binder_match_text),
       ("top-level-slice", top_slice_text),
       ("nested-slice", nested_slice_text),
       ("fuelled-while", while_text),
       ("fuelled-while-let", while_let_text),
       ("fuelled-loop", loop_text)]
    val _ =
      invariant_sources
      |> map_index
          (fn (index, (label, text)) =>
            audit_term_invariant (280 + index)
              (label ^ "-invariant") text)
      |> ignore

    fun audit_registered_macro serial label text notation expected_backend
        expected_keyword3 =
      let
        val {start, markup, ...} =
          capture serial label text
        val qualifier =
          if String.isSubstring "NavigationMacro" text
          then SOME (token_position text start "NavigationMacro" 0)
          else NONE
        val terminal =
          token_position text start label 0
        val bang = token_position text start "!" 0
      in
        Option.app
          (fn position =>
            audit_assert
              (label ^ " qualifier lost notation navigation")
              (entity_names Micro_Rust_Names.notationN
                position markup = [notation]))
          qualifier;
        audit_assert (label ^ " terminal lost notation navigation")
          (entity_names Micro_Rust_Names.notationN
            terminal markup = [notation]);
        audit_assert (label ^ " bang acquired notation navigation")
          (entity_names Micro_Rust_Names.notationN
            bang markup = []);
        audit_assert (label ^ " terminal backend target changed")
          (constant_targets terminal markup = expected_backend);
        audit_assert (label ^ " bang backend target changed")
          (constant_targets bang markup = expected_backend);
        audit_assert (label ^ " keyword3 styling changed")
          (count_markup Markup.keyword3N terminal markup =
            expected_keyword3)
      end

    val _ =
      audit_registered_macro 19 "named"
        "NavigationMacro::named!(true)"
        "NavigationMacro::named!"
        [\<^const_name>\<open>semantic_navigation_named_macro\<close>] 1
    val _ =
      audit_registered_macro 20 "abbrev"
        "NavigationMacro::abbrev!(true)"
        "NavigationMacro::abbrev!"
        [abbreviation_name] 1
    val _ =
      audit_registered_macro 21 "anonymous"
        "NavigationMacro::anonymous!(true)"
        "NavigationMacro::anonymous!"
        [] 1
    val _ =
      audit_registered_macro 99 "info"
        "info!(l\<llangle>\"navigation\"\<rrangle>)"
        "info!"
        [info_name] 1

    val failure_text = "1u32 + true"
    val failure_start =
      Position.make0 700 300000 0 "" ""
        "resolved-semantic-navigation-failure"
    val failure_source =
      Parser_Lex_Util.positioned_content_source
        failure_text failure_start
    val (failure_result, failure_markup) =
      Parser_Test_Reports.markup (fn () =>
        Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression
              ctxt failure_source)
          ())
    val _ =
      (case failure_result of
         Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ()
       | Exn.Res _ =>
           error
             "resolved semantic navigation audit: failing expression elaborated")
    val _ =
      List.app
        (fn (needle, occurrence) =>
          let
            val position =
              token_position failure_text failure_start
                needle occurrence
          in
            audit_assert
              ("failed elaboration replayed a target at " ^
                quote needle)
              (constant_targets position failure_markup = [] andalso
               count_markup Markup.constN
                 position failure_markup = 0)
          end)
        [("1", 0), ("u32", 0), ("+", 0), ("true", 0)]
    val failure_type_position =
      token_position failure_text failure_start "u32" 0
    val _ =
      audit_assert "failed elaboration replayed a type target"
        (entity_names Markup.type_nameN
           failure_type_position failure_markup = [] andalso
          count_markup Markup.tconstN
            failure_type_position failure_markup = 0)

    val generated_failure_text = "NavigationGeneratedValue::Payload(true)"
    val generated_failure_start =
      Position.make0 710 310000 0 "" ""
        "resolved-generated-navigation-failure"
    val generated_failure_source =
      Parser_Lex_Util.positioned_content_source
        generated_failure_text generated_failure_start
    val (generated_failure_result, generated_failure_markup) =
      Parser_Test_Reports.markup (fn () =>
        Exn.result
          (fn () =>
            Parser_Test_Elaboration.expression ctxt generated_failure_source)
          ())
    val _ =
      (case generated_failure_result of
         Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn else ()
       | Exn.Res _ =>
           error "generated constructor accepted an ill-typed argument")
    val _ =
      List.app
        (fn needle =>
          let
            val position =
              token_position generated_failure_text generated_failure_start needle 0
          in
            audit_assert
              ("failed generated constructor replayed navigation at " ^ quote needle)
              (constant_targets position generated_failure_markup = [] andalso
               entity_names Markup.type_nameN position generated_failure_markup = [] andalso
               entity_names "urust_item" position generated_failure_markup = [] andalso
               entity_names "urust_constructor" position generated_failure_markup = [])
          end)
        ["NavigationGeneratedValue", "Payload"]

    val marker_names =
      [\<^const_name>\<open>semantic_navigation_target\<close>,
       \<^const_name>\<open>semantic_navigation_annotation\<close>,
       \<^const_name>\<open>semantic_navigation_probe\<close>]
    val _ =
      List.app
        (fn marker_name =>
          (case
              Exn.result (Syntax.check_term ctxt)
                (Const (marker_name, dummyT)) of
             Exn.Exn exn =>
               if Exn.is_interrupt exn
               then Exn.reraise exn
               else ()
           | Exn.Res _ =>
               error
                 ("resolved semantic navigation audit: " ^
                   "internal marker " ^ quote marker_name ^
                   " survived checking")))
        marker_names
  in
    val _ =
      writeln
        "Checked exact-range overload, delimiter, binding, case, slice, loop, macro, transaction, failure, term-invariance, and marker-erasure navigation audits passed"
  end
\<close>

chapter\<open> Slice pattern syntax \<close>

section\<open> Slice pattern ASTs and source ranges \<close>

declare [[urust_verbosity = 0]]

no_adhoc_overloading assign_add_const \<rightleftharpoons> semantic_navigation_assign_add
no_adhoc_overloading focus_lens_const \<rightleftharpoons> semantic_navigation_focus
no_adhoc_overloading store_dereference_const \<rightleftharpoons> semantic_navigation_dereference
no_adhoc_overloading store_reference_const \<rightleftharpoons> semantic_navigation_allocate
no_adhoc_overloading store_update_const \<rightleftharpoons> semantic_navigation_update

text\<open>
These tests inspect the production parser's unresolved AST directly. Named rests retain three
distinct token ranges, while a slice retains its complete bracket span. Expected positions count
Isabelle symbols, including symbols in comments and embedded HOL before the pattern.
\<close>

ML_val\<open>
  local
    open URust_AST
    val ctxt = \<^context>
    val start = Position.make0 17 300 0 "" "" "slice-pattern-syntax-audit"

    fun assert label condition =
      if condition then () else error ("slice pattern syntax audit: " ^ label)
    fun parse text =
      (case URust_Parser.parse_source ctxt
          (Parser_Lex_Util.positioned_content_source text start) of
         SOME expression => expression
       | NONE => error "slice pattern syntax audit: empty parse")
    fun match_pattern text =
      (case parse text of
         UE_Match (_, _, [UR_Arm (pattern, NONE, _, _)], _) => pattern
       | _ => error "slice pattern syntax audit: unexpected match AST")
    val prefix = "// \<alpha> before the pattern\nmatch_case \<llangle>undefined\<rrangle> { "
    fun pattern_source pattern = prefix ^ pattern ^ " => () }"
    fun parse_pattern pattern = match_pattern (pattern_source pattern)

    fun find_from text needle raw =
      if raw + size needle > size text then
        error ("slice pattern syntax audit: missing " ^ quote needle)
      else if String.substring (text, raw, size needle) = needle then raw
      else find_from text needle (raw + 1)
    fun token_position text needle raw =
      let
        val found = find_from text needle raw
        val left = Position.symbol_explode (String.substring (text, 0, found)) start
      in
        (found, Position.range_position (left, Position.symbol_explode needle left))
      end
    fun same_position actual expected =
      Position.offset_of actual = Position.offset_of expected andalso
      Position.end_offset_of actual = Position.end_offset_of expected andalso
      Position.line_of actual = Position.line_of expected

    fun bound_rests pattern =
      (case pattern of
         P_Slice (items, _) => maps slice_item_rests items
       | P_Constr (_, children, _) => maps bound_rests children
       | P_Tuple (children, _) => maps bound_rests children
       | P_Group (inner, _) => bound_rests inner
       | P_Borrow (_, inner, _) => bound_rests inner
       | P_Alias (_, _, inner, _) => bound_rests inner
       | P_Range (_, lower, upper, _) => bound_rests lower @ bound_rests upper
       | P_Struct (_, fields, _) =>
           maps (fn SF_Field (_, _, child) => bound_rests child | _ => []) fields
       | P_Or (alternatives, _) => maps bound_rests alternatives
       | _ => [])
    and slice_item_rests (SI_BoundRest rest) = [rest]
      | slice_item_rests (SI_Pat child) = bound_rests child
      | slice_item_rests (SI_Rest _) = []

    fun audit_bound_positions text raw rests =
      fold
        (fn (name, id_pos, alias_pos, rest_pos) => fn after_previous =>
          let
            val (id_raw, expected_id) = token_position text name after_previous
            val (alias_raw, expected_alias) = token_position text "@" (id_raw + size name)
            val (rest_raw, expected_rest) = token_position text ".." (alias_raw + 1)
            val _ = assert (name ^ " identifier span changed") (same_position id_pos expected_id)
            val _ = assert (name ^ " alias span changed") (same_position alias_pos expected_alias)
            val _ = assert (name ^ " rest span changed") (same_position rest_pos expected_rest)
          in rest_raw + 2 end)
        rests raw

    fun item_shape (SI_BoundRest (name, _, _, _)) = "rest:" ^ name
      | item_shape (SI_Rest _) = "bare"
      | item_shape (SI_Pat (P_Ident (name, _))) = "element:" ^ name
      | item_shape (SI_Pat (P_Literal (LP_Integer (Integer_Literal (lexeme, Source_Layout ( _, _), _))))) = "integer:" ^ lexeme
      | item_shape _ = "other"
    fun audit_slice spelling expected =
      let
        val text = pattern_source spelling
        val pattern = match_pattern text
        val slice_start = Position.symbol_explode prefix start
        val slice_position =
          Position.range_position (slice_start, Position.symbol_explode spelling slice_start)
      in
        (case pattern of
           P_Slice (items, Source_Layout (position, _)) =>
             (assert (spelling ^ " item order changed") (map item_shape items = expected);
              assert (spelling ^ " complete slice span changed")
                (same_position position slice_position);
              ignore (fold
                (fn item => fn raw =>
                  let
                    fun token label lexeme actual =
                      let val (found, expected) = token_position text lexeme raw in
                        assert (label ^ " token span changed") (same_position actual expected);
                        found + size lexeme
                      end
                  in
                    case item of
                      SI_BoundRest rest => audit_bound_positions text raw [rest]
                    | SI_Rest position => token "bare rest" ".." position
                    | SI_Pat (P_Ident (name, position)) => token name name position
                    | SI_Pat (P_Literal (LP_Integer (Integer_Literal (lexeme, Source_Layout ( position, _), _)))) =>
                        token "integer" lexeme position
                    | _ => raw
                  end)
                items (size prefix)))
         | _ => error ("slice pattern syntax audit: expected a slice for " ^ quote spelling));
        ignore (audit_bound_positions text (size prefix) (bound_rests pattern))
      end

    val _ =
      List.app (fn (spelling, expected) => audit_slice spelling expected)
        [("[tail@..]", ["rest:tail"]),
         ("[tail @ ..,]", ["rest:tail"]),
         ("[tail@.., last]", ["rest:tail", "element:last"]),
         ("[tail @ .., last,]", ["rest:tail", "element:last"]),
         ("[first, tail@..]", ["element:first", "rest:tail"]),
         ("[first, tail @ ..,]", ["element:first", "rest:tail"]),
         ("[first,tail@..,last]", ["element:first", "rest:tail", "element:last"]),
         ("[first, second, tail @ .., last,]",
           ["element:first", "element:second", "rest:tail", "element:last"]),
         ("[tail'@..]", ["rest:tail'"]),
         ("[first, .., last,]", ["element:first", "bare", "element:last"]),
         ("[..,]", ["bare"]),
         ("[\n first, // \<alpha> trivia\n tail' // binder\n @ // alias\n .., // rest\n last,\n]",
           ["element:first", "rest:tail'", "element:last"]),
         ("[\<comment>\<open>\<alpha>\<close> tail @ \<comment>\<open>gap\<close> ..]",
           ["rest:tail"])]

    val _ =
      (case parse_pattern "[[inside @ ..,], outside @ ..,]" of
         P_Slice
           ([SI_Pat (P_Slice ([SI_BoundRest ("inside", _, _, _)], _)),
             SI_BoundRest ("outside", _, _, _)], _) => ()
       | _ => error "slice pattern syntax audit: nested rest AST changed")
    val _ =
      (case parse_pattern "whole @ [first @ item, middle @ .., last]" of
         P_Alias ("whole", _,
           P_Slice
             ([SI_Pat (P_Alias ("first", _, P_Ident ("item", _), _)),
               SI_BoundRest ("middle", _, _, _),
               SI_Pat (P_Ident ("last", _))], _), _) => ()
       | _ => error "slice pattern syntax audit: whole-list or element alias changed")
    val _ =
      (case parse_pattern "Some(([inside @ ..], Head { field: [outside @ ..], .. }))" of
         P_Constr (path,
           [P_Tuple
             ([P_Slice ([SI_BoundRest ("inside", _, _, _)], _),
               P_Struct (_, [SF_Field ("field", _,
                 P_Slice ([SI_BoundRest ("outside", _, _, _)], _)), SF_Rest _], _)], _)], _) =>
           assert "constructor nesting changed" (render_path path = "Some")
       | _ => error "slice pattern syntax audit: tuple or struct nesting changed")
    val _ =
      (case parse_pattern "&mut [0..=3, middle @ .., last]" of
         P_Borrow (BM_Mut,
           P_Slice
             ([SI_Pat (P_Range (RK_Inclusive, _, _, _)),
               SI_BoundRest ("middle", _, _, _),
               SI_Pat (P_Ident ("last", _))], _), _) => ()
       | _ => error "slice pattern syntax audit: range or reference wrapper changed")
    val _ =
      List.app
        (fn spelling =>
          let
            val text = pattern_source spelling
            val pattern = match_pattern text
          in
            ignore (audit_bound_positions text (size prefix) (bound_rests pattern))
          end)
        ["[[inside @ ..,], outside @ ..,]",
         "Some(([inside @ ..], Head { field: [outside @ ..], .. }))",
         "whole @ [first @ item, middle @ .., last]",
         "&mut [0..=3, middle @ .., last]"]

    val _ =
      List.app
        (fn lexeme =>
          (audit_slice ("[" ^ lexeme ^ ", tail @ .., " ^ lexeme ^ ",]")
             ["integer:" ^ lexeme, "rest:tail", "integer:" ^ lexeme];
           case parse_pattern ("Some(" ^ lexeme ^ ")") of
             P_Constr (path, [P_Literal (LP_Integer (Integer_Literal (actual, Source_Layout ( _, _), _)))], _) =>
               assert ("nested integer lexeme changed: " ^ lexeme)
                 (render_path path = "Some" andalso actual = lexeme)
           | _ => error "slice pattern syntax audit: nested integer AST changed"))
        ["0", "17", "0b1_0", "0o1_7", "0xff", "1u8", "2_u16", "3u32", "4_u64",
         "5usize", "0xff_u8"]

    fun consumer_pattern text =
      (case parse text of
         UE_Match (_, _, [UR_Arm (pattern, NONE, _, _)], _) => pattern
       | UE_IfLet (pattern, _, _, _, _) => pattern
       | UE_LetElse (pattern, _, _, _, _) => pattern
       | UE_WhileLet (_, pattern, _, _, _) => pattern
       | UE_For (pattern, _, _, _) => pattern
       | UE_Let (pattern, _, _, _) => pattern
       | UE_Const (pattern, _, _, _) => pattern
       | UE_LetMut (pattern, _, _, _) => pattern
       | UE_Macro (_, MP_Matches (_, pattern), _) => pattern
       | UE_Closure ([pattern], _, _) => pattern
       | _ => error "slice pattern syntax audit: unexpected consumer AST")
    val _ =
      List.app
        (fn text =>
          let val pattern = consumer_pattern text in
            assert "consumer lost its positioned rest"
              (map #1 (bound_rests pattern) = ["tail"]);
            ignore (audit_bound_positions text 0 (bound_rests pattern))
          end)
        ["match \<llangle>undefined\<rrangle> { [tail @ ..] => () }",
         "match_case \<llangle>undefined\<rrangle> { [tail @ ..] => () }",
         "match_switch \<llangle>undefined\<rrangle> { [tail @ ..] => () }",
         "if let [tail @ ..] = \<llangle>undefined\<rrangle> { () } else { () }",
         "let [tail @ ..] = \<llangle>undefined\<rrangle> else { () }; ()",
         "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let [tail @ ..] = \<llangle>undefined\<rrangle> { () }",
         "for [tail @ ..] in \<llangle>undefined\<rrangle> { () }",
         "let whole @ outer @ ([tail @ ..], other) = \<llangle>undefined\<rrangle>; ()",
         "const [tail @ ..] = \<llangle>undefined\<rrangle>; ()",
         "let mut [tail @ ..] = \<llangle>undefined\<rrangle>; ()",
         "matches!(\<llangle>undefined\<rrangle>, [tail @ ..,])",
         "|[tail @ ..]| ()",
         "|whole @ ([tail @ ..], other)| ()"]

    val _ =
      (case parse "let whole @ outer @ ([tail @ ..], other) = \<llangle>undefined\<rrangle>; ()" of
         UE_Let
           (P_Alias ("whole", _,
             P_Alias ("outer", _,
               P_Tuple
                 ([P_Slice ([SI_BoundRest ("tail", _, _, _)], _),
                   P_Ident ("other", _)], _), _), _), _, _, _) => ()
       | _ => error "slice pattern syntax audit: recursive ordinary alias AST changed")

    fun audit_arm_count text expected =
      (case parse text of
         UE_Match (_, _, arms, _) =>
           assert "match arm separator changed" (length arms = expected)
       | _ => error "slice pattern syntax audit: expected match arms")
    val _ =
      List.app (fn text => audit_arm_count text 2)
        ["match_case \<llangle>undefined\<rrangle> { [head, ..] => (), [tail @ ..] => (), }",
         "match_case \<llangle>undefined\<rrangle> { [head, ..] => {} , [tail @ ..,] => {} }",
         "match_case \<llangle>undefined\<rrangle> { [head, ..] => {} ([tail @ ..]) => {} }"]
  in
  end
\<close>

section\<open> Token markup and binder navigation \<close>

datatype 'a binder_markup_point = BinderMarkupPoint (x: 'a)

datatype 'a binder_markup_option_point = BinderMarkupOptionPoint (None: "'a option")

datatype binder_markup_fields =
  BinderMarkupFields (field_x: nat) (field_tag: nat) (field_ignored: bool)

text\<open>
Parser-owned declarations have no entity destination properties. A reference ID at a pattern
declaration still connects shared highlighting to the canonical definition; it is not a hyperlink.
Explicit struct labels and constructor/value patterns retain their own declaration navigation.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    fun assert label condition =
      if condition then () else error ("slice pattern markup audit: " ^ label)
    fun find_from text needle raw =
      if raw + size needle > size text then
        error ("slice pattern markup audit: missing " ^ quote needle)
      else if String.substring (text, raw, size needle) = needle then raw
      else find_from text needle (raw + 1)
    fun token_position text start needle raw =
      let
        val found = find_from text needle raw
        val left = Position.symbol_explode (String.substring (text, 0, found)) start
      in
        (found, Position.range_position (left, Position.symbol_explode needle left))
      end
    fun has_position properties position =
      Properties.get properties Markup.offsetN =
        Option.map Value.print_int (Position.offset_of position) andalso
      Properties.get properties Markup.end_offsetN =
        Option.map Value.print_int (Position.end_offset_of position)
    fun has_markup reports name position =
      exists (fn (actual, properties) =>
        actual = name andalso has_position properties position) reports
    fun entity_id reports property position =
      (case reports
          |> map_filter
            (fn (name, properties) =>
              if name = Markup.entityN andalso
                 Properties.get properties Markup.kindN = SOME "urust_var" andalso
                 has_position properties position
              then Properties.get properties property
              else NONE)
          |> distinct (op =) of
         [id] => id
       | _ => error "slice pattern markup audit: binder entity identity changed")
    fun capture text start =
      let
        val (_, reports) = Parser_Test_Reports.markup (fn () =>
          Parser_Test_Elaboration.expression ctxt
            (Parser_Lex_Util.positioned_content_source text start))
        (* Capture is process-wide: concurrent theories may report at the same offsets. *)
      in
        filter (fn (_, properties) =>
          Properties.get properties Markup.idN = Position.id_of start) reports
      end
      handle ERROR message => error ("markup audit source " ^ quote text ^ ": " ^ message)
    fun entity_properties reports position =
      map_filter (fn (name, properties) =>
        if name = Markup.entityN andalso has_position properties position
        then SOME properties else NONE) reports
    fun assert_declaration reports position =
      (assert "binder lost its exact bound span"
         (has_markup reports Markup.boundN position);
       assert "binder lost its entity tooltip"
         (exists (fn properties =>
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            is_some (Properties.get properties Markup.nameN))
           (entity_properties reports position));
       assert "binder declaration acquired a hyperlink destination"
         (List.all (fn properties =>
            not (exists (String.isPrefix "def_" o fst) properties))
           (entity_properties reports position)))
    fun assert_reference reports definition reference =
      let
        val id = entity_id reports Markup.defN definition
      in
        assert "use lost its canonical binder identity"
          (entity_id reports Markup.refN reference = id);
        assert "use lost its canonical hyperlink destination"
          (exists (fn properties =>
             Properties.get properties Markup.refN = SOME id andalso
             List.all (fn (key, value) =>
               Properties.get properties key = SOME value)
               (Position.def_properties_of definition))
            (entity_properties reports reference))
      end

    val text =
      "match_case \<llangle>[1 :: nat, 4, 9]\<rrangle> { " ^
      "[head, middle' // \<alpha> after binder\n @ // alias trivia\n .., last,] => " ^
      "{ let _ = head; let _ = middle'; let _ = \<llangle>middle'\<rrangle>; let _ = last; () }, _ => () }"
    val start = Position.make0 29 700 0 "" "" "slice-pattern-markup-audit"
    val reports = capture text start
    val (id_raw, definition) = token_position text start "middle'" 0
    val (alias_raw, alias_position) = token_position text start "@" (id_raw + size "middle'")
    val (_, rest_position) = token_position text start ".." (alias_raw + 1)
    val (reference_raw, reference) =
      token_position text start "middle'" (id_raw + size "middle'")
    val (_, antiquotation_reference) =
      token_position text start "middle'" (reference_raw + size "middle'")
    val (_, first_comment) = token_position text start "// \<alpha> after binder" 0
    val (_, second_comment) = token_position text start "// alias trivia" 0

    val _ =
      List.app
        (fn (label, position) =>
          (assert (label ^ " lost operator markup")
             (has_markup reports Markup.operatorN position);
           assert (label ^ " lost typing markup")
             (has_markup reports Markup.typingN position);
           assert (label ^ " acquired bound markup")
             (not (has_markup reports Markup.boundN position))))
        [("rest alias", alias_position), ("rest dots", rest_position)]
    val _ =
      List.app
        (fn position =>
          assert "line comment span or markup changed"
            (has_markup reports Markup.comment1N position))
        [first_comment, second_comment]
    val _ =
      List.app
        (fn position =>
          assert "rest binder or occurrence lost bound markup"
            (has_markup reports Markup.boundN position))
        [definition, reference, antiquotation_reference]
    val _ =
      assert "body reference no longer navigates to its rest binder"
        (entity_id reports Markup.defN definition = entity_id reports Markup.refN reference)
    val _ =
      assert "antiquotation reference no longer navigates to its rest binder"
        (entity_id reports Markup.defN definition =
          entity_id reports Markup.refN antiquotation_reference)
    val _ =
      assert "rest binder was reported as a HOL constant"
        (not (exists (fn (name, properties) =>
          name = Markup.entityN andalso
          Properties.get properties Markup.kindN = SOME Markup.constantN andalso
          has_position properties definition) reports))
    val _ = assert_declaration reports definition
    val _ = List.app (assert_reference reports definition)
      [reference, antiquotation_reference]

    val (_, left_bracket) = token_position text start "[" (find_from text " { " 0)
    val (_, right_bracket) = token_position text start "]" alias_raw
    val (_, comma) = token_position text start "," alias_raw
    val (_, arrow) = token_position text start "=>" alias_raw
    val _ =
      List.app
        (fn position =>
          (assert "slice punctuation lost delimiter markup"
             (has_markup reports Markup.delimiterN position);
           assert "slice punctuation lost typing markup"
             (has_markup reports Markup.typingN position)))
        [left_bracket, right_bracket, comma, arrow]

    val numeral_text =
      "match_case \<llangle>[0 :: nat, 4, 9]\<rrangle> { [0, tail @ .., 9] => " ^
      "{ let _ = tail; () }, _ => () }"
    val numeral_start = Position.make0 37 1100 0 "" "" "slice-pattern-numeral-markup"
    val numeral_reports = capture numeral_text numeral_start
    val pattern_raw = find_from numeral_text " { " 0
    val (_, zero_position) = token_position numeral_text numeral_start "0" pattern_raw
    val (_, nine_position) = token_position numeral_text numeral_start "9" pattern_raw
    val _ =
      List.app
        (fn position =>
          (assert "structural integer lost numeral markup"
             (has_markup numeral_reports Markup.numeralN position);
           assert "structural integer lost typing markup"
             (has_markup numeral_reports Markup.typingN position)))
        [zero_position, nine_position]

    val _ =
      List.app
        (fn (name, spelling) =>
          let
            val text = "match_case \<llangle>[] :: nat list\<rrangle> { [" ^ spelling ^
              "] => { let _ = " ^ name ^ "; () } }"
            val start = Position.make0 39 1200 0 "" "" "slice-pattern-tight-markup"
            val reports = capture text start
            val (id_raw, definition) = token_position text start name 0
            val (alias_raw, alias_position) = token_position text start "@" id_raw
            val (_, rest_position) = token_position text start ".." alias_raw
            val (_, reference) = token_position text start name (id_raw + size name)
          in
            assert "tight or multiline rest binder navigation changed"
              (entity_id reports Markup.defN definition = entity_id reports Markup.refN reference);
            List.app
              (fn position =>
                (assert "tight or multiline operator span changed"
                   (has_markup reports Markup.operatorN position);
                 assert "tight or multiline operator lost typing"
                   (has_markup reports Markup.typingN position)))
              [alias_position, rest_position]
          end)
        [("tail", "tail@.."), ("tail", "tail @ .."),
         ("tail'", "tail'@.."), ("tail'", "tail'\n @\n ..")]

    (* Preparation must report the pattern occurrence as well as allocate its definition.
       Reversed captures use an alias over a wildcard, so later basic binding cannot report it. *)
    val _ =
      List.app
        (fn pattern =>
          let
            val text =
              "// \<alpha> before the pattern\n" ^
              "match_case \<llangle>[11 :: nat, 23, 37]\<rrangle> { [" ^ pattern ^
              "] => { let _ = rest; let _ = \<llangle>rest\<rrangle>; () } }"
            val start = Position.make0 40 1300 0 "" "" "slice-pattern-rest-preparation"
            val reports = capture text start
            val (raw, definition) = token_position text start "rest" 0
            val (body_raw, reference) =
              token_position text start "rest" (raw + size "rest")
            val (_, antiquotation_reference) =
              token_position text start "rest" (body_raw + size "rest")
            val id = entity_id reports Markup.defN definition
          in
            assert (pattern ^ " lost its prepared binder occurrence")
              (entity_id reports Markup.refN definition = id);
            assert_declaration reports definition;
            List.app
              (fn position =>
                assert_reference reports definition position)
              [reference, antiquotation_reference]
          end)
        ["rest @ ..", "_, rest @ ..", "rest @ .., _", "_, rest @ .., _"]

    val _ =
      List.app
        (fn (binding, names) =>
          let
            val text =
              "// \<alpha> before the binding\n" ^ binding ^
              String.concat (map (fn name =>
                "let _ = " ^ name ^ "; let _ = \<llangle>" ^ name ^ "\<rrangle>; ") names) ^
              "()"
            val start = Position.make0 40 1300 0 "" "" "slice-pattern-direct-binding"
            val reports = capture text start
            fun audit name =
              let
                val (raw, definition) = token_position text start name 0
                val (body_raw, reference) =
                  token_position text start name (raw + size name)
                val (_, antiquotation_reference) =
                  token_position text start name (body_raw + size name)
                val id = entity_id reports Markup.defN definition
              in
                assert_declaration reports definition;
                assert "direct binding lost its definition identity" (id <> "");
                List.app (assert_reference reports definition)
                  [reference, antiquotation_reference]
              end
          in List.app audit names end)
        [("let [tail @ ..] = \<llangle>[11 :: nat, 23]\<rrangle>; ", ["tail"]),
         ("let [tail' @ ..] = \<llangle>[] :: nat list\<rrangle>; ", ["tail'"]),
         ("let whole @ [tail @ ..] = \<llangle>[11 :: nat, 23]\<rrangle>; ", ["whole", "tail"]),
         ("let ([tail @ ..], other) = (\<llangle>[11 :: nat, 23]\<rrangle>, 37); ",
           ["tail", "other"]),
         ("let item = 11; ", ["item"]),
         ("const item = 11; ", ["item"]),
         ("let whole @ outer @ (item, (other, [tail @ ..])) = " ^
            "(11, (23, \<llangle>[37 :: nat]\<rrangle>)); ",
           ["whole", "outer", "item", "other", "tail"])]

    val alternatives_text =
      "match_case \<llangle>[1 :: nat, 4, 9]\<rrangle> { " ^
      "[head, tail @ ..] | [tail @ .., head] => { let _ = tail; let _ = head; () }, _ => () }"
    val alternatives_start = Position.make0 41 1400 0 "" "" "slice-pattern-alternatives-markup"
    val alternatives_reports = capture alternatives_text alternatives_start
    val (head_raw, head_def) = token_position alternatives_text alternatives_start "head" 0
    val (tail_raw, tail_def) = token_position alternatives_text alternatives_start "tail" head_raw
    val (tail_alt_raw, tail_alt) =
      token_position alternatives_text alternatives_start "tail" (tail_raw + size "tail")
    val (head_alt_raw, head_alt) =
      token_position alternatives_text alternatives_start "head" (tail_alt_raw + size "tail")
    val (tail_body_raw, tail_body) =
      token_position alternatives_text alternatives_start "tail" (head_alt_raw + size "head")
    val (_, head_body) =
      token_position alternatives_text alternatives_start "head" (tail_body_raw + size "tail")
    val _ =
      List.app
        (fn (definition, reference) =>
          assert "repositioned alternative binder lost its canonical entity"
            (entity_id alternatives_reports Markup.defN definition =
              entity_id alternatives_reports Markup.refN reference))
        [(tail_def, tail_alt), (head_def, head_alt), (tail_def, tail_body), (head_def, head_body)]
    val _ = List.app (assert_declaration alternatives_reports)
      [head_def, tail_def, tail_alt, head_alt]
    val _ = assert_reference alternatives_reports tail_def tail_body
    val _ = assert_reference alternatives_reports head_def head_body

    (* The same policy applies to every consumer of prepared case/binding patterns. *)
    val _ =
      List.app
        (fn text =>
          let
            val text = "// \<alpha> before the binding\n" ^ text
            val start = Position.make0 43 1500 0 "" "" "binder-consumer-markup"
            val reports = capture text start
            val (raw, definition) = token_position text start "item" 0
            val (_, reference) = token_position text start "item" (raw + size "item")
          in
            assert_declaration reports definition;
            assert_reference reports definition reference
          end)
        ["let mut item = 11; let _ = item; ()",
         "for item in \<llangle>[11 :: nat]\<rrangle> { let _ = item; () }",
         "for whole @ (item, _) in \<llangle>[(11 :: nat, (23 :: nat, TNil))]\<rrangle> " ^
           "{ let _ = item; () }",
         "|item| { let _ = item; () }",
         "|(item, _)| { let _ = item; () }",
         "|whole @ (item, _)| { let _ = item; () }",
         "|[item @ ..]| { let _ = item; () }",
         "match Some(11) { Some(item) => { let _ = item; () }, _ => () }",
         "if let Some(item) = Some(11) { let _ = item; () } else { () }",
         "let Some(item) = Some(11) else { return 0; }; let _ = item; ()",
         "#[fuel(\<epsilon>\<open>1 :: nat\<close>)] while let Some(item) = Some(11) " ^
           "{ let _ = item; () }"]

    val macro_text = "matches!(Some(11), Some(item))"
    val macro_start = Position.make0 45 1600 0 "" "" "matches-binder-markup"
    val macro_reports = capture macro_text macro_start
    val (_, macro_binder) = token_position macro_text macro_start "item" 0
    val _ = assert_declaration macro_reports macro_binder
    val _ = assert "matches binder lost its allocated entity"
      (entity_id macro_reports Markup.defN macro_binder <> "")

    (* Alias heads in later alternatives have the same identity without a destination. *)
    val alias_text =
      "// \<alpha> before aliases\nmatch_case \<llangle>[11 :: nat]\<rrangle> { " ^
      "whole @ [item] | whole @ [item, _] if item == 11 => " ^
      "{ let _ = whole; let _ = \<llangle>whole\<rrangle>; let _ = item; () }, _ => () }"
    val alias_start = Position.make0 47 1700 0 "" "" "alias-alternative-markup"
    val alias_reports = capture alias_text alias_start
    val _ =
      List.app (fn name =>
        let
          val (raw, definition) = token_position alias_text alias_start name 0
          val (alt_raw, alternative) =
            token_position alias_text alias_start name (raw + size name)
          val (use_raw, reference) =
            token_position alias_text alias_start name (alt_raw + size name)
        in
          assert_declaration alias_reports definition;
          assert_declaration alias_reports alternative;
          assert "later alias alternative lost shared highlighting"
            (entity_id alias_reports Markup.refN alternative =
              entity_id alias_reports Markup.defN definition);
          assert_reference alias_reports definition reference;
          if name = "whole" then
            assert_reference alias_reports definition
              (#2 (token_position alias_text alias_start name (use_raw + size name)))
          else ()
        end) ["whole", "item"]

    (* A shorthand binder has no selector entity at the same token. Explicit labels do. *)
    val _ =
      List.app (fn (pattern, name, shorthand) =>
        let
          val text = "match_case \<llangle>BinderMarkupPoint (11 :: nat)\<rrangle> { " ^
            pattern ^ " => { let _ = " ^ name ^ "; () } }"
          val start = Position.make0 49 1800 0 "" "" "struct-binder-markup"
          val reports = capture text start
          val pattern_raw = find_from text " { " 0
          val (label_raw, label) = token_position text start "x" pattern_raw
          val (raw, definition) =
            token_position text start name
              (if shorthand then label_raw else label_raw + size "x:")
          val _ = assert_declaration reports definition
          val _ =
            assert "struct label navigation policy changed"
              (exists (fn properties =>
                 Properties.get properties Markup.kindN = SOME Markup.constantN andalso
                 Properties.get properties Markup.nameN = SOME \<^const_name>\<open>x\<close> andalso
                 is_some (Properties.get properties "def_offset"))
                (entity_properties reports label) = not shorthand)
        in
          assert_reference reports definition
            (#2 (token_position text start name
              (find_from text " => " raw + size " => ")))
        end)
        [("BinderMarkupPoint { x: value }", "value", false),
         ("BinderMarkupPoint { x }", "x", true),
         ("BinderMarkupPoint { x: x }", "x", false)]

    val shorthand_text =
      "// \<alpha> before mixed fields\nmatch_case \<llangle>BinderMarkupFields 11 0 True\<rrangle> { " ^
      "BinderMarkupFields { field_tag: 0, field_x, .. } | " ^
      "BinderMarkupFields { field_x, field_tag: 1, .. } => " ^
      "{ let _ = field_x; let _ = \<llangle>field_x\<rrangle>; () }, _ => () }"
    val shorthand_start = Position.make0 50 1900 0 "" "" "shorthand-alternative-markup"
    val shorthand_reports = capture shorthand_text shorthand_start
    val (shorthand_raw, shorthand_def) =
      token_position shorthand_text shorthand_start "field_x" 0
    val (shorthand_alt_raw, shorthand_alt) =
      token_position shorthand_text shorthand_start "field_x" (shorthand_raw + size "field_x")
    val (shorthand_body_raw, shorthand_body) =
      token_position shorthand_text shorthand_start "field_x" (shorthand_alt_raw + size "field_x")
    val (_, shorthand_antiq) =
      token_position shorthand_text shorthand_start "field_x" (shorthand_body_raw + size "field_x")
    val _ = List.app (assert_declaration shorthand_reports)
      [shorthand_def, shorthand_alt]
    val _ = assert "shorthand alternative lost its canonical entity"
      (entity_id shorthand_reports Markup.refN shorthand_alt =
        entity_id shorthand_reports Markup.defN shorthand_def)
    val _ = List.app (assert_reference shorthand_reports shorthand_def)
      [shorthand_body, shorthand_antiq]
    val (first_label_raw, first_label) =
      token_position shorthand_text shorthand_start "field_tag" 0
    val (_, second_label) =
      token_position shorthand_text shorthand_start "field_tag"
        (first_label_raw + size "field_tag")
    val _ =
      List.app (fn position =>
        assert "mixed explicit field lost its selector destination"
          (exists (fn properties =>
             Properties.get properties Markup.kindN = SOME Markup.constantN andalso
             Properties.get properties Markup.nameN = SOME \<^const_name>\<open>field_tag\<close> andalso
             is_some (Properties.get properties "def_offset"))
            (entity_properties shorthand_reports position)))
        [first_label, second_label]
    val mixed_ast =
      the (URust_Parser.parse_source ctxt
        (Parser_Lex_Util.positioned_content_source shorthand_text shorthand_start))
    val mixed_patterns =
      (case mixed_ast of
         URust_AST.UE_Match (_, _, URust_AST.UR_Arm (URust_AST.P_Or (patterns, _), _, _, _) :: _, _) =>
           patterns
       | _ => error "mixed field markup audit: alternative AST changed")
    val mixed_resolver = URust_Resolution.make_constructor_resolver ctxt shorthand_start
    val _ = List.app (fn pattern =>
      (case pattern of
         URust_AST.P_Struct (path, fields, _) =>
           (case URust_Resolution.resolve_struct_pattern ctxt mixed_resolver (path, fields) of
              URust_Resolution.Resolved_Constructor_Struct (_, ordered) =>
                assert "resolved field order, shorthand flag, or omitted field changed"
                  (map (fn {selector, source_position, shorthand, ...} =>
                     (#1 (dest_Const selector), is_some source_position, shorthand)) ordered =
                   [(\<^const_name>\<open>field_x\<close>, true, true),
                    (\<^const_name>\<open>field_tag\<close>, true, false),
                    (\<^const_name>\<open>field_ignored\<close>, false, false)])
            | _ => error "mixed field markup audit: constructor metadata changed")
       | _ => error "mixed field markup audit: struct AST changed")) mixed_patterns

    val constructor_text =
      "match_case \<llangle>undefined :: nat binder_markup_option_point\<rrangle> { " ^
      "BinderMarkupOptionPoint { None } => (), _ => () }"
    val constructor_start = Position.make0 51 1950 0 "" "" "shorthand-constructor-markup"
    val constructor_reports = capture constructor_text constructor_start
    val (_, constructor_pos) = token_position constructor_text constructor_start "None" 0
    val _ = assert "shorthand constructor lost its own navigation"
      (exists (fn properties =>
         Properties.get properties Markup.kindN = SOME Markup.constantN andalso
         Properties.get properties Markup.nameN = SOME "Option.option.None" andalso
         is_some (Properties.get properties "def_offset"))
        (entity_properties constructor_reports constructor_pos))
    val _ = assert "shorthand constructor acquired a competing selector entity"
      ((map_filter (fn properties =>
         if Properties.get properties Markup.kindN = SOME Markup.constantN
         then Properties.get properties Markup.nameN else NONE)
        (entity_properties constructor_reports constructor_pos)
        |> distinct (op =)) = ["Option.option.None"])

    (* Shadowing and sibling arms retain distinct canonical declarations. *)
    val _ =
      List.app (fn text =>
        let
          val start = Position.make0 52 1970 0 "" "" "binder-scope-markup"
          val reports = capture text start
          val (first_raw, first) = token_position text start "item" 0
          val (first_use_raw, first_use) =
            token_position text start "item" (first_raw + size "item")
          val (second_raw, second) =
            token_position text start "item" (first_use_raw + size "item")
          val (_, second_use) =
            token_position text start "item" (second_raw + size "item")
        in
          List.app (assert_declaration reports) [first, second];
          assert "independent declarations reused a binder ID"
            (entity_id reports Markup.defN first <> entity_id reports Markup.defN second);
          assert_reference reports first first_use;
          assert_reference reports second second_use
        end)
        ["let item = 11; let _ = item; let item = 23; let _ = item; ()",
         "match_case Some(11) { Some(item) if item == 0 => (), " ^
           "Some(item) => { let _ = item; () }, _ => () }"]

    (* One formal list cannot repeat a binder; a nested closure's list is independent. *)
    val closure_text = "|item| (|item| { let _ = item; () })"
    val closure_start = Position.make0 52 1990 0 "" "" "nested-closure-formals-markup"
    val closure_reports = capture closure_text closure_start
    val (closure_first_raw, closure_first) =
      token_position closure_text closure_start "item" 0
    val (closure_second_raw, closure_second) =
      token_position closure_text closure_start "item" (closure_first_raw + size "item")
    val (_, closure_use) =
      token_position closure_text closure_start "item" (closure_second_raw + size "item")
    val _ = List.app (assert_declaration closure_reports) [closure_first, closure_second]
    val _ = assert "nested closure formals reused their entity"
      (entity_id closure_reports Markup.defN closure_first <>
        entity_id closure_reports Markup.defN closure_second)
    val _ = assert_reference closure_reports closure_second closure_use

    val _ =
      List.app
        (fn name =>
          let
            val collision_text =
              "match_case \<llangle>[] :: nat list\<rrangle> { [" ^ name ^
              " @ ..] => { let _ = " ^ name ^ "; () } }"
            val collision_start = Position.make0 53 2000 0 "" "" "slice-pattern-binder-collision"
            val collision_reports = capture collision_text collision_start
            val (raw, definition) = token_position collision_text collision_start name 0
            val (_, reference) =
              token_position collision_text collision_start name (raw + size name)
          in
            assert (name ^ " rest stopped introducing a binder")
              (entity_id collision_reports Markup.defN definition =
                entity_id collision_reports Markup.refN reference)
          end)
        ["Some", "Nil", "length", "True"]
  in
  end
\<close>

section\<open> Atomic validation and positioned failures \<close>

text\<open>
Multiplicity, duplicates, and unequal alternative binder sets fail before local allocation or
guard/body macro resolution. Each failure is followed by a successful elaboration through the same
parser API. Diagnostics retain both primary and secondary source ranges where the existing policy
provides them.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val source_id = "slice-pattern-rejection-audit"
    val start = Position.make0 67 3000 0 "" "" source_id
    val prefix = "// \<alpha> before validation\nmatch_case \<llangle>[] :: nat list\<rrangle> { "
    fun assert label condition =
      if condition then () else error ("slice pattern rejection audit: " ^ label)
    fun find_from text needle raw =
      if raw + size needle > size text then
        error ("slice pattern rejection audit: missing " ^ quote needle)
      else if String.substring (text, raw, size needle) = needle then raw
      else find_from text needle (raw + 1)
    fun occurrence text needle count =
      let
        fun next 0 raw = find_from text needle raw
          | next n raw = next (n - 1) (find_from text needle raw + size needle)
      in next count (size prefix) end
    fun expected_position text (needle, count) =
      let
        val raw = occurrence text needle count
        val left = Position.symbol_explode (String.substring (text, 0, raw)) start
      in Position.range_position (left, Position.symbol_explode needle left) end
    fun diagnostic_spans message =
      fold Parser_Test_Reports.collect_markup (YXML.parse_body message) []
      |> map_filter (fn (_, properties) =>
        case (Properties.get properties Markup.offsetN,
              Properties.get properties Markup.end_offsetN) of
          (SOME left, SOME right) => SOME (left, right)
        | _ => NONE)
    fun span position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))
    fun recovery () =
      ignore (Parser_Test_Elaboration.expression ctxt
        (Parser_Lex_Util.text_source
          "match_case \<llangle>[] :: nat list\<rrangle> { [tail @ ..,] => { let _ = tail; () } }"))

    fun reject (pattern, expected, primary, secondary) =
      let
        val text = prefix ^ pattern ^
          " if unknown_slice_guard!() => unknown_slice_body!(), _ => () }"
        val (result, reports) =
          Parser_Test_Reports.markup (fn () =>
            Exn.result (fn () => Parser_Test_Elaboration.expression ctxt
              (Parser_Lex_Util.positioned_content_source text start)) ())
        val message =
          (case result of
             Exn.Res _ => error ("slice pattern rejection audit: accepted " ^ quote pattern)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn)
        val plain = XML.content_of (YXML.parse_body message)
        val spans = diagnostic_spans message
        val _ = assert (pattern ^ " diagnostic changed") (String.isSubstring expected plain)
        val _ = assert (pattern ^ " primary diagnostic range changed")
          (member (op =) spans (span (expected_position text primary)))
        val _ =
          (case secondary of
             NONE => ()
           | SOME token =>
               assert (pattern ^ " secondary diagnostic range changed")
                 (member (op =) spans (span (expected_position text token))))
        (* Report capture is process-wide; concurrent theory commands may also emit entities. *)
        val _ = assert (pattern ^ " allocated a rejected binder")
          (not (exists (fn (name, properties) =>
            name = Markup.entityN andalso
            Properties.get properties Markup.kindN = SOME "urust_var" andalso
            Properties.get properties Markup.idN = SOME source_id) reports))
        val _ = assert (pattern ^ " lowered a rejected guard or body")
          (not (String.isSubstring "unknown macro" plain))
        val _ = assert (pattern ^ " leaked a generated identifier")
          (not (String.isSubstring "_urust_" plain))
      in recovery () end

    val multiple = "slice pattern has multiple `..` rest entries"
    val _ =
      List.app reject
        [("[.., ..]", multiple, ("..", 1), NONE),
         ("[left @ .., right @ ..]", multiple, ("..", 1), NONE),
         ("[tail @ .., ..]", multiple, ("..", 1), NONE),
         ("[.., tail @ ..]", multiple, ("..", 1), NONE),
         ("[first, [left @ .., right @ ..], outer @ ..]", multiple, ("..", 1), NONE),
         ("[tail, tail @ ..]", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("[tail @ .., tail]", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("whole @ [whole @ ..]", "duplicate pattern binder \"whole\"",
           ("whole", 1), SOME ("whole", 0)),
         ("([tail @ ..], [tail @ ..])", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("[item @ tail, tail @ ..]", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("[tail @ ..] | [..]", "or-pattern alternative is missing binder \"tail\"",
           ("|", 0), SOME ("tail", 0)),
         ("[..] | [tail @ ..]", "or-pattern alternative has extra binder \"tail\"",
           ("tail", 0), NONE),
         ("[first, tail @ ..] | [other, tail @ ..]",
           "or-pattern alternative is missing binder \"first\"", ("|", 0), SOME ("first", 0)),
         ("[tail @ ..] | [tail @ .., tail]", "duplicate pattern binder \"tail\"",
           ("tail", 2), SOME ("tail", 1)),
         ("[tail, tail @ ..] | [other @ ..]", "duplicate pattern binder \"tail\"",
           ("tail", 1), SOME ("tail", 0)),
         ("Some([tail @ ..] | [..])", "or-pattern alternative is missing binder \"tail\"",
           ("|", 0), SOME ("tail", 0)),
         ("[_ @ ..]", "slice rest binder cannot be `_`", ("_", 0), NONE)]
    val (_, recovery_reports) =
      Parser_Test_Reports.markup (fn () =>
        Parser_Test_Elaboration.expression ctxt
          (Parser_Lex_Util.positioned_content_source
            (prefix ^ "[tail @ ..] => { let _ = tail; () } }") start))
    val _ = assert "source-scoped report audit lost successful binder reports"
      (exists (fn (name, properties) =>
        name = Markup.entityN andalso
        Properties.get properties Markup.kindN = SOME "urust_var" andalso
        Properties.get properties Markup.idN = SOME source_id) recovery_reports)
  in
  end
\<close>

section\<open> Malformed rest syntax, separators, and recovery \<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val start = Position.make0 79 4000 0 "" "" "slice-pattern-malformed-audit"
    fun parse text =
      URust_Parser.parse_source ctxt
        (Parser_Lex_Util.positioned_content_source text start)
    fun find_from text needle raw =
      if raw + size needle > size text then
        error ("slice pattern malformed audit: missing " ^ quote needle)
      else if String.substring (text, raw, size needle) = needle then raw
      else find_from text needle (raw + 1)
    fun token_position text needle count =
      let
        fun occurrence 0 raw = find_from text needle raw
          | occurrence n raw =
              occurrence (n - 1) (find_from text needle raw + size needle)
        val raw = occurrence count 0
        val left = Position.symbol_explode (String.substring (text, 0, raw)) start
      in Position.range_position (left, Position.symbol_explode needle left) end
    fun diagnostic_spans message =
      fold Parser_Test_Reports.collect_markup (YXML.parse_body message) []
      |> map_filter (fn (_, properties) =>
        case (Properties.get properties Markup.offsetN,
              Properties.get properties Markup.end_offsetN) of
          (SOME left, SOME right) => SOME (left, right)
        | _ => NONE)
    fun span position =
      (Value.print_int (the (Position.offset_of position)),
       Value.print_int (the (Position.end_offset_of position)))
    fun reject text =
      (case Exn.result parse text of
         Exn.Res _ => error ("slice pattern malformed audit: accepted " ^ quote text)
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message = Runtime.exn_message exn
               val _ =
                 if String.isSubstring "syntax error" message then ()
                 else error ("slice pattern malformed audit: unexpected diagnostic " ^ message)
               val _ =
                 (case parse "match_case \<llangle>undefined\<rrangle> { [tail@..,] => () }" of
                    SOME (URust_AST.UE_Match
                      (_, _, [URust_AST.UR_Arm
                        (URust_AST.P_Slice
                          ([URust_AST.SI_BoundRest ("tail", _, _, _)], _), NONE, _, _)], _)) => ()
                  | _ => error "slice pattern malformed audit: parser did not recover")
             in () end)
    fun reject_pattern pattern =
      reject ("match_case \<llangle>undefined\<rrangle> { " ^ pattern ^ " => () }")
    fun reject_positioned (pattern, diagnostic, needle, count) =
      let
        val text = "// \<alpha> before malformed pattern\nmatch_case \<llangle>undefined\<rrangle> { " ^
          pattern ^ " => () }"
        val expected = token_position text needle count
        val _ =
          (case Exn.result parse text of
             Exn.Res _ => error ("slice pattern malformed audit: accepted " ^ quote pattern)
           | Exn.Exn exn =>
               if Exn.is_interrupt exn then Exn.reraise exn
               else
                 let
                   val message = Runtime.exn_message exn
                   val plain = XML.content_of (YXML.parse_body message)
                   val _ =
                     if String.isSubstring diagnostic plain then ()
                     else error ("slice pattern malformed audit: diagnostic changed: " ^ message)
                 in
                   if member (op =) (diagnostic_spans message) (span expected) then ()
                   else error ("slice pattern malformed audit: token range changed: " ^ message)
                 end)
      in
        ignore (parse "match_case \<llangle>undefined\<rrangle> { [tail @ ..,] => () }")
      end

    val _ =
      List.app reject_positioned
        [("[tail @ .]", "syntax error: deleting  . ] =>", ".", 0),
         ("[tail @ ...]", "syntax error: deleting  . ] =>", ".", 2),
         ("[tail @ ..,,]", "syntax error: deleting  , ] =>", ",", 1),
         ("[Scope::tail @ ..]", "syntax error: deleting  @ .. ]", "@", 0),
         ("[(tail @ ..)]", "syntax error: deleting  .. ) ]", "..", 0),
         ("[outer @ tail @ ..]", "syntax error: deleting  .. ] =>", "..", 0)]

    val _ =
      List.app reject_pattern
        ["[(tail @ ..)]", "[(tail) @ ..]", "[outer @ tail @ ..]", "[tail @ (..)]",
         "[Scope::tail @ ..]", "[tail::Part @ ..]",
         "[mut tail @ ..]", "[ref tail @ ..]", "[ref mut tail @ ..]",
         "[tail @ mut ..]", "[tail @ ref ..]", "[&tail @ ..]",
         "[tail @ .]", "[tail @ ...]", "[tail @ ....]", "[tail @ ..=]",
         "[...]", "[....]", "[..=]",
         "[tail @ ..=last]", "[tail @ .. last]", "[first tail @ ..]",
         "[, tail @ ..]", "[tail @ ..,,]", "[tail @ .., , last]",
         "[tail @ ]", "[@ ..]", "tail @ ..", "Some(tail @ ..)",
         "(tail @ .., other)", "Head { field: tail @ .. }",
         "..", "Some(..)", "(.., other)", "Head { field: .. }"]
    val _ =
      List.app reject
        ["match_case \<llangle>undefined\<rrangle> { [tail @ ..] => () _ => () }",
         "match_case \<llangle>undefined\<rrangle> { [head, ..] => {} [tail @ ..] => {} }",
         "match_case \<llangle>undefined\<rrangle> { [tail @ ..] => (),, }",
         "match_case \<llangle>undefined\<rrangle> { [tail @ ..",
         "match_case \<llangle>undefined\<rrangle> { [tail @",
         "match_case \<llangle>undefined\<rrangle> { [tail @ ..] =>"]

    val eof_text = "// \<alpha> before EOF\nmatch_case \<llangle>undefined\<rrangle> { [tail @ .."
    val eof = Position.symbol_explode eof_text start
    val _ =
      (case Exn.result parse eof_text of
         Exn.Res _ => error "slice pattern malformed audit: incomplete slice accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             let
               val message = Runtime.exn_message exn
               val plain = XML.content_of (YXML.parse_body message)
               val expected_here = XML.content_of (YXML.parse_body (Position.here eof))
               val _ =
                 if String.isSubstring "syntax error found at end of input" plain andalso
                    String.isSubstring expected_here plain
                 then ()
                 else error ("slice pattern malformed audit: EOF diagnostic moved: " ^ message)
             in () end)
    val _ = ignore (parse "match_case \<llangle>undefined\<rrangle> { [tail @ ..] => (), }")
  in
  end
\<close>

section\<open> Rest-only slice list type constraints \<close>

text\<open>
Iteration reports this mismatch at checked adhoc overloading: no \<open>into_iter\<close> instance can
iterate booleans with a list-pattern body. The same iterable with an ordinary binder elaborates.
\<close>

ML_val\<open>
  ignore (Parser_Test_Elaboration.expression \<^context>
    (Parser_Lex_Util.text_source "for item in \<llangle>[True]\<rrangle> { () }"))
\<close>

section\<open> Unrelated HOL lambda term shapes \<close>

text\<open>
The native cleanup of generated pattern typing witnesses must preserve ordinary HOL abstractions
and checked applications whose binder names share the witness prefix. These checks use explicitly
named, concretely typed abstractions and hand-built expected syntax trees. Ordinary HOL checking
beta-normalizes applications. Each checked prefix-named term must also agree with its checked
non-prefix reference.
\<close>

ML_val\<open>
  local
    val ctxt = \<^context>
    val nat_type = \<^typ>\<open>nat\<close>
    val eleven = \<^term>\<open>11 :: nat\<close>
    val used = Abs ("_urust_pattern_type_probe_used", nat_type, Bound 0)
    val unused = Abs ("_urust_pattern_type_probe_unused", nat_type, \<^term>\<open>True\<close>)
    val used_reference = Abs ("ordinary_lambda_used", nat_type, Bound 0)
    val unused_reference = Abs ("ordinary_lambda_unused", nat_type, \<^term>\<open>True\<close>)

    fun unchanged label raw expected reference =
      let
        val actual = Syntax.check_term ctxt raw |> Term_Position.strip_positions
        val baseline = Syntax.check_term ctxt reference |> Term_Position.strip_positions
      in
        if Term.aconv (actual, expected) andalso Term.aconv (actual, baseline) then ()
        else error ("slice pattern HOL lambda shape audit: " ^ label ^
          "\nactual: " ^ Syntax.string_of_term ctxt actual ^
          "\nbaseline: " ^ Syntax.string_of_term ctxt baseline ^
          "\nexpected: " ^ Syntax.string_of_term ctxt expected)
      end

    val _ = unchanged "used abstraction" used used used_reference
    val _ = unchanged "unused abstraction" unused unused unused_reference
    val _ = unchanged "used application" (used $ eleven) eleven (used_reference $ eleven)
    val _ = unchanged "unused application" (unused $ eleven) \<^term>\<open>True\<close>
      (unused_reference $ eleven)
  in
    val _ = writeln "Unrelated HOL lambda abstractions and applications retain their term shapes"
  end
\<close>

end
