theory Micro_Rust_Matcher_Normalize
  imports Micro_Rust_Elab_Terms
begin

section\<open> Controlled matcher normalization \<close>

text\<open>
The parser matcher is executable continuation-passing code.  Its proof normalizer therefore
rewrites only an active runtime application.  Failure and remaining-alternative thunks are left
opaque until the surrounding matcher selects them; constructor cases and booleans likewise expose
only the selected branch.
\<close>

ML\<open>
structure URust_Matcher_Normalize =
struct
  val runtime_rules =
    @{thms urust_matcher_normalization_defs}

  val basic_rules =
    @{thms
      Let_def
      if_True
      if_False
      fst_conv
      snd_conv
      bind_literal_unit
      bind_literal_unit2}

  fun transitive eq1 eq2 =
    if Thm.is_reflexive eq1 then eq2
    else if Thm.is_reflexive eq2 then eq1
    else Thm.transitive eq1 eq2

  fun strip_cterm ct =
    let
      fun strip current arguments =
        (case try Thm.dest_comb current of
           SOME (head, argument) =>
             strip head (argument :: arguments)
         | NONE => (current, arguments))
    in
      strip ct []
    end

  fun rebuild head arguments =
    fold (fn argument => fn function =>
      Thm.apply function argument) arguments head

  fun rebuild_equation head arguments =
    fold (fn argument => fn function =>
      Thm.combination function argument) arguments head

  fun head_name term =
    (case Term.head_of term of
       Const (name, _) => SOME name
     | _ => NONE)

  fun case_rules context term =
    (case head_name term of
       SOME name =>
         (case Ctr_Sugar.ctr_sugar_of_case context name of
            SOME sugar => #case_thms sugar
          | NONE => [])
     | NONE => [])

  fun is_case_term context term =
    (case head_name term of
       SOME name =>
         name = \<^const_name>\<open>If\<close> orelse
         is_some (Ctr_Sugar.ctr_sugar_of_case context name)
     | NONE => false)

  fun is_expression_type (Type (name, _)) =
        name = \<^type_name>\<open>expression\<close>
    | is_expression_type _ = false

  fun eventually_expression_type (Type (\<^type_name>\<open>fun\<close>, [_, result])) =
        eventually_expression_type result
    | eventually_expression_type result =
        is_expression_type result

  fun is_expression_thunk_type
      (Type (\<^type_name>\<open>fun\<close>, [domain, result])) =
        domain = HOLogic.unitT andalso is_expression_type result
    | is_expression_thunk_type _ = false

  fun is_lazy_cps_call term =
    let
      val (_, arguments) = strip_comb term
    in
      (case rev arguments of
         failure :: success :: _ =>
           is_expression_thunk_type (fastype_of failure) andalso
           (case fastype_of success of
              Type (\<^type_name>\<open>fun\<close>, _) =>
                eventually_expression_type (fastype_of success)
            | _ => false)
       | _ => false)
    end

  fun root_conversion context ct =
    let
      val meta =
        map (Local_Defs.meta_rewrite_rule context)
      val runtime = meta runtime_rules
      val basic = meta basic_rules
      val cases =
        meta (case_rules context (Thm.term_of ct))
    in
      Conv.first_conv
        [Thm.beta_conversion false,
         Conv.rewrs_conv runtime,
         Conv.rewrs_conv basic,
         Conv.rewrs_conv cases]
        ct
    end

  fun normalize_conversion context ct =
    let
      fun normalize context' current =
        ((let
            val root = root_conversion context' current
            val rest = normalize context' (Thm.rhs_of root)
          in
            transitive root rest
          end)
        handle THM _ => descend context' current
          | CTERM _ => descend context' current
          | TERM _ => descend context' current
          | TYPE _ => descend context' current)

      and retry_root context' equation =
        if Thm.is_reflexive equation then equation
        else
          ((let
              val rest = normalize context' (Thm.rhs_of equation)
            in
              if Thm.is_reflexive rest then equation
              else transitive equation rest
            end)
          handle THM _ => equation
            | CTERM _ => equation
            | TERM _ => equation
            | TYPE _ => equation)

      and normalize_case context' current =
        let
          val (head, arguments) = strip_cterm current
          val name = head_name (Thm.term_of current)
          val selected =
            (case name of
               SOME constant =>
                 if constant = \<^const_name>\<open>If\<close>
                 then 0
                 else length arguments - 1
             | NONE => length arguments - 1)
          val equations =
            map_index
              (fn (index, argument) =>
                if index = selected
                then normalize context' argument
                else Thm.reflexive argument)
              arguments
          val equation =
            rebuild_equation (Thm.reflexive head) equations
        in
          retry_root context' equation
        end

      and normalize_lazy_call context' current =
        let
          val (head, arguments) = strip_cterm current
          val prefix_count = length arguments - 2
          val (prefix_arguments, protected_arguments) =
            chop prefix_count arguments
          val prefix = rebuild head prefix_arguments
          val prefix_equation = normalize context' prefix
          val protected_equations =
            map Thm.reflexive protected_arguments
          val equation =
            rebuild_equation prefix_equation protected_equations
        in
          retry_root context' equation
        end

      and descend context' current =
        let
          val term = Thm.term_of current
        in
          if is_case_term context' term then
            normalize_case context' current
          else if is_lazy_cps_call term then
            normalize_lazy_call context' current
          else
            (case term of
               Abs _ =>
                 Conv.abs_conv
                   (fn (_, inner_context) =>
                     normalize inner_context)
                   context' current
             | _ $ _ =>
                 let
                   val (function, argument) =
                     Thm.dest_comb current
                   val equation =
                     Thm.combination
                       (normalize context' function)
                       (normalize context' argument)
                 in
                   retry_root context' equation
                 end
             | _ => Thm.reflexive current)
        end
    in
      normalize context ct
    end

  fun normalize_tac context =
    CONVERSION
      (Conv.params_conv ~1
        (fn inner_context =>
          Conv.concl_conv ~1
            (normalize_conversion inner_context))
        context)
end
\<close>

end
