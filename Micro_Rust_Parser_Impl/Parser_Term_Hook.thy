theory Parser_Term_Hook
  imports
    Parser_Impl
    Parser_Impl_Translate
    Micro_Rust_Parsing_Legacy_Frontend.Micro_Rust_Parsing_Legacy_Frontend
begin

section\<open> Experimental term-position parser hook \<close>

text\<open>
The tagged cartouche \<open>\<mu>\<open> SOURCE \<close>\<close> lowers one dedicated-parser expression during parse
translation and returns an unchecked HOL term to the enclosing Isabelle syntax pipeline. The
surrounding term therefore supplies expected types and binders.

The scoped configuration \<open>urust_term_hook_conformance_check\<close> defaults to false. When enabled, the
same source is also parsed through the legacy \<open>\<lbrakk>_\<rbrakk>\<close> frontend without emitting a second
set of PIDE reports. A concealed marker carries both unchecked terms and the source-cartouche range
through ordinary type inference. Stage 50 checks untyped alpha-equivalence and unifies corresponding
types; stage 51 requires typed alpha-equivalence and erases the marker. Clients opt in by importing
this theory; ordinary parser commands do not import it.
\<close>

ML\<open>
val urust_term_hook_conformance_check =
  Attrib.setup_config_bool
    \<^binding>\<open>urust_term_hook_conformance_check\<close> (K false)
\<close>

consts urust_term_hook_conformance_marker ::
  \<open>'term \<Rightarrow> 'term \<Rightarrow> 'position \<Rightarrow> 'term\<close>

ML\<open>
local
  val marker_name =
    \<^const_name>\<open>urust_term_hook_conformance_marker\<close>

  val position_prefix = "_urust_term_hook_position___"

  fun strip_file pos =
    let
      val {line, offset, end_offset, props = {label, id, ...}} =
        Position.dest pos
    in
      Position.make
        {line = line,
         offset = offset,
         end_offset = end_offset,
         props = {label = label, file = "", id = id}}
    end

  fun position_payload pos =
    Free
      (position_prefix ^
        Term_Position.encode_no_syntax [strip_file pos],
       dummyT)

  fun payload_position (Free (name, _)) =
        if String.isPrefix position_prefix name then
          (case
              Term_Position.decode
                (String.extract
                  (name, size position_prefix, NONE)) of
             [{pos, ...}] => SOME pos
           | _ => NONE)
        else NONE
    | payload_position _ = NONE

  fun source_of_cartouche args =
    let
      fun bad () = raise TERM ("urust_term_source", args)
    in
      (case args of
         [(Const (\<^syntax_const>\<open>_constrain\<close>, _) $
             Free (raw, _) $ encoded_pos)] =>
           (case Term_Position.decode_position1 encoded_pos of
              SOME {pos, ...} =>
                let
                  val all_symbols = Symbol_Pos.explode (raw, pos)
                  val cartouche_pos =
                    Position.range_position
                      (Position.range
                        (pos, Position.symbol_explode raw pos))
                  val symbols =
                    all_symbols
                    |> Symbol_Pos.cartouche_content
                  val content_pos = Position.symbol Symbol.open_ pos
                  val range =
                    if null symbols
                    then Position.range (content_pos, content_pos)
                    else Symbol_Pos.range symbols
                  val (text, _) = Symbol_Pos.implode_range range symbols
                in (Input.source true text range, cartouche_pos) end
            | NONE => bad ())
       | _ => bad ())
    end

  fun reembed_constraints ctxt
      (Const (\<^syntax_const>\<open>_type_constraint_\<close>,
          Type (\<^type_name>\<open>fun\<close>, [T, _])) $ term) =
        Syntax.const \<^syntax_const>\<open>_constrain\<close> $
          reembed_constraints ctxt term $
          Syntax_Phases.term_of_typ ctxt T
    | reembed_constraints ctxt (term $ argument) =
        reembed_constraints ctxt term $
          reembed_constraints ctxt argument
    | reembed_constraints ctxt (Abs (name, T, body)) =
        Abs (name, T, reembed_constraints ctxt body)
    | reembed_constraints ctxt (constant as Const (name, T)) =
        if Lexicon.is_const name orelse
            Proof_Context.is_syntax_const ctxt name
        then constant
        else Const (Lexicon.mark_const name, T)
    | reembed_constraints _ atom = atom

  fun plain_message exn =
    XML.content_of (YXML.parse_body (Runtime.exn_message exn))
      handle Fail _ => Runtime.exn_message exn

  fun legacy_term ctxt source cartouche_pos =
    let
      val oracle_ctxt =
        Context_Position.set_visible false ctxt
      val wrapped =
        "\<lbrakk> " ^ Input.string_of source ^ " \<rbrakk>"
    in
      (case Exn.result (Syntax.parse_term oracle_ctxt) wrapped of
         Exn.Res term => term
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else
             error
               ("uRust term conformance: legacy frontend rejected the source: " ^
                 plain_message exn ^
                 Position.here cartouche_pos))
      |> reembed_constraints ctxt
    end

  fun conformance_marker parser_term legacy_term cartouche_pos =
    Syntax.const (Lexicon.mark_const marker_name) $
      parser_term $
      legacy_term $
      position_payload cartouche_pos

  fun urust_term_tr ctxt args =
    let
      val (source, cartouche_pos) = source_of_cartouche args
      (* Inner syntax reports the complete token as an orange inner cartouche before invoking this
         translation. Restore the ordinary command-cartouche baseline first, then let the dedicated
         parser's lexical and semantic reports override it token by token. *)
      val _ =
        Context_Position.report ctxt cartouche_pos Markup.cartouche
      val ast =
        (case URust_Parser.parse_source ctxt source of
           SOME expression => expression
         | NONE =>
             error
               ("urust term: empty expression" ^
                 Position.here (Input.pos_of source)))
      val parser_term =
        URust_Translate.mk_expression ctxt [] ast
        |> reembed_constraints ctxt
    in
      if Config.get ctxt urust_term_hook_conformance_check
      then
        conformance_marker parser_term
          (legacy_term ctxt source cartouche_pos)
          cartouche_pos
      else parser_term
    end

  fun dest_marker
      (Const (name, _) $ parser_term $ legacy_term $ payload) =
        if name = marker_name then
          (case payload_position payload of
             SOME pos => SOME (parser_term, legacy_term, pos)
           | NONE => NONE)
        else NONE
    | dest_marker _ = NONE

  fun has_marker_head term =
    (case Term.head_of term of
       Const (name, _) => name = marker_name
     | _ => false)

  fun marker_error message pos =
    error
      ("uRust term conformance: " ^ message ^
        Position.here pos)

  fun malformed_marker () =
    error "uRust term conformance: malformed internal marker"

  fun unify_types thy (T, U) (tyenv, maxidx) =
    Sign.typ_unify thy (T, U) (tyenv, maxidx)

  fun unify_term_types thy terms env =
    (case terms of
       (Const (name, T), Const (other, U)) =>
         if name = other then unify_types thy (T, U) env
         else raise Match
     | (Free (name, T), Free (other, U)) =>
         if name = other then unify_types thy (T, U) env
         else raise Match
     | (Var (name, T), Var (other, U)) =>
         if name = other then unify_types thy (T, U) env
         else raise Match
     | (Bound index, Bound other) =>
         if index = other then env else raise Match
     | (Abs (_, T, body), Abs (_, U, other_body)) =>
         unify_term_types thy (body, other_body)
           (unify_types thy (T, U) env)
     | (function $ argument, other_function $ other_argument) =>
         unify_term_types thy (argument, other_argument)
           (unify_term_types thy (function, other_function) env)
     | _ => raise Match)

  fun collect_marker_types thy term env =
    (case dest_marker term of
       SOME (parser_term, legacy_term, pos) =>
         if not (Term.aconv_untyped (parser_term, legacy_term)) then
           marker_error
             "dedicated and legacy frontends produced different untyped terms"
             pos
         else
           let
             val env' =
               (unify_term_types thy (parser_term, legacy_term) env
                 handle Match =>
                   marker_error
                     "internal structural comparison failed"
                     pos
                      | Type.TUNIFY =>
                   marker_error
                     "dedicated and legacy frontend types do not agree"
                     pos)
           in
             collect_marker_types thy legacy_term
               (collect_marker_types thy parser_term env')
           end
     | NONE =>
         if has_marker_head term then malformed_marker ()
         else
           (case term of
              function $ argument =>
                collect_marker_types thy argument
                  (collect_marker_types thy function env)
            | Abs (_, _, body) =>
                collect_marker_types thy body env
            | _ => env))

  fun project_markers term =
    (case dest_marker term of
       SOME (parser_term, _, _) =>
         project_markers parser_term
     | NONE =>
         if has_marker_head term then malformed_marker ()
         else
           (case term of
              function $ argument =>
                project_markers function $
                  project_markers argument
            | Abs (name, T, body) =>
                Abs (name, T, project_markers body)
            | _ => term))

  fun collect_reflexive_types thy term env =
    let
      val env' =
        (case term of
           Const (\<^const_name>\<open>HOL.eq\<close>, _) $ left $ right =>
             let
               val projected_left = project_markers left
               val projected_right = project_markers right
             in
               if Term.aconv_untyped
                    (projected_left, projected_right)
               then
                 (unify_term_types thy
                    (projected_left, projected_right) env
                   handle Match => env
                        | Type.TUNIFY => env)
               else env
             end
         | _ => env)
    in
      (case term of
         function $ argument =>
           collect_reflexive_types thy argument
             (collect_reflexive_types thy function env')
       | Abs (_, _, body) =>
           collect_reflexive_types thy body env'
       | _ => env')
    end

  fun share_conformance_types ctxt terms =
    let
      val thy = Proof_Context.theory_of ctxt
      val maxidx = fold Term.maxidx_term terms ~1
      val marker_env =
        fold (collect_marker_types thy) terms
          (Vartab.empty, maxidx)
      val (tyenv, _) =
        fold (collect_reflexive_types thy) terms marker_env
    in
      if Vartab.is_empty tyenv then terms
      else map (Envir.subst_term_types tyenv) terms
    end

  fun erase_markers term =
    (case dest_marker term of
       SOME (parser_term, legacy_term, pos) =>
         let
           val parser_term' = erase_markers parser_term
           val legacy_term' = erase_markers legacy_term
         in
           if Term.aconv (parser_term', legacy_term')
           then parser_term'
           else
             marker_error
               "dedicated and legacy frontends produced different typed terms"
               pos
         end
     | NONE =>
         if has_marker_head term then malformed_marker ()
         else
           (case term of
              function $ argument =>
                erase_markers function $
                  erase_markers argument
            | Abs (name, T, body) =>
                Abs (name, T, erase_markers body)
            | _ => term))
in
  val urust_term_translation = urust_term_tr

  val _ =
    Context.>>
      (Syntax_Phases.term_check 50
        "urust_term_hook_conformance_types"
        share_conformance_types #>
       Syntax_Phases.term_check 51
        "urust_term_hook_conformance"
        (K (map erase_markers)))
end
\<close>

syntax
  "_urust_term_hook" :: "cartouche_position \<Rightarrow> logic" ("\<mu>_")

parse_translation \<open>
  [(\<^syntax_const>\<open>_urust_term_hook\<close>,
    urust_term_translation)]
\<close>

hide_const (open) urust_term_hook_conformance_marker

end
