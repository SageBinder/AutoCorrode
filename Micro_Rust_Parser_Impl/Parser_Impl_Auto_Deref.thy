theory Parser_Impl_Auto_Deref
  imports Parser_Impl_Shallow_Terms
begin

section\<open>Automatic reads of parser-classified places\<close>

ML\<open>
signature URUST_AUTO_DEREF =
sig
  type lowered_expression

  val plain: term -> lowered_expression
  val eligible:
    URust_AST.ur_expr -> term -> lowered_expression
  val transparent:
    URust_AST.ur_expr ->
      lowered_expression -> lowered_expression
  val project_field:
    URust_AST.ur_expr ->
      lowered_expression -> term -> lowered_expression
  val project_index:
    URust_AST.ur_expr ->
      lowered_expression -> term -> lowered_expression
  val raw_term: lowered_expression -> term
  val value_term:
    URust_AST.ur_expr -> lowered_expression -> term
end
\<close>

text\<open>
This module is the only owner of automatic-read eligibility, private projection recipes, marker
metadata, and type-directed resolution. Paths are conditional candidates, fields and indices append
policy-checked projection segments, and groups and blocks are transparent. Every other result is
plain. Translation may consume a lowered result only as its raw place form or as its value form.
\<close>

ML\<open>
structure URust_Auto_Deref :> URUST_AUTO_DEREF =
struct
  open URust_AST
  structure T = URust_Shallow_Terms

  datatype read_origin =
      Allocated_Place
    | Projected_Place
    | Ordinary_Projection

  datatype read_state =
      Fresh_Read
    | Deferred_Read

  datatype result_policy =
      Conditional_Path_Candidate
    | Projected_Candidate
    | Transparent_Carrier
    | Never_Candidate

  datatype projection_segment =
      Field_Segment of Position.T list * term
    | Index_Segment of Position.T list * term

  datatype lowered_expression =
      Plain of term
    | Eligible of read_origin * term * projection_segment list

  fun result_policy expression =
    (case expression of
       UE_Path _ => Conditional_Path_Candidate
     | UE_Field _ => Projected_Candidate
     | UE_Index _ => Projected_Candidate
     | UE_Group _ => Transparent_Carrier
     | UE_Block _ => Transparent_Carrier
     | _ => Never_Candidate)

  val payload_prefix = "_urust_read_adjustment_payload___"
  val projection_payload_prefix =
    "_urust_place_projection_payload___"
  val payload_sep = String.str (Char.chr 0)

  fun read_state_tag Fresh_Read = "fresh"
    | read_state_tag Deferred_Read = "deferred"

  fun read_origin_tag Allocated_Place = "allocated"
    | read_origin_tag Projected_Place = "projected"
    | read_origin_tag Ordinary_Projection = "ordinary"

  fun strip_file pos =
    let
      val {line, offset, end_offset, props = {label, id, ...}} =
        Position.dest pos
    in
      Position.make
        {line = line, offset = offset, end_offset = end_offset,
         props = {label = label, file = "", id = id}}
    end

  fun read_payload state origin pos =
    Free
      (payload_prefix ^ read_state_tag state ^ payload_sep ^
        read_origin_tag origin ^ payload_sep ^
        Term_Position.encode_no_syntax [strip_file pos],
       dummyT)

  fun projection_payload positions =
    Free
      (projection_payload_prefix ^
        Term_Position.encode_no_syntax (map strip_file positions),
       dummyT)

  fun make_read_adjustment state origin pos place =
    Const (\<^const_name>\<open>urust_internal_read_adjustment\<close>, dummyT) $
      read_payload state origin pos $ place

  fun make_projection (Field_Segment (positions, field)) receiver =
        Const
          (\<^const_name>\<open>urust_internal_field_projection\<close>,
           dummyT) $
          projection_payload positions $ receiver $ field
    | make_projection (Index_Segment (positions, index)) receiver =
        Const
          (\<^const_name>\<open>urust_internal_index_projection\<close>,
           dummyT) $
          projection_payload positions $ receiver $ index

  fun materialize_projection segment receiver =
    (case segment of
       Field_Segment (positions, field) =>
         Micro_Rust_Semantic_Navigation.with_source positions
           (fn () => T.focus_field field receiver)
     | Index_Segment (positions, index) =>
         Micro_Rust_Semantic_Navigation.with_source positions
           (fn () => T.index receiver index))

  fun make_value_recipe base segments =
    fold make_projection segments base

  fun make_raw_recipe base [] = base
    | make_raw_recipe base [segment] =
        materialize_projection segment base
    | make_raw_recipe base segments =
        fold make_projection segments base

  fun plain term = Plain term

  fun eligible expression term =
    (case result_policy expression of
       Conditional_Path_Candidate =>
         Eligible (Allocated_Place, term, [])
     | Projected_Candidate =>
         error
           "urust read adjustment: projection requires a projection operation"
     | Transparent_Carrier =>
         error
           "urust read adjustment: transparent expression cannot create a candidate"
     | Never_Candidate =>
         error
           "urust read adjustment: ineligible expression cannot create a candidate")

  fun transparent expression lowered =
    (case result_policy expression of
       Transparent_Carrier => lowered
     | _ =>
         error
           "urust read adjustment: non-transparent expression cannot carry a candidate")

  fun append_projection expression segment lowered =
    (case result_policy expression of
       Projected_Candidate =>
         (case lowered of
            Plain base =>
              Eligible (Projected_Place, base, [segment])
          | Eligible (_, base, segments) =>
              Eligible
                (Projected_Place, base, segments @ [segment]))
     | _ =>
         error
           "urust read adjustment: projection operation requires a field or index")

  fun project_field expression lowered field =
    (case expression of
       UE_Field (_, _, layout) =>
         append_projection expression
           (Field_Segment
             (source_token_positions layout (Delimiter_Token "."),
              field))
           lowered
     | _ =>
         error
           "urust read adjustment: field projection requires a field expression")

  fun project_index expression lowered index =
    (case expression of
       UE_Index (_, _, layout) =>
         append_projection expression
           (Index_Segment
             (source_token_positions_for layout
               [Delimiter_Token "[", Delimiter_Token "]"],
              index))
           lowered
     | _ =>
         error
           "urust read adjustment: index projection requires an index expression")

  fun raw_term (Plain term) = term
    | raw_term (Eligible (_, base, segments)) =
        make_raw_recipe base segments

  fun value_term expression (Plain term) = term
    | value_term expression (Eligible (origin, base, segments)) =
        make_read_adjustment Fresh_Read origin
          (expression_position expression)
          (make_value_recipe base segments)

  val expression_type_name =
    (case \<^typ>\<open>('s, 'v, 'c, 'abort, 'i, 'o) expression\<close> of
       Type (name, _) => name
     | _ =>
         error
           "urust read adjustment: expression is not a type constructor")

  val reference_type_name =
    (case \<^typ>\<open>('a, 'b, 'v) Global_Store.ref\<close> of
       Type (name, _) => name
     | _ =>
         error
           "urust read adjustment: reference is not a type constructor")

  fun decode_origin "allocated" = Allocated_Place
    | decode_origin "projected" = Projected_Place
    | decode_origin "ordinary" = Ordinary_Projection
    | decode_origin tag =
        error
          ("urust read adjustment: malformed place origin " ^ quote tag)

  fun decode_state "fresh" = Fresh_Read
    | decode_state "deferred" = Deferred_Read
    | decode_state tag =
        error
          ("urust read adjustment: malformed read state " ^ quote tag)

  fun decode_payload text =
    (case String.fields (fn character => character = Char.chr 0) text of
       [state, origin, encoded_position] =>
         let
           val positions =
             map #pos (Term_Position.decode encoded_position)
         in
           (decode_state state, decode_origin origin,
            (case positions of
               [pos] => pos
             | _ =>
                 error
                   "urust read adjustment: malformed source position"))
         end
     | _ => error "urust read adjustment: malformed payload")

  fun dest_payload (Free (name, _)) =
        if String.isPrefix payload_prefix name
        then
          SOME
            (decode_payload
              (String.extract (name, size payload_prefix, NONE)))
        else NONE
    | dest_payload _ = NONE

  fun dest_projection_payload (Free (name, _)) =
        if String.isPrefix projection_payload_prefix name
        then
          SOME
            (map #pos
              (Term_Position.decode
                (String.extract
                  (name, size projection_payload_prefix, NONE))))
        else NONE
    | dest_projection_payload _ = NONE

  fun dest_read_marker
      (Const (\<^const_name>\<open>urust_internal_read_adjustment\<close>, typ) $
          payload $ place) =
        ((case dest_payload payload of
            SOME place_info =>
              SOME
                (place_info, place,
                 Term.range_type (Term.range_type typ))
          | NONE => NONE)
         handle TYPE _ => NONE)
    | dest_read_marker _ = NONE

  fun dest_projection_marker
      (Const (\<^const_name>\<open>urust_internal_field_projection\<close>, typ) $
          payload $ receiver $ field) =
        ((case dest_projection_payload payload of
            SOME positions =>
              SOME
                (Field_Segment (positions, field), receiver)
          | NONE => NONE)
         handle TYPE _ => NONE)
    | dest_projection_marker
        (Const (\<^const_name>\<open>urust_internal_index_projection\<close>, typ) $
          payload $ receiver $ index) =
        ((case dest_projection_payload payload of
            SOME positions =>
              SOME
                (Index_Segment (positions, index), receiver)
          | NONE => NONE)
         handle TYPE _ => NONE)
    | dest_projection_marker _ = NONE

  fun expression_value_type
      (Type (name, [_, value_type, _, _, _, _])) =
        if name = expression_type_name then SOME value_type else NONE
    | expression_value_type _ = NONE

  fun is_reference_type (Type (name, _)) =
        name = reference_type_name
    | is_reference_type _ = false

  fun reference_value_type (Type (name, [_, _, value_type])) =
        if name = reference_type_name then SOME value_type else NONE
    | reference_value_type _ = NONE

  datatype receiver_kind =
      Core_Reference of typ
    | Ordinary_Value
    | Unknown_Receiver

  fun receiver_kind receiver =
    (case expression_value_type (fastype_of receiver) of
       SOME value_type =>
         (case reference_value_type value_type of
            SOME stored_value_type =>
              Core_Reference stored_value_type
          | NONE =>
              if value_type = dummyT then Unknown_Receiver
              else
                (case value_type of
                   TVar _ => Unknown_Receiver
                 | _ => Ordinary_Value))
     | NONE => Unknown_Receiver)
    handle TYPE _ => Unknown_Receiver

  fun is_storage_place Allocated_Place = true
    | is_storage_place Projected_Place = true
    | is_storage_place Ordinary_Projection = false

  fun preserve_reference place_type expected_type =
    (case
        (expression_value_type place_type,
         expression_value_type expected_type) of
       (SOME place_value_type, SOME expected_value_type) =>
         is_reference_type expected_value_type andalso
           Type.could_unify
             (place_value_type, expected_value_type)
     | _ => false)

  datatype projection_progress =
      No_Projection_Progress
    | Projection_Progress of term * read_origin option

  fun advance_projection term =
    (case dest_projection_marker term of
       SOME (segment, receiver) =>
         (case advance_projection receiver of
            Projection_Progress (receiver', _) =>
              Projection_Progress
                (make_projection segment receiver', NONE)
          | No_Projection_Progress =>
              (case receiver_kind receiver of
                 Unknown_Receiver => No_Projection_Progress
               | Core_Reference stored_value_type =>
                   if is_reference_type stored_value_type
                   then
                     Projection_Progress
                       (make_projection segment
                         (T.automatic_dereference receiver),
                        NONE)
                   else
                     Projection_Progress
                       (materialize_projection segment receiver,
                        SOME Projected_Place)
               | Ordinary_Value =>
                   Projection_Progress
                     (materialize_projection segment receiver,
                      SOME Ordinary_Projection)))
     | NONE => No_Projection_Progress)

  fun function_call_arity name =
    let
      val base = Long_Name.base_name name
      val prefix = "funcall"
    in
      if String.isPrefix prefix base
      then
        (case Int.fromString
            (String.extract (base, size prefix, NONE)) of
           SOME arity =>
             if 0 <= arity andalso arity <= 14
             then SOME arity
             else NONE
         | NONE => NONE)
      else NONE
    end

  fun rebuild_function_call name function arguments =
    Term.list_comb
      (Const (name, dummyT),
       Term.map_types (K dummyT) function :: arguments)

  fun advance_argument_projection argument =
    (case dest_read_marker argument of
       SOME ((state, origin, pos), place, _) =>
         (case advance_projection place of
            Projection_Progress (place', resolved_origin) =>
              SOME
                (make_read_adjustment state
                  (the_default origin resolved_origin) pos place')
          | No_Projection_Progress => NONE)
     | NONE => NONE)

  fun advance_argument_projections arguments =
    let
      fun advance [] = ([], false)
        | advance (argument :: rest) =
            let
              val (rest', changed_rest) = advance rest
            in
              (case advance_argument_projection argument of
                 SOME argument' =>
                   (argument' :: rest', true)
               | NONE =>
                   (argument :: rest', changed_rest))
            end
    in advance arguments end

  fun can_unify_types (left, right) =
    Type.could_unify (left, right) orelse
      Type.could_unify (right, left)

  fun read_marker_accepts parameter_type argument =
    (case dest_read_marker argument of
       SOME ((_, origin, _), place, _) =>
         (case expression_value_type (fastype_of place) of
            SOME place_value_type =>
              can_unify_types (place_value_type, parameter_type) orelse
                (is_storage_place origin andalso
                  (case reference_value_type place_value_type of
                     SOME stored_value_type =>
                       can_unify_types
                         (stored_value_type, parameter_type)
                   | NONE => false))
          | NONE => true)
     | NONE => true)
    handle TYPE _ => true

  fun candidate_accepts arguments candidate =
    let
      val parameters =
        binder_types
          (Micro_Rust_Dispatch.notation_candidate_type candidate)

      fun accepts ([], []) = true
        | accepts
            (argument :: remaining_arguments,
             parameter :: remaining_parameters) =
            read_marker_accepts parameter argument andalso
              accepts
                (remaining_arguments, remaining_parameters)
        | accepts _ = false
    in accepts (arguments, parameters) end

  datatype dispatch_progress =
      Not_A_Dispatch_Call
    | Dispatch_Call of term

  fun preserve_reference_arguments function arguments =
    let
      val parameters = binder_types (fastype_of function)

      fun preserve ([], []) = ([], false)
        | preserve
            (argument :: remaining_arguments,
             parameter :: remaining_parameters) =
            let
              val (remaining', changed_rest) =
                preserve
                  (remaining_arguments, remaining_parameters)
            in
              (case dest_read_marker argument of
                 SOME ((_, origin, _), place, _) =>
                   if is_storage_place origin andalso
                      is_reference_type parameter
                   then (place :: remaining', true)
                   else
                     (argument :: remaining', changed_rest)
               | NONE =>
                   (argument :: remaining', changed_rest))
            end
        | preserve _ = (arguments, false)
    in preserve (arguments, parameters) end
    handle TYPE _ => (arguments, false)
         | TERM _ => (arguments, false)

  fun resolve_selected_reference_call term =
    (case Term.strip_comb term of
       (Const (call_name, _), function :: arguments) =>
         (case function_call_arity call_name of
            SOME arity =>
              if arity <> length arguments orelse
                 is_some (Micro_Rust_Dispatch.dest_marker function)
              then Not_A_Dispatch_Call
              else
                let
                  val (arguments', changed) =
                    preserve_reference_arguments
                      function arguments
                in
                  if changed
                  then
                    Dispatch_Call
                      (rebuild_function_call
                        call_name function arguments')
                  else Not_A_Dispatch_Call
                end
          | NONE => Not_A_Dispatch_Call)
     | _ => Not_A_Dispatch_Call)

  fun resolve_dispatch_call ctxt term =
    (case Term.strip_comb term of
       (Const (call_name, _), function :: arguments) =>
         (case
             (function_call_arity call_name,
              Micro_Rust_Dispatch.dest_marker function) of
            (SOME arity,
             SOME
               ((kind, name, positions), _, occurrence_type)) =>
              if arity <> length arguments orelse
                 kind <> Micro_Rust_Names.NFunction
              then Not_A_Dispatch_Call
              else
                let
                  val (arguments', advanced) =
                    advance_argument_projections arguments
                in
                  if advanced
                  then
                    Dispatch_Call
                      (rebuild_function_call
                        call_name function arguments')
                  else
                    let
                      val candidates =
                        Micro_Rust_Dispatch.notation_candidates
                          ctxt kind name occurrence_type
                      val compatible =
                        filter (candidate_accepts arguments)
                          candidates
                      fun select candidate =
                        Micro_Rust_Dispatch.select_notation_candidate
                          ctxt kind name positions candidate
                    in
                      (case compatible of
                         [candidate] =>
                           Dispatch_Call
                             (rebuild_function_call call_name
                               (select candidate) arguments)
                       | [] =>
                           Micro_Rust_Dispatch.no_match_error ctxt
                             kind name (#terminal_pos positions)
                             occurrence_type
                       | _ => Dispatch_Call term)
                    end
                end
          | _ => Not_A_Dispatch_Call)
     | _ => Not_A_Dispatch_Call)

  fun resolve ctxt terms =
    let
      fun go term =
        (case resolve_selected_reference_call term of
           Dispatch_Call replacement => replacement
         | Not_A_Dispatch_Call =>
             (case resolve_dispatch_call ctxt term of
                Dispatch_Call replacement => replacement
              | Not_A_Dispatch_Call =>
                  (case dest_read_marker term of
                     SOME
                       ((state, origin, pos), place,
                        expected_type) =>
                       (case advance_projection place of
                          Projection_Progress
                            (place',
                             SOME Ordinary_Projection) =>
                            place'
                        | Projection_Progress
                            (place', resolved_origin) =>
                            make_read_adjustment state
                              (the_default origin
                                resolved_origin)
                              pos place'
                        | No_Projection_Progress =>
                            let
                              val place_type =
                                fastype_of place
                            in
                              if not
                                  (is_storage_place origin) orelse
                                 preserve_reference
                                   place_type expected_type
                              then place
                              else
                                (case state of
                                   Fresh_Read =>
                                     make_read_adjustment
                                       Deferred_Read origin
                                       pos place
                                 | Deferred_Read =>
                                     T.automatic_dereference
                                       place)
                            end)
                   | NONE =>
                       (case advance_projection term of
                          Projection_Progress (term', _) =>
                            term'
                        | No_Projection_Progress =>
                            (case term of
                               function $ argument =>
                                 go function $ go argument
                             | Abs (name, typ, body) =>
                                 Abs (name, typ, go body)
                             | atom => atom)))))
    in map go terms end

  fun reject_unresolved _ terms =
    let
      fun is_internal_marker name =
        member (op =)
          [\<^const_name>\<open>urust_internal_read_adjustment\<close>,
           \<^const_name>\<open>urust_internal_field_projection\<close>,
           \<^const_name>\<open>urust_internal_index_projection\<close>]
          name

      fun check term =
        if Term.exists_subterm
            (fn Const (name, _) => is_internal_marker name
              | _ => false)
            term
        then
          error
            "urust read adjustment: internal marker survived type checking"
        else ()
    in List.app check terms; terms end

  val _ =
    Context.>>
      (Syntax_Phases.term_check 0 "urust_read_adjustment" resolve
       #> Syntax_Phases.term_check 1
            "urust_read_adjustment_unresolved" reject_unresolved)
end
\<close>

end
