theory Parser_Impl_Auto_Deref
  imports Parser_Impl_Shallow_Terms
begin

section\<open>Automatic reads of parser-classified places\<close>

ML\<open>
structure URust_Auto_Deref =
struct
  open URust_Shallow_Terms

  datatype read_state =
      Fresh_Read
    | Deferred_Read

  val payload_prefix = "_urust_read_adjustment_payload___"

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

  fun dest_marker
      (Const (\<^const_name>\<open>urust_internal_read_adjustment\<close>, typ) $
          payload $ place) =
        ((case dest_payload payload of
            SOME place_info =>
              SOME
                (place_info, place,
                 Term.range_type (Term.range_type typ))
          | NONE => NONE)
         handle TYPE _ => NONE)
    | dest_marker _ = NONE

  fun expression_value_type
      (Type (name, [_, value_type, _, _, _, _])) =
        if name = expression_type_name then SOME value_type else NONE
    | expression_value_type _ = NONE

  fun is_reference_type (Type (name, _)) =
        name = reference_type_name
    | is_reference_type _ = false

  fun projected_receiver place =
    let
      val stripped = Term_Position.strip_positions place
    in
      (case Term.strip_comb stripped of
         (Const (\<^const_name>\<open>bindlift1\<close>, _),
            [_, receiver]) =>
           SOME receiver
       | (Const (\<^const_name>\<open>funcall2\<close>, _),
            [_, receiver, _]) =>
           SOME receiver
       | _ => NONE)
    end

  fun is_core_reference_expression term =
    (case expression_value_type (fastype_of term) of
       SOME value_type => is_reference_type value_type
     | NONE => false)

  fun is_storage_place Allocated_Place _ = true
    | is_storage_place Projected_Place place =
        (case projected_receiver place of
           SOME receiver => is_core_reference_expression receiver
         | NONE => false)

  fun preserve_reference place_type expected_type =
    (case
        (expression_value_type place_type,
         expression_value_type expected_type) of
       (SOME place_value_type, SOME expected_value_type) =>
         is_reference_type expected_value_type andalso
           Type.could_unify
             (place_value_type, expected_value_type)
     | _ => false)

  fun resolve ctxt terms =
    let
      fun go term =
        (case dest_marker term of
           SOME ((state, origin, pos), place, expected_type) =>
             let
               val place_type = fastype_of place
               val replacement =
                 if not (is_storage_place origin place) orelse
                    preserve_reference place_type expected_type
                 then place
                 else
                   (case state of
                      Fresh_Read =>
                        deferred_read_adjustment origin pos place
                    | Deferred_Read =>
                        automatic_dereference place)
             in replacement end
         | NONE =>
             (case term of
                function $ argument => go function $ go argument
              | Abs (name, typ, body) =>
                  Abs (name, typ, go body)
              | atom => atom))
    in map go terms end

  fun reject_unresolved _ terms =
    let
      fun check term =
        if Term.exists_subterm
            (fn Const (name, _) =>
                  name =
                    \<^const_name>\<open>urust_internal_read_adjustment\<close>
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
