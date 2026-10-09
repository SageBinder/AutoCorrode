theory Parser_Pointer_Type_Tests
  imports Parser_Type_Alias_Tests
begin

declare [[urust_pp_test = true]]
declare [[urust_pretty = true]]
declare [[urust_verbosity = 2]]

ML\<open>
structure Datatype_Pointer_Probe =
struct
  fun require message condition =
    if condition then () else error ("datatype pointer probe: " ^ message)
end
\<close>

urust_type_alias \<open> type DatatypeWidth = u16; \<close>
urust_type_alias \<open> type DatatypePtr<T> = *const T; \<close>
urust_type_alias \<open> type DatatypeMut<T> = *mut T; \<close>
urust_type_alias \<open> type DatatypePtrChain<T> = DatatypePtr<T>; \<close>

urust_datatype \<open>
  struct PointerPacket {
    pointer: DatatypePtr<u8>,
    count: DatatypeWidth,
  }
\<close>

urust_datatype \<open>
  struct PointerFields {
    left: DatatypePtrChain<u8>,
    right: DatatypeMut<u16>,
    nested: *const DatatypePtr<u32>,
  }
\<close>

urust_datatype \<open>
  struct PointerTuple(DatatypePtr<u8>, *mut u16, PointerPacket);
\<close>

urust_datatype \<open>
  enum PointerChoice {
    Empty,
    Packet(PointerPacket),
    Pair { left: DatatypePtr<u16>, right: PointerTuple },
  }
\<close>

urust_datatype \<open>
  struct PointerOuter {
    packet: PointerPacket,
    tuple: PointerTuple,
    choice: PointerChoice,
  }
\<close>

urust_type_alias \<open> type DatatypePacketAlias = PointerPacket; \<close>

urust_datatype \<open>
  struct PointerWrapped(DatatypePacketAlias, *const u8);
\<close>

urust_datatype \<open> struct PlainPacket { count: u16, ready: bool } \<close>
urust_datatype \<open> struct PlainTuple(u32, bool); \<close>
urust_datatype \<open> enum PlainChoice { EmptyPlain, ValuePlain(u32) } \<close>

lemma pointer_packet_selector:
  \<open> pointer_packet_pointer (make_pointer_packet p n) = p \<close>
  by simp

lemma pointer_packet_lens:
  \<open>
    lens_view pointer_packet_pointer_packet_pointer_lens
      (make_pointer_packet p n) = p
  \<close>
  by (simp add: pointer_packet_pointer_packet_pointer_lens_view_update_modify)

lemma pointer_packet_update:
  \<open>
    update_pointer_packet_pointer h (make_pointer_packet p n) =
      make_pointer_packet (h p) n
  \<close>
  by (simp add: datatype_record_update)

urust_fn \<open>
  fn BuildPointerPacket(pointer: DatatypePtr<u8>, count: DatatypeWidth) -> PointerPacket {
    PointerPacket { pointer: pointer, count: count }
  }
\<close>

urust_fn \<open>
  fn ReadPointerPacket(packet: DatatypePacketAlias) -> DatatypePtr<u8> {
    packet.pointer
  }
\<close>

urust_fn \<open>
  fn BuildPointerTuple(pointer: *const u8, mutable: *mut u16, packet: PointerPacket) -> PointerTuple {
    PointerTuple(pointer, mutable, packet)
  }
\<close>

urust_fn \<open>
  fn BuildPointerChoice(packet: PointerPacket) -> PointerChoice {
    PointerChoice::Packet(packet)
  }
\<close>

urust_fn \<open>
  fn MatchPointerChoice(choice: PointerChoice) -> *const u8 {
    match choice {
      PointerChoice::Empty => \<llangle>undefined\<rrangle>,
      PointerChoice::Packet(packet) => packet.pointer,
      PointerChoice::Pair { left: _, right: _ } => \<llangle>undefined\<rrangle>,
    }
  }
\<close>

ML_val\<open>
  local
    open Datatype_Pointer_Probe
    val ctxt = \<^context>
    fun mapping name = the (URust_Type_Mappings.lookup ctxt name)
    fun sugar name = the (Ctr_Sugar.ctr_sugar_of ctxt name)
    fun require_pointer name hol_name =
      let
        val entry = mapping name
        val native = sugar hol_name
        val (_, parameters) = dest_Type (#T native)
        val _ = require (name ^ " lost its address/global parameters")
          (length parameters = 2 andalso hd parameters <> hd (tl parameters) andalso
           forall Term.is_TVar parameters)
        val _ = require (name ^ " exposed extra Rust generic arguments")
          (URust_Type_Mappings.entry_arities entry = [0] andalso
           null (URust_Type_Mappings.entry_parameter_sorts entry))
        val _ = require (name ^ " registry lost implicit backend parameters")
          (length (URust_Type_Mappings.entry_backend_parameter_sorts entry) = 2)
        val _ = require (name ^ " fields use different backend parameters")
          (forall (fn constructor =>
             eq_set (op =)
               (Term.add_tvars constructor [], Term.add_tvarsT (#T native) []))
            (#ctrs native))
      in () end
    val _ = List.app (fn (name, hol_name) => require_pointer name hol_name)
      [("PointerPacket", \<^type_name>\<open>pointer_packet\<close>),
       ("PointerFields", \<^type_name>\<open>pointer_fields\<close>),
       ("PointerTuple", \<^type_name>\<open>pointer_tuple\<close>),
       ("PointerChoice", \<^type_name>\<open>pointer_choice\<close>),
       ("PointerOuter", \<^type_name>\<open>pointer_outer\<close>),
       ("PointerWrapped", \<^type_name>\<open>pointer_wrapped\<close>)]
    val SOME packet = URust_Item_Scope.lookup_constructor ctxt "PointerPacket"
    val _ = require "stored constructor lost its native scheme"
      (fastype_of (URust_Item_Scope.constructor_scheme packet) =
        fastype_of (hd (#ctrs (sugar \<^type_name>\<open>pointer_packet\<close>))))
    val _ = require "expression constructor no longer infers fresh type instances"
      (URust_Item_Scope.constructor_term packet =
        Const (\<^const_name>\<open>make_pointer_packet\<close>, dummyT))
    val pointer_field = hd (URust_Item_Scope.constructor_field_entries packet)
    val _ = require "stored selector lost its native scheme"
      (fastype_of (URust_Item_Scope.field_scheme pointer_field) =
        fastype_of (hd (hd (#selss (sugar \<^type_name>\<open>pointer_packet\<close>)))))
    val _ = require "expression selector no longer infers fresh type instances"
      (URust_Item_Scope.field_selector pointer_field =
        Const (\<^const_name>\<open>pointer_packet_pointer\<close>, dummyT))
    val descriptor =
      prepare_record_descriptor "pointer_packet" (Named_Target.theory_init \<^theory>)
    val _ = require "lens descriptor uses a different record scheme"
      (#record_type descriptor = #T (sugar \<^type_name>\<open>pointer_packet\<close>))
    val _ = require "pointer selector scheme diverged from its record parameter pair"
      (eq_set (op =)
        (Term.add_tvarsT (#field_type (hd (#fields descriptor))) [],
         Term.add_tvarsT (#record_type descriptor) []))
    val _ = List.app
      (fn name =>
        require (name ^ " gained implicit parameters")
          (null (URust_Type_Mappings.entry_backend_parameter_sorts (mapping name))))
      ["PlainPacket", "PlainTuple", "PlainChoice"]
    val _ = require "nonpointer record became polymorphic"
      (null (snd (dest_Type (#T (sugar \<^type_name>\<open>plain_packet\<close>)))))
    fun function_type name =
      Consts.the_constraint (Proof_Context.consts_of ctxt) name
    val build_type = function_type \<^const_name>\<open>build_pointer_packet\<close>
    val read_type = function_type \<^const_name>\<open>read_pointer_packet\<close>
    val _ = require "constructor function did not generalize pointer backends"
      (length (Term.add_tvarsT (hd (binder_types build_type)) []) = 2)
    val _ = require "selector function did not generalize pointer backends"
      (length (Term.add_tvarsT (hd (binder_types read_type)) []) = 2)
    val lthy = Named_Target.theory_init \<^theory>
    val rejected =
      Exn.result (fn () =>
        URust_Datatype.define
          {source = Input.string "struct PointerBad { pointer: *const u8, unrelated: \<tau>\<open>'unrelated\<close> }",
           explicit_binding = NONE, interactive = false, verbosity = 0,
           pp_test = true, pretty = false, register_notation = true, renames = []}
          lthy) ()
    val _ =
      (case rejected of
         Exn.Res _ => error "unrelated HOL field variable was accepted"
       | Exn.Exn exn =>
           if Exn.is_interrupt exn then Exn.reraise exn
           else require "wrong unrelated-variable diagnostic"
             (String.isSubstring "type variables are not supported"
               (Runtime.exn_message exn)))
    val _ = require "failed datatype installed its mapping"
      (is_none (URust_Type_Mappings.lookup lthy "PointerBad"))
  in val _ = writeln "datatype pointer probes passed" end
\<close>

section\<open> Signature constraints and independent instantiation \<close>

urust_fn \<open>
  fn PointerBodyConstraint(value: DatatypePtr<u8>) -> DatatypePtr<u8> {
    \<llangle>value :: (nat, bool, 8 word) Global_Store.ref\<rrangle>
  }
\<close>

urust_fn \<open>
  fn PointerResultConstraint(value: DatatypePtr<u8>)
      -> \<tau>\<open> (int, nat, 8 word) Global_Store.ref \<close> {
    value
  }
\<close>

urust_expr pointer_independent_calls \<open>
  (
    CommandPointerIdentity(\<llangle>undefined :: (nat, bool, 8 word) Global_Store.ref\<rrangle>),
    CommandPointerIdentity(\<llangle>undefined :: (int, nat, 8 word) Global_Store.ref\<rrangle>)
  )
\<close>

ML_val\<open>
local
  val ctxt = \<^context>
  fun require message condition =
    if condition then () else error ("pointer signature audit: " ^ message)
  fun argument_type name =
    Consts.the_constraint (Proof_Context.consts_of ctxt) name
    |> binder_types |> hd
  val _ = require "body did not constrain the pointer backend"
    (argument_type \<^const_name>\<open>pointer_body_constraint\<close> =
      \<^typ>\<open>(nat, bool, 8 word) Global_Store.ref\<close>)
  val _ = require "explicit result did not constrain the pointer backend"
    (argument_type \<^const_name>\<open>pointer_result_constraint\<close> =
      \<^typ>\<open>(int, nat, 8 word) Global_Store.ref\<close>)
  val independent_type =
    Consts.the_constraint (Proof_Context.consts_of ctxt)
      \<^const_name>\<open>pointer_independent_calls\<close>
  val _ = require "independent calls lost one concrete backend"
    (Term.exists_subtype
       (fn T => T = \<^typ>\<open>(nat, bool, 8 word) Global_Store.ref\<close>)
       independent_type andalso
     Term.exists_subtype
       (fn T => T = \<^typ>\<open>(int, nat, 8 word) Global_Store.ref\<close>)
       independent_type)
in
  val _ = ()
end
\<close>

locale pointer_alias_context =
  fixes pointer :: "('address, 'global, 8 word) Global_Store.ref"
begin

urust_type_alias \<open> type LocalePointer<T> = *const T; \<close>
urust_datatype \<open> struct LocalePointerPacket { pointer: LocalePointer<u8> } \<close>

urust_fn \<open>
  fn LocalePointerIdentity(value: LocalePointer<u8>) -> LocalePointer<u8> {
    if true { value } else { pointer }
  }
\<close>

ML_val\<open>
local
  val typ =
    fastype_of (Syntax.read_term \<^context> "locale_pointer_identity")
  val pointer_type = fastype_of (Syntax.read_term \<^context> "pointer")
in
  val _ =
    if member (op =) (binder_types typ) pointer_type then ()
    else error "locale signature lost its rigid pointer backend"
end
\<close>

end

context pointer_alias_context
begin

urust_fn \<open>
  fn ReopenLocalePointer(packet: LocalePointerPacket) -> LocalePointer<u8> {
    packet.pointer
  }
\<close>

ML_val\<open>
  val _ =
    if is_some (URust_Item_Scope.lookup_constructor \<^context> "LocalePointerPacket") andalso
       is_some (URust_Type_Mappings.lookup \<^context> "LocalePointer")
    then ()
    else error "locale reopening lost pointer type schemes"
\<close>

end

locale pointer_alias_left = pointer_alias_context pointer for pointer
locale pointer_alias_right = pointer_alias_context pointer for pointer
locale pointer_alias_join =
  pointer_alias_left pointer + pointer_alias_right pointer for pointer
begin

urust_fn \<open>
  fn MergedLocalePointer(packet: LocalePointerPacket) -> LocalePointer<u8> {
    packet.pointer
  }
\<close>

ML_val\<open>
local
  val ctxt = \<^context>
  val entry = the (URust_Type_Mappings.lookup ctxt "LocalePointerPacket")
  val constructor = the (URust_Item_Scope.lookup_constructor ctxt "LocalePointerPacket")
in
  val _ =
    if length (URust_Type_Mappings.entry_backend_parameter_sorts entry) = 2 andalso
       length (Term.add_tvars (URust_Item_Scope.constructor_scheme constructor) []) = 2
    then ()
    else error "merged locale lost its native pointer constructor scheme"
end
\<close>

end

ML_val\<open>
  val _ =
    if is_none (URust_Type_Mappings.lookup \<^context> "LocalePointer") andalso
       is_none (URust_Type_Mappings.lookup \<^context> "LocalePointerPacket")
    then ()
    else error "locale pointer registrations escaped their target"
\<close>

end
