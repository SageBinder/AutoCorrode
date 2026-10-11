theory Parser_Use_Fixtures
  imports Parser_Test_Utils
begin

text\<open>
Declaration-only items shared by the Rust import tests and their imported-theory fixtures. Every
name is synthetic. The items cover each namespace and shape that an import can target: generated
enums, variants and structs, a generated function, exact literal and call notations, an overloaded
literal, Rust type mappings and a type alias.
\<close>

declare [[urust_verbosity = 0]]

urust_datatype \<open> enum UseChoice { Empty, Value(u32), Named { sample: u32 } } \<close>
urust_datatype \<open> enum UseOtherChoice { Value(bool) } \<close>
urust_datatype \<open> struct UsePacket { sample: u32 } \<close>
urust_datatype \<open> struct UseTuple(u32); \<close>
urust_datatype \<open> struct UseUnit; \<close>
urust_datatype \<open> struct UseWrapper<T> { inner: T } \<close>

urust_fn \<open> fn use_increment(x: u32) -> u32 { x + 1 } \<close>
urust_fn \<open> fn use_pair(x: u32, y: u64) -> u64 { y } \<close>

urust_fn [register_notation = false] use_demo_increment_impl
  \<open> fn demo_increment(x: u32) -> u32 { x + 2 } \<close>
urust_fn [register_notation = false] use_demo_value_impl
  \<open> fn demo_value() -> u32 { 9 } \<close>

definition use_demo_width :: \<open>32 word\<close> where
  \<open>use_demo_width = 4\<close>
definition use_demo_zero_narrow :: \<open>32 word\<close> where
  \<open>use_demo_zero_narrow = 0\<close>
definition use_demo_zero_wide :: \<open>64 word\<close> where
  \<open>use_demo_zero_wide = 0\<close>

micro_rust_notation (call) use_demo_increment_impl ("demo::increment")
micro_rust_notation (call) use_demo_value_impl ("demo::value")
micro_rust_notation (literal) use_demo_width ("demo::WIDTH")
micro_rust_notation (literal) use_demo_zero_narrow ("demo::ZERO")
micro_rust_notation (literal) use_demo_zero_wide ("demo::ZERO")

urust_type "demo::Width" = \<open> 32 word \<close>
urust_type "demo::Cell<'a>" = \<open> 'a list \<close>
urust_type_alias "demo::Short" \<open> type Short = u16; \<close>

ML\<open>
structure Parser_Use_Test =
struct
  structure S = URust_Import_Scope

  val layout = URust_AST.make_source_layout Position.none []
  fun segment name = (name, Position.none)
  fun leaf names alias =
    URust_AST.mk_use_path (map segment names, Option.map segment alias, layout)
  fun self_member alias = leaf ["self"] alias
  fun group prefix members = URust_AST.mk_use_group (map segment prefix, members, layout)
  fun item tree = URust_AST.mk_use_item (tree, layout)

  fun require label condition =
    if condition then () else error ("import regression: " ^ label)

  fun failure action =
    (case Exn.result action () of
       Exn.Res _ => NONE
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else SOME (Runtime.exn_message exn))

  fun rejects label expected action =
    (case failure action of
       NONE => error ("import regression: " ^ label ^ " was accepted")
     | SOME message =>
         require (label ^ " rejected for the wrong reason: " ^ message)
           (String.isSubstring expected message))

  fun lookup_key ctxt namespace alias =
    Option.map #key (S.lookup ctxt namespace alias)

  fun lookup_roles ctxt namespace alias =
    Option.map #roles (S.lookup ctxt namespace alias)

  fun prepare ctxt trees = URust_Imports.prepare_batch ctxt (map item trees)
end
\<close>

end
