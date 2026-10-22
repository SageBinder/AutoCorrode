(* Left branch of the fixture merge diamond: constructor and struct basenames that become
   ambiguous only in a theory that imports both branches, and impl-member registrations of one key
   whose Self types differ between the branches. *)

theory Parser_Test_Fixtures_Left
  imports
    Parser_Test_Fixtures
    Micro_Rust_Parser_Impl.Parser_Impl_Trait_Mappings
    Enum_Theory.Enum_Theory
    Misc.Simple_Word_Enums
begin

chapter\<open> Constructor ambiguity \<close>

declare [[urust_pp_test = true, urust_pretty = true, urust_verbosity = 2, urust_abbrev = false,
  urust_application_def = false, urust_register_notation = true]]

enum constructor_ambiguity_left =
    Shared
  | LeftOnly

simple_word_enum (plugins del: word_conversion) (8)
  word_constructor_ambiguity_left =
    SharedWordState = 11
  | LeftWordState = 12

chapter\<open> Struct ambiguity \<close>

datatype struct_ambiguity_left =
  AmbiguousStruct (ambiguous_field: nat)

datatype nullary_ambiguity_left =
  AmbiguousNullary

chapter\<open> Impl-member registrations \<close>

text\<open>
An impl member of \<open>nat list\<close>, registered as the impl registration path does: an
associated-function owner and an automatic path entry sharing the member identity, and a
method-only bare entry. The other branch registers the same keys for a different Self type.
\<close>

definition merge_cell_left_get ::
  \<open>nat list \<Rightarrow> ('s, nat list, 'a, 'i, 'o) function_body\<close> where
  \<open>merge_cell_left_get cell = FunctionBody (literal cell)\<close>

local_setup \<open>
  fn lthy =>
    let
      val identity = serial ()
      val method_serial = serial ()
      val pos = \<^here>
      val backend = \<^term>\<open>merge_cell_left_get\<close>
    in
      lthy |> Local_Theory.declaration {pervasive = false, syntax = true, pos = pos}
        (fn phi =>
          Micro_Rust_Names.reserve_associated_function
            {name = "MergeCell::get", self_type = Morphism.typ phi \<^typ>\<open>nat list\<close>,
             identity = identity, pos = pos} #>
          Micro_Rust_Names.mark_automatic identity #>
          Micro_Rust_Names.register_with_source_serial Micro_Rust_Names.NFunction "MergeCell::get"
            (Morphism.term phi backend) NONE pos identity #>
          Micro_Rust_Names.mark_automatic method_serial #>
          Micro_Rust_Names.mark_method_only method_serial #>
          Micro_Rust_Names.register_with_source_serial Micro_Rust_Names.NFunction "merge_cell_get"
            (Morphism.term phi backend) NONE pos method_serial)
    end
\<close>

chapter\<open> Trait mapping merge fixtures \<close>

urust_trait "merge::SharedMarker" = \<open> type \<close>
  urust_consts "COUNT" = \<open> \<lambda>(_ :: 'a itself). (5 :: nat) \<close>

urust_trait "merge::LeftMarker" = \<open> type \<close>

end
