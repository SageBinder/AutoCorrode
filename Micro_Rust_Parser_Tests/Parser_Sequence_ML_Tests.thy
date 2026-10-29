(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Sequence_ML_Tests
  imports Parser_Sequence_Examples
begin

ML\<open>
structure Parser_Sequence_Test =
struct
  structure M = URust_Type_Mappings
  fun require message condition =
    if condition then () else error ("sequence denotation regression: " ^ message)
  fun start label = Position.make0 1 1 0 "" label label
  fun source label text = Parser_Lex_Util.positioned_content_source text (start label)
  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close
  fun run thy label text =
    fold (Toplevel.command_exception true)
      (Outer_Syntax.parse_text thy (K thy) (start label) text)
      (Toplevel.make_state (SOME thy))
  fun parsed ctxt text = URust_Parser.parse_type_source ctxt (source "sequence-type" text)
  fun resolved ctxt text = M.resolve_type_identity ctxt (parsed ctxt text)
  fun identity ctxt text =
    (case #2 (resolved ctxt text) of
       SOME meaning => M.source_identity_name meaning
     | NONE => resolved ctxt ("SequencePayload<IdentityTag," ^ text ^ ">")
         |> #2 |> the |> M.source_identity_name)
  fun find text needle offset =
    if offset + size needle > size text then error ("missing token " ^ quote needle)
    else if String.substring (text, offset, size needle) = needle then offset
    else find text needle (offset + 1)
  fun range label text needle =
    let
      fun last offset =
        (case try (find text needle) (offset + size needle) of
           SOME next => last next
         | NONE => offset)
      val offset = last (find text needle 0)
      val first = Position.symbol_explode (String.substring (text, 0, offset)) (start label)
    in Position.range_position (Position.range (first, Position.symbol_explode needle first)) end
  fun positioned pos message =
    let
      fun collect (XML.Text _) result = result
        | collect (XML.Elem ((_, props), body)) result = fold collect body (props :: result)
      val properties = fold collect (YXML.parse_body message) []
      fun same props = Properties.get props Markup.offsetN =
          Option.map Value.print_int (Position.offset_of pos) andalso
        Properties.get props Markup.end_offsetN =
          Option.map Value.print_int (Position.end_offset_of pos) andalso
        Properties.get props Markup.fileN = Position.file_of pos
    in exists same properties end
  fun rejection thy label expected needle text =
    let
      val (result, reports) = Parser_Test_Reports.markup
        (fn () => Exn.capture (fn () => run thy label text) ())
      val message = case result of Exn.Res _ => error (label ^ ": accepted invalid source")
        | Exn.Exn exn => if Exn.is_interrupt exn then Exn.reraise exn else Runtime.exn_message exn
      val _ = require (label ^ ": wrong diagnostic " ^ XML.content_of (YXML.parse_body message))
        (String.isSubstring expected message)
      val _ = require (label ^ ": wrong source leaf") (positioned (range label text needle) message)
      val _ = require (label ^ ": failed declaration leaked semantic reports")
        (not (exists (fn (name, _) => name = Markup.entityN) reports))
    in () end
end
\<close>

section\<open> Canonical carriers and independent source structure \<close>

ML_val\<open>
local
  open Parser_Sequence_Test
  val ctxt = \<^context>
  fun canonical typ = Term_Subst.instantiateT (TVars.make
    (rev (Term.add_tvarsT typ []) |> map_index
      (fn (index, variable as (_, sort)) => (variable, TVar (("sequence", index), sort))))) typ
  fun typ name = canonical (Sign.the_const_type \<^theory> (Proof_Context.intern_const ctxt name))
  val _ = List.app (fn (native, escaped) =>
    require ("complete type, sorts or sharing changed: " ^ native) (typ native = typ escaped))
    [("sequence_value", "sequence_value_escape"),
     ("sequence_vector", "sequence_value_escape"),
     ("sequence_fixed", "sequence_nominal"),
     ("sequence_alias", "sequence_alias_escape"),
     ("sequence_nested", "sequence_nested_escape"),
     ("sequence_generic", "sequence_generic_escape"),
     ("sequence_call", "sequence_call_escape"),
     ("sequence_recursive_generic_call", "sequence_recursive_generic_call_escape"),
     ("sequence_array_element_call", "sequence_array_element_call_escape"),
     ("sequence_construct", "sequence_construct_escape"),
     ("sequence_shared", "sequence_shared_escape"),
     ("sequence_shared_lifetime", "sequence_shared_escape"),
     ("sequence_shared_static", "sequence_shared_escape"),
     ("sequence_shared_alias", "sequence_shared_escape"),
     ("sequence_optional_borrow", "sequence_optional_borrow_escape"),
     ("sequence_mutable", "sequence_mutable_escape"),
     ("sequence_mutable_lifetime", "sequence_mutable_escape"),
     ("sequence_mutable_placeholder", "sequence_mutable_escape"),
     ("sequence_nested_borrow", "sequence_nested_borrow_escape"),
     ("sequence_erased_generic", "sequence_erased_generic_escape"),
     ("sequence_erased_call", "sequence_erased_call_escape")]
in end
\<close>

ML_val\<open>
local
  open Parser_Sequence_Test
  val ctxt = \<^context>
  val _ = List.app (fn (source, expected) =>
    require ("wrong carrier for " ^ source) (#1 (resolved ctxt source) = expected))
    [("[u8]", \<^typ>\<open>8 word list\<close>),
     ("std::vec::Vec<u8>", \<^typ>\<open>8 word list\<close>),
     ("[u8;4]", \<^typ>\<open>(8 word, 4) array\<close>),
     ("Vec<u8,4>", \<^typ>\<open>(8 word, 4) array\<close>),
     ("SequenceAliasAgain<u8>", \<^typ>\<open>8 word option list\<close>),
     ("[[u8]]", \<^typ>\<open>8 word list list\<close>)]
  val _ = require "equal carriers conflated slice/vector/array source types"
    (length (distinct (op =) (map (identity ctxt)
      ["[u8]", "std::vec::Vec<u8>", "[u8;4]", "Vec<u8,4>"])) = 4)
  val _ = require "aliases did not expand structural slice meaning"
    (identity ctxt "SequenceBytes" = identity ctxt "[u8]" andalso
     identity ctxt "SequenceAliasAgain<u8>" = identity ctxt "[Option<u8>]")
  val _ = require "erased slices lost recursive source meaning"
    (identity ctxt "SequenceErasedAlias<u8>" = identity ctxt "SequenceTag<[u8]>" andalso
     identity ctxt "SequenceTag<[[u8]]>" <> identity ctxt "SequenceTag<[u8]>" andalso
     identity ctxt "SequenceTag<[u8]>" <> identity ctxt "SequenceTag<std::vec::Vec<u8>>")
  val _ = require "retained slices/arrays/vectors under erased owner lost identity"
    (length (distinct (op =) (map (identity ctxt)
      ["SequencePayload<Tag,[u8]>", "SequencePayload<Tag,[u8;4]>",
       "SequencePayload<Tag,std::vec::Vec<u8>>"])) = 3)
  val _ = require "generic alias substitution failed inside a slice"
    (identity ctxt "SequencePayloadAlias<Tag,u8>" = identity ctxt "SequencePayload<Tag,[u8]>" andalso
     identity ctxt "SequencePayloadAlias<Tag,u8>" <> identity ctxt "SequencePayloadAlias<Tag,u16>")
  val _ = require "erased slice allocated an unused reference backend"
    (#1 (resolved ctxt "SequenceTag<[SequenceElement<u8>]>") = \<^typ>\<open>nat\<close> andalso
      null (#backend_parameters (M.resolve_fields ctxt
        [parsed ctxt "SequenceTag<[SequenceElement<u8>]>"])))
  val entry = the_single (Parser_Test_Calls.entries ctxt "SequenceErasedGeneric")
  val slots = the (M.generic_source_scheme_for_source ctxt (#serial entry))
  val _ = require "slice element scope was lost in an erased argument"
    (map #rust slots = ["T"] andalso forall (is_none o #hol) slots andalso
      map #source_used slots = [SOME true])
  val owners = Micro_Rust_Names.associated_source_functions ctxt "SequenceTag::sequence_owner"
  val _ = require "same-carrier associated calls merged slice and vector owners"
    (length owners = 2 andalso length (distinct (op =) (map #source_identity owners)) = 2)
  val interpreted = Micro_Rust_Names.associated_source_functions ctxt "SequencePayload::sequence_locale"
  val _ = require "locale morphism failed to transport HOL leaves inside structural slices"
    (length interpreted = 2 andalso forall (fn owner =>
      member (op =) [SOME (identity ctxt "SequencePayload<Tag,[\<tau>\<open>nat\<close>]>"),
        SOME (identity ctxt "SequencePayload<Tag,[\<tau>\<open>bool\<close>]>")] (#source_identity owner)) interpreted)
in end
\<close>

section\<open> Dispatch serialization and source origin paths \<close>

ML_val\<open>
local
  open Parser_Sequence_Test
  open Micro_Rust_Names
  val tree = Source_Node (Slice_Source,
    [Source_Node (Mapped_Source "std::vec::Vec", [Source_HOL (Type_Source, \<^typ>\<open>nat\<close>)])])
  val selected: target_selection =
    {self_type = \<^typ>\<open>nat list list\<close>, source = SOME tree,
     source_identity = SOME "sequence-serialization", evidence = [([0, 0], \<^typ>\<open>nat\<close>)],
     inputs = [([0, 0], ("nat", start "sequence-origin"))], pos = start "sequence-target"}
  val bundle: Micro_Rust_Dispatch.scoped_sparse_arguments =
    {instances = [{source = 7, target = SOME selected, arguments = NONE, identities = []}],
     pending = NONE, pos = start "sequence-dispatch"}
  val (encoded, witnesses) = Micro_Rust_Dispatch.scoped_sparse_encoding bundle
  val (instances, pending) = Micro_Rust_Dispatch.scoped_sparse_instances encoded (map fst witnesses)
  val decoded = the (#target (the_single instances))
  val _ = require "dispatch slice tree roundtrip changed source identity or origins"
    (#source decoded = SOME tree andalso #source_identity decoded = #source_identity selected andalso
      #evidence decoded = #evidence selected andalso
      map fst (#inputs decoded) = [[0, 0]] andalso is_none pending)
in end
\<close>

section\<open> Positioned failures, rollback and printer roundtrips \<close>

ML_val\<open>
local
  open Parser_Sequence_Test
  val ctxt = \<^context>
  val label = "sequence-leaf-markup"
  val text = "[u8]"
  val (_, reports) = Parser_Test_Reports.markup (fn () =>
    M.resolve_type_identity ctxt (URust_Parser.parse_type_source ctxt (source label text)))
  val _ = require "slice element lost native type navigation"
    (exists (fn (name, _) => name = Markup.entityN) reports)
  val _ = require "slice brackets lost delimiter markup"
    (length (filter (fn (name, _) => name = Markup.delimiterN) reports) >= 2)
  val malformed = parsed ctxt "[Option<MissingElement>]"
  val (result, reports) = Parser_Test_Reports.markup (fn () =>
    Exn.capture (fn () => M.resolve_type_identity ctxt malformed) ())
  val _ = require "failed recursive slice resolution leaked reports"
    (Exn.is_exn result andalso null reports)
in end
\<close>

ML_val\<open>
local
  open Parser_Sequence_Test
  val thy = \<^theory>
  val _ = List.app (fn (label, expected, needle, body) =>
    rejection thy label expected needle ("urust_fn sequence_failure " ^ cartouche body))
    [("sequence-unknown", "unknown Rust type", "MissingElement",
      "fn Bad(value: [MissingElement]) { () }"),
     ("sequence-nested-unknown", "unknown Rust type", "MissingElement",
      "fn Bad(value: [[Option<MissingElement>]]) { () }"),
     ("sequence-kind", "const parameters used as type arguments", "N",
      "fn Bad<const N: usize>(value: [N]) { () }"),
     ("sequence-erased-kind", "const parameters used as type arguments", "N",
      "fn Bad<const N: usize>(value: SequenceTag<[N]>) { () }"),
     ("sequence-lifetime", "undeclared lifetime", "'missing",
      "fn Bad(value: &'missing [u8]) { () }")]
  val _ = List.app (fn policy =>
    rejection thy ("sequence-policy-" ^ policy) "HOL type antiquotation" "&[u8]"
      ("urust_fn [shared_references = [\"arg:0\" \<rightarrow> " ^ cartouche policy ^ "]] " ^
        "sequence_failure " ^ cartouche "fn Bad(value: &[u8]) { () }"))
    ["value", "reference"]
  val _ = rejection thy "sequence-alias-policy" "HOL type antiquotation" "&SequenceBytes"
    ("urust_fn [shared_references = [\"arg:0\" \<rightarrow> " ^ cartouche "value" ^ "]] " ^
      "sequence_failure " ^ cartouche "fn Bad(value: &SequenceBytes) { () }")
  val _ = rejection thy "sequence-field-reference" "Rust reference types" "&[u8]"
    ("urust_datatype " ^ cartouche "struct BadSequenceField { value: &[u8] }")
  val _ = rejection thy "sequence-alias-reference" "Rust reference types" "&mut [u8]"
    ("urust_type_alias " ^ cartouche "type BadSequenceAlias = &mut [u8];")
  val _ = rejection thy "sequence-cast" "no supported cast operation" "[u8]"
    ("urust_expr sequence_failure " ^ cartouche "0 as [u8]")
  val _ = rejection thy "sequence-alias-cast" "no supported cast operation" "SequenceBytes"
    ("urust_expr sequence_failure " ^ cartouche "0 as SequenceBytes")
  val _ = List.app (fn text =>
    ignore (run thy "sequence-roundtrip"
      ("urust_fn [pp_test] _ " ^ cartouche text)))
    ["fn Roundtrip(value: [[u8]]) -> [[u8]] { value }",
     "fn Roundtrip<'a>(value: &'a [Option<u8>]) -> &'a [Option<u8>] { value }",
     "fn Roundtrip<'a>(value: &'a mut [u8]) -> &'a mut [u8] { value }",
     "fn Roundtrip(value: std::vec::Vec<[u8]>) -> std::vec::Vec<[u8]> { value }"]
in end
\<close>

end
