theory Parser_Impl_Chunk
  imports Parser_Impl_Command
  keywords "urust" :: thy_decl
begin

section\<open> Source-ordered item chunks \<close>

text\<open>
The chunk surface is \<open>urust [OPTIONS] src\<close>, whose cartouche contains a nonempty source-ordered
list of complete \<open>fn\<close>, \<open>struct\<close>, \<open>enum\<close> and \<open>use\<close> items. An optional annotation
\<open>\<omega>\<open>OPTION, OPTION = VALUE, ...\<close>\<close> occupies its own line or lines immediately before the line
on which its item starts; a leading \<open>#[repr(...)]\<close> line belongs to its enum. Its payload uses
the entry syntax of the bracketed lists with the function or datatype schema of the single-item
commands, plus the positioned HOL binding \<open>name\<close>; functions also accept \<open>name = _\<close> to check
without installing anything. The outer list accepts only \<open>pp_test\<close>, \<open>pretty\<close>,
\<open>verbosity\<close> and \<open>register_notation\<close>. Annotation entries replace outer defaults, which
replace scoped configurations; configurations are never changed.

The whole chunk parses, and every annotation payload, schema and option combination of every
member is validated, before the first declaration. Checks that depend on earlier members
(registration conflicts, Rust and HOL signature types, unresolved names) run when the member is
declared. Members use the parsed-item operations of \<open>urust_fn\<close> and \<open>urust_datatype\<close>, each
in the context that the next command of the equivalent single-item sequence would receive, so
earlier items are available to later ones and forward references are not resolved. Type alias
items are rejected as chunk members. With \<open>pp_test\<close>, each member's annotation and item
roundtrip through the serialized chunk printer before any declaration.

A use member is one complete use item with the grammar of \<open>urust_use\<close>; it takes no options, so
an annotation before it is rejected. The chunk's imports form one batch, validated as a whole
(duplicates and cycles) before the first declaration. Its aliases are visible to every declaration
of the chunk, including those written before the use item, and to nothing else: each declaration
elaborates in its member context extended with the batch, prepared afresh for that context. An
entity that the declaration itself or a later member declares is unavailable in its namespace,
and its use is rejected without fallback, while entities that already exist keep resolving. A
target that neither exists nor is declared, with a Rust registration, by a member is rejected as
unknown before the first declaration. After the last declaration every target must resolve, and
no chunk import may share a namespace and name with an item that the chunk declares. Chunk aliases
shadow persistent \<open>urust_use\<close> aliases, body imports shadow chunk aliases, and no alias survives
the command. As for Rust module-level imports, member parameters and other lexical locals shadow
chunk and persistent aliases, while a body import shadows the parameters of its member.

The command is one report transaction. uRust semantic reports, the markup of embedded HOL
sources read during elaboration, regenerated declaration definition entities, warnings and
successful output are released in source order only after every member succeeds; native
declaration backends run in invisible contexts. Any failure rejects the whole command.

This theory is opt-in above \<open>Parser_Impl_Command\<close>. The \<open>simple_word_enum\<close> clause is
spelled \<open>urust_name: "Name"\<close>, so it does not collide with the \<open>urust\<close> command keyword.
\<close>

ML\<open>
signature URUST_CHUNK =
sig
  val define:
    URust_Command.command_options * Input.source -> bool -> local_theory -> local_theory
end

(* Orchestration only: option values, naming choices and declaration semantics belong to the
   exported URust_Command operations shared with the single-item commands. *)
structure URust_Chunk :> URUST_CHUNK =
struct

datatype member =
    Function_Member of URust_Command.prepared_function
  | Datatype_Member of URust_Command.prepared_datatype
  | Use_Member of URust_AST.use_item

fun prepare_member lthy interactive outer envelope =
  let
    val annotation = URust_AST.annotated_item_annotation envelope
    val source = URust_AST.annotated_item_source envelope
    fun options schema =
      (case annotation of
         NONE => outer
       | SOME annotation =>
           URust_Command.override_options
             (URust_Command.read_annotation_options lthy schema annotation) outer)
  in
    (case URust_AST.annotated_item_item envelope of
       URust_AST.Function_Item_Node function =>
         let val options = options URust_Command.Function_Annotation in
           (URust_Command.configured_pp_test lthy options,
            Function_Member
              (URust_Command.prepare_function_item lthy
                {interactive = interactive, roundtrip = false, options = options,
                 source = source, function = function}))
         end
     | URust_AST.Datatype_Item item =>
         let val options = options URust_Command.Datatype_Annotation in
           (URust_Command.configured_pp_test lthy options,
            Datatype_Member
              (URust_Command.prepare_datatype_item lthy
                {interactive = interactive, roundtrip = false, options = options,
                 source = source, item = item}))
         end
     | URust_AST.Type_Alias_Item_Node item =>
         error
           ("urust: type alias items are not chunk members; declare them with urust_type_alias" ^
             Position.here (#2 (URust_AST.type_alias_name item)))
     | URust_AST.Use_Item_Node item =>
         (case annotation of
            SOME annotation =>
              error
                ("urust: an \<omega> annotation cannot precede a use item; use items take no options" ^
                  Position.here (URust_AST.annotation_position annotation))
          | NONE => (URust_Command.configured_pp_test lthy outer, Use_Member item)))
  end

fun declare_member (Function_Member prepared) = URust_Command.declare_prepared_function prepared
  | declare_member (Datatype_Member prepared) = URust_Command.declare_prepared_datatype prepared
  | declare_member (Use_Member _) = raise Fail "urust: use members are not declarations"

fun use_member (_, Use_Member item) = SOME item
  | use_member _ = NONE

(* The registry entities a member contributes once declared, as its declaration backend
   decides them. *)
fun member_entities ctxt member =
  URust_Imports.registration_entities
    (case member of
       Function_Member prepared => URust_Command.prepared_function_registrations prepared
     | Datatype_Member prepared => URust_Command.prepared_datatype_registrations ctxt prepared
     | Use_Member _ => URust_Imports.no_registrations)

fun first_differing_token_index left right =
  let
    fun first index (left_token :: left_tokens) (right_token :: right_tokens) =
          if left_token = right_token then first (index + 1) left_tokens right_tokens
          else index
      | first index _ _ = index
  in first 0 left right end

(* The serialized envelope roundtrip covers the item and its annotation payload. *)
fun roundtrip ctxt envelope =
  let
    val original_tokens =
      URust_Printer.tokens_of_annotated_item URust_Printer.serialized_options envelope
    val generated =
      URust_Printer.string_of_annotated_item URust_Printer.serialized_options envelope
    fun mismatch index detail =
      error
        ("uRust chunk pretty-printer roundtrip mismatch" ^
          Position.here (Input.pos_of (URust_AST.annotated_item_source envelope)) ^ "\n" ^
          "generated source:\n" ^ generated ^ "\n" ^
          "first differing token index: " ^ string_of_int index ^
          (if detail = "" then "" else "\n" ^ detail))
    val reparsed =
      (case Exn.capture
          (URust_Parser.parse_chunk_source ctxt)
          (Parser_Lex_Util.text_source generated) of
         Exn.Res (SOME chunk) =>
           (case URust_AST.chunk_items chunk of
              [reparsed] => reparsed
            | _ => mismatch 0 "generated source did not reparse as one chunk member")
       | Exn.Res NONE =>
           mismatch 0 "generated source reparsed as empty input"
       | Exn.Exn exn =>
           mismatch 0
             ("generated source failed to parse: " ^
               Runtime.exn_message exn))
    val reparsed_tokens =
      URust_Printer.tokens_of_annotated_item URust_Printer.serialized_options reparsed
  in
    if original_tokens = reparsed_tokens then ()
    else
      mismatch
        (first_differing_token_index original_tokens reparsed_tokens) ""
  end

(* Within one command, earlier definitions remain fixed-type terms of a growing auxiliary
   context. Each next member instead receives the context that the next command of an
   equivalent single-item sequence would: a fresh theory target at theory level, as the
   toplevel creates between commands, and otherwise the target context recovered by closing
   an empty nested target. No declaration is applied at an extra level. *)
fun next_command_context lthy =
  if Named_Target.is_theory lthy
  then Named_Target.theory_init (Local_Theory.exit_global lthy)
  else Local_Theory.end_nested (#2 (Local_Theory.begin_nested lthy))

fun define (outer, source) interactive lthy =
  let
    val ((outputs, completed), reports) =
      URust_Report_Transaction.capture_members (fn () =>
        let
          val chunk =
            (case URust_Parser.parse_chunk_source lthy source of
               SOME chunk => chunk
             | NONE =>
                 error
                   ("urust: empty chunk; expected at least one fn, struct, enum, or use item" ^
                     Position.here (Input.pos_of source)))
          val envelopes = URust_AST.chunk_items chunk
          val members = map (prepare_member lthy interactive outer) envelopes
          val batch = URust_Imports.validate_batch (map_filter use_member members)
          val _ =
            List.app
              (fn (envelope, (pp_test, _)) => if pp_test then roundtrip lthy envelope else ())
              (envelopes ~~ members)
          val declarations = filter_out (is_some o use_member o #2) (envelopes ~~ members)
          (* For each declaration, the entities that it and every later declaration introduce. A
             target entity among them is unavailable to that declaration in its own namespace;
             any other absent target is unknown, so the first preparation rejects it before the
             first declaration. *)
          val later_entities =
            fold_rev
              (fn (_, (_, member)) => fn later =>
                (member_entities lthy member @ (case later of [] => [] | next :: _ => next)) ::
                  later)
              declarations []
          (* Each declaration elaborates and declares in its member context extended with the
             batch frame. The frame is proof data of the auxiliary context, which the next-command
             context replaces by a target context, so it never outlives its declaration. A failing
             member releases its own queued markup with its error; markup of earlier members stays
             queued and is discarded with the transaction. *)
          fun declare ((_, (_, member)), later) lthy' =
            let
              val member_lthy =
                URust_Imports.prepare_batch_unreported (URust_Imports.Declared_Later later)
                  lthy' batch
            in
              URust_Report_Transaction.release_on_failure member_lthy
                (fn () => declare_member member member_lthy)
              ||> next_command_context
            end
          val (outputs, completed) = fold_map declare (declarations ~~ later_entities) lthy
          val _ = URust_Imports.conclude_batch {initial = lthy} completed batch
        in (outputs, completed) end)
    val _ = URust_Report_Transaction.replay completed reports
    val _ = List.app (fn output => output ()) outputs
  in completed end

val _ =
  Outer_Syntax.local_theory' \<^command_keyword>\<open>urust\<close>
    "Declare a source-ordered chunk of uRust functions, datatypes and imports"
    (URust_Command.parse_options URust_Command.Chunk_Defaults --
      (Parse.token Parse.cartouche >> Parser_Lex_Util.cartouche_source) >>
      define)

end
\<close>

end
