theory Parser_Utils
  imports
    "Parser_Common.Parser_Common"
    "Shallow_Micro_Rust.Semantic_Navigation"
begin

ML\<open>
structure URust_Parser_Config =
struct
  val (verbosity, setup_verbosity) =
    Attrib.config_int \<^binding>\<open>urust_verbosity\<close> (K 0)
  val _ = Theory.setup (fn thy =>
    let val naming = Sign.naming_of thy in
      thy |> Sign.root_path |> Sign.add_path "Parser_Impl_Command" |> setup_verbosity
      |> Sign.map_naming (K naming)
    end)
end
\<close>

section\<open> Report transactions \<close>

text\<open>
A uRust declaration command is one report transaction. uRust-owned elaboration markup is queued
and released by the command after it succeeds; Isabelle readers whose markup belongs to the
command (embedded HOL terms, types and names) read in an invisible context and repeat the same
deterministic read for its markup at release. Native declaration backends run in invisible
contexts; their authored definition entities are regenerated from the completed name spaces and
released with the transaction. Semantic navigation targets keep their own queue, which is
released after these reports, preserving the former immediate-before-deferred order.

A multi-member transaction also buffers the markup of term checks over embedded HOL sources:
such a check runs invisibly and is repeated for its typing reports at release. A single-member
transaction checks visibly, as its own failure leaves no earlier member behind.
\<close>

ML\<open>
signature URUST_REPORT_TRANSACTION =
sig
  type reports
  val capture: (unit -> 'a) -> 'a * reports
  val replay: Proof.context -> reports -> unit
  val with_private_reports: (unit -> 'a) -> 'a
  val output_reporter: (string list -> unit) -> string list -> unit
  val report: Proof.context -> Position.T -> Markup.T -> unit
  val report_text: Proof.context -> Position.T -> Markup.T -> string -> unit
  val native: Proof.context -> (Proof.context -> 'a) -> 'a
  val release_on_failure: Proof.context -> (unit -> 'a) -> 'a
  val capture_members: (unit -> 'a) -> 'a * reports
  val check_term: Proof.context -> term -> term
  val invisible_declarations:
    (morphism -> 'a -> 'a) -> (local_theory -> 'a * local_theory) -> local_theory ->
      'a * local_theory
  val defer_definitions: Proof.context -> (Name_Space.T * string) list -> unit
end

structure URust_Report_Transaction : URUST_REPORT_TRANSACTION =
struct
  structure Navigation = Micro_Rust_Semantic_Navigation

  datatype event =
      Report of Position.T * Markup.T * string
    | Native_Read of unit -> unit
    | Output_Report of string list

  type reports = event list * Navigation.reports

  type transaction = {events: event list Unsynchronized.ref, buffer_checks: bool}

  val active: transaction Thread_Data.var = Thread_Data.var ()

  fun enqueue event ({events, ...}: transaction) = events := event :: !events

  (* A nested capture joins the outermost transaction of the thread. *)
  fun gen_capture buffer_checks action =
    (case Thread_Data.get active of
       SOME {events, ...} =>
         let val mark = !events in
           (case Exn.capture Navigation.capture action of
              Exn.Res (result, navigation) => (result, ([], navigation))
            | Exn.Exn exn => (events := mark; Exn.reraise exn))
         end
     | NONE =>
         let
           val events = Unsynchronized.ref ([]: event list)
           val (result, navigation) =
             Thread_Data.setmp active (SOME {events = events, buffer_checks = buffer_checks})
               Navigation.capture action
         in (result, (rev (!events), navigation)) end)

  fun capture action = gen_capture false action
  fun capture_members action = gen_capture true action

  fun replay_events ctxt events =
    List.app
      (fn Report (pos, markup, text) => Context_Position.report_text ctxt pos markup text
        | Native_Read read => read ()
        | Output_Report chunks => Output.report chunks)
      events

  fun replay ctxt (events, navigation) =
    (replay_events ctxt events; Navigation.replay ctxt navigation)

  (* A failing elaboration releases the reports it queued itself, which explain its diagnostic;
     reports of earlier successful work stay queued and are discarded with the transaction. *)
  fun release_on_failure ctxt action =
    (case Thread_Data.get active of
       NONE => action ()
     | SOME {events, ...} =>
         let val mark = !events in
           (case Exn.result action () of
              Exn.Res result => result
            | Exn.Exn exn =>
                if Exn.is_interrupt exn then Exn.reraise exn
                else
                  let val added = take (length (!events) - length mark) (!events) in
                    events := mark; replay_events ctxt (rev added); Exn.reraise exn
                  end)
         end)

  (* Reports that a read-only replay forwards to the authored source belong to the transaction
     active when the replay starts. *)
  fun output_reporter report =
    (case Thread_Data.get active of
       SOME transaction => (fn chunks => enqueue (Output_Report chunks) transaction)
     | NONE => report)

  (* Read-only replay owns its report sink, independently of any surrounding transaction. *)
  fun with_private_reports action =
    Thread_Data.setmp active NONE Navigation.with_private_reports action

  fun report_text ctxt pos markup text =
    if not (Context_Position.is_reported ctxt pos) then ()
    else
      (case Thread_Data.get active of
         SOME transaction => enqueue (Report (pos, markup, text)) transaction
       | NONE => Context_Position.report_text ctxt pos markup text)

  fun report ctxt pos markup = report_text ctxt pos markup ""

  fun native ctxt read =
    (case Thread_Data.get active of
       SOME transaction =>
         if Context_Position.is_visible ctxt then
           let val result = read (Context_Position.set_visible false ctxt)
           in enqueue (Native_Read (fn () => ignore (read ctxt))) transaction; result end
         else read ctxt
     | NONE => read ctxt)

  (* Parsed HOL sources keep their positions as internal type constraints until checking. *)
  val has_source_positions =
    Term.exists_subterm
      (fn Const (\<^syntax_const>\<open>_type_constraint_\<close>,
            Type (\<^type_name>\<open>fun\<close>, [position_type, _])) =>
            not (null (Term_Position.decode_positionT position_type))
        | _ => false)

  (* Only positioned HOL sources produce check-time reports. The repeated check resolves its
     navigation markers into a discarded private queue. *)
  fun check_term ctxt term =
    (case Thread_Data.get active of
       SOME (transaction as {buffer_checks = true, ...}) =>
         if Context_Position.is_visible ctxt andalso has_source_positions term
         then
           let
             val checked = Syntax.check_term (Context_Position.set_visible false ctxt) term
             val repeat = fn () => ignore (Navigation.capture (fn () => Syntax.check_term ctxt term))
           in enqueue (Native_Read repeat) transaction; checked end
         else Syntax.check_term ctxt term
     | _ => Syntax.check_term ctxt term)

  (* At theory level the target is re-initialised from an invisible background theory, as the
     toplevel re-initialises it between commands; elsewhere an invisible nested target over an
     invisible background theory keeps every backend context invisible. The constant-default
     visibility flags are restored exactly. The result leaves the backend context through the
     native export morphism of that context. *)
  fun invisible_declarations transfer declare lthy =
    if Named_Target.is_theory lthy then
      let
        val thy = Local_Theory.exit_global lthy
        val (result, thy') =
          Local_Theory.exit_result_global transfer
            (declare (Named_Target.theory_init (Context_Position.set_visible_global false thy)))
      in
        (result, Named_Target.theory_init (Context_Position.restore_visible_global thy thy'))
      end
    else
      let
        val thy = Proof_Context.theory_of lthy
        val (_, nested) =
          lthy
          |> Context_Position.set_visible false
          |> Local_Theory.background_theory (Context_Position.set_visible_global false)
          |> Local_Theory.begin_nested
        val (result, outer) = Local_Theory.end_nested_result transfer (declare nested)
      in
        (result,
         outer
         |> Local_Theory.background_theory (Context_Position.restore_visible_global thy)
         |> Context_Position.restore_visible lthy)
      end

  (* Native declarations report definitions only at proper binding positions; an entry without
     one carries the position of the declaring command. *)
  fun defer_definitions ctxt entries =
    let
      val command_position = Position.properties_of (Position.thread_data ())
    in
      List.app
        (fn (space, name) =>
          (case try (Name_Space.the_entry space) name of
             SOME {pos, ...} =>
               if Position.properties_of pos = command_position then ()
               else report ctxt pos (Name_Space.markup_def space name)
           | NONE => ()))
        entries
    end
end
\<close>

section\<open> Parser utilities \<close>

ML\<open>
structure Parser_Utils =
struct

(* Basis scanners accept prefixes. Source literals must consume every digit, including
   after a radix prefix; otherwise a const argument can silently acquire the wrong type. *)
fun read_unsigned_integer text =
  let
    val (radix, base, start) =
      if String.isPrefix "0b" text then (StringCvt.BIN, 2, 2)
      else if String.isPrefix "0o" text then (StringCvt.OCT, 8, 2)
      else if String.isPrefix "0x" text then (StringCvt.HEX, 16, 2)
      else (StringCvt.DEC, 10, 0)
    val digits = String.extract (text, start, NONE)
    val clean = String.translate (fn #"_" => "" | c => str c) digits
    fun digit c =
      if #"0" <= c andalso c <= #"9" then Char.ord c - Char.ord #"0"
      else if #"a" <= c andalso c <= #"f" then 10 + Char.ord c - Char.ord #"a"
      else if #"A" <= c andalso c <= #"F" then 10 + Char.ord c - Char.ord #"A"
      else base
  in
    if clean = "" orelse
      (start = 0 andalso digit (String.sub (digits, 0)) >= base) orelse
      exists (fn c => c <> #"_" andalso digit c >= base) (String.explode digits)
    then NONE
    else
      (case Int.scan radix Substring.getc (Substring.full clean) of
         SOME (value, rest) =>
           if Substring.isEmpty rest then SOME value else NONE
       | NONE => NONE)
  end

type var_info = { free : term, def_pos : Position.T, id : int }

fun report_def kind ctxt id (x, def_pos) =
  (URust_Report_Transaction.report ctxt def_pos Markup.bound;
   URust_Report_Transaction.report ctxt def_pos
     (Position.make_entity_markup {def = true} id kind (x, def_pos)))

fun report_ref kind ctxt id (x, def_pos) use_pos =
  (URust_Report_Transaction.report ctxt use_pos Markup.bound;
   URust_Report_Transaction.report ctxt use_pos
     (Position.make_entity_markup {def = false} id kind (x, def_pos)))

fun bind_typed_var kind ctxt (env : var_info Symtab.table) ((x, def_pos), T) =
  let
    val id   = serial ()
    val _    = report_def kind ctxt id (x, def_pos)
    (* Source spelling belongs in the environment and markup, not in Free identity. Distinct
       identities prevent a later abstraction for a shadowing binder from capturing an outer
       same-spelled local that has been placed in a shared continuation. Abstract with
       Term.lambda_name and the source spelling: the internal name must not reach Abs names,
       which become printed binders and application_def left-hand sides. *)
    val free =
      Free ("_urust_local_" ^ string_of_int id ^ "_" ^ x, T)
  in (free, Symtab.update (x, {free = free, def_pos = def_pos, id = id}) env) end

fun bind_var kind ctxt env binding =
  bind_typed_var kind ctxt env (binding, dummyT)

(* Do not represent anonymous binders with invented Frees: such a name can capture a source binder held
   only in the elaboration environment. *)
fun anon_abs body = Abs (Name.uu, dummyT, body)

(* Parse lexical binders through fresh internal fixes, then restore their source Frees. Variants avoid
   collisions with same-named HOL context fixes while still shadowing constants during parsing. *)
fun parse_antiq kind ctxt env src =
  let
    val names = Symtab.keys env
    val (variants, ctxt') = Variable.variant_fixes names ctxt
    fun replacement source_name =
      (case Symtab.lookup env source_name of
         SOME {free, def_pos, id} =>
           {source_name = source_name, free = free, def_pos = def_pos, id = id}
       | NONE =>
           error ("internal missing antiquotation binder " ^ quote source_name))
    val replacements =
      Symtab.make
        (map2 (fn source_name => fn variant =>
          (variant, replacement source_name)) names variants)

    fun report_at {syntax, pos} markup =
      URust_Report_Transaction.report ctxt pos
        (Markup.syntax_properties syntax markup)
    fun report_replacement
        {source_name, def_pos, id, ...} position =
      (report_at position Markup.bound;
       report_at position
         (Position.make_entity_markup {def = false} id kind
           (source_name, def_pos)))

    (* Syntax.parse_term has already decoded HOL binders to Abs/Bound and retained source positions as
       internal type constraints. Follow the same position flow as Isabelle's term decoder: constraints
       accumulate on one atom, while applications and abstractions start fresh occurrence scopes. *)
    fun restore positions
        ((constant as
            Const (\<^syntax_const>\<open>_type_constraint_\<close>,
              Type (\<^type_name>\<open>fun\<close>, [position_type, _]))) $ inner) =
          let
            val positions' =
              Term_Position.decode_positionT position_type @ positions
          in
            constant $ restore positions' inner
          end
      | restore _ (function $ argument) =
          restore [] function $ restore [] argument
      | restore _ (Abs (name, T, body)) =
          Abs (name, T, restore [] body)
      | restore positions (free as Free (name, _)) =
          (case Symtab.lookup replacements name of
             SOME (replacement as {free = lexical_free, ...}) =>
               (List.app (report_replacement replacement) positions;
                lexical_free)
           | NONE => free)
      | restore _ atom = atom
  in
    restore []
      (URust_Report_Transaction.native ctxt'
        (fn read_ctxt => Syntax.parse_term read_ctxt (Syntax.implode_input src)))
  end

end
\<close>

end
