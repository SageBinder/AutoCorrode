(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Semantic_Navigation
  imports Main
begin

section\<open>Deferred semantic navigation reports\<close>

text\<open>
Semantic lowering marks only the shallow terms selected by surface syntax. A late term-check phase
observes those markers after overloading and case translation, records the surviving qualified HOL
constant, and erases the marker. The enclosing command replays the resulting native Isabelle markup
only after checking and declaration audits accept the complete elaboration.
\<close>

consts
  semantic_navigation_target :: \<open>'p \<Rightarrow> 'a \<Rightarrow> 'a\<close>
  semantic_navigation_annotation :: \<open>'p \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b\<close>
  semantic_navigation_probe :: \<open>'a \<Rightarrow> 'b \<Rightarrow> 'b\<close>

ML\<open>
signature MICRO_RUST_SEMANTIC_NAVIGATION =
sig
  datatype target_kind = Primary | Secondary
  type reports

  val capture: (unit -> 'a) -> 'a * reports
  val replay: Proof.context -> reports -> unit

  val defer_report:
    Proof.context -> Position.T -> Markup.T -> unit
  val defer_type:
    Proof.context -> Position.T -> string -> unit

  val with_source:
    Position.T list -> (unit -> 'a) -> 'a
  val with_source_position:
    Position.T -> (unit -> 'a) -> 'a
  val mark:
    target_kind -> term -> term
  val annotate:
    target_kind -> term -> term -> term
  val probe:
    term -> term -> term
end

structure Micro_Rust_Semantic_Navigation
  :> MICRO_RUST_SEMANTIC_NAVIGATION =
struct
  datatype target_kind = Primary | Secondary

  datatype selected_target =
    Selected_Target of target_kind * string

  datatype deferred_event =
      Deferred_Markup of Position.T * Markup.T
    | Deferred_Targets of Position.T list * selected_target list

  type reports = deferred_event list

  val active_reports:
    deferred_event list Unsynchronized.ref Thread_Data.var =
      Thread_Data.var ()

  val active_source:
    Position.T list Thread_Data.var =
      Thread_Data.var ()

  fun enqueue event =
    (case Thread_Data.get active_reports of
       SOME reports => reports := event :: !reports
     | NONE =>
         error
           "Micro_Rust_Semantic_Navigation: no active report capture")

  fun capture action =
    (case Thread_Data.get active_reports of
       SOME _ => (action (), [])
     | NONE =>
         let
           val reports =
             Unsynchronized.ref ([]: deferred_event list)
           val result =
             Thread_Data.setmp active_reports (SOME reports)
               action ()
         in (result, rev (!reports)) end)

  fun defer_report ctxt pos markup =
    if not (Position.is_reported pos) then ()
    else
      (case Thread_Data.get active_reports of
         SOME reports =>
           reports := Deferred_Markup (pos, markup) :: !reports
       | NONE =>
           Context_Position.report ctxt pos markup)

  fun defer_type ctxt pos name =
    List.app (defer_report ctxt pos)
      [Name_Space.markup
         (Type.type_space (Proof_Context.tsig_of ctxt)) name,
       Markup.tconst]

  fun same_position (left, right) =
    Position.properties_of left = Position.properties_of right

  fun stable_positions positions =
    positions
    |> filter Position.is_reported
    |> distinct same_position

  fun with_source positions action =
    let
      val reported_positions = stable_positions positions
    in
      if null reported_positions orelse
         is_none (Thread_Data.get active_reports)
      then action ()
      else
        Thread_Data.setmp active_source (SOME reported_positions)
          action ()
    end

  fun with_source_position pos action =
    with_source [pos] action

  val payload_prefix = "_urust_semantic_navigation_payload___"
  val payload_sep = String.str (Char.chr 0)

  fun strip_file pos =
    let
      val {line, offset, end_offset, props = {label, id, ...}} =
        Position.dest pos
    in
      Position.make
        {line = line, offset = offset, end_offset = end_offset,
         props = {label = label, file = "", id = id}}
    end

  fun kind_tag Primary = "primary"
    | kind_tag Secondary = "secondary"

  fun tag_kind "primary" = Primary
    | tag_kind "secondary" = Secondary
    | tag_kind tag =
        error
          ("Micro_Rust_Semantic_Navigation: malformed target kind " ^
            quote tag)

  fun mk_payload kind positions =
    Free
      (payload_prefix ^ kind_tag kind ^ payload_sep ^
        Term_Position.encode_no_syntax (map strip_file positions),
       dummyT)

  fun dest_payload (Free (name, _)) =
        if String.isPrefix payload_prefix name
        then
          (case
              String.fields (fn character => character = Char.chr 0)
                (String.extract
                  (name, size payload_prefix, NONE)) of
             [kind, encoded_positions] =>
               SOME
                 (tag_kind kind,
                  map #pos
                    (Term_Position.decode encoded_positions))
           | _ =>
               error
                 "Micro_Rust_Semantic_Navigation: malformed target payload")
        else NONE
    | dest_payload _ = NONE

  fun active_payload kind =
    Option.map (mk_payload kind) (Thread_Data.get active_source)

  fun mark kind target =
    (case active_payload kind of
       SOME payload =>
         Const (\<^const_name>\<open>semantic_navigation_target\<close>, dummyT) $
           payload $ target
     | NONE => target)

  fun annotate kind target body =
    (case active_payload kind of
       SOME payload =>
         Const
           (\<^const_name>\<open>semantic_navigation_annotation\<close>, dummyT) $
           payload $ target $ body
     | NONE => body)

  (*
    A probe type-checks and resolves navigation markers in target, then erases
    the complete target and returns body. It is for syntax whose denotation must
    be observed without inserting that denotation into the generated program.
  *)
  fun probe target body =
    if is_some (Thread_Data.get active_source)
    then
      Const (\<^const_name>\<open>semantic_navigation_probe\<close>, dummyT) $
        target $ body
    else body

  fun target_name (Selected_Target (_, name)) = name

  fun is_primary_for targets name =
    exists
      (fn Selected_Target (Primary, target_name) =>
            target_name = name
        | _ => false)
      targets

  fun ordered_target_names targets =
    let
      val names =
        targets
        |> map target_name
        |> distinct (op =)
      val (primary, secondary) =
        List.partition (is_primary_for targets) names
    in secondary @ primary end

  fun same_positions (left, right) =
    eq_list same_position (left, right)

  fun selected_head target =
    let
      fun strip_abstractions (Abs (_, _, body)) =
            strip_abstractions body
        | strip_abstractions term = term
    in
      (case
          Term.head_of
            (strip_abstractions
              (Term_Position.strip_positions target)) of
         Const (name, _) => SOME name
       | _ => NONE)
    end

  fun resolve_markers _ terms =
    let
      val grouped =
        Unsynchronized.ref
          ([]: (Position.T list * selected_target list) list)

      fun record positions target =
        Unsynchronized.change grouped
          (fn groups =>
            (case AList.lookup same_positions groups positions of
               SOME targets =>
                 AList.update same_positions
                   (positions, targets @ [target]) groups
             | NONE => groups @ [(positions, [target])]))

      fun target_marker
          (Const (name, _) $ payload $ target) =
            if name =
                \<^const_name>\<open>semantic_navigation_target\<close>
            then Option.map (fn data => (data, target))
              (dest_payload payload)
            else NONE
        | target_marker _ = NONE

      fun annotation_marker
          (Const (name, _) $ payload $ target $ body) =
            if name =
                \<^const_name>\<open>semantic_navigation_annotation\<close>
            then Option.map (fn data => (data, target, body))
              (dest_payload payload)
            else NONE
        | annotation_marker _ = NONE

      fun probe_marker
          (Const (name, _) $ target $ body) =
            if name =
                \<^const_name>\<open>semantic_navigation_probe\<close>
            then SOME (target, body)
            else NONE
        | probe_marker _ = NONE

      fun go term =
        (case probe_marker term of
           SOME (target, body) =>
             let
               val _ = go target
             in go body end
         | NONE =>
             (case target_marker term of
                SOME ((kind, positions), target) =>
                  let
                    val resolved_target = go target
                    val _ =
                      (case selected_head resolved_target of
                         SOME name =>
                           record positions
                             (Selected_Target (kind, name))
                       | NONE => ())
                  in resolved_target end
              | NONE =>
                  (case annotation_marker term of
                     SOME ((kind, positions), target, body) =>
                       let
                         val resolved_target = go target
                         val _ =
                           (case selected_head resolved_target of
                              SOME name =>
                                record positions
                                  (Selected_Target (kind, name))
                            | NONE => ())
                         val resolved_body = go body
                       in resolved_body end
                   | NONE =>
                       (case term of
                          function $ argument =>
                            go function $ go argument
                        | Abs (name, typ, body) =>
                            Abs (name, typ, go body)
                        | atom => atom))))

      val resolved = map go terms

      fun marker_constant name =
        name =
          \<^const_name>\<open>semantic_navigation_target\<close> orelse
        name =
          \<^const_name>\<open>semantic_navigation_annotation\<close> orelse
        name =
          \<^const_name>\<open>semantic_navigation_probe\<close>

      val _ =
        if exists
            (Term.exists_subterm
              (fn Const (name, _) => marker_constant name
                | _ => false))
            resolved
        then
          error
            ("Micro_Rust_Semantic_Navigation: internal target marker " ^
              "survived checking")
        else ()

      val _ =
        List.app
          (fn (positions, targets) =>
            if null targets then ()
            else enqueue (Deferred_Targets (positions, targets)))
          (!grouped)
    in resolved end

  fun report_constant ctxt pos name =
    List.app
      (Context_Position.report ctxt pos)
      [Name_Space.markup
         (Consts.space_of (Proof_Context.consts_of ctxt)) name,
       Markup.const]

  fun replay_event ctxt event =
    (case event of
       Deferred_Markup (pos, markup) =>
         Context_Position.report ctxt pos markup
     | Deferred_Targets (positions, targets) =>
         List.app
           (fn pos =>
             List.app (report_constant ctxt pos)
               (ordered_target_names targets))
           positions)

  fun replay ctxt reports =
    List.app (replay_event ctxt) reports

  val _ =
    Context.>>
      (Syntax_Phases.term_check 2 "micro_rust_semantic_navigation"
        resolve_markers)
end
\<close>

end
