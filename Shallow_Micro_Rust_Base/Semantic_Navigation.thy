(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Semantic_Navigation
  imports Main
begin

section\<open>Deferred semantic navigation reports\<close>

text\<open>
Semantic lowering selects HOL constants before the enclosing command knows whether later type
checking and declaration audits will succeed. This module records those selections without changing
the generated term and replays their native Isabelle constant markup only after the caller accepts
the complete elaboration.
\<close>

ML\<open>
signature MICRO_RUST_SEMANTIC_NAVIGATION =
sig
  datatype target_kind = Primary | Secondary
  type reports

  val capture: (unit -> 'a) -> 'a * reports
  val replay: Proof.context -> reports -> unit

  val defer_report:
    Proof.context -> Position.T -> Markup.T -> unit

  val with_source:
    Position.T list -> (unit -> 'a) -> 'a
  val with_source_position:
    Position.T -> (unit -> 'a) -> 'a
  val select:
    target_kind -> string -> unit
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

  val active_targets:
    selected_target list Unsynchronized.ref Thread_Data.var =
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

  fun same_position (left, right) =
    Position.properties_of left = Position.properties_of right

  fun stable_positions positions =
    positions
    |> filter Position.is_reported
    |> distinct same_position

  fun select kind name =
    (case Thread_Data.get active_targets of
       SOME targets =>
         targets := Selected_Target (kind, name) :: !targets
     | NONE => ())

  fun with_source positions action =
    let
      val reported_positions = stable_positions positions
    in
      if null reported_positions orelse
         is_none (Thread_Data.get active_reports)
      then action ()
      else
        let
          val targets =
            Unsynchronized.ref ([]: selected_target list)
          val result =
            Thread_Data.setmp active_targets (SOME targets)
              action ()
          val selected = rev (!targets)
          val _ =
            if null selected then ()
            else
              enqueue
                (Deferred_Targets
                  (reported_positions, selected))
        in result end
    end

  fun with_source_position pos action =
    with_source [pos] action

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
end
\<close>

end
