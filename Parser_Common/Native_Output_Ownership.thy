theory Native_Output_Ownership
  imports Main
begin

text\<open>
Temporary native output hooks and tool hook publication share one process-lifetime owner.
Temporary work may overlap and join child scopes; publication waits for their restored hooks.
The publication callback is a short handler update, never generation, output forwarding or
a thread join. A waiting publisher does not close admission to an active parent's child.

Native imports and this export give theory and bootstrap consumers the same state. This
foundation is loaded once per process; changing it requires an idle fresh process. Hook writers
outside this protocol must enclose temporary scopes properly. No handler is captured at load.
\<close>

ML_export\<open>
signature NATIVE_OUTPUT_OWNERSHIP =
sig
  val quiet_results: (unit -> 'a) -> 'a
  val with_temporary_hooks: (unit -> 'a) -> 'a
  val publish_hooks: (unit -> 'a) -> 'a
end

structure Native_Output_Ownership : NATIVE_OUTPUT_OWNERSHIP =
struct
  val temporary: unit Thread_Data.var = Thread_Data.var ()
  val publishing: unit Thread_Data.var = Thread_Data.var ()
  val temporary_count = Synchronized.var "native output hook ownership" 0

  fun with_temporary_hooks action =
    if is_some (Thread_Data.get publishing) then
      error "Native_Output_Ownership: temporary hooks inside publication"
    else if is_some (Thread_Data.get temporary) then action ()
    else
      Thread_Attributes.uninterruptible_body (fn run =>
        let
          val _ = Synchronized.change temporary_count (fn count => count + 1)
          val result = Exn.capture0 (run (Thread_Data.setmp temporary (SOME ()) action)) ()
          val _ = Synchronized.change temporary_count (fn count => count - 1)
        in Exn.release result end)

  fun publish_hooks action =
    if is_some (Thread_Data.get temporary) then
      error "Native_Output_Ownership: publication inside temporary hooks"
    else if is_some (Thread_Data.get publishing) then
      error "Native_Output_Ownership: recursive publication"
    else
      Synchronized.guarded_access temporary_count (fn count =>
        if count <> 0 then NONE
        else SOME
          (Thread_Attributes.uninterruptible_body (fn _ =>
             Exn.capture0 (Thread_Data.setmp publishing (SOME ()) action) ()), count))
      |> Exn.release

  local
    type channels =
      {writeln: string list -> unit, urgent: string list -> unit,
       state: string list -> unit, tracing: string list -> unit, system: string list -> unit}

    val quiet: unit Thread_Data.var = Thread_Data.var ()
    val owners = Synchronized.var "native quiet results" (0, NONE: channels option)

    fun route output chunks =
      if is_some (Thread_Data.get quiet) then () else output chunks

    (* Standalone semantic channels can delegate to writeln; keep that delegation audible. *)
    fun semantic output chunks = Thread_Data.setmp quiet NONE output chunks

    fun enter () =
      Synchronized.change owners (fn (count, saved) =>
        if count > 0 then (count + 1, saved)
        else
          let
            val channels =
              {writeln = !Private_Output.writeln_fn,
               urgent = !Private_Output.writeln_urgent_fn,
               state = !Private_Output.state_fn,
               tracing = !Private_Output.tracing_fn,
               system = !Private_Output.system_message_fn}
            val _ = Private_Output.writeln_fn := route (#writeln channels)
            val _ = Private_Output.writeln_urgent_fn := route (#urgent channels)
            val _ = Private_Output.state_fn := semantic (#state channels)
            val _ = Private_Output.tracing_fn := semantic (#tracing channels)
            val _ = Private_Output.system_message_fn := semantic (#system channels)
          in (1, SOME channels) end)

    fun leave () =
      Synchronized.change owners (fn (count, saved) =>
        if count > 1 then (count - 1, saved)
        else
          let
            val channels = the saved
            val _ = Private_Output.writeln_fn := #writeln channels
            val _ = Private_Output.writeln_urgent_fn := #urgent channels
            val _ = Private_Output.state_fn := #state channels
            val _ = Private_Output.tracing_fn := #tracing channels
            val _ = Private_Output.system_message_fn := #system channels
          in (0, NONE) end)
  in
    (* No lock covers the action or forwarding. Unmarked physical threads keep their channels;
       futures do not inherit the marker. The last owner forgets every saved predecessor. *)
    fun quiet_results action =
      with_temporary_hooks (fn () =>
        if is_some (Thread_Data.get quiet) then action ()
        else
          Thread_Attributes.uninterruptible_body (fn run =>
            let
              val _ = enter ()
              val result = Exn.capture0 (run (Thread_Data.setmp quiet (SOME ()) action)) ()
              val _ = leave ()
            in Exn.release result end))
  end
end
\<close>

end
