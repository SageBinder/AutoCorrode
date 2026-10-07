(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature FRONTEND_DIAGNOSTICS =
sig
  datatype severity = Error | Warning | Information

  type diagnostic =
    {severity: severity,
     message: string,
     position: Position.T,
     notes: string list}

  val make:
    severity -> Position.T -> string -> string list -> diagnostic
  val render: diagnostic -> string
  val raise_error: diagnostic -> 'a
  val error_at: Position.T -> string -> 'a
  val warning_at: Position.T -> string -> unit
  val information_at: Position.T -> string -> unit
  val unsupported: Position.T -> string -> 'a
  val duplicate:
    string -> string -> Position.T -> Position.T -> 'a
  val protect:
    Position.T -> string -> (unit -> 'a) -> 'a
end

structure Frontend_Diagnostics : FRONTEND_DIAGNOSTICS =
struct

datatype severity = Error | Warning | Information

type diagnostic =
  {severity: severity,
   message: string,
   position: Position.T,
   notes: string list}

fun make severity position message notes : diagnostic =
  {severity = severity,
   message = message,
   position = position,
   notes = notes}

fun severity_prefix Error = ""
  | severity_prefix Warning = "warning: "
  | severity_prefix Information = "information: "

fun render ({severity, message, position, notes}: diagnostic) =
  severity_prefix severity ^ message ^
  Position.here position ^
  String.concat (map (fn note => "\n  note: " ^ note) notes)

fun raise_error diagnostic = error (render diagnostic)

fun error_at position message =
  raise_error (make Error position message [])

fun warning_at position message =
  warning (render (make Warning position message []))

fun information_at position message =
  writeln (render (make Information position message []))

fun unsupported position construct =
  error_at position ("unsupported source construct: " ^ construct)

fun duplicate kind name first_position duplicate_position =
  raise_error
    (make Error duplicate_position
      ("duplicate " ^ kind ^ " " ^ quote name)
      ["the first declaration is here" ^ Position.here first_position])

fun protect position description body =
  (case Exn.capture_body body of
     Exn.Res result => result
   | Exn.Exn exn =>
       if Exn.is_interrupt exn then Exn.reraise exn
       else
         error_at position
           (description ^ ": " ^ Runtime.exn_message exn))

end
