(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Legacy_Parser_Isolation_Tests
  imports Shallow_Micro_Rust
begin

section\<open>Legacy parser isolation\<close>

ML_val\<open>
  val legacy_source = "\<lbrakk> skip \<rbrakk>"

  val _ =
    (case Exn.result (Syntax.parse_term \<^context>) legacy_source of
       Exn.Res _ =>
         error "legacy Micro Rust embedding syntax is available in the shallow session"
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn else ())
\<close>

end
