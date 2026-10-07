(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Expected_Failures
  imports Micro_C_Parsing_Frontend.C_Definition_Generation
begin

section \<open>C command failure transactions\<close>

definition expected_failure_abort ::
    \<open>c_abort \<Rightarrow> ('s, 'v, 'r, c_abort, 'i, 'o) expression\<close> where
  \<open>expected_failure_abort reason \<equiv> c_abort reason\<close>

ML_val\<open>
local
  structure A = Micro_C_Isabelle_C_Adapter

  fun assert message condition =
    if condition then ()
    else error ("C expected-failure test: " ^ message)

  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close

  fun command_transitions source_name thy command_text =
    Outer_Syntax.parse_text thy (K thy)
      (Position.line_file 1 source_name) command_text

  fun run_command source_name command_text state =
    let
      val thy = Toplevel.theory_of state
      val transitions =
        command_transitions source_name thy command_text
    in
      fold (Toplevel.command_exception true) transitions state
    end

  fun expect_failure source_name expected command_text state =
    (case Exn.result (run_command source_name command_text) state of
       Exn.Res _ =>
         error
           ("invalid C command was unexpectedly accepted" ^
             Position.here (Position.file source_name))
     | Exn.Exn exn =>
         if Exn.is_interrupt exn then Exn.reraise exn
         else
           let val message = Runtime.exn_message exn
           in
             if String.isSubstring expected message andalso
                String.isSubstring source_name message
             then message
             else
               error
                 ("unexpected C command diagnostic:\n" ^ message ^
                  "\nexpected: " ^ quote expected ^
                  "\nat: " ^ quote source_name)
           end)

  fun declared state name =
    let
      val thy = Toplevel.theory_of state
      val ctxt = Proof_Context.init_global thy
    in
      can (Proof_Context.read_const {proper = true, strict = true} ctxt) name
    end

  fun require_declared state name =
    assert ("missing declaration " ^ quote name) (declared state name)

  fun require_absent state name =
    assert ("failed command leaked declaration " ^ quote name)
      (not (declared state name))

  val base_theory = \<^theory>
  val base_state = Toplevel.make_state (SOME base_theory)

  val configured_state =
    run_command "config-initial.c"
      ("c_source Config_Probe " ^
       "[abi = lp64-le, compiler = gcc-x86_64] " ^
       cartouche "int first(void) { return 1; }")
      base_state
  val _ = require_declared configured_state "Config_Probe.first"

  fun expect_config_mismatch source_name options function_name =
    let
      val _ =
        expect_failure source_name
          "configuration mismatch while extending unit"
          ("c_source Config_Probe " ^ options ^ " " ^
           cartouche
             ("int " ^ function_name ^ "(void) { return 2; }"))
          configured_state
      val _ = require_declared configured_state "Config_Probe.first"
      val _ =
        require_absent configured_state ("Config_Probe." ^ function_name)
    in
      ()
    end

  val _ =
    expect_config_mismatch "abi-config-mismatch.c"
      "[abi = ilp32-le, compiler = gcc-x86_64]"
      "abi_mismatched"
  val _ =
    expect_config_mismatch "compiler-config-mismatch.c"
      "[abi = lp64-le, compiler = conservative]"
      "compiler_mismatched"
  val _ =
    expect_config_mismatch "addr-config-mismatch.c"
      "[abi = lp64-le, compiler = gcc-x86_64, addr = nat]"
      "addr_mismatched"
  val _ =
    expect_config_mismatch "gv-config-mismatch.c"
      "[abi = lp64-le, compiler = gcc-x86_64, gv = nat]"
      "gv_mismatched"
  val _ =
    expect_config_mismatch "abort-config-mismatch.c"
      ("[abi = lp64-le, compiler = gcc-x86_64, " ^
       "abort = expected_failure_abort]")
      "abort_mismatched"

  val extended_state =
    run_command "config-recovery.c"
      ("c_source Config_Probe " ^
       "[abi = lp64-le, compiler = gcc-x86_64] " ^
       cartouche "int recovered(void) { return 3; }")
      configured_state
  val _ = require_declared extended_state "Config_Probe.first"
  val _ = require_declared extended_state "Config_Probe.recovered"

  val collision_theory =
    Sign.add_consts
      [(Binding.name "clash"
          |> Binding.qualify true "Collision_Probe",
        HOLogic.natT, NoSyn)]
      base_theory
  val collision_state =
    Toplevel.make_state (SOME collision_theory)

  val _ =
    expect_failure "declaration-collision.c" "clash"
      ("c_source Collision_Probe " ^
       "[abi = lp64-le] " ^
       cartouche "int clash(void) { return 4; }")
      collision_state
  val _ = require_declared collision_state "Collision_Probe.clash"
  val _ =
    require_absent collision_state "Collision_Probe.abi_pointer_bits"
  val _ =
    require_absent collision_state "Collision_Probe.abi_long_bits"

  val collision_recovery_state =
    run_command "collision-recovery.c"
      ("c_source Collision_Probe " ^
       "[abi = ilp32-be, compiler = conservative] " ^
       cartouche "int fresh(void) { return 5; }")
      collision_state
  val _ =
    require_declared collision_recovery_state "Collision_Probe.clash"
  val _ =
    require_declared collision_recovery_state "Collision_Probe.fresh"

  val _ =
    expect_failure "selection-manifest-conflict.thy" "mutually exclusive"
      ("c_file Selection_Manifest_Probe " ^
       "[functions = all, " ^
       "manifest = \"Expected_Failure_Manifest.txt\"] " ^
       "\"Expected_Failure_Input.c\"")
      base_state
  val _ =
    require_absent base_state "Selection_Manifest_Probe.selected"
  val _ =
    require_absent base_state
      "Selection_Manifest_Probe.abi_pointer_bits"

  fun expect_pristine_source_failure
      source_name expected unit options function_name =
    let
      val _ =
        expect_failure source_name expected
          ("c_source " ^ unit ^ " " ^ options ^ " " ^
           cartouche
             ("int " ^ function_name ^ "(void) { return 6; }"))
          base_state
      val _ = require_absent base_state (unit ^ "." ^ function_name)
      val _ = require_absent base_state (unit ^ ".abi_pointer_bits")
    in
      ()
    end

  val _ =
    expect_pristine_source_failure "duplicate-abi-option.c"
      "duplicate \"abi\" option" "Duplicate_Abi_Probe"
      "[abi = lp64-le, abi = ilp32-le]" "rejected"
  val _ =
    expect_pristine_source_failure "duplicate-verbose-option.c"
      "duplicate \"verbose\" option" "Duplicate_Verbose_Probe"
      "[verbose, verbose]" "rejected"
  val _ =
    expect_pristine_source_failure "unknown-option.c"
      "unknown option \"mystery\"" "Unknown_Option_Probe"
      "[mystery = value]" "rejected"
  val _ =
    expect_pristine_source_failure "unknown-abi-profile.c"
      "unsupported ABI profile" "Unknown_ABI_Probe"
      "[abi = impossible-profile]" "rejected"
  val _ =
    expect_pristine_source_failure "unknown-compiler-profile.c"
      "unknown compiler profile" "Unknown_Compiler_Probe"
      "[compiler = impossible-profile]" "rejected"
  val _ =
    expect_pristine_source_failure "qualified-unit-name.c"
      "UNIT must be an unqualified Isabelle name" "Qualified.Unit"
      "" "rejected"

  val _ =
    expect_failure "anonymous-unit-name.c"
      "UNIT must be a non-empty, non-anonymous Isabelle name"
      ("c_source _ " ^
       cartouche "int rejected(void) { return 6; }")
      base_state
  val _ = require_absent base_state "rejected"

  val _ =
    expect_failure "manifest-on-c-source.c"
      "manifest is only available for c_file"
      ("c_source Manifest_Source_Probe " ^
       "[manifest = \"Expected_Failure_Manifest.txt\"] " ^
       cartouche "int rejected(void) { return 6; }")
      base_state
  val _ =
    require_absent base_state "Manifest_Source_Probe.rejected"
  val _ =
    require_absent base_state "Manifest_Source_Probe.abi_pointer_bits"

  fun expect_manifest_failure source_name expected unit manifest =
    let
      val _ =
        expect_failure source_name expected
          ("c_file " ^ unit ^ " [manifest = " ^ quote manifest ^ "] " ^
           quote "Expected_Failure_Input.c")
          base_state
      val _ = require_absent base_state (unit ^ ".selected")
      val _ = require_absent base_state (unit ^ ".abi_pointer_bits")
    in
      ()
    end

  val _ =
    expect_manifest_failure "manifest-entry-outside-section.thy"
      "manifest entry outside functions:/types: section"
      "Manifest_Outside_Probe"
      "Expected_Failure_Manifest_Outside.txt"
  val _ =
    expect_manifest_failure "manifest-unknown-section.thy"
      "unknown manifest section"
      "Manifest_Unknown_Section_Probe"
      "Expected_Failure_Manifest_Unknown_Section.txt"
  val _ =
    expect_manifest_failure "manifest-empty-entry.thy"
      "malformed empty manifest entry"
      "Manifest_Empty_Entry_Probe"
      "Expected_Failure_Manifest_Empty_Entry.txt"

  val duplicate_base_state =
    run_command "duplicate-initial.c"
      ("c_source Duplicate_Probe [abi = lp64-le] " ^
       cartouche "int first(void) { return 9; }")
      base_state
  val _ = require_declared duplicate_base_state "Duplicate_Probe.first"
  val _ =
    require_declared duplicate_base_state "Duplicate_Probe.abi_pointer_bits"

  val _ =
    expect_failure "repeated-duplicate-declaration.c"
      "Duplicate_Probe.first"
      ("c_source Duplicate_Probe [abi = lp64-le] " ^
       cartouche
         ("int staged(void) { return 10; }\n" ^
          "int first(void) { return 11; }"))
      duplicate_base_state
  val _ = require_declared duplicate_base_state "Duplicate_Probe.first"
  val _ =
    require_declared duplicate_base_state "Duplicate_Probe.abi_pointer_bits"
  val _ = require_absent duplicate_base_state "Duplicate_Probe.staged"

  val duplicate_recovery_state =
    run_command "duplicate-recovery.c"
      ("c_source Duplicate_Probe [abi = lp64-le] " ^
       cartouche "int recovered(void) { return 12; }")
      duplicate_base_state
  val _ =
    require_declared duplicate_recovery_state "Duplicate_Probe.first"
  val _ =
    require_declared duplicate_recovery_state "Duplicate_Probe.recovered"
  val _ =
    require_absent duplicate_recovery_state "Duplicate_Probe.staged"

  val unsupported_source_name = "unsupported-variadic.c"
  val unsupported_text =
    "int variadic(int first, ...) { return first; }"
  val unsupported_start =
    Position.line_file 1 unsupported_source_name
  val unsupported_input =
    Input.source true unsupported_text
      (Position.range
        (unsupported_start,
         Position.symbol_explode unsupported_text unsupported_start))
  val unsupported_parsed =
    A.parse_translation_unit unsupported_input base_theory
  val unsupported_node =
    (case A.ast unsupported_parsed of
       C_Ast.CTranslUnit0
         ([C_Ast.CFDefExt0 (C_Ast.CFunDef0 (_, _, _, _, node))], _) =>
           node
     | _ => error "expected a variadic function-definition AST")
  val unsupported_position = A.node_position unsupported_node
  val _ =
    assert "unsupported AST node has no reported range"
      (Position.is_reported_range unsupported_position)

  val unsupported_diagnostic =
    expect_failure unsupported_source_name
      "variadic function definition"
      ("c_source Unsupported_Probe " ^
       cartouche unsupported_text)
      base_state
  val _ =
    assert "unsupported-feature diagnostic has no line position"
      (String.isSubstring "line 1" unsupported_diagnostic)
  val _ =
    require_absent base_state "Unsupported_Probe.variadic"
  val _ =
    require_absent base_state "Unsupported_Probe.abi_pointer_bits"

  val rollback_text =
    "int staged_global = 7;\n" ^
    "int broken(void) { return missing_callee(); }"
  val _ =
    expect_failure "late-translation-failure.c"
      "call to undeclared function"
      ("c_source Rollback_Probe " ^
       "[abi = lp64-le, compiler = gcc-x86_64] " ^
       cartouche rollback_text)
      base_state
  val _ = require_absent base_state "Rollback_Probe.staged_global"
  val _ = require_absent base_state "Rollback_Probe.broken"
  val _ =
    require_absent base_state "Rollback_Probe.abi_pointer_bits"
  val _ =
    require_absent base_state "Rollback_Probe.abi_char_is_signed"

  val rollback_recovery_state =
    run_command "late-translation-recovery.c"
      ("c_source Rollback_Probe " ^
       "[abi = ilp32-be, compiler = conservative] " ^
       cartouche "int recovered(void) { return 8; }")
      base_state
  val _ =
    require_declared rollback_recovery_state "Rollback_Probe.recovered"
  val _ =
    require_declared rollback_recovery_state
      "Rollback_Probe.abi_pointer_bits"
  val _ =
    require_absent rollback_recovery_state
      "Rollback_Probe.staged_global"
in
  val _ = ()
end
\<close>

end
