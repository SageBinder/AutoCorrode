(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory C_Parser_Command_Tests
  imports C_Parser_Test_Utils
begin

section \<open>Command surface and generated artifacts\<close>

c_source Inline [types = [kept_record], functions = [kept]] \<open>
  struct kept_record { unsigned int value; };
  struct dropped_record { unsigned int value; };
  unsigned int kept(unsigned int x) { return x + 1; }
  unsigned int dropped(unsigned int x) { return x + 2; }
\<close>

c_file FileInline [types = [kept_record], functions = [kept]] "Command_Fixture.c"
c_file FileManifest [manifest = "Command_Selection.txt"] "Command_Fixture.c"

c_file Split [manifest = "Command_Types.txt"] "Command_Fixture.c"
c_file Split [manifest = "Command_Functions.txt"] "Command_Fixture.c"

c_source NoFunctions [functions = []] \<open>
  unsigned int omitted(void) { return 7; }
\<close>

c_source NoTypes [types = [], functions = []] \<open>
  struct omitted { unsigned int value; };
\<close>

c_source Extension \<open>unsigned int first(void) { return 1; }\<close>
c_source Extension \<open>unsigned int second(void) { return 2; }\<close>

ML_val \<open>
  val _ = List.app (fn unit =>
    let
      val _ = C_Parser_Test.check_definitions \<^context> unit ["kept"]
      val _ = C_Parser_Test.absent \<^context> (unit ^ ".dropped")
      val _ = C_Parser_Test.absent_type \<^context> (unit ^ ".dropped_record")
      val _ = Proof_Context.get_thms \<^context> (unit ^ ".kept_record.record_simps")
    in () end) ["Inline", "FileInline", "FileManifest"]
  val _ = C_Parser_Test.check_definitions \<^context> "Split" ["kept", "read_record"]
  val _ = C_Parser_Test.absent \<^context> "NoFunctions.omitted"
  val _ = C_Parser_Test.absent_type \<^context> "NoTypes.omitted"
  val _ = C_Parser_Test.check_definitions \<^context> "Extension" ["first", "second"]
  val _ = C_Parser_Test.assert "loaded C fixtures are not current"
    (Resources.loaded_files_current \<^theory>)
  val _ = C_Parser_Test.evaluates \<^context> "Inline.kept 41" "Success 42"
  val _ = C_Parser_Test.evaluates \<^context> "FileInline.kept 41" "Success 42"
  val _ = C_Parser_Test.evaluates \<^context> "FileManifest.kept 41" "Success 42"
  val _ = C_Parser_Test.evaluates \<^context> "Split.kept 41" "Success 42"
\<close>

section \<open>Duplicate options and generated namespace collisions\<close>

ML_val \<open>
  val duplicate_options =
    [("abi", "lp64-le"), ("compiler", "default"), ("addr", "nat"),
     ("gv", "nat"), ("abort", "c_abort"), ("types", "all"), ("functions", "all")]
  val _ = List.app (fn (name, value) =>
    C_Parser_Test.rejects ("duplicate " ^ name) ["duplicate " ^ quote name ^ " option"]
      (fn () => C_Parser_Test.translate \<^theory> ("duplicate-" ^ name ^ ".thy")
        "Invalid" ("[" ^ name ^ " = " ^ value ^ ", " ^ name ^ " = " ^ value ^ "]")
        "unsigned int probe(void) { return 1; }") |> K ()) duplicate_options

  val _ = C_Parser_Test.rejects "reserved ABI name"
    ["abi_pointer_bits", "duplicate"]
    (fn () => C_Parser_Test.translate \<^theory> "reserved-name.c" "Reserved" ""
      "unsigned int abi_pointer_bits(void) { return 1; }")
  val _ = C_Parser_Test.absent \<^context> "Reserved.abi_pointer_bits"

  val _ = C_Parser_Test.rejects "existing generated record" ["kept_record", "already exists"]
    (fn () => C_Parser_Test.translate \<^theory> "record-collision.c" "Inline" ""
      "struct kept_record { unsigned int other; };")
  val _ = C_Parser_Test.absent \<^context> "Inline.kept_record_other"

  val _ = C_Parser_Test.rejects "selection syntax" ["expected selection list or all"]
    (fn () => C_Parser_Test.translate \<^theory> "selection-syntax.thy" "Invalid"
      "[functions = kept]" "unsigned int kept(void) { return 1; }")
\<close>

section \<open>Local theory invocation\<close>

locale c_command_test_locale =
  fixes marker :: 'marker
begin

c_source Local \<open>
  struct pair { unsigned int value; };
  unsigned int answer(void) { return 42; }
\<close>

thm Local.pair.record_simps Local.answer_def

ML_val \<open>
  val _ = C_Parser_Test.checked_definition \<^context> "Local.answer"
\<close>

end

end
