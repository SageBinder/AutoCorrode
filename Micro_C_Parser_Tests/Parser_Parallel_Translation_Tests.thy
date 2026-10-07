(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Parallel_Translation_Tests
  imports Micro_C_Parsing_Frontend.C_Definition_Generation
begin

section \<open>Parallel translation with isolated target configurations\<close>

ML_val\<open>
local
  fun assert message condition =
    if condition then ()
    else error ("parallel C translation test: " ^ message)

  fun cartouche text = Symbol.open_ ^ text ^ Symbol.close

  fun run_command source_name command_text =
    let
      val thy = \<^theory>
      val transitions =
        Outer_Syntax.parse_text thy (K thy)
          (Position.line_file 1 source_name) command_text
      val _ =
        assert ("expected one command in " ^ source_name)
          (length transitions = 1)
      val state =
        fold (Toplevel.command_exception true) transitions
          (Toplevel.make_state (SOME thy))
    in
      Toplevel.theory_of state
    end

  val translations =
    [("parallel-translate-ilp32.c",
      "Parallel_ILP32",
      "parallel_left",
      "c_source Parallel_ILP32 " ^
        "[abi = ilp32-le, compiler = gcc-x86_64] " ^
        cartouche
          "long parallel_left(long x) { return x + 1; }",
      32, 32, true, false),
     ("parallel-translate-lp64be.c",
      "Parallel_LP64_BE",
      "parallel_right",
      "c_source Parallel_LP64_BE " ^
        "[abi = lp64-be, compiler = conservative] " ^
        cartouche
          "long parallel_right(long x) { return x - 1; }",
      64, 64, false, true),
     ("parallel-translate-llp64.c",
      "Parallel_LLP64",
      "parallel_llp64",
      "c_source Parallel_LLP64 " ^
        "[abi = llp64-le, compiler = clang-aarch64] " ^
        cartouche
          "long parallel_llp64(long x) { return x * 2; }",
      64, 32, false, false),
     ("parallel-translate-ilp32be.c",
      "Parallel_ILP32_BE",
      "parallel_ilp32be",
      "c_source Parallel_ILP32_BE " ^
        "[abi = ilp32-be, compiler = clang-x86_64] " ^
        cartouche
          "long parallel_ilp32be(long x) { return x / 2; }",
      32, 32, true, true)]

  val futures =
    Future.forks
      {name = "parallel-c-translation",
       group = NONE,
       deps = [],
       pri = 0,
       interrupts = true}
      (map
        (fn (source_name, unit, function_name, command,
             pointer_bits, long_bits,
             char_is_signed, big_endian) =>
          fn () =>
            (unit, function_name, run_command source_name command,
             pointer_bits, long_bits, char_is_signed, big_endian))
        translations)

  val results = Future.joins futures

  fun definition_rhs thy name =
    let
      val ctxt = Proof_Context.init_global thy
      val theorem = Proof_Context.get_thm ctxt (name ^ "_def")
    in
      snd (Logic.dest_equals (Thm.prop_of theorem))
    end

  fun definition_nat thy name =
    HOLogic.dest_nat (definition_rhs thy name)

  fun definition_bool thy name =
    let val rhs = definition_rhs thy name
    in
      if rhs aconv \<^term>\<open>True\<close> then true
      else if rhs aconv \<^term>\<open>False\<close> then false
      else error ("expected Boolean definition for " ^ quote name)
    end

  fun declared thy name =
    let val ctxt = Proof_Context.init_global thy
    in
      can (Proof_Context.read_const {proper = true, strict = true} ctxt) name
    end

  fun check_result
      (unit, function_name, thy,
       pointer_bits, long_bits, char_is_signed, big_endian) =
    let
      val prefix = unit ^ "."
      val _ =
        assert (unit ^ " did not generate its function")
          (declared thy (prefix ^ function_name))
      val _ =
        assert (unit ^ " has the wrong pointer width")
          (definition_nat thy (prefix ^ "abi_pointer_bits") = pointer_bits)
      val _ =
        assert (unit ^ " has the wrong long width")
          (definition_nat thy (prefix ^ "abi_long_bits") = long_bits)
      val _ =
        assert (unit ^ " has the wrong plain-char signedness")
          (definition_bool thy (prefix ^ "abi_char_is_signed") =
            char_is_signed)
      val _ =
        assert (unit ^ " has the wrong endianness")
          (definition_bool thy (prefix ^ "abi_big_endian") = big_endian)
      val foreign_units =
        map (fn (_, foreign, _, _, _, _, _, _) => foreign) translations
        |> filter_out (fn foreign => foreign = unit)
      val _ =
        List.app
          (fn foreign =>
            assert
              (unit ^ " result leaked declarations from " ^ foreign)
              (not (declared thy (foreign ^ ".abi_pointer_bits"))))
          foreign_units
    in
      ()
    end

  val _ =
    assert "not every parallel translation completed"
      (length results = length translations)
  val _ = List.app check_result results
in
  val _ = ()
end
\<close>

end
