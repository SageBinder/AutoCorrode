(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Parallel_Adapter_Tests
  imports Micro_C_Isabelle_C_Adapter.Micro_C_Isabelle_C_Adapter
begin

section \<open>Parallel direct-AST parsing\<close>

ML_val\<open>
local
  structure A = Micro_C_Isabelle_C_Adapter

  fun assert message condition =
    if condition then ()
    else error ("parallel C adapter test: " ^ message)

  fun source source_name text =
    let
      val start = Position.line_file 1 source_name
      val stop = Position.symbol_explode text start
    in
      Input.source true text (Position.range (start, stop))
    end

  val cases =
    [("parallel-scalar.c",
      "int scalar(int x) { return x + 1; }", 1),
     ("parallel-control.c",
      "int control(int x) {" ^
      "  for (int i = 0; i < 3; i++) x += i;" ^
      "  return x;" ^
      "}", 1),
     ("parallel-aggregate.c",
      "union value { int integer; char byte; };\n" ^
      "int aggregate(union value *p) { return p->integer; }", 2),
     ("parallel-globals.c",
      "int first_global = 1;\n" ^
      "int second_global = 2;\n" ^
      "int globals(void) { return first_global + second_global; }", 3),
     ("parallel-types.c",
      "typedef unsigned long word;\n" ^
      "struct pair { word left; word right; };\n" ^
      "word types(struct pair *p) { return p->left; }", 3),
     ("parallel-switch.c",
      "int choose(int x) {" ^
      "  switch (x) { case 0: return 1; default: return 2; }" ^
      "}", 1)]

  fun parse_one (index, (base_name, text, expected_declarations)) =
    let
      val source_name =
        base_name ^ "-" ^ string_of_int index
      val parsed =
        A.parse_translation_unit (source source_name text) \<^theory>
      val (declarations, node) =
        (case A.ast parsed of C_Ast.CTranslUnit0 data => data)
      val position = A.node_position node
      val recovered = A.source_text parsed position
      val _ =
        assert ("wrong declaration count for " ^ source_name)
          (length declarations = expected_declarations)
      val _ =
        assert ("translation unit has no reported range for " ^ source_name)
          (Position.is_reported_range position)
      val _ =
        assert ("translation unit source recovery failed for " ^ source_name)
          (case recovered of
             SOME recovered_text =>
               Symbol.trim_blanks recovered_text =
                 Symbol.trim_blanks text
           | NONE => false)
    in
      source_name
    end

  val jobs =
    maps
      (fn round =>
        map_index
          (fn (index, test_case) =>
            (round * length cases + index, test_case))
          cases)
      (0 upto 5)

  val futures =
    Future.forks
      {name = "parallel-c-adapter",
       group = NONE,
       deps = [],
       pri = 0,
       interrupts = true}
      (map (fn job => fn () => parse_one job) jobs)

  val completed = Future.joins futures
  val _ =
    assert "not every parallel parser task completed"
      (length completed = length jobs)
  val _ =
    assert "parallel parser tasks reused a source identity"
      (length (distinct (op =) completed) = length completed)
in
  val _ = ()
end
\<close>

end
