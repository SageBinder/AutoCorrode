(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

theory Parser_Adapter_Tests
  imports Micro_C_Isabelle_C_Adapter.Micro_C_Isabelle_C_Adapter
begin

ML_val\<open>
local
  open Micro_C_Isabelle_C_Adapter

  fun assert message condition =
    if condition then ()
    else error ("C adapter test: " ^ message)

  fun source text =
    let
      val start = \<^here>
      val stop = Position.symbol_explode text start
    in
      Input.source true text (Position.range (start, stop))
    end

  fun parse text =
    parse_function (source text) \<^theory>

  fun offset pos =
    the (Position.offset_of pos)

  fun reported_range message pos =
    assert message (Position.is_reported_range pos)

  fun rejects label fragment text =
    ((parse text;
      error ("C adapter test: accepted " ^ label))
     handle ERROR message =>
       assert
         ("wrong rejection for " ^ label ^ ": " ^ message)
         (String.isSubstring fragment message))

  val constant = parse "int constant(void) { return 42; }"
  val _ =
    (case (#parameters constant, #body constant) of
       (VoidParameters parameter_pos,
        IntLiteral
          {value, spelling, representation = Decimal,
           has_suffix = false, position}) =>
         (assert "constant value" (value = 42);
          assert "constant spelling" (spelling = "42");
          reported_range "void parameter range" parameter_pos;
          reported_range "literal range" position)
     | _ => error "C adapter test: wrong constant normalization")

  val identity = parse "int identity(int x) { return x; }"
  val _ =
    (case (#name identity, #parameters identity, #body identity) of
       (SOME ("identity", name_pos),
        NamedParameters
          {parameters =
            [{type_spec = {kind = PlainInt, position = type_pos},
              name = SOME ("x", parameter_name_pos),
              position = parameter_pos,
              plain_declarator = true}],
           variadic = false,
           position = clause_pos},
        Identifier {name = "x", position = identifier_pos}) =>
         (List.app
            (reported_range "identity positioned node")
            [#position identity, name_pos, type_pos, parameter_name_pos,
             parameter_pos, clause_pos, #return_position identity,
             identifier_pos];
          assert "identity source order"
            (offset (#position identity) <= offset name_pos andalso
             offset name_pos < offset parameter_name_pos andalso
             offset parameter_name_pos < offset (#return_position identity) andalso
             offset (#return_position identity) <= offset identifier_pos))
     | _ => error "C adapter test: wrong identity normalization")

  val multi_specifier =
    parse
      ("unsigned long long wide_identity(unsigned long long value) {" ^
       " return value; }")
  val _ =
    (case
      (#return_type multi_specifier,
       #parameters multi_specifier,
       #body multi_specifier) of
       ({kind = UnsupportedType _, ...},
        NamedParameters
          {parameters =
            [{type_spec = {kind = UnsupportedType _, ...}, ...}],
           variadic = false,
           ...},
        Identifier {name = "value", ...}) => ()
     | _ => error "C adapter test: multi-specifier baseline normalization failed")

  val addition = parse "int add(int x, int y) { return x + y; }"
  val _ =
    (case #body addition of
       Add
         {left = Identifier {name = "x", position = left_pos},
          right = Identifier {name = "y", position = right_pos},
          position,
          operator_position} =>
         (List.app
            (reported_range "addition positioned node")
            [left_pos, right_pos, position, operator_position];
          assert "addition span"
            (offset position = offset left_pos andalso
             the (Position.end_offset_of position) =
               the (Position.end_offset_of right_pos));
          assert "operator lies within expression"
            (offset position <= offset operator_position andalso
             offset operator_position <
               the (Position.end_offset_of position)))
     | _ => error "C adapter test: wrong addition normalization")

  val nested = parse "int nested(int x, int y) { return x + 1 + y; }"
  val _ =
    (case #body nested of
       Add
         {left =
            Add
              {left = Identifier {name = "x", ...},
               right = IntLiteral {value = 1, ...},
               ...},
          right = Identifier {name = "y", ...},
          ...} => ()
     | _ => error "C adapter test: addition association was not preserved")

  val parenthesized =
    parse "int grouped(int x, int y) { return x + (1 + y); }"
  val _ =
    (case #body parenthesized of
       Add
         {left = Identifier {name = "x", ...},
          right =
            Add
              {left = IntLiteral {value = 1, ...},
               right = Identifier {name = "y", ...},
               ...},
          ...} => ()
     | _ => error "C adapter test: parenthesized association was not preserved")

  val _ =
    rejects "multiple functions" "multiple external declarations"
      "int first(void) { return 0; } int second(void) { return 1; }"
  val _ =
    rejects "global declaration" "expected one function definition"
      "int global;"
  val _ =
    rejects "local declaration" "locals and additional statements"
      "int local(void) { int x = 0; return x; }"
  val _ =
    rejects "function call" "function calls are not supported"
      "int caller(void) { return callee(); }"
  val _ =
    rejects "other operator" "only the + operator is supported"
      "int subtract(int x, int y) { return x - y; }"
  val _ =
    rejects "unary operator" "unary operators are not supported"
      "int negate(int x) { return -x; }"
  val _ =
    rejects "return without value" "return without a value"
      "int empty_return(void) { return; }"
in
  val _ = ()
end
\<close>

end
