theory Parser_Type_Alias_Syntax_Tests
  imports Parser_Test_Utils
begin

ML\<open>
local
  open URust_AST
  val ctxt = \<^context>
  fun require label condition =
    if condition then () else error ("alias syntax probe: " ^ label)
  fun source text = Parser_Lex_Util.text_source text
  fun alias text =
    (case URust_Parser.parse_type_alias_source ctxt (source text) of
       SOME item => item
     | NONE => error "alias syntax probe: missing item")
  fun expression text =
    (case URust_Parser.parse_source ctxt (source text) of
       SOME ast => ast
     | NONE => error "alias syntax probe: missing expression")
  fun reject label parse text =
    (case Exn.result (fn () => parse text) () of
       Exn.Exn _ => ()
     | Exn.Res _ => error ("alias syntax probe: accepted " ^ label))
  fun alias_roundtrip text =
    let
      val original = alias text
      val options = URust_Printer.serialized_options
      val rendered = URust_Printer.string_of_type_alias options original
      val reparsed = alias rendered
    in
      require ("alias tokens changed for " ^ text)
        (URust_Printer.tokens_of_type_alias options original =
         URust_Printer.tokens_of_type_alias options reparsed);
      require ("alias printer is unstable for " ^ text)
        (rendered = URust_Printer.string_of_type_alias options reparsed)
    end
  fun expression_roundtrip text =
    let
      val original = expression text
      val options = URust_Printer.serialized_options
      val rendered = URust_Printer.string_of_expr options original
      val reparsed = expression rendered
      val human = URust_Printer.string_of_expr URust_Printer.human_options original
      val human_reparsed = expression human
    in
      require ("cast tokens changed for " ^ text)
        (URust_Printer.tokens_of_expr options original =
         URust_Printer.tokens_of_expr options reparsed);
      require ("human printer is unstable for " ^ text)
        (human = URust_Printer.string_of_expr URust_Printer.human_options human_reparsed)
    end
  val _ =
    List.app alias_roundtrip
      ["type Width = u16;",
       "type OtherWidth = Width;",
       "type Pair<T> = (T, T);",
       "type Pair<T, U,> = (T, U);",
       "type Ptr<T> = *const T;",
       "type MutPtr<T> = *mut T;",
       "type Nested<T> = Option<*const Pair<T, T>>;",
       "type Deep<T> = Option<Option<Option<T>>>;",
       "type Qualified = types::Width;",
       "type Mapped<T> = containers::Array<T, 32>;",
       "type Group<T> = (T);",
       "type OneTuple<T> = (T,);",
       "type Array = [u8; 32];",
       "type NestedArray<T> = Option<Option<[T; 32]>>;",
       "type Escaped = \<tau>\<open>nat\<close>;",
       "/* outer /* nested */ comment */ type Comments<T> = /* rhs */ T;"]
  val _ =
    List.app (reject "malformed alias" alias)
      ["", "type Width = u16", "type = u16;", "type Width u16;",
       "type Width = ;", "type Pair<> = u16;", "type Pair<T: Bound> = T;",
       "type Pair<T = u8> = T;", "type Pair<const N> = u8;",
       "type Pair<T> = Option<T>;;", "type Width = u16; type Extra = u8;",
       "struct Width;", "fn width() {}"]
  val _ =
    List.app expression_roundtrip
      ["value as u8", "value as i32", "value as *const u16",
       "value as *mut u32", "value as Width", "value as types::Width",
       "value as Identity<u16>", "value as Pair<u8, u16>",
       "value as Identity<Identity<u16>>",
       "value as Identity<Identity<Identity<u16>>>",
       "value as Ptr<Option<u16>>",
       "value as *const Identity<u16>",
       "value as &&u8",
       "value as Identity<&&u8>",
       "value as (u16)", "value as (u8, u16)", "value as [u8; 4]",
       "value as bool", "value as i16", "value as u128",
       "value as Identity<u16> as Identity<u32>",
       "(value as u16) < limit",
       "(value as Width) << shift",
       "(value + other as u16) < limit",
       "value as (u16) < limit",
       "value as Identity<u16> < limit",
       "value as Identity<u16> << shift",
       "value as Identity<Identity<u16>> >> shift",
       "value as Identity<u16>> limit",
       "value as Identity<u16>>= limit",
       "value as Identity<Identity<u16>>>= limit",
       "left >> right", "left << right",
       "left >>= right", "left <<= right",
       "if value as Identity<u16> < limit { left } else { right }",
       "if (value as u16) < limit { left } else { right }",
       "[value as Identity<u16>; 2 as usize]"]
  val _ =
    List.app (reject "ambiguous or malformed cast" expression)
      ["value as u16 < limit", "value as u16 << shift",
       "value as Width < limit", "value as Width << shift",
       "if value as u16 < limit { left } else { right }",
       "value as Identity<>", "value as Identity<u16",
       "[value; 2 as Width]", "[value; 2 as Identity<usize>]",
       "[value; 2 as (usize)]", "type Width = u16;"]
  val recovered = alias "type Recovered<T> = Option<Option<T>>;"
  val _ = require "parser state did not recover" (#1 (type_alias_name recovered) = "Recovered")
  val recovered_expression = expression "left >> right"
  val _ =
    (case recovered_expression of
       UE_Bin (Shr, _, _, _) => ()
     | _ => error "alias syntax probe: expression shift changed after recovery")
  val positions_source =
    Parser_Lex_Util.positioned_content_source
      "type Positioned<T, U> = Pair<T, U>;"
      (Position.make0 23 5000 0 "" "" "type-alias-syntax-positions")
  val positions_item = the (URust_Parser.parse_type_alias_source ctxt positions_source)
  fun offsets pos = (Position.offset_of pos, Position.end_offset_of pos)
  val _ =
    require "alias parameter source ranges changed"
      (map (offsets o #2) (type_alias_parameters positions_item) =
        [(SOME 5016, SOME 5017), (SOME 5019, SOME 5020)])
  val _ =
    require "alias complete span changed"
      (offsets (type_alias_item_position positions_item) =
        (SOME 5000, SOME 5035))
  val _ =
    (case expression "value as Identity<u16>" of
       UE_Cast (_, SCT_Type (Path_Type
         ([Rust_Type_Path_Segment
           ("Identity", _, SOME [Rust_Type_Argument (Primitive_Type (DPT_U16, _))], _)],
           _)), _) => ()
     | _ => error "alias syntax probe: cast did not use shared type AST")
  val _ =
    (case expression "value as *const u16" of
       UE_Cast (_, target as SCT_Primitive
         (CT_RawPointer (RPM_Const, UT_U16), _), _) =>
           require "legacy primitive position API disappeared"
             (is_some (source_cast_target_type_position target))
     | _ => error "alias syntax probe: primitive compatibility AST changed")
  val _ =
    URust_Printer_Output.pretty_human_type_alias_with_reparse
      (fn input => ignore (URust_Parser.parse_type_alias_source ctxt input))
      (alias "type Printable<T> = (T, T);")
    |> ignore
in
  val _ = writeln "W2 alias syntax, shared casts, positions, recovery and printer probes passed"
end
\<close>

end
