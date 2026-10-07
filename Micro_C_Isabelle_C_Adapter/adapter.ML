(* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT *)

signature MICRO_C_ISABELLE_C_ADAPTER =
sig
  type parsed_translation_unit

  val parse_translation_unit:
    Input.source -> theory -> parsed_translation_unit
  val ast:
    parsed_translation_unit ->
    C_Ast.nodeInfo C_Ast.cTranslationUnit
  val node_position: C_Ast.nodeInfo -> Position.T
  val source_text:
    parsed_translation_unit -> Position.T -> string option
end

structure Micro_C_Isabelle_C_Adapter : MICRO_C_ISABELLE_C_ADAPTER =
struct

datatype parsed_translation_unit =
  Parsed_Translation_Unit of
    {source: Input.source,
     ast: C_Ast.nodeInfo C_Ast.cTranslationUnit}

fun decoded_position position =
  (case C11_Ast_Lib.toPos_positiona position of
     pos :: _ => pos
   | [] => Position.none)

fun advance_position count pos =
  Position.symbol_explode
    (String.implode (replicate count #"x")) pos

fun node_position node =
  let
    val (first, _) = C_Ast.p_first_of_NodeInfo node
    val (last, raw_length) = C_Ast.p_last_of_NodeInfo node
    val start = decoded_position first
    val last_start = decoded_position last
    val length =
      Int.max (0, IntInf.toInt raw_length)
      handle Overflow => 0
    val stop = advance_position length last_start
  in
    if start = Position.none orelse stop = Position.none
    then start
    else Position.range_position (start, stop)
  end

fun ast (Parsed_Translation_Unit {ast, ...}) = ast

fun source_text (Parsed_Translation_Unit {source, ...}) pos =
  let
    val (content, content_position) = Input.source_content source
  in
    (case
      (Position.offset_of content_position,
       Position.offset_of pos,
       Position.end_offset_of pos) of
       (SOME source_start, SOME range_start, SOME range_stop) =>
         let
           val symbols = Symbol.explode content
           val left = range_start - source_start
           val count = range_stop - range_start
         in
           if 0 <= left andalso 0 <= count andalso
              left + count <= length symbols
           then
             SOME
               (symbols
                |> drop left
                |> take count
                |> String.concat)
           else NONE
         end
     | _ => NONE)
  end

fun parse_translation_unit source thy =
  let
    val parsed_context =
      C_Module.exec_eval source (Context.Theory thy)
    val parsed_theory = Context.theory_of parsed_context
  in
    Parsed_Translation_Unit
      {source = source,
       ast = get_CTranslUnit parsed_theory}
  end

end
