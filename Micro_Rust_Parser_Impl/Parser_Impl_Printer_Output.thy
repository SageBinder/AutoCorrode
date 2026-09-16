theory Parser_Impl_Printer_Output
  imports
    Parser_Impl_Printer
    Parser_Utils
begin

section\<open> Report-transferred printer output \<close>

text\<open>
Human expression and datatype output uses the canonical generated source and lexeme ranges
finalized by the pure printer core. This adapter reparses that source through a caller-supplied
new-frontend callback, captures its PIDE reports, removes synthetic position properties, and
attaches the transferred markup to individual lexeme nodes before the ordinary Pretty layout
chooses line breaks. Expression replay preserves unrelated source-language reports required by the
declaration command; datatype replay is a private validation pass and forwards only reports that
belong to the generated probe.
\<close>

ML\<open>
signature URUST_PRINTER_OUTPUT =
sig
  val pretty_human_expr_with_reparse:
    (Input.source -> unit) -> URust_AST.ur_expr -> Pretty.T
  val pretty_human_datatype_with_reparse:
    (Input.source -> unit) ->
      URust_AST.urust_datatype -> Pretty.T
end

local

datatype captured_report =
  Captured_Report of
    {start_offset: int,
     end_offset: int,
     markup: Markup.T,
     body: XML.body}

val report_capture_lock =
  Synchronized.var "uRust pretty-printer report capture" ()

fun tree_uses_position_id expected tree =
  (case tree of
     XML.Elem ((_, properties), body) =>
       Position.id_of (Position.of_properties properties) =
         SOME expected orelse
       exists (tree_uses_position_id expected) body
   | XML.Text _ => false)

fun capture_reports forward_other probe_id action =
  Synchronized.change_result report_capture_lock (fn () =>
    let
      val captured =
        Synchronized.var
          "uRust pretty-printer captured reports"
          ([]: string list)
      val previous = ! Private_Output.report_fn
      fun capture chunks =
        let
          val trees = maps YXML.parse_body chunks
          val (probe_trees, other_trees) =
            List.partition (tree_uses_position_id probe_id) trees
          val probe_chunks =
            map (YXML.string_of_body o single) probe_trees
          val other_chunks =
            map (YXML.string_of_body o single) other_trees
          val _ =
            Synchronized.change captured
              (fn reports => rev probe_chunks @ reports)
          val _ =
            if not forward_other orelse null other_chunks then ()
            else previous other_chunks
        in
          ()
        end
      val result =
        Unsynchronized.setmp Private_Output.report_fn capture action ()
    in
      ((result, rev (Synchronized.value captured)), ())
    end)

fun reports_for_id probe_id chunks =
  let
    val def_id_name = Markup.def_name Markup.idN
    val def_position_names =
      map Markup.def_name
        [Markup.lineN, Markup.end_lineN, Markup.offsetN,
         Markup.end_offsetN, Markup.labelN, Markup.fileN,
         Markup.idN]

    fun clean_markup (name, properties) =
      let
        val synthetic_definition =
          Properties.get properties def_id_name = SOME probe_id
        fun keep property =
          not (Markup.position_property property) andalso
          not
            (synthetic_definition andalso
              member (op =) def_position_names (#1 property))
      in
        (name, filter keep properties)
      end

    fun collect (XML.Elem ((name, properties), body)) reports =
          let
            val position = Position.of_properties properties
          in
            (case
                (Position.id_of position,
                 Position.offset_of position,
                 Position.end_offset_of position) of
               (SOME id, SOME start_offset, SOME end_offset) =>
                 if id = probe_id andalso start_offset < end_offset
                 then
                   Captured_Report
                     {start_offset = start_offset,
                      end_offset = end_offset,
                      markup = clean_markup (name, properties),
                      body = body} :: reports
                 else fold collect body reports
             | _ => fold collect body reports)
          end
      | collect (XML.Text _) reports = reports
  in
    rev
      (fold collect
        (maps YXML.parse_body chunks)
        [])
  end

fun report_markup
    (Captured_Report {markup, body, ...}) pretty =
  let
    val ((begin_markup, begin_body), end_markup) =
      YXML.output_markup_elem markup
    val output_markup =
      (begin_markup ^ YXML.string_of_body body ^ begin_body,
       end_markup)
  in
    Pretty.make_block
      {markup = output_markup,
       open_block = false,
       consistent = false,
       indent = 0}
      [pretty]
  end

fun report_covers left right
    (Captured_Report {start_offset, end_offset, ...}) =
  start_offset <= left andalso right <= end_offset

fun report_overlaps left right
    (Captured_Report {start_offset, end_offset, ...}) =
  start_offset < right andalso left < end_offset

fun report_boundaries left right reports =
  let
    fun boundaries
        (Captured_Report {start_offset, end_offset, ...}) values =
      Int.max (left, start_offset) ::
      Int.min (right, end_offset) :: values
  in
    fold boundaries
      (filter (report_overlaps left right) reports)
      [left, right]
    |> sort int_ord
    |> distinct (op =)
  end

fun symbol_slice symbols first count =
  take count (drop first symbols)
  |> String.concat

fun consecutive_pairs [] = []
  | consecutive_pairs [_] = []
  | consecutive_pairs (left :: right :: rest) =
      (left, right) :: consecutive_pairs (right :: rest)

fun reported_lexeme reports
    ({text, range = (left, right), fallback}:
      URust_Printer_Document.lexeme) =
  let
    val symbols = Symbol.explode text
    val boundaries = report_boundaries left right reports

    fun segment (segment_left, segment_right) =
      let
        val segment_text =
          symbol_slice symbols
            (segment_left - left)
            (segment_right - segment_left)
        val active =
          filter (report_covers segment_left segment_right) reports
        val base =
          if null reports
          then fallback segment_text
          else Pretty.str segment_text
      in
        fold_rev report_markup active base
      end
  in
    boundaries
    |> consecutive_pairs
    |> map segment
    |> Pretty.block0
  end

fun pretty_human_document_with_reparse
    forward_other reparse document =
  let
    val text =
      URust_Printer_Document.probe_text document
    val probe_id = Value.print_int (serial ())
    val probe_start =
      Position.make0 1 1 0 "" "" probe_id
    val probe_stop =
      Position.symbol_explode text probe_start
    val source =
      Parser_Lex_Util.delimited_content_source
        text (Position.range (probe_start, probe_stop))
    val (_, chunks) =
      capture_reports forward_other probe_id (fn () =>
        Print_Mode.with_modes [Print_Mode.PIDE] reparse source)
    val reports = reports_for_id probe_id chunks
  in
    URust_Printer_Document.pretty
      (reported_lexeme reports) document
  end

fun pretty_human_expr_with_reparse reparse expression =
  pretty_human_document_with_reparse true reparse
    (URust_Printer_Document.human_expr expression)

fun pretty_human_datatype_with_reparse reparse item =
  pretty_human_document_with_reparse false reparse
    (URust_Printer_Document.human_datatype item)

in

structure URust_Printer_Output :> URUST_PRINTER_OUTPUT =
struct
  val pretty_human_expr_with_reparse =
    pretty_human_expr_with_reparse
  val pretty_human_datatype_with_reparse =
    pretty_human_datatype_with_reparse
end

end
\<close>

end
