/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      Micro_Rust_Parser_Timing/src/timing.scala

Structured µRust parser timing records, aggregation, rendering, and session-database access.
*/

package isabelle.micro_rust_parser_timing

import isabelle._

import java.nio.charset.StandardCharsets
import java.nio.file.{AtomicMoveNotSupportedException, Files, StandardCopyOption}
import java.text.NumberFormat
import java.util.Locale


object Timing_Record {
  val element_name = "micro_rust_parser_timing"
  val schema_version = 1

  sealed trait Decode_Result
  final case class Decoded(entry: Entry) extends Decode_Result
  final case class Malformed(message: String) extends Decode_Result
  final case class Unsupported_Version(version: String) extends Decode_Result

  final case class Source_Position(
    file: Option[String] = None,
    line: Option[Int] = None,
    offset: Option[Int] = None,
    end_offset: Option[Int] = None
  ) {
    def print: String = {
      val file_part = file.getOrElse("<unknown>")
      val line_part = line.map(":" + _).getOrElse("")
      file_part + line_part
    }

    def json: JSON.Object.T =
      JSON.Object.empty ++
        file.map("file" -> _) ++
        line.map("line" -> _) ++
        offset.map("offset" -> _) ++
        end_offset.map("end_offset" -> _)
  }

  final case class Entry(
    theory: String,
    command_kind: String,
    declaration_name: String,
    position: Source_Position,
    source_symbols: Int,
    source_bytes: Int,
    new_elapsed_us: Long,
    old_elapsed_us: Option[Long],
    delta_us: Option[Long]
  ) {
    def paired: Boolean = old_elapsed_us.isDefined

    def json: JSON.Object.T =
      JSON.Object(
        "theory" -> theory,
        "command_kind" -> command_kind,
        "declaration_name" -> declaration_name,
        "source_position" -> position.json,
        "source_symbols" -> source_symbols,
        "source_bytes" -> source_bytes,
        "new_elapsed_us" -> new_elapsed_us,
        "old_elapsed_us" -> old_elapsed_us.map(_.asInstanceOf[JSON.T]).orNull,
        "delta_us" -> delta_us.map(_.asInstanceOf[JSON.T]).orNull)
  }

  private def required(props: Properties.T, name: String): Either[String, String] =
    Properties.get(props, name) match {
      case Some(value) => Right(value)
      case None => Left("missing property " + quote(name))
    }

  private def parse_int(props: Properties.T, name: String): Either[String, Int] =
    required(props, name).flatMap(value =>
      Value.Int.unapply(value).toRight("bad integer property " + quote(name) + ": " + quote(value)))

  private def parse_long(props: Properties.T, name: String): Either[String, Long] =
    required(props, name).flatMap(value =>
      Value.Long.unapply(value).toRight("bad integer property " + quote(name) + ": " + quote(value)))

  private def parse_optional_long(
    props: Properties.T,
    name: String
  ): Either[String, Option[Long]] =
    Properties.get(props, name) match {
      case None => Right(None)
      case Some(value) =>
        Value.Long.unapply(value) match {
          case Some(n) => Right(Some(n))
          case None => Left("bad integer property " + quote(name) + ": " + quote(value))
        }
    }

  def decode(
    theory: String,
    elem: XML.Elem,
    source_position: Option[Source_Position] = None
  ): Decode_Result = {
    val props = elem.markup.properties
    Properties.get(props, "schema_version") match {
      case None => Malformed("missing property " + quote("schema_version"))
      case Some(version) if version != schema_version.toString =>
        Unsupported_Version(version)
      case Some(_) =>
        val decoded =
          for {
            command_kind <- required(props, "command_kind")
            _ <-
              if (command_kind == "urust_expr" || command_kind == "urust_fn") Right(())
              else Left("bad command kind " + quote(command_kind))
            declaration_name <- required(props, "declaration_name")
            _ <-
              if (declaration_name.nonEmpty) Right(())
              else Left("empty declaration name")
            source_symbols <- parse_int(props, "source_symbols")
            _ <-
              if (source_symbols >= 0) Right(())
              else Left("negative source symbol count")
            source_bytes <- parse_int(props, "source_bytes")
            _ <-
              if (source_bytes >= 0) Right(())
              else Left("negative source byte count")
            new_elapsed_us <- parse_long(props, "new_elapsed_us")
            _ <-
              if (new_elapsed_us >= 0) Right(())
              else Left("negative new-parser elapsed time")
            old_elapsed_us <- parse_optional_long(props, "old_elapsed_us")
            _ <-
              if (old_elapsed_us.forall(_ >= 0)) Right(())
              else Left("negative old-parser elapsed time")
            delta_us <- parse_optional_long(props, "delta_us")
            _ <-
              (old_elapsed_us, delta_us) match {
                case (None, None) => Right(())
                case (Some(old_us), Some(delta)) if delta == new_elapsed_us - old_us => Right(())
                case (Some(_), None) => Left("missing paired delta")
                case (None, Some(_)) => Left("delta without old-parser elapsed time")
                case (Some(old_us), Some(delta)) =>
                  Left(
                    "inconsistent paired delta " + delta +
                      " (expected " + (new_elapsed_us - old_us) + ")")
              }
          } yield {
            val position =
              source_position.getOrElse(
                Source_Position(
                  file = Position.File.unapply(props),
                  line = Position.Line.unapply(props),
                  offset = Position.Offset.unapply(props),
                  end_offset = Position.End_Offset.unapply(props)))
            Entry(
              theory = theory,
              command_kind = command_kind,
              declaration_name = declaration_name,
              position = position,
              source_symbols = source_symbols,
              source_bytes = source_bytes,
              new_elapsed_us = new_elapsed_us,
              old_elapsed_us = old_elapsed_us,
              delta_us = delta_us)
          }

        decoded match {
          case Right(entry) => Decoded(entry)
          case Left(message) => Malformed(message)
        }
    }
  }

  def decode_tree(theory: String, tree: XML.Tree): List[Decode_Result] =
    tree match {
      case elem @ XML.Elem(Markup(name, _), _) if name == element_name =>
        List(decode(theory, elem))
      case XML.Elem(_, body) => body.flatMap(decode_tree(theory, _))
      case XML.Text(_) => Nil
    }

  def decode_snapshot(theory: String, snapshot: Document.Snapshot): List[Decode_Result] = {
    val line_document = Line.Document(snapshot.node.source)
    val file = snapshot.node_name.node

    def traverse(body: XML.Body, start: Text.Offset): (Text.Offset, List[Decode_Result]) =
      body.foldLeft((start, List.empty[Decode_Result])) {
        case ((offset, results), XML.Text(text)) =>
          (offset + text.length, results)
        case ((offset, results), elem @ XML.Elem(Markup(name, _), elem_body)) =>
          val (stop, nested) = traverse(elem_body, offset)
          if (name == element_name) {
            val source_position =
              Source_Position(
                file = Some(file),
                line = Some(line_document.position(offset).line1),
                offset = Some(offset),
                end_offset = Some(stop))
            (stop, results ::: List(decode(theory, elem, Some(source_position))))
          }
          else (stop, results ::: nested)
      }

    traverse(
      snapshot.xml_markup(elements = Markup.Elements(element_name)),
      0)._2
  }
}


object Timing_Report {
  import Timing_Record._

  final case class Diagnostic(theory: String, kind: String, message: String) {
    def print: String = theory + ": " + kind + ": " + message
    def json: JSON.Object.T =
      JSON.Object("theory" -> theory, "kind" -> kind, "message" -> message)
  }

  final case class Summary(
    declarations: Int,
    paired: Int,
    source_symbols: Long,
    source_bytes: Long,
    new_elapsed_us: Long,
    old_elapsed_us: Long,
    delta_us: Long
  ) {
    def new_only: Int = declarations - paired

    def json: JSON.Object.T =
      JSON.Object(
        "declarations" -> declarations,
        "paired_declarations" -> paired,
        "new_only_declarations" -> new_only,
        "source_symbols" -> source_symbols,
        "source_bytes" -> source_bytes,
        "new_elapsed_us" -> new_elapsed_us,
        "paired_old_elapsed_us" -> old_elapsed_us,
        "paired_delta_us" -> delta_us)
  }

  object Summary {
    def apply(entries: Iterable[Entry]): Summary =
      entries.foldLeft(Summary(0, 0, 0L, 0L, 0L, 0L, 0L)) {
        case (summary, entry) =>
          Summary(
            declarations = summary.declarations + 1,
            paired = summary.paired + (if (entry.paired) 1 else 0),
            source_symbols = summary.source_symbols + entry.source_symbols,
            source_bytes = summary.source_bytes + entry.source_bytes,
            new_elapsed_us = summary.new_elapsed_us + entry.new_elapsed_us,
            old_elapsed_us = summary.old_elapsed_us + entry.old_elapsed_us.getOrElse(0L),
            delta_us = summary.delta_us + entry.delta_us.getOrElse(0L))
      }
  }

  final case class Theory_Summary(theory: String, summary: Summary) {
    def json: JSON.Object.T = summary.json + ("theory" -> theory)
  }

  final case class Report(
    session: String,
    theory_filters: List[String],
    totals: Summary,
    theories: List[Theory_Summary],
    declarations: List[Entry],
    diagnostics: List[Diagnostic]
  ) {
    private val integer_format = NumberFormat.getIntegerInstance(Locale.ROOT)

    private def number(n: Long): String = integer_format.format(n)
    private def signed(n: Long): String =
      if (n > 0) "+" + number(n) else number(n)

    private def table(headers: List[String], rows: List[List[String]]): String = {
      val widths =
        headers.indices.map(i =>
          (headers(i) :: rows.map(_(i))).map(_.length).max).toList
      def line(columns: List[String]): String =
        columns.zip(widths).map { case (value, width) =>
          value + (" " * (width - value.length))
        }.mkString("  ").stripTrailing()
      (line(headers) :: rows.map(line)).mkString("\n")
    }

    def print(hotspots: Option[Int]): String = {
      val filter_line =
        if (theory_filters.isEmpty) Nil
        else List("Theories: " + theory_filters.mkString(", "))
      val paired_lines =
        if (totals.paired == 0) Nil
        else
          List(
            "Paired old-parser cumulative elapsed: " + number(totals.old_elapsed_us) + " us",
            "Paired delta (new - old): " + signed(totals.delta_us) + " us")
      val theory_rows =
        theories.map { theory =>
          val s = theory.summary
          List(
            theory.theory,
            s.declarations.toString,
            s.paired.toString,
            number(s.new_elapsed_us),
            if (s.paired == 0) "-" else number(s.old_elapsed_us),
            if (s.paired == 0) "-" else signed(s.delta_us))
        }
      val theory_table =
        table(
          List("Theory", "Decls", "Paired", "New us", "Old us", "Delta us"),
          theory_rows)
      val hotspot_lines =
        hotspots match {
          case None => Nil
          case Some(limit) =>
            val selected =
              if (limit == 0) declarations else declarations.take(limit)
            val rows =
              selected.map(entry =>
                List(
                  entry.new_elapsed_us.toString,
                  entry.command_kind,
                  entry.theory,
                  entry.declaration_name,
                  entry.position.print))
            List(
              "",
              "Slowest declarations by new-parser elapsed time:",
              table(List("New us", "Kind", "Theory", "Declaration", "Position"), rows))
        }

      (List(
        "µRust parser timing report for session " + quote(session)) :::
        filter_line :::
        List(
          "Declarations: " + totals.declarations +
            " (" + totals.paired + " paired, " + totals.new_only + " new-only)",
          "Source size: " + number(totals.source_symbols) + " symbols, " +
            number(totals.source_bytes) + " bytes",
          "New-parser cumulative elapsed: " + number(totals.new_elapsed_us) + " us") :::
        paired_lines :::
        List(
          "",
          "Per-theory cumulative declaration latency:",
          theory_table) :::
        hotspot_lines).mkString("\n")
    }

    def json: JSON.Object.T =
      JSON.Object(
        "schema_version" -> 1,
        "session" -> session,
        "theory_filters" -> theory_filters,
        "totals" -> totals.json,
        "theories" -> theories.map(_.json),
        "declarations" -> declarations.map(_.json),
        "diagnostics" -> diagnostics.map(_.json))
  }

  private def slower(left: Entry, right: Entry): Boolean =
    if (left.new_elapsed_us != right.new_elapsed_us)
      left.new_elapsed_us > right.new_elapsed_us
    else {
      val left_key =
        (left.theory, left.declaration_name, left.command_kind, left.position.offset.getOrElse(0))
      val right_key =
        (right.theory, right.declaration_name, right.command_kind, right.position.offset.getOrElse(0))
      Ordering[(String, String, String, Int)].lt(left_key, right_key)
    }

  def make(
    session: String,
    available_theories: List[String],
    entries: List[Entry],
    diagnostics: List[Diagnostic],
    theory_filters: List[String]
  ): Report = {
    val distinct_filters = theory_filters.distinct
    val unknown = distinct_filters.filterNot(available_theories.toSet)
    if (unknown.nonEmpty) error("Unknown theories " + commas_quote(unknown))
    val selected =
      if (distinct_filters.isEmpty) entries
      else entries.filter(entry => distinct_filters.contains(entry.theory))
    val selected_diagnostics =
      if (distinct_filters.isEmpty) diagnostics
      else diagnostics.filter(diagnostic => distinct_filters.contains(diagnostic.theory))
    val ordered = selected.sortWith(slower)
    val theory_summaries =
      ordered.groupBy(_.theory).toList.sortBy(_._1).map {
        case (theory, theory_entries) =>
          Theory_Summary(theory, Summary(theory_entries))
      }
    Report(
      session = session,
      theory_filters = distinct_filters,
      totals = Summary(ordered),
      theories = theory_summaries,
      declarations = ordered,
      diagnostics = selected_diagnostics)
  }

  def write_json_atomic(path: Path, report: Report): Unit = {
    val target = path.absolute.file.toPath
    val parent = Option(target.getParent).getOrElse(error("JSON target has no parent: " + path))
    if (!Files.isDirectory(parent)) error("JSON target directory does not exist: " + parent)
    val temporary = Files.createTempFile(parent, "." + target.getFileName.toString + ".", ".tmp")
    try {
      val text = JSON.Format.pretty_print(report.json) + "\n"
      Files.write(temporary, text.getBytes(StandardCharsets.UTF_8))
      try {
        Files.move(
          temporary,
          target,
          StandardCopyOption.ATOMIC_MOVE,
          StandardCopyOption.REPLACE_EXISTING)
      }
      catch {
        case _: AtomicMoveNotSupportedException =>
          error("Atomic JSON replacement is not supported for " + path.absolute)
      }
    }
    finally {
      Files.deleteIfExists(temporary)
    }
  }
}


object Timing_Database {
  import Timing_Record._
  import Timing_Report._

  final case class Contents(
    available_theories: List[String],
    entries: List[Entry],
    diagnostics: List[Diagnostic])

  def read(options: Options, session: String): Contents = {
    val store = Store(options)
    using(Export.open_session_context0(store, session)) { session_context =>
      val db =
        session_context.session_db().getOrElse {
          store.error_database(session)
        }
      store.read_build(db, session) match {
        case None => store.error_database(session)
        case Some(build) if !build.ok =>
          error(
            "Session " + quote(session) + " did not complete successfully " +
              "(return code " + build.return_code + ")")
        case Some(_) =>
      }

      val theories = Export.read_theory_names(db, session)
      val decoded =
        theories.flatMap { theory =>
          val snapshot =
            Build.read_theory(session_context.theory(theory)).getOrElse {
              error("Missing final PIDE snapshot for theory " + quote(theory))
            }
          Timing_Record.decode_snapshot(theory, snapshot).map(theory -> _)
        }
      val entries =
        decoded.collect { case (_, Decoded(entry)) => entry }
      val diagnostics =
        decoded.flatMap {
          case (_, Decoded(_)) => Nil
          case (theory, Malformed(message)) =>
            List(Diagnostic(theory, "malformed record", message))
          case (theory, Unsupported_Version(version)) =>
            List(
              Diagnostic(
                theory,
                "unsupported record version",
                quote(version)))
        }
      Contents(theories, entries, diagnostics)
    }
  }
}
