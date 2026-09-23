/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      Micro_Rust_Parser_Timing/src/test_tool.scala

Unit and session-database tests for the µRust parser timing component.
*/

package isabelle.micro_rust_parser_timing

import isabelle._

import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.util.concurrent.atomic.AtomicInteger


object Timing_Test_Tool {
  import Timing_Record._
  import Timing_Report._

  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(
      "urust_timing_test",
      "test runner for the µRust parser timing component",
      Scala_Project.here,
      { args => run(args) })

  private final class Runner {
    private val passed = new AtomicInteger(0)
    private val failed = new AtomicInteger(0)

    private def test(name: String)(body: => Unit): Unit = {
      Output.writeln("--- " + name + " ---")
      try {
        body
        passed.incrementAndGet()
        Output.writeln("    PASS")
      }
      catch {
        case exn: Throwable =>
          failed.incrementAndGet()
          Output.error_message("    FAIL: " + Exn.message(exn))
      }
    }

    private def assert_true(condition: Boolean, message: String): Unit =
      if (!condition) error(message)

    private def record(
      theory: String,
      name: String,
      elapsed_us: Long,
      kind: String = "urust_expr",
      version: String = "1",
      extra: Properties.T = Nil
    ): XML.Elem = {
      XML.Elem(
        Markup(
          element_name,
          List(
            "schema_version" -> version,
            "command_kind" -> kind,
            "declaration_name" -> name,
            "source_symbols" -> "7",
            "source_bytes" -> "9",
            "elapsed_us" -> elapsed_us.toString) :::
            Position.Line_File(3, theory + ".thy") :::
            Position.Range(Text.Range(10, 17)) :::
            extra),
        Nil)
    }

    private def entry(
      theory: String,
      name: String,
      elapsed_us: Long,
      kind: String = "urust_expr"
    ): Entry =
      Entry(
        theory,
        kind,
        name,
        Source_Position(Some(theory + ".thy"), Some(3), Some(10), Some(17)),
        7,
        9,
        elapsed_us)

    def unit(): Boolean = {
      test("record decoding") {
        decode("A", record("A", "function", 90, kind = "urust_fn")) match {
          case Decoded(got) =>
            assert_true(got.declaration_name == "function", "wrong declaration name")
            assert_true(got.command_kind == "urust_fn", "wrong command kind")
            assert_true(got.elapsed_us == 90, "wrong elapsed time")
            assert_true(got.position.line.contains(3), "source line missing")
          case other => error("unexpected decode result: " + other)
        }
      }

      test("malformed and versioned data") {
        decode("A", record("A", "future", 1, version = "2")) match {
          case Unsupported_Version("2") =>
          case other => error("future record was not rejected safely: " + other)
        }
        val malformed =
          record("A", "bad", 5).copy(
            markup =
              Markup(
                element_name,
                record("A", "bad", 5).markup.properties.filterNot(_._1 == "elapsed_us")))
        decode("A", malformed) match {
          case Malformed(message) =>
            assert_true(message.contains("elapsed_us"), "malformed diagnostic lacks field")
          case other => error("malformed record was accepted: " + other)
        }
      }

      test("aggregation filtering and ordering") {
        val entries =
          List(
            entry("B", "middle", 20),
            entry("A", "slow", 30),
            entry("A", "fast", 10))
        val report = Timing_Report.make("S", List("A", "B"), entries, Nil, Nil)
        assert_true(
          report.declarations.map(_.declaration_name) == List("slow", "middle", "fast"),
          "hotspot ordering is not slowest-first")
        assert_true(report.totals.elapsed_us == 60, "bad parser total")

        val filtered = Timing_Report.make("S", List("A", "B"), entries, Nil, List("B"))
        assert_true(
          filtered.declarations.map(_.declaration_name) == List("middle"),
          "theory filtering failed")
        assert_true(filtered.theories.map(_.theory) == List("B"), "filtered table is wrong")
      }

      test("JSON report") {
        val report =
          Timing_Report.make(
            "S",
            List("A"),
            List(entry("A", "slow", 30)),
            Nil,
            Nil)
        val json = report.json
        assert_true(JSON.string(json, "session").contains("S"), "JSON session missing")
        val declarations =
          JSON.list(json, "declarations", JSON.Object.unapply).getOrElse(error("bad declarations"))
        assert_true(declarations.length == 1, "JSON declaration count is wrong")
        assert_true(
          JSON.string(declarations.head, "declaration_name").contains("slow"),
          "JSON declaration name missing")
      }

      report()
    }

    def e2e(options: Options, session: String): Boolean = {
      test("built-session records") {
        val contents = Timing_Database.read(options, session)
        val report =
          Timing_Report.make(
            session,
            contents.available_theories,
            contents.entries,
            contents.diagnostics,
            Nil)
        val names = report.declarations.map(_.declaration_name).toSet
        val expected =
          Set(
            "timing_fixture_alpha",
            "timing_fixture_beta",
            "timing_fixture_gamma",
            "timing_fixture_delta")
        assert_true(names == expected, "unexpected fixture declarations: " + names)
        assert_true(
          report.declarations.map(_.elapsed_us) ==
            report.declarations.map(_.elapsed_us).sorted.reverse,
          "database records are not ordered slowest-first")
        assert_true(
          report.declarations.forall(entry =>
            entry.position.file.isDefined &&
              entry.position.line.isDefined &&
              entry.position.offset.isDefined &&
              entry.position.end_offset.isDefined &&
              entry.position.end_offset.get > entry.position.offset.get),
          "fixture records lack complete source positions")
      }

      test("theory filter") {
        val contents = Timing_Database.read(options, session)
        val selected_theory =
          contents.available_theories.find(_.endsWith("Timing_Fixture_A"))
            .getOrElse(error("fixture theory A not found"))
        val report =
          Timing_Report.make(
            session,
            contents.available_theories,
            contents.entries,
            contents.diagnostics,
            List(selected_theory))
        assert_true(
          report.declarations.map(_.declaration_name).toSet ==
            Set("timing_fixture_alpha", "timing_fixture_beta"),
          "theory filter returned the wrong declarations")
      }

      test("atomic JSON output") {
        val contents = Timing_Database.read(options, session)
        val report =
          Timing_Report.make(
            session,
            contents.available_theories,
            contents.entries,
            contents.diagnostics,
            Nil)
        val dir = Files.createTempDirectory("urust_timing_json")
        val path = File.path(dir.resolve("report.json").toFile)
        try {
          Timing_Report.write_json_atomic(path, report)
          val text = Files.readString(path.file.toPath, StandardCharsets.UTF_8)
          val json = JSON.parse(text)
          val declarations =
            JSON.list(json, "declarations", JSON.Object.unapply)
              .getOrElse(error("written JSON lacks declarations"))
          assert_true(declarations.length == 4, "written JSON declaration count is wrong")
        }
        finally {
          Files.deleteIfExists(path.file.toPath)
          Files.deleteIfExists(dir)
        }
      }

      report()
    }

    private def report(): Boolean = {
      Output.writeln("")
      Output.writeln(
        "=== " + passed.get + " passed, " + failed.get + " failed ===")
      failed.get == 0
    }
  }

  private def run(args: List[String]): Unit = {
    var options = Options.init()
    val getopts = Getopts("""
Usage: isabelle urust_timing_test [OPTIONS] MODE [SESSION]

  MODE:
    unit                    run pure unit tests
    e2e [SESSION]           inspect a built fixture session
    all [SESSION]           run both suites

  Options are:
    -o OPTION               override Isabelle system/database options
""",
      "o:" -> (arg => options = options + arg))

    val rest = getopts(args)
    val (mode, session) =
      rest match {
        case Nil => ("all", "Micro_Rust_Parser_Timing_Fixture")
        case List("unit") => ("unit", "Micro_Rust_Parser_Timing_Fixture")
        case List("e2e") => ("e2e", "Micro_Rust_Parser_Timing_Fixture")
        case List("all") => ("all", "Micro_Rust_Parser_Timing_Fixture")
        case List("e2e", name) => ("e2e", name)
        case List("all", name) => ("all", name)
        case _ => getopts.usage()
      }

    val runner = new Runner
    val ok =
      mode match {
        case "unit" => runner.unit()
        case "e2e" => runner.e2e(options, session)
        case "all" => runner.unit() && runner.e2e(options, session)
      }
    if (!ok) sys.exit(1)
  }
}
