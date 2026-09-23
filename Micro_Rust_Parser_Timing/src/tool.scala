/* Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
   SPDX-License-Identifier: MIT */

/*  Title:      Micro_Rust_Parser_Timing/src/tool.scala

Command-line front end for `isabelle urust_timing`.
*/

package isabelle.micro_rust_parser_timing

import isabelle._


object Timing_Tool {
  val isabelle_tool: Isabelle_Tool =
    Isabelle_Tool(
      "urust_timing",
      "aggregate structured µRust parser timings from a built session",
      Scala_Project.here,
      { args => run(args) })

  def run(args: List[String]): Unit = {
    var theories: List[String] = Nil
    var hotspots: Option[Int] = None
    var json_file: Option[Path] = None
    var options = Options.init()

    val getopts = Getopts("""
Usage: isabelle urust_timing [OPTIONS] SESSION

  Options are:
    -T NAME      restrict to a theory; repeatable
    -C NUM       show the NUM slowest declarations by parser time
                 (0 shows all declarations)
    -J FILE      atomically write the complete JSON report
    -o OPTION    override Isabelle system/database options

  Read the named session database and aggregate final PIDE timing records.
  This command does not build the session or check source freshness.
""",
      "T:" -> (arg => theories = theories ::: List(arg)),
      "C:" -> (arg => hotspots = Some(Value.Nat.parse(arg))),
      "J:" -> (arg => json_file = Some(Path.explode(arg))),
      "o:" -> (arg => options = options + arg))

    val more_args = getopts(args)
    val session =
      more_args match {
        case List(name) => name
        case _ => getopts.usage()
      }

    val contents = Timing_Database.read(options, session)
    val report =
      Timing_Report.make(
        session,
        contents.available_theories,
        contents.entries,
        contents.diagnostics,
        theories)

    val progress = new Console_Progress()
    report.diagnostics.foreach(diagnostic => progress.echo_warning(diagnostic.print))
    progress.echo(report.print(hotspots))
    json_file.foreach { path =>
      Timing_Report.write_json_atomic(path, report)
      progress.echo("Wrote JSON report to " + path.absolute)
    }
  }
}
