package sygus

import ast.ASTNode
import enumeration.ProbUpdate

object ProbeMain extends App {
  def runBenchmarks(filename: String,
                    resultPrinter: (ASTNode, Long, Long) => String
                   ): String = {
    var program: List[ASTNode] = null
    val t0 = System.currentTimeMillis()
    ProbUpdate.resetPrior()
    program = Main.synthesize(filename)
    val t1 = System.currentTimeMillis()
    if (!program.isEmpty) {
      println(filename + resultPrinter(program.head, t1 - t0, program.head.terms))
      filename + resultPrinter(program.head, t1 - t0, program.head.terms)
    }
    else {
      println(filename + ",None" + ",Timeout" + "None")
      filename + ",None" + ",Timeout" + ",None"
    }
  }

  def regularBenchmarkPrinter(program: ASTNode, msec: Long, size: Long): String = {
    "," + program.code + "," + (msec.toFloat / 1000) + "," + size
  }

  val probeBenchmarks = runBenchmarks(args(0), regularBenchmarkPrinter)


}
