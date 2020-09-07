package sygus

import ast.ASTNode
import enumeration.ProbUpdate

object ProbeMain extends App {
  def runBenchmarks(filename: String,
                    resultPrinter: (ASTNode, Long, Long, Long) => String
                   ): String = {
    var program: List[ASTNode] = null
    val t0 = System.currentTimeMillis()
    ProbUpdate.resetPrior()
    program = Main.synthesize(filename, true, true, false)
    val t1 = System.currentTimeMillis()
    if (!program.isEmpty) {
      println(filename.drop(20)  + resultPrinter(program.head, t1 - t0, program.head.terms, "ite".r.findAllMatchIn(program.head.code).length))
      filename.drop(20) + resultPrinter(program.head, t1 - t0, program.head.terms, "ite".r.findAllMatchIn(program.head.code).length)
    }
    else {
      println(filename + ",None" + ",Timeout" + "None" + "None")
      filename + ",None" + ",Timeout" + ",None" + "None"
    }
  }

  def regularBenchmarkPrinter(program: ASTNode, msec: Long, size: Long, ite: Long): String = {
    "," + program.code+ "," + (msec.toFloat / 1000) + "," + size + "," + ite
  }

  val probeBenchmarks = runBenchmarks(args(0), regularBenchmarkPrinter)


}
