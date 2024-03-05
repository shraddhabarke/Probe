package sygus

import ast.ASTNode
import enumeration.ProbUpdate

object SizeMain {
  def runBenchmarks(filename: String,
                    resultPrinter: (ASTNode, Long, Long) => String
                  ): String = {
    var program: List[ASTNode] = null
    val t0 = System.currentTimeMillis()
    ProbUpdate.resetPrior()
    program = Main.synthesize(filename, true, false, false)
    val t1 = System.currentTimeMillis()
    if (!program.isEmpty) {
      println(filename.drop(20) + resultPrinter(program.head, t1 - t0, program.head.terms))
      filename.drop(20) + resultPrinter(program.head, t1 - t0, program.head.terms)
    }
    else {
      println(filename + ",None" + ",Timeout" + "None")
      filename + ",None" + ",Timeout" + ",None"
    }
  }

  def regularBenchmarkPrinter(program: ASTNode, msec: Long, size: Long): String = {
    "," + program.code + "," + (msec.toFloat / 1000) + "," + size
  }

  //val probeBenchmarks = runBenchmarks(args(0), regularBenchmarkPrinter)
  def main(args: Array[String]): Unit = {
    if (args.length > 0) {
      val filename = args(0)
      println(filename)
      val result = runBenchmarks(filename, regularBenchmarkPrinter)
      println(result)
    } else {
      println("No filename provided.")
    }
    //result
  }

}
