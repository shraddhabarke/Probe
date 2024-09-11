package sygus

import ast.ASTNode
import enumeration.ProbUpdate
import java.nio.file.{FileSystems, Files}
import scala.Console.println
import scala.collection.JavaConverters.*

object ProbeMain{
  def runBenchmarks(filename: String,
                    resultPrinter: (ASTNode, Long, Long, Long) => String
                  ): String = {
    var program: List[ASTNode] = null
    val t0 = System.currentTimeMillis()
    ProbUpdate.resetPrior()
    program = Main.synthesize(filename, true, true, false)
    val t1 = System.currentTimeMillis()
    if (!program.isEmpty) {
      println(filename + resultPrinter(program.head, t1 - t0, program.head.terms, "ite".r.findAllMatchIn(program.head.code).length))
      filename + resultPrinter(program.head, t1 - t0, program.head.terms, "ite".r.findAllMatchIn(program.head.code).length)
    }
    else {
      println(filename + ",None" + ",Timeout" + ",None" + ",None")
      filename + ",None" + ",Timeout" + ",None" + "None"
    }
  }

  def regularBenchmarkPrinter(program: ASTNode, msec: Long, size: Long, ite: Long): String = {
    ", " + program.code+ ", " + (msec.toFloat / 1000) + ", " + size + ", " + ite
  }

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

  //main()
}
