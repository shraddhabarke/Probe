package sygus

import ast.ASTNode
import enumeration.ProbUpdate
import java.nio.file.{FileSystems, Files}
import scala.Console.println
import scala.collection.JavaConverters.*

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

  //val probeBenchmarks = runBenchmarks("src/test/benchmarks/string/count-total-words-in-a-cell.sl", regularBenchmarkPrinter)
  val files = Files.list(FileSystems.getDefault.getPath("src/test/benchmarks/string/")).iterator().asScala
  for (file <- files) {
    println(file)
    runBenchmarks(file.toString, regularBenchmarkPrinter)
    print("\n\n")
  }
}
