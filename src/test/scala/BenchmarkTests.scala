import sygus.Main
import ast.ASTNode
import enumeration.ProbUpdate

object BenchmarksTests extends App {
  def runBenchmarks(dirname: String,
                    resultPrinter: (ASTNode, Long) => String
                   ): List[String] = for (file <- new java.io.File(dirname).listFiles().toList) yield {
    var program: List[ASTNode] = null
    val t0 = System.currentTimeMillis()
    ProbUpdate.resetPrior()
    program = Main.synthesize(file.getAbsolutePath, true, false, false)
    val t1 = System.currentTimeMillis()
    if (!program.isEmpty) {
      println(file.getName + resultPrinter(program.head, t1 - t0))
      file.getName + resultPrinter(program.head, t1 - t0)
    }
    else {
      println(file.getName + ",None" + ",Timeout")
      file.getName + ",None" + ",Timeout"
    }
  }

  def regularBenchmarkPrinter(program: ASTNode, msec: Long): String = {
    "," + program.code + "," + (msec.toFloat / 1000)
  }

  val tooHardBenchmarks = runBenchmarks("src/test/benchmarks/hackers-delight", regularBenchmarkPrinter)

}