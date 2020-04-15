import BenchmarksHarness.tooHardBenchmarks
import sygus.Main.RankedProgram
import sygus.Main
import ast.{ASTNode, BoolLiteral, BoolVariable, Contains, IndexOf, IntAddition, IntEquals, IntITE, IntLessThanEq, IntLiteral, IntSubtraction, IntToString, IntVariable, PrefixOf, StringAt, StringConcat, StringITE, StringLength, StringLiteral, StringReplace, StringToInt, StringVariable, Substring, SuffixOf}
import enumeration.ProbUpdate
import sygus.SygusFileTask
import trace.DebugPrints.dprintln

import scala.collection.mutable


object BenchmarksTests extends App {
    def runBenchmarks(dirname: String,
                      resultPrinter: (List[RankedProgram], Long) => String
                     ): List[String] = for (file <- new java.io.File(dirname).listFiles().toList) yield {
      val t0 = System.currentTimeMillis()
      ProbUpdate.priors = mutable.Map[Class[_], Int](
        classOf[StringConcat] -> 10,
        classOf[StringAt] -> 10,
        classOf[IntAddition] -> 10,
        classOf[IntSubtraction] -> 10,
        classOf[IntLessThanEq] -> 10,
        classOf[IntEquals] -> 10,
        classOf[PrefixOf] -> 10,
        classOf[SuffixOf] -> 10,
        classOf[Contains] -> 10,
        classOf[StringLiteral] -> 10,
        classOf[IntLiteral] -> 10,
        classOf[BoolLiteral] -> 10,
        classOf[StringReplace] -> 10,
        classOf[StringITE] -> 10,
        classOf[IntITE] -> 10,
        classOf[Substring] -> 10,
        classOf[IndexOf] -> 10,
        classOf[IntToString] -> 10,
        classOf[StringToInt] -> 10,
        classOf[StringLength] -> 10,
        classOf[StringVariable] -> 10,
        classOf[IntVariable] -> 10,
        classOf[BoolVariable] -> 10,
      )

      val programs = Main.synthesize(file.getAbsolutePath)
      //programs.foreach(pr => println((pr.program.code, pr.rank)))
      val t1 = System.currentTimeMillis()
      println(file.getName + resultPrinter(programs.toList,t1 - t0))
      file.getName + resultPrinter(programs.toList,t1 - t0)
    }

  def regularBenchmarkPrinter(programs: List[RankedProgram], msec: Long) : String = {
    "," + programs.head.program.code + "," + msec/1000 + "s"
  }

  val tooHardBenchmarks = runBenchmarks("src/test/benchmarks/too-hard", regularBenchmarkPrinter)
  tooHardBenchmarks.foreach(println)

}
