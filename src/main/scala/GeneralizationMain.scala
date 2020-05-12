package sygus

import ast.{ASTNode, BoolLiteral, BoolVariable, Contains, IndexOf, IntAddition, IntEquals, IntITE, IntLessThanEq, IntLiteral, IntSubtraction, IntToString, IntVariable, PrefixOf, StringAt, StringConcat, StringITE, StringLength, StringLiteral, StringReplace, StringToInt, StringVariable, Substring, SuffixOf}
import enumeration.ProbUpdate
import enumeration.{InputsValuesManager, ProgramRanking}
import jline.console.ConsoleReader
import org.antlr.v4.runtime.{BufferedTokenStream, CharStreams, RecognitionException, Token}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import util.control.Breaks._
import scala.concurrent.duration._
import trace.DebugPrints.{dprintln, iprintln}
import pcShell.ConsolePrints._
import sygus.SygusFileTask

import scala.collection.mutable
object GeneralizationMain extends App{

  def synthesizeFullSols(filename: String) = {
    val task = new SygusFileTask(scala.io.Source.fromFile(filename).mkString)
    assert(task.isPBE)
    synthesizeProbe(filename, task)
  }

  def runBenchmarks(filename: String,
                    resultPrinter: (ASTNode, Double) => String
                   ): String = {
    var program: List[ASTNode] = null
    var fit : Double = 0.0
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
    program = synthesizeFullSols(filename)

    for (file <- new java.io.File("src/test/benchmarks/quality-tests").listFiles().toList) {
      if (filename.replace(".sl", "").contains(file.getName.replace("-long.sl", ""))) {
        val tasks = new SygusFileTask(scala.io.Source.fromFile(file).mkString)
        val exampleFit = tasks.fit(program.head)
        fit = (exampleFit._1.toFloat) / exampleFit._2
        }
      }

    if (!program.isEmpty) {
      println(filename + resultPrinter(program.head, fit))
      filename + resultPrinter(program.head, fit)
    }
    else {
      println(filename + ",None" + "None")
      filename + ",None" + "None"
    }
  }

  def regularBenchmarkPrinter(program: ASTNode, accuracy: Double): String = {
    "," + program.code + "," + accuracy
  }

  val probeBenchmarks = runBenchmarks(args(0), regularBenchmarkPrinter)

  def synthesizeProbe(filename: String, task: SygusFileTask, timeout: Int = 1800): List[ASTNode] = {
    val oeManager = new InputsValuesManager()
    //val enumerator = new enumeration.Enumerator(task.vocab, oeManager, task.examples.map(_.input))
    val enumerator = new enumeration.ProbEnumerator(false, filename, task.vocab, oeManager, task, true)
    //val foundPrograms: mutable.Map[List[Boolean], mutable.ListBuffer[ASTNode]] = mutable.HashMap()
    val deadline = timeout.seconds.fromNow
    var p = List[ASTNode]()
    breakable {
      for ((program, i) <- enumerator.zipWithIndex) {
        if (program.nodeType == task.functionReturnType) {
          val results = task.examples.zip(program.values).map(pair => pair._1.output == pair._2)
          //There will only be one program matching 1...1, but potentially many for 1..101..1, do rank those as well?
          if (results.forall(identity)) {
            p = List(program)
            iprintln(program.code)
            break
          }
        }
        if ((consoleEnabled && in.ready()) || !deadline.hasTimeLeft) {
          cprintln("")
          break
        }
      }
    }
    p
  }
}
