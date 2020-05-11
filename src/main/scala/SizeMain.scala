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

import scala.collection.mutable

object SizeMain extends App {
  def runBenchmarks(filename: String,
                    resultPrinter: (ASTNode, Long, Long) => String
                   ): String = {
    var program: List[ASTNode] = null
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
    program = synthesizeFullSols(filename)
    //programs.foreach(pr => println((pr.program.code, pr.raenk)))
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
  //tooHardBenchmarks.foreach(println)
  def synthesizeFullSols(filename: String) = {
    val task = new SygusFileTask(scala.io.Source.fromFile(filename).mkString)
    assert(task.isPBE)
    synthesizeProbe(filename, task)
  }

  def synthesizeProbe(filename: String, task: SygusFileTask, timeout: Int = 600): List[ASTNode] = {
    val oeManager = new InputsValuesManager()
    //val enumerator = new enumeration.Enumerator(task.vocab, oeManager, task.examples.map(_.input))
    val enumerator = new enumeration.ProbEnumerator(false, filename, task.vocab, oeManager, task, false)
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
