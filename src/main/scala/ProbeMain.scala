package sygus

import ast.{ASTNode, BVAdd, BVAnd, BVEquals, BVITE, BVMul, BVNeg, BVNot, BVOr, BVSDiv, BVSRem, BVShiftLeft, BVShrArithmetic, BVShrLogical, BVSub, BVUDiv, BVURem, BVVariable, BVXor, BoolLiteral, BoolVariable, Contains, IndexOf, IntAddition, IntEquals, IntITE, IntLessThanEq, IntLiteral, IntSubtraction, IntToString, IntVariable, LAnd, LNot, LOr, PrefixOf, StringAt, StringConcat, StringITE, StringLength, StringLiteral, StringReplace, StringToInt, StringVariable, Substring, SuffixOf}
import enumeration.ProbUpdate
import enumeration.{InputsValuesManager}
import jline.console.ConsoleReader
import org.antlr.v4.runtime.{BufferedTokenStream, CharStreams, RecognitionException, Token}

import scala.collection.mutable
import scala.collection.mutable.ListBuffer
import util.control.Breaks._
import scala.concurrent.duration._
import trace.DebugPrints.{dprintln, iprintln}
import pcShell.ConsolePrints._
object ProbeMain extends App {
  def runBenchmarks(filename: String,
                    resultPrinter: (ASTNode, Long, Long) => String
                   ): String = {
    var program: List[ASTNode] = null
    val t0 = System.currentTimeMillis()
    ProbUpdate.resetPrior()
    program = synthesizeFullSols(filename)
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
  def synthesizeFullSols(filename: String) = {
    val task = new SygusFileTask(scala.io.Source.fromFile(filename).mkString)
    assert(task.isPBE)
    synthesizeProbe(filename, task)
  }

  def synthesizeProbe(filename: String, task: SygusFileTask, timeout: Int = 3600): List[ASTNode] = {
    val oeManager = new InputsValuesManager()
    //val enumerator = new enumeration.Enumerator(task.vocab, oeManager, task.examples.map(_.input))
    val enumerator = new enumeration.ProbEnumerator(filename, task.vocab, oeManager, task, true)
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
