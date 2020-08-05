package sygus

import ast.ASTNode
import enumeration.{InputsValuesManager}
import org.antlr.v4.runtime.{BufferedTokenStream, CharStreams, RecognitionException, Token}

import util.control.Breaks._
import scala.concurrent.duration._
import trace.DebugPrints.{iprintln}

object Main extends App {
  val filename =
  //"src/test/benchmarks/euphony/extract-word-that-begins-with-specific-character.sl"
  //"src/test/benchmarks/euphony/initials.sl"
  //"src/test/benchmarks/too-hard/43606446.sl"
  "src/test/benchmarks/euphony/count-total-words-in-a-cell.sl"

  case class ExpectedEOFException() extends Exception

  def interpret(task: SygusFileTask, str: String): ASTNode = {
    val parser = new SyGuSParser(new BufferedTokenStream(new SyGuSLexer(CharStreams.fromString(str))))
    val parsed = parser.bfTerm()
    val visitor = new ASTGenerator(task)
    val ast = visitor.visit(parsed)
    if (parser.getCurrentToken.getType != Token.EOF) {
      throw ExpectedEOFException()
    }
    ast
  }

  def interpret(filename: String, str: String): Option[(ASTNode, List[Any])] = try {
    val task = new SygusFileTask(scala.io.Source.fromFile(filename).mkString)
    val ast = interpret(task, str)
    Some(ast, task.examples.map(_.output))
  } catch {
    case e: RecognitionException => {
      iprintln(s"Cannot parse program: ${e.getMessage}")
      None
    }
    case e: ResolutionException => {
      iprintln(s"Cannot resolve program: ${e.badCtx.getText}")
      None
    }
    case e: ExpectedEOFException => {
      iprintln("Expected <EOF>")
      None
    }
  }

  def synthesizeTask(filename: String, task: SygusFileTask, sizeBased: Boolean, probBased: Boolean, timeout: Int = 600): List[ASTNode] = {
    val oeManager = new InputsValuesManager()

    val enumerator =  if (!sizeBased) new enumeration.Enumerator(task.vocab, oeManager, task.examples.map(_.input))
    else new enumeration.ProbEnumerator(filename, task.vocab, oeManager, task, task.examples.map(_.input), probBased)

      val deadline = timeout.seconds.fromNow
    var p = List[ASTNode]()
    val t0 = System.currentTimeMillis / 1000

    breakable {
      for ((program, i) <- enumerator.zipWithIndex) {
        if (program.nodeType == task.functionReturnType) {
          val results = task.examples.zip(program.values).map(pair => pair._1.output == pair._2)
          if (results.forall(identity)) {
            p = List(program)
            //println(program.code, results)
            break
          }
        }

        if (!deadline.hasTimeLeft) {
          break
        }
      }
    }
    val t1 = System.currentTimeMillis / 1000
    iprintln(s"${t1 - t0}s")
    p
  }

  def synthesize(filename: String, sizeBased: Boolean = true, probBased: Boolean = true) = {
    val task = new SygusFileTask(scala.io.Source.fromFile(filename).mkString)
    assert(task.isPBE)
    synthesizeTask(filename, task, sizeBased, probBased)
  }

  trace.DebugPrints.setInfo()
  synthesize(filename)
}
