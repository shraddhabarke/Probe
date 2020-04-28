import java.io.{BufferedWriter, FileWriter}

import spray.json._
import DefaultJsonProtocol._
import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Token}
import sygus.{ASTGenerator, SyGuSLexer, SyGuSParser, SygusFileTask, ThrowingLexerErrorListener}

object Reevaluator extends App {
  val slFile = args(0)
  val jsonFile = args(1)
  val outFile = args(2)
  val origTask = new SygusFileTask(scala.io.Source.fromFile(slFile).mkString)
  val jsonified = scala.io.Source.fromFile(jsonFile).mkString.parseJson
  val res = for ((key,value) <- jsonified.asInstanceOf[JsObject].fields) yield {
    val inputsList: Iterable[Map[String,Any]] = for (inputs <- value.asInstanceOf[JsArray].elements) yield inputs.asJsObject.fields.map { case (name,value) =>
      val scalaValue = value match {
        case s: JsString => s.value
        case n: JsNumber => n.value.toInt
        case b: JsBoolean => b.value
      }
      (name, scalaValue)
    }.toMap
    val task = origTask.enhance(inputsList)
    val lexer = new SyGuSLexer(CharStreams.fromString(key))
    lexer.removeErrorListeners()
    lexer.addErrorListener(new ThrowingLexerErrorListener)
    val parser = new SyGuSParser(new BufferedTokenStream(lexer))
    parser.removeErrorListeners()
    parser.setErrorHandler(new BailErrorStrategy)
    val parsed = parser.bfTerm()
    if (parser.getCurrentToken.getType != Token.EOF)
      throw new Exception(parser.getCurrentToken.getText)
    val visitor = new ASTGenerator(task)
    val ast = visitor.visit(parsed)
    key -> JsArray(ast.values.zipWithIndex.map{case (output,idx) =>
      JsArray(value.asInstanceOf[JsArray].elements(idx),output match {
        case s: String => JsString(s)
        case b: Boolean => JsBoolean(b)
        case i: Int => JsNumber(i)
      })
    }.toVector)
  }
  val bw = new BufferedWriter(new FileWriter(outFile))
  bw.write(JsObject(res).prettyPrint)
  bw.close()
}
