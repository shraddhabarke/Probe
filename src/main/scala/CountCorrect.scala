package sygus
import scala.io.Source
import ujson.Value
import ast.ASTNode
import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Parser, RecognitionException, Token}
import enumeration.ProbUpdate
import scala.io.Source
import scala.collection.mutable
import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.ArrayBuffer

object CountCorrect extends App {
    class EOFExpectedException(recognizer: Parser) extends RecognitionException(recognizer,recognizer.getInputStream(), recognizer.getContext) {
        this.setOffendingToken(recognizer.getCurrentToken)
    }

    val filename = "completions/larger-string-grammar-completions.json"
    val jsonString = Source.fromFile(filename).mkString
    val json = ujson.read(jsonString)

    def evalExpr(filename: String, s: String): Double = {
        val task = new SygusFileTask(scala.io.Source.fromFile(filename).mkString)
        val lexer = new SyGuSLexer(CharStreams.fromString(s))
        lexer.removeErrorListeners()
        lexer.addErrorListener(new ThrowingLexerErrorListener)
        val parser = new SyGuSParser(new BufferedTokenStream(lexer))
        parser.removeErrorListeners()
        parser.setErrorHandler(new BailErrorStrategy)
        val parsed = parser.bfTerm()
        if (parser.getCurrentToken.getType != Token.EOF)
        throw new EOFExpectedException(parser)
        val visitor = new ASTGenerator(task)
        val ast = visitor.visit(parsed)
        println(ast.code)
        val exampleFit = task.fit(ast)
        println((exampleFit._1.toFloat) / exampleFit._2)
        (exampleFit._1.toFloat) / exampleFit._2
    }

    json.obj.foreach { case (taskName, taskData) =>
        val taskFilePath = s"src/test/benchmarks/larger-grammar/$taskName"
        println(taskFilePath)
        val solutions: ArrayBuffer[String] = taskData("solutions").arr.map(_.str)
        val fitCounts = solutions.count(solution => 1.0 == evalExpr(taskFilePath, solution))
        json(taskName)("fit_count_of_1") = fitCounts
        println(fitCounts)
    }

    val modifiedJsonString = ujson.write(json, indent = 4)
    val outputFile = new java.io.File(filename.replace(".json", "_modified.json"))
    val writer = new java.io.PrintWriter(outputFile)
    try writer.write(modifiedJsonString)
    finally writer.close()

    println(s"Updated JSON written to ${outputFile.getAbsolutePath}")
}
