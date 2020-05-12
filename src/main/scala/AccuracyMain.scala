package sygus
import ast.ASTNode
import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Token}
import pcShell.ShellMain.{EOFExpectedException, args, task, taskFilename}
import sygus.{ASTGenerator, SyGuSLexer, SyGuSParser, SygusFileTask, ThrowingLexerErrorListener}
//args(0) is the long version filename; args(1) is the string solution of the normal version.
object AccuracyMain extends App {

    def evalExpr(filename: String, s: String, resultPrinter: (String, ASTNode, Long) => String): Double = {
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
        val exampleFit = task.fit(ast)
        val fit = (exampleFit._1.toFloat) / exampleFit._2
        println(filename + "," + fit + "," + ast.code)
        fit
    }

    val eval = evalExpr(args(0), args(1), regularBenchmarkPrinter)
    
    def regularBenchmarkPrinter(filename: String, eval: ASTNode, fit: Long): String = {
    "," + filename + "," + eval.code + "," + fit
  }

}