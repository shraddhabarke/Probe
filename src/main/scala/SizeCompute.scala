package sygus
import ast.ASTNode
import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Parser, RecognitionException, Token}
import sygus.{ASTGenerator, SyGuSLexer, SyGuSParser, SygusFileTask, ThrowingLexerErrorListener}
//args(0) is the long version filename; args(1) is the string solution of the normal version.
object SizeCompute extends App {

  class EOFExpectedException(recognizer: Parser) extends RecognitionException(recognizer,recognizer.getInputStream(), recognizer.getContext) {
    this.setOffendingToken(recognizer.getCurrentToken)
  }
  def evalExpr(filename: String, s: String): ASTNode = {
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
    //println(filename + "," + fit + "," + ast.code)
    println(filename + "," + ast.terms)
    ast
  }

  val eval = evalExpr(args(0), args(1))

}








