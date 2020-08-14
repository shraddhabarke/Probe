package sygus

import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Token}
import sygus.{ASTGenerator, Example, SyGuSLexer, SyGuSParser, SygusFileTask, ThrowingLexerErrorListener}

import collection.JavaConverters._
import ast._

import scala.sys.process._

object SMTProcess {
  val cvc4exe = "C:\\cvc4-1.8-win64-opt.exe"
  val cvc4_SyGus = cvc4exe + " --sygus-out=status-or-def --lang sygus1 -m" //" --cegqi-si=all --sygus-out=status-or-def --lang sygus"
  val cvc4_Smt = cvc4exe + " --lang smt -m" //" --cegqi-si=all --sygus-out=status-or-def --lang sygus"

  def invokeCVC(task: String, cmd: String): List[String] = {
    var out: List[String] = null
    val io = BasicIO.standard{ostream =>
      ostream.write(task.getBytes())
      ostream.flush();
      ostream.close()
    }.withOutput{istream =>
      out = scala.io.Source.fromInputStream(istream).getLines().toList
    }
    val cvc4 = cmd.run(io)
    if(cvc4.exitValue() != 0) Nil
    else if (out.head == "unknown") Nil //unsynthesizable
    else out
  }

  def toSMT(syData: String, program: String): (String, List[String], String) = {
    val parsed = new SyGuSParser(new BufferedTokenStream(new SyGuSLexer(CharStreams.fromString(syData)))).syGuS()
    val synthFun = parsed.cmd().asScala.filter(cmd => cmd.getChild(1) != null && cmd.getChild(1).getText == "synth-fun").head
    val defineFun = parsed.cmd().asScala.filter(cmd => cmd.smtCmd() != null).map(_.smtCmd()).filter(cmd => cmd.getChild(1).getText == "define-fun").head
    val functionName = synthFun.Symbol(0).getSymbol.getText
    val functionReturnType = Types.withName(synthFun.sort().getText.replaceAllLiterally("(","").replaceAllLiterally(")",""))
    val functionParameters = synthFun.sortedVar().asScala.map(svar =>
      (svar.Symbol().getText -> svar.sort().getText.replaceAllLiterally("(","").replaceAllLiterally(")","").replaceAll("64", " 64"))).toList
    val targetTerm = for (i <- 0 to 10 if defineFun.term().term(i) != null)
      yield {defineFun.term().term(i).getText}
    val lhs = '(' + defineFun.term().identifier().getText + targetTerm.mkString("") + ')'
    val lhsFormat = functionParameters.foldLeft(lhs)((curr, str) => curr.replaceAll(s"(?<![#v])${str._1}", s" ${str._1}"))
      .replaceAll(s"(?<![\\(])\\(", s" \\(").replaceAll(s"\\)(?![\\)])", s"\\) ")
      .replaceAll("  +", " ").replaceAll("\\s+$", "").replaceAll("^\\s+", "")

    val smtString = "(set-option :produce-models true)\n" +
      "(set-logic ALL)\n" +
        functionParameters.map{v => s"(declare-const ${v._1} (_ ${v._2}))"}.mkString("", "\n", "\n") +
        s"(declare-fun $functionName" + " (" + functionParameters.map(v => s"(_ ${v._2})").mkString(" ") + ") " + s"(_ ${functionReturnType.toString.replaceAll("64", " 64")}))\n" +
        s"(assert (not (= $lhsFormat $program)))\n" +
        "(check-sat)\n" +
        s"(get-value (${functionParameters.map{v => v._1}.mkString(" ")}))"

    (smtString, functionParameters.map(c => c._1), lhsFormat)
  }

  def checkSat(solverOut: List[String]): Boolean = if (solverOut.head == "sat") true else false

  def getCEx(content: String, query: List[String], solverOut: List[String], solution: String): Example = {
    val model = solverOut.last.split("\\) \\(").toList.map(c => {java.lang.Long.parseUnsignedLong(c.substring(c.indexOf("#b") + 2)
      .replaceAll("\\)", ""), 2).asInstanceOf[AnyRef]})
    val inputsList = Iterable((query zip model).toMap)
    val origTask = new SygusFileTask(content)   //TODO: Fix circular dependency
    val task = origTask.enhance(inputsList)
    val lexer = new SyGuSLexer(CharStreams.fromString(solution))
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
    Example((query zip model).toMap, ast.values.head)
  }
}
