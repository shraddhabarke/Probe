package sygus

import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Token}

import collection.JavaConverters._
import ast._

import scala.collection.mutable.ListBuffer
import scala.sys.process._

object SMTProcess {
  val cvc4exe = "cvc4" //"C:\\cvc4-1.8-win64-opt.exe"
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

  def getquery(program: String, smtStrings: List[String]): String = {
    var smtString = smtStrings.head + program + smtStrings.last
    smtString = smtString.replaceAll("\\(_ Bool\\)", "Bool").replaceAll("false", " false")
        .replaceAll("true", " true")
    smtString
  }

  def toSMT(syData: String): (List[String], List[String], String) = {
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
      .replaceAll("x#", "x #")

    val smtString1 = "(set-option :produce-models true)\n" +
      "(set-logic ALL)\n" +
        functionParameters.map{v => s"(declare-const ${v._1} (_ ${v._2}))"}.mkString("", "\n", "\n") +
        s"(declare-fun $functionName" + " (" + functionParameters.map(v => s"(_ ${v._2})").mkString(" ") + ") " + s"(_ ${functionReturnType.toString.replaceAll("64", " 64")}))\n" +
        s"(assert (not (= $lhsFormat "
    val smtString2 = s")))\n" +
        "(check-sat)\n" +
        s"(get-value (${functionParameters.map{v => v._1}.mkString(" ")}))"

    (List(smtString1,smtString2), functionParameters.map(c => c._1), lhsFormat)
  }

  def getCEx(origTask: SygusFileTask, query: List[String], solverOut: List[String], solution: String): Example = {
    val model = solverOut.last.split("\\) \\(").toList.map(c => {java.lang.Long.parseUnsignedLong(c.substring(c.indexOf("#b") + 2)
      .replaceAll("\\)", ""), 2).asInstanceOf[AnyRef]})
    //val model = solverOut.last.split("\\) \\(").toList.map(c => {java.lang.Boolean.parseBoolean(c.substring(c.indexOf(" ") + 1)
      //.replaceAll("\\)", ""))})
    val inputsList = Iterable((query zip model).toMap)
    val task = origTask.enhance(inputsList)
    val lexer = new SyGuSLexer(CharStreams.fromString(solution
      .replaceAll("false", " false")
      .replaceAll("true", " true")))
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

  def getEx(origTask: SygusFileTask, cExamples: List[Example], program: ASTNode): (Boolean, Example, List[Example]) = {
    val inputsList = cExamples.map(_.input)
    val task = origTask.enhance(inputsList)
    val lexer = new SyGuSLexer(CharStreams.fromString(program.code))
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
    if (cExamples.zip(ast.values).map(pair => pair._1.output == pair._2).forall(identity))
      (true, null, List())
    else {
      val cex = cExamples.zip(ast.values).map(pair => (pair, pair._1.output == pair._2)).find(_._2 == false).get._1._1
      (false, cex, cExamples.filter(_.input != cex.input))
    }
  }
}
