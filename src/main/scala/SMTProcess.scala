import org.antlr.v4.runtime.{BufferedTokenStream, CharStreams}
import sygus.{SyGuSLexer, SyGuSParser}

import collection.JavaConverters._
import ast._

import scala.collection.mutable.ListBuffer
import scala.sys.process._

object SMTProcess {
  val cvc4exe = "C:\\cvc4-1.7-win64-opt.exe"
  val cvc4_SyGus = cvc4exe + " --sygus-out=status-or-def --lang sygus -m" //" --cegqi-si=all --sygus-out=status-or-def --lang sygus"
  val cvc4_Smt = cvc4exe + " --lang smt -m" //" --cegqi-si=all --sygus-out=status-or-def --lang sygus"

  def invokeCVC(task: String, cmd: String): List[String] = {
    var out: List[String] = null
    val io = BasicIO.standard{ostream =>
      ostream.write(task.getBytes)
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

  def toSMT(syData: String): String = {
    val parsed = new SyGuSParser(new BufferedTokenStream(new SyGuSLexer(CharStreams.fromString(syData)))).syGuS()
    val synthFun = parsed.cmd().asScala.filter(cmd => cmd.getChild(1) != null && cmd.getChild(1).getText == "synth-fun").head
    val defineFun = parsed.cmd().asScala.filter(cmd => cmd.smtCmd() != null).map(_.smtCmd()).filter(cmd => cmd.getChild(1).getText == "define-fun").head
    val functionName = synthFun.Symbol(0).getSymbol.getText
    val functionReturnType = Types.withName(synthFun.sort().getText.replaceAllLiterally("(","").replaceAllLiterally(")",""))
    val functionParameters = synthFun.sortedVar().asScala.map(svar =>
      (svar.Symbol().getText -> svar.sort().getText.replaceAllLiterally("(","").replaceAllLiterally(")","").replaceAll("64", " 64"))).toList
    val functionParametersString = functionParameters.map{v => v._1}.mkString(" ")
    val targetTerm = for (i <- 0 to 5 if defineFun.term().term(i) != null)
      yield {defineFun.term().term(i).getText}
    val lhs = '(' + defineFun.term().identifier().getText + targetTerm.mkString("") + ')'
    val lhsFormat = functionParameters.foldLeft(lhs)((curr, str) => curr.replaceAll(s"(?<![#v])${str._1}", s" ${str._1}"))
      .replaceAll(s"(?<![\\(])\\(", s" \\(").replaceAll(s"\\)(?![\\)])", s"\\) ")
      .replaceAll("  +", " ").replaceAll("\\s+$", "").replaceAll("^\\s+", "")
    val rhs = '(' + functionName + " " + functionParametersString + ')'

    val smtString = "(set-option :produce-models true)\n" +
      "(set-logic ALL)\n" +
        functionParameters.map{v => s"(declare-const ${v._1} (_ ${v._2}))"}.mkString("", "\n", "\n") +
        s"(declare-fun $functionName" + " (" + functionParameters.map(v => s"(_ ${v._2})").mkString(" ") + ") " + s"(_ ${functionReturnType.toString.replaceAll("64", " 64")}))\n" +
        s"(assert (not (= $lhsFormat $rhs)))\n" +
        "(check-sat)\n" +
        s"(get-value ($functionParametersString))"

    smtString
  }

  def checkSat(solverOut: List[String]): Boolean = if (solverOut.head == "sat") true else false

  def getCEx(query: List[String], solverOut: List[String]) : ListBuffer[Map[String, Any]] = {
    var modelMap: ListBuffer[Map[String, Any]] = ListBuffer()
    val words = solverOut.last.split("\\) \\(").toList.map(c => c.substring(c.indexOf("bv") + 2, c.indexOf("64")).trim)
    modelMap += (query zip words).toMap
    modelMap
  }
}
