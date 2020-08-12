import org.antlr.v4.runtime.{BufferedTokenStream, CharStreams}
import sygus.{SyGuSLexer, SyGuSParser}

import collection.JavaConverters._
import ast._
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
    print(cvc4)
    if(cvc4.exitValue() != 0) Nil
    else if (out.head == "unknown") Nil //unsynthesizable
    else out

  }
}
