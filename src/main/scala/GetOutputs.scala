package sygus
import ast.ASTNode
import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Parser, RecognitionException, Token}
import enumeration.ProbUpdate
import scala.io.Source
import scala.collection.mutable
import scala.collection.mutable.{Map => MutableMap}
import ujson.Value
import scala.util.matching.Regex
import java.io.{File, FileWriter, PrintWriter}
import ujson._

//args(0) is the long version filename; args(1) is the string solution of the normal version.
object GetOutputs extends App {

    class EOFExpectedException(recognizer: Parser) extends RecognitionException(recognizer,recognizer.getInputStream(), recognizer.getContext) {
        this.setOffendingToken(recognizer.getCurrentToken)
    }

    def readCompletionsFromFile(filePath: String): ujson.Value = {
        val source = Source.fromFile(filePath)
        val jsonString = try source.mkString finally source.close()
        val json = ujson.read(jsonString)
        json
    }

    // filename
    def getCEx(json: String, filename: String): String = {
        //val model = solverOut.last.split("\\) \\(").toList.map(c => {java.lang.Long.parseUnsignedLong(c.substring(c.indexOf("#b") + 2)
        //.replaceAll("\\)", ""), 2).asInstanceOf[AnyRef]}) -- bitvector
        //todo -- val cex = SMTProcess.getCEx(funcArgs, solverOut)
        val values = readCompletionsFromFile(json)
        val sfile = filename.split("/").last
        val source = scala.io.Source.fromFile(filename)
        val origTask = new SygusFileTask(scala.io.Source.fromFile(filename).mkString)
        val out = SMTProcess.toSMT(source.mkString)
        val smtOut = out._1
        val solution = out._3 // String
        val query = out._2 // List[String]
        val inputValues = values(sfile)
        val transformedInputValues = inputValues.arr.map { inputValue =>
            val inputs = inputValue("inputs-modified").arr.map { input =>
                input.num.toLong
            }
            val inputsList = Iterable((query zip inputs).toMap)
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
            println("output-correct" + ujson.Str(ast.values.head.toString))
            inputValue.obj.put("output-correct", ujson.Str(ast.values.head.toString))
            inputValue
        }
        ujson.write(transformedInputValues)
        }

        val directoryPath = "src/test/benchmarks/hackers-delight/"
        val jsonFilePath = "output.json" //"completions/hackers-delight-generated-examples.json"
        val outputFileName = "aggregate-results-bitvec.json" // Name of the file where you want to save all results
        val outputFile = new File(directoryPath + outputFileName)
        val pw = new PrintWriter(new FileWriter(outputFile, true)) // Open for 
        val resultsMap = scala.collection.mutable.Map[String, ujson.Value]()

        try {
            new File(directoryPath).listFiles
            .filter(file => file.isFile && file.getName.endsWith(".sl"))
            .foreach { file =>
                val resultJsonString = getCEx(jsonFilePath, file.getPath)
                val resultJsonValue = ujson.read(resultJsonString)
                resultsMap(file.getName) = resultJsonValue
            }
        val aggregatedResultsJson = ujson.Obj.from(resultsMap.toMap)
        val pw = new PrintWriter(outputFile)
        try {
            pw.write(aggregatedResultsJson.render(indent = 4)) // Pretty print the JSON
        } finally {
            pw.close()
        }
        } catch {
        case e: Exception => e.printStackTrace()
    }
}