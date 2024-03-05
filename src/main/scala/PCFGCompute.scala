package sygus
import ast.ASTNode
import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Parser, RecognitionException, Token}
import enumeration.ProbUpdate
import scala.io.Source
import scala.collection.mutable
import scala.collection.mutable.{Map => MutableMap}
import ujson.Value
import scala.util.matching.Regex

//args(0) is the long version filename; args(1) is the string solution of the normal version.
object PCFGCompute {

    class EOFExpectedException(recognizer: Parser) extends RecognitionException(recognizer,recognizer.getInputStream(), recognizer.getContext) {
        this.setOffendingToken(recognizer.getCurrentToken)
    }

    def readCompletionsFromFile(filePath: String): ujson.Value = {
        val source = Source.fromFile(filePath)
        val jsonString = try source.mkString finally source.close()
        val json = ujson.read(jsonString)
        json
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
        val exampleFit = task.fit(ast)
        return ast
    }

    def processElementByKey(json: String, elementKey: String) = {
        val completionsMap = readCompletionsFromFile(json)
        val sfile = elementKey.split("/").last
        println("sfile" + sfile)
        completionsMap(sfile)
        val completionsValue = completionsMap(sfile)("solutions")
        val completions = completionsValue.arr.toSeq.map(_.str)
        val task = new SygusFileTask(scala.io.Source.fromFile(elementKey).mkString)
        //val task = new SygusFileTask(scala.io.Source.fromFile(s"src/test/benchmarks/larger-grammar/$elementKey").mkString)
        val probMap: mutable.Map[(Class[_], Option[Any]), Double] = ProbUpdate.createProbMap(task.vocab) // initial probabilities
        val numberOfUniqueOperations = probMap.size
        val aggregate_operation_counts = mutable.Map.empty[(Class[_], Option[Any]), Int].withDefaultValue(0)

        // Get the frequency of all the Sygus Operation Counts
        completions.foreach { completion =>
            val program = evalExpr(elementKey, completion)
            val changed = ProbUpdate.getAllNodeTypesCount(program)
            changed.foreach { case (clazz, matchCount) =>
                aggregate_operation_counts(clazz) += matchCount
            }
        }

        aggregate_operation_counts.foreach { case (operation, count) =>
            println(s"$operation: $count")
        }

        val adjustedTotalOperationsCount = aggregate_operation_counts.values.sum + (1 * numberOfUniqueOperations)
        def log2(x: Double): Double = scala.math.log(x) / scala.math.log(2)
        val updatedProbabilities = probMap.map { case (operationKey, _) =>
            val count = aggregate_operation_counts.getOrElse(operationKey, 0)
            val probability = (count.toDouble + 1) / adjustedTotalOperationsCount
            operationKey -> probability
        }

        val updatedPriors = probMap.map { case (operationKey, _) =>
            val count = aggregate_operation_counts.getOrElse(operationKey, 0)
            val probability = ProbUpdate.createRoundValue(-log2((count.toDouble + 1) / adjustedTotalOperationsCount))
            operationKey -> probability
        }
    
        //println(s"Updated probabilities for $elementKey with Laplace smoothing: $updatedProbabilities")
        //println(s"Updated priors for $elementKey with Laplace smoothing: $updatedPriors")
        (updatedProbabilities, updatedPriors)
    }
    //processElementByKey("completions/larger-string-grammar-completions.json", "exceljet2modified.sl")
}