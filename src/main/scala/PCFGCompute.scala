package sygus
import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Parser, RecognitionException, Token}
import enumeration.ProbUpdate
import scala.io.Source
import scala.collection.mutable
import scala.collection.mutable.{Map => MutableMap}
import scala.util.matching.Regex
import ujson.Value
import ast._
import collection.JavaConverters.asScalaBufferConverter
//args(0) is the long version filename; args(1) is the string solution of the normal version.
object PCFGCompute extends App {

    class EOFExpectedException(recognizer: Parser) extends RecognitionException(recognizer,recognizer.getInputStream(), recognizer.getContext) {
        this.setOffendingToken(recognizer.getCurrentToken)
    }

    val tokenToClass: Map[String, (Class[_], Option[Any])] = Map(
        "str.++" -> (classOf[StringConcat], None),
        "-" -> (classOf[IntSubtraction], None),
        "+" -> (classOf[IntAddition], None),
        "str.indexof" -> (classOf[IndexOf], None),
        "str.len" -> (classOf[StringLength], None),
        "str.substr" -> (classOf[Substring], None),
        "str.at" -> (classOf[StringAt], None),
        "<=" -> (classOf[IntLessThanEq], None),
        "=" -> (classOf[IntEquals], None), // todo: BoolEquals
        "str.prefixof" -> (classOf[PrefixOf], None),
        "str.suffixof" -> (classOf[SuffixOf], None),
        "str.contains" -> (classOf[Contains], None),
        "str.replace" -> (classOf[StringReplace], None),
        "int.to.str" -> (classOf[IntToString], None),
        "str.to.int" -> (classOf[StringToInt], None),
        "ite" -> (classOf[StringITE], None),
        "bvnot" -> (classOf[BVNot], None),
        "bvneg" -> (classOf[BVNeg], None),
        "not" -> (classOf[LNot], None),
        "bvredor" -> (classOf[BVRedor], None),
        "_arg_0" -> (classOf[StringVariable], Some("_arg_0")),
        "_arg_1" -> (classOf[StringVariable], Some("_arg_1")),
        "_arg_2" -> (classOf[StringVariable], Some("_arg_2")),
        "1" -> (classOf[IntLiteral], Some("1")),
        "2" -> (classOf[IntLiteral], Some("2")),
        "-1" -> (classOf[IntLiteral], Some("-1")),
        "3" -> (classOf[IntLiteral], Some("3")),
        "4" -> (classOf[IntLiteral], Some("4")),
        "5" -> (classOf[IntLiteral], Some("5")),
        "6" -> (classOf[IntLiteral], Some("6")),
        "7" -> (classOf[IntLiteral], Some("7")),
        "8" -> (classOf[IntLiteral], Some("8")),
        "9" -> (classOf[IntLiteral], Some("9")),
        "0" -> (classOf[IntLiteral], Some("0")),
        "true" -> (classOf[BoolLiteral], Some("true")),
        "false" -> (classOf[BoolLiteral], Some("false")),
        "\".\"" -> (classOf[StringLiteral], Some("\".\"")),
        "\"\"" -> (classOf[StringLiteral], Some("\"\"")),
        "\" \"" -> (classOf[StringLiteral], Some("\" \"")),
        "BRD" -> (classOf[StringLiteral], Some("BRD")),
        "DRS" -> (classOf[StringLiteral], Some("DRS")),
        "LDS" -> (classOf[StringLiteral], Some("LDS")),
        "Direct Response" -> (classOf[StringLiteral], Some("Direct Response")),
        "Branding" -> (classOf[StringLiteral], Some("Branding")),
        "Leads" -> (classOf[StringLiteral], Some("Leads")),
        "\"=\"" -> (classOf[StringLiteral], Some("\"=\"")),
        "\"/\"" -> (classOf[StringLiteral], Some("\"/\"")),
        "in" -> (classOf[StringLiteral], Some("in")),
        "\"_\"" -> (classOf[StringLiteral], Some("\"_\"")),
        "\"9\"" -> (classOf[StringLiteral], Some("\"9\"")),
        "\"1\"" -> (classOf[StringLiteral], Some("\"1\"")),
        "\"2\"" -> (classOf[StringLiteral], Some("\"2\"")),
        "\"3\"" -> (classOf[StringLiteral], Some("\"3\"")),
        "\"4\"" -> (classOf[StringLiteral], Some("\"4\"")),
        "\"5\"" -> (classOf[StringLiteral], Some("\"5\"")),
        "\"6\"" -> (classOf[StringLiteral], Some("\"6\"")),
        "\"7\"" -> (classOf[StringLiteral], Some("\"7\"")),
        "\"8\"" -> (classOf[StringLiteral], Some("\"8\"")),
        "\"0\"" -> (classOf[StringLiteral], Some("\"0\"")),
        "\"-\"" -> (classOf[StringLiteral], Some("\"-\"")),
        "\".\"" -> (classOf[StringLiteral], Some("\".\"")),
        "\",\"" -> (classOf[StringLiteral], Some("\",\"")),
        "microsoft" -> (classOf[StringLiteral], Some("microsoft")),
        "windows" -> (classOf[StringLiteral], Some("windows")),
        "apple" -> (classOf[StringLiteral], Some("apple")),
        "mac" -> (classOf[StringLiteral], Some("mac")),
        "bananas" -> (classOf[StringLiteral], Some("bananas")),
        "strawberries" -> (classOf[StringLiteral], Some("strawberries")),
        "oranges" -> (classOf[StringLiteral], Some("oranges")),
        "LLC" -> (classOf[StringLiteral], Some("LLC")),
        "Inc" -> (classOf[StringLiteral], Some("Inc")),
        "Corporation" -> (classOf[StringLiteral], Some("Corporation")),
        "Enterprises" -> (classOf[StringLiteral], Some("Enterprises")),
        "Company" -> (classOf[StringLiteral], Some("Company")),
        "\"<\"" -> (classOf[StringLiteral], Some("\"<\"")),
        "\">\"" -> (classOf[StringLiteral], Some("\">\"")),
        "\"/n\"" -> (classOf[StringLiteral], Some("\"/n\"")),
        "\"%\"" -> (classOf[StringLiteral], Some("\"%\"")),
        "\"b\"" -> (classOf[StringLiteral], Some("\"b\"")),
        "\"(\"" -> (classOf[StringLiteral], Some("\"(\"")),
        "\")\"" -> (classOf[StringLiteral], Some("\")\"")),
        "\"+\"" -> (classOf[StringLiteral], Some("\"+\"")),
        "\"name\"" -> (classOf[StringLiteral], Some("\"name\"")),
        "\",\"" -> (classOf[StringLiteral], Some("\",\""))
        //"Leads" "=" "/" "in" "_" "9" "." "microsoft" "windows" "apple" "mac" "-" "1" "2" "3" "4" "5" "6" "7" "8" "0" "," "<" ">" "/n" "%" "b" "apple" "bananas" "strawberries" "oranges" "LLC" "Inc" "Corporation" "Enterprises" "Company" "(" ")" "+" "name" ","
    )

    def readCompletionsFromFile(filePath: String): ujson.Value = {
        val source = Source.fromFile(filePath)
        val jsonString = try source.mkString finally source.close()
        val json = ujson.read(jsonString)
        json
    }
    var aggregateOperationCounts = mutable.Map.empty[(Class[_], Option[Any]), Int].withDefaultValue(0)
    
    def updateAggregateCounts(tokenCounts: Map[String, Int]): Unit = {
        tokenCounts.foreach { case (token, count) =>
            tokenToClass.get(token).foreach { opClass =>
                //println("Inside updateAggregateCounts " + opClass + count)
                aggregateOperationCounts(opClass) += count
            }
        }
    }

    def evalExpr(filename: String, s: String): Unit = {
        val task = new SygusFileTask(scala.io.Source.fromFile(filename).mkString)
        val lexer = new SyGuSLexer(CharStreams.fromString(s))
        val alltokens = new BufferedTokenStream(lexer)
        lexer.removeErrorListeners()
        lexer.addErrorListener(new ThrowingLexerErrorListener)
        alltokens.fill()
        val tokens = alltokens.getTokens.asScala.map(_.getText).filterNot(t => t == "(" || t == ")" || t == "<EOF>")
        val tokenCounts = tokens.groupBy(identity).view.mapValues(_.size).toMap
        //println("Token counts excluding parentheses:")
        //tokenCounts.foreach { case (token, count) =>
            //println(s"$token: $count")
        //}

        try {
            val parser = new SyGuSParser(new BufferedTokenStream(lexer))
            val parsed = new SyGuSParser(new BufferedTokenStream(new SyGuSLexer(CharStreams.fromString(s)))).bfTerm()
            val visitor = new ASTGenerator(task)
            val ast = visitor.visit(parsed)
            val exampleFit = task.fit(ast)
            val changed = ProbUpdate.getAllNodeTypesCount(ast)
            //println("AST Correct:" + ast.code)
            changed.foreach { case (clazz, matchCount) =>
                aggregateOperationCounts(clazz) += matchCount
            }
        }
        catch {
        case e: Exception => 
            //println(s"Failed to parse and fit, using token counts for aggregate operations. Error: ${e.getMessage}")
            //println("AST Incorrect:" + s)
            updateAggregateCounts(tokenCounts) // Update aggregate counts if parsing fails
            //println("Aggregate Operation Counts:")
            //aggregateOperationCounts.foreach { case (operation, count) =>
                //println(s"$operation: $count")
            //}
        }
    }

    def processElementByKey(json: String, elementKey: String) = {
        val completionsMap = readCompletionsFromFile(json)
        val sfile = elementKey.split("/").last
        //println("Filename:" + sfile)
        completionsMap(sfile)
        val completionsValue = completionsMap(sfile)("solutions")
        val completions = completionsValue.arr.toSeq.map(_.str)
        val task = new SygusFileTask(scala.io.Source.fromFile(elementKey).mkString)
        //val task = new SygusFileTask(scala.io.Source.fromFile(s"src/test/benchmarks/larger-grammar/$elementKey").mkString)
        val probMap: mutable.Map[(Class[_], Option[Any]), Double] = ProbUpdate.createProbMap(task.vocab) // initial probabilities
        val numberOfUniqueOperations = probMap.size
        //val aggregate_operation_counts = mutable.Map.empty[(Class[_], Option[Any]), Int].withDefaultValue(0)

        // Get the frequency of all the Sygus Operation Counts
        //"""
        completions.foreach { completion =>
            //println("Completion:" + completion)
            val program = evalExpr(elementKey, completion)
        }
        //println("aggregateOperationCounts" + aggregateOperationCounts)
        
        //aggregateOperationCounts.foreach { case (operation, count) =>
            //println(s"$operation: $count")
        //}
        val adjustedTotalOperationsCount = aggregateOperationCounts.values.sum + (1 * numberOfUniqueOperations)
        def log2(x: Double): Double = scala.math.log(x) / scala.math.log(2)
        val updatedProbabilities = probMap.map { case (operationKey, _) =>
            val count = aggregateOperationCounts.getOrElse(operationKey, 0)
            val probability = (count.toDouble + 1) / adjustedTotalOperationsCount
            operationKey -> probability
        }

        val updatedPriors = probMap.map { case (operationKey, _) =>
            val count = aggregateOperationCounts.getOrElse(operationKey, 0)
            val probability = ProbUpdate.createRoundValue(-log2((count.toDouble + 1) / adjustedTotalOperationsCount))
            operationKey -> probability
        }
    
        //println(s"Updated probabilities for $elementKey with Laplace smoothing: $updatedProbabilities")
        //println(s"Updated priors for $elementKey with Laplace smoothing: $updatedPriors")
        (updatedProbabilities, updatedPriors)
        
    }
    ///Users/shraddhabarke/arga-arc/sygus/string-completions.gpt-4o.100.json
    //val filename = "ncompletions/larger-string-completions.deepseek-100.json"
    //val jsonString = Source.fromFile(filename).mkString
    //val json = ujson.read(jsonString)
    //json.obj.foreach { case (taskName, taskData) =>
     //   val taskFilePath = s"src/test/benchmarks/larger-grammar/$taskName"
     //   processElementByKey(filename, taskFilePath)
    //}
    //processElementByKey("ncompletions/larger-string-completions.gpt-3.5-turbo.10.json", "src/test/benchmarks/larger-grammar/exceljet2modified.sl")
    //processElementByKey("ncompletions/larger-string-completions.gpt-3.5-turbo.10.json", "src/test/benchmarks/larger-grammar/31753108modified.sl")
    //processElementByKey("ncompletions/larger-string-completions.gpt-3.5-turbo.10.json", "src/test/benchmarks/larger-grammar/find-nth-occurrence-of-charactermodified.sl")
    //processElementByKey("ncompletions/larger-string-completions.gpt-3.5-turbo.10.json", "src/test/benchmarks/larger-grammar/clean-and-reformat-telephone-numbersmodified.sl")
    //processElementByKey("ncompletions/larger-string-completions.gpt-3.5-turbo.10.json", "src/test/benchmarks/larger-grammar/17212077modified.sl")
    //evalExpr("src/test/benchmarks/larger-grammar/exceljet2modified.sl", "(str.substr _arg_0 (+ (str.indexof _arg_0 \".\" DRS) 1) (str.len _arg_0))")
}