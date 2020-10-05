package enumeration

import org.antlr.v4.runtime.{BailErrorStrategy, BufferedTokenStream, CharStreams, Token}
import sygus._
import ast._
import java.io.FileOutputStream
import sygus.SygusFileTask
import scala.collection.mutable.ListBuffer
import scala.collection.mutable

object ProbUpdate {

  trace.DebugPrints.setInfo()
  var phaseChange: Boolean = false
  var newPrior = 0.0
  var count = 0
  var cache = mutable.Map[String, Double]()
  var cacheCost = mutable.Map[Set[Any], Double]()
  var cacheExamples = mutable.ListBuffer[Set[Any]]()
  var cacheStrings: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  var fitMap = mutable.Map[(Class[_],Option[Any]), Double]()
  var probMap = mutable.Map[(Class[_], Option[Any]), Double]()
  var priors = mutable.Map[(Class[_], Option[Any]), Int]()
  var examplesCovered = mutable.ListBuffer[Set[Any]]()
  var maximalExamples = mutable.Set[Any]()
  var currBest = Set[Any]()
  val lnOf2 = scala.math.log(2) // natural log of 2
  var fos = new FileOutputStream("motivating.txt", true)
  def log2(x: Double): Double = scala.math.log(x) / lnOf2
  def expo (i: Double, exp:Double):Double = scala.math.pow(i,exp)

  def getAllNodeTypes(program: ASTNode): Set[(Class[_], Option[Any])] = {
    val recurseValue = if (program.isInstanceOf[StringLiteral] || program.isInstanceOf[IntLiteral] || program.isInstanceOf[StringVariable]
    || program.isInstanceOf[IntVariable] || program.isInstanceOf[StringLiteral] || program.isInstanceOf[BoolLiteral] || program.isInstanceOf[BoolVariable]
    ||  program.isInstanceOf[BVLiteral] || program.isInstanceOf[BVVariable])
      (program.getClass -> Some(program.code)) else (program.getClass -> None)
      program.children.flatMap(c => getAllNodeTypes(c)).toSet + recurseValue
  }
/**
  def update(fitsMap: mutable.Map[(Class[_], Option[Any]), Double], currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask): mutable.Map[(Class[_], Option[Any]), Double] = {
    fitMap = fitsMap
    val examples = ListBuffer[Set[Any]]()
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0) {
        val examplesPassed = task.fitExs(program)
        examples += examplesPassed
        cacheCost += (examplesPassed -> program)
      }
    }
    if (!examples.isEmpty) {
      val theExample = examples.sortBy(_.toList.length).last
      if (!theExample.isEmpty) {
        if (currBest.toList.length < theExample.toList.length) {
          currBest = theExample
          val prog = cacheCost(theExample)
          //println(prog.code, theExample, prog.cost)
          val changed: Set[(Class[_], Option[Any])] = getAllNodeTypes(prog)
            for (changedNode <- changed) {
              if (!fitMap.contains(changedNode) || fitMap(changedNode) > (1 - theExample.toList.length)) {
                val update = expo(probMap(changedNode), (1- theExample.toList.length))
                fitMap += (changedNode -> update)
                probMap += (changedNode -> update)
              }
            }
          }
        }
      }
    fitMap
  }
**/

  def readjustCosts(task: SygusFileTask): Unit = this.synchronized {
    probMap = ProbUpdate.createProbMap(task.vocab)
    priors = ProbUpdate.createPrior(task.vocab)
    var localMap = mutable.Map[(Class[_],Option[Any]), Double]()
    for (program <- cache.keys) {
      val lexer = new SyGuSLexer(CharStreams.fromString(program))
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
      val changed: Set[(Class[_], Option[Any])] = getAllNodeTypes(ast)
      val exampleFit = task.fit(ast)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0) {
        val examplesPassed = task.fitExs(ast)
        //val union = maximalExamples.union(examplesPassed)
        //if (union.toList.length > maximalExamples.toList.length) {
            //maximalExamples = union
        //if (!cacheCost.contains(examplesPassed) || ((!examplesCovered.contains(examplesPassed)) && (cacheCost(examplesPassed) == program.cost))) {
        if (!cacheExamples.contains(examplesPassed)) {
        //if (!cacheCost.contains(examplesPassed) || ((cacheCost(examplesPassed) >= program.cost) && !cacheStrings.contains(program.code))) {
          cache += (ast.code -> examplesPassed.toList.length)
          cacheExamples += (examplesPassed)
          //cacheStrings += program.code
          //examples += examplesPassed
          val changed: Set[(Class[_], Option[Any])] = getAllNodeTypes(ast)
          for (changedNode <- changed) {
            if (!fitMap.contains(changedNode) || fitMap(changedNode) > (1 - fit)) {
              val update = expo(probMap(changedNode), (1- fit))
              fitMap += (changedNode -> update)
              probMap += (changedNode -> update)
            }
          }
          //println("Chosen partial solution:" , program.code, examplesPassed, program.cost)
          //Console.withOut(fos) { println("Chosen partial solution:" , ast.code, examplesPassed, ast.cost) }
        }
        //Console.withOut(fos) { println(program.code, examplesPassed, program.cost) }
      }
      /**
      val fit = (cache(ast.code).toFloat) / task.examples.length
      for (changedNode <- changed) {
        Console.withOut(fos) { (task.examples) }
        if (!localMap.contains(changedNode) || localMap(changedNode) > (1 - fit)) {
          val update = expo(ProbUpdate.probMap(changedNode), (1 - fit))
          localMap += (changedNode -> update)
          probMap += (changedNode -> update)
        }
      }
    }
    **/
  } 
}

  def update(fitsMap: mutable.Map[(Class[_], Option[Any]), Double], currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask): mutable.Map[(Class[_], Option[Any]), Double] = {
    fitMap = fitsMap
    val examples = ListBuffer[Set[Any]]()
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0) {
        val examplesPassed = task.fitExs(program)
        //val union = maximalExamples.union(examplesPassed)
        //if (union.toList.length > maximalExamples.toList.length) {
            //maximalExamples = union
        //if (!cacheCost.contains(examplesPassed) || ((!examplesCovered.contains(examplesPassed)) && (cacheCost(examplesPassed) == program.cost))) {
        if (!cacheCost.contains(examplesPassed)) {
        //if (!cacheExamples.contains(examplesPassed)) {
        //if (!cacheCost.contains(examplesPassed) || ((cacheCost(examplesPassed) >= program.cost) && !cacheStrings.contains(program.code))) {
          //cache += (program.code -> examplesPassed.toList.length)
          cacheCost += (examplesPassed -> program.cost)
          cacheExamples += (examplesPassed)
        cacheStrings += program.code
          //examples += examplesPassed
          val changed: Set[(Class[_], Option[Any])] = getAllNodeTypes(program)
          for (changedNode <- changed) {
            if (!fitMap.contains(changedNode) || fitMap(changedNode) > (1 - fit)) {
              val update = expo(probMap(changedNode), (1- fit))
              fitMap += (changedNode -> update)
              probMap += (changedNode -> update)
            }
          }
          println(program.code, examplesPassed, program.cost)
          //Console.withOut(fos) { println(program.code, examplesPassed, program.cost) }
        }
      //Console.withOut(fos) { println(program.code, examplesPassed, program.cost) }
      }
    }
    examplesCovered = examplesCovered ++ examples
    fitMap
  }

  def updatePriors(pMap: mutable.Map[(Class[_], Option[Any]), Double], round: Int): mutable.Map[(Class[_], Option[Any]), Int] = {
    val probList = pMap.map(c => c._2)
    probMap = pMap.map(c => (c._1 -> (c._2.toFloat / probList.sum)))
    probMap.map(c => priors += (c._1 -> roundValue(-log2(c._2), round)))
    priors
  }

  def getRootPrior(node: ASTNode): Int = if (node.isInstanceOf[StringLiteral] || node.isInstanceOf[StringVariable] || node.isInstanceOf[IntVariable]
                                              || node.isInstanceOf[IntLiteral] || node.isInstanceOf[BoolVariable] || node.isInstanceOf[BoolLiteral]
                                              || node.isInstanceOf[BVVariable] || node.isInstanceOf[BVLiteral]) {
                                        priors((node.getClass,Some(node.code)))
                                        } else priors((node.getClass, None))

  def roundValue(num: Double, round: Int): Int = if (num < 1) 1
  //else if (num > round) round //todo: test with 4
  else if (num - num.toInt > 0.5) math.ceil(num).toInt else math.floor(num).toInt

  def createRoundValue(num: Double): Int =
    if (num - num.toInt > 0.5) math.ceil(num).toInt else math.floor(num).toInt

  def resetPrior(): mutable.Map[(Class[_], Option[Any]), Int] = {
    priors.map(c => (c._1 -> createRoundValue(-log2(probMap((c._1))))))
    priors
  }

  def createPrior(vocab: VocabFactory): mutable.Map[(Class[_], Option[Any]), Int] = {
    vocab.leavesMakers.map(l => priors += ((l.nodeType, Some(l.head)) -> createRoundValue(-log2(probMap((l.nodeType, Some(l.head)))))))
    vocab.nodeMakers.map(l => priors += ((l.nodeType, None) -> createRoundValue(-log2(probMap((l.nodeType, None))))))
    priors
  }

  def createProbMap(vocab: VocabFactory): mutable.Map[(Class[_], Option[Any]), Double] = {
    val uniform = 1.0 / (vocab.leavesMakers.length + vocab.nonLeaves().length)
    vocab.leavesMakers.map(l => probMap += ((l.nodeType, Some(l.head)) -> uniform))
    vocab.nodeMakers.map(l => probMap += ((l.nodeType, None) -> uniform))
    probMap
  }
}