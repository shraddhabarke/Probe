package enumeration

import ast._
import sygus.SygusFileTask

import scala.collection.mutable

object ProbUpdate {

  trace.DebugPrints.setInfo()
  var phaseChange: Boolean = false
  var newPrior = 0.0
  var cache = mutable.Map[ASTNode, Double]()
  var cacheCost = mutable.Map[Set[Any], Double]()
  var cacheStrings: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  var fitMap = mutable.Map[(Class[_],Option[Any]), Double]()
  var probMap = mutable.Map[(Class[_], Option[Any]), Double]()
  var priors = mutable.Map[(Class[_], Option[Any]), Int]()
  val lnOf2 = scala.math.log(2) // natural log of 2
  def log2(x: Double): Double = scala.math.log(x) / lnOf2
  def expo (i: Double, exp:Double):Double = scala.math.pow(i,exp)

  def getAllNodeTypes(program: ASTNode): Set[(Class[_], Option[Any])] = {
    val recurseValue = if (program.isInstanceOf[StringLiteral] || program.isInstanceOf[IntLiteral] || program.isInstanceOf[StringVariable]
    || program.isInstanceOf[IntVariable] || program.isInstanceOf[StringLiteral] || program.isInstanceOf[BoolLiteral] || program.isInstanceOf[BoolVariable]
    ||  program.isInstanceOf[BVLiteral] || program.isInstanceOf[BVVariable])
      (program.getClass -> Some(program.code)) else (program.getClass -> None)
      program.children.flatMap(c => getAllNodeTypes(c)).toSet + recurseValue
  }

  def readjustCosts(task: SygusFileTask): Unit = this.synchronized {
    probMap = ProbUpdate.createProbMap(task.vocab)
    priors = ProbUpdate.createPrior(task.vocab)
    var localMap = mutable.Map[(Class[_],Option[Any]), Double]()
    for (program <- cache.keys) {
      val changed: Set[(Class[_], Option[Any])] = getAllNodeTypes(program)
      val fit = (cache(program).toFloat) / task.examples.length
      for (changedNode <- changed) {
        if (!localMap.contains(changedNode) || localMap(changedNode) > (1 - fit)) {
          val update = expo(ProbUpdate.probMap(changedNode), (1 - fit))
          localMap += (changedNode -> update)
          probMap += (changedNode -> update)
        }
      }
    }
  }

  def update(fitsMap: mutable.Map[(Class[_], Option[Any]), Double], currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask): mutable.Map[(Class[_], Option[Any]), Double] = {
    fitMap = fitsMap
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0) {
        val examplesPassed = task.fitExs(program)
        if (!cacheCost.contains(examplesPassed) || ((cacheCost(examplesPassed) >= program.cost) && !cacheStrings.contains(program.code))) {
          cache += (program -> examplesPassed.toList.length)
          cacheCost += (examplesPassed -> program.cost)
          cacheStrings += program.code
          val changed: Set[(Class[_], Option[Any])] = getAllNodeTypes(program)
          for (changedNode <- changed) {
            if (!fitMap.contains(changedNode) || fitMap(changedNode) > (1 - fit)) {
              val update = expo(probMap(changedNode), (1- fit))
              fitMap += (changedNode -> update)
              probMap += (changedNode -> update)
            }
          }
        }
      }
    }
    fitMap
  }

  def updatePriors(pMap: mutable.Map[(Class[_], Option[Any]), Double]): mutable.Map[(Class[_], Option[Any]), Int] = {
    val probList = pMap.map(c => c._2)
    probMap = pMap.map(c => (c._1 -> (c._2.toFloat / probList.sum)))
    probMap.map(c => priors += (c._1 -> roundValue(-log2(c._2))))
    priors
  }

  def getRootPrior(node: ASTNode): Int = if (node.isInstanceOf[StringLiteral] || node.isInstanceOf[StringVariable] || node.isInstanceOf[IntVariable]
                                              || node.isInstanceOf[IntLiteral] || node.isInstanceOf[BoolVariable] || node.isInstanceOf[BoolLiteral]
                                              || node.isInstanceOf[BVVariable] || node.isInstanceOf[BVLiteral]) {
                                        priors((node.getClass,Some(node.code)))
                                        } else priors((node.getClass, None))

  def roundValue(num: Double): Int = if (num < 1) 1 else if (num > 4) 4 else if (num - num.toInt > 0.5) math.ceil(num).toInt else math.floor(num).toInt //todo: test

  def resetPrior(): mutable.Map[(Class[_], Option[Any]), Int] = {
    priors.map(c => (c._1 -> roundValue(-log2(probMap((c._1))))))
    priors
  }

  def createPrior(vocab: VocabFactory): mutable.Map[(Class[_], Option[Any]), Int] = {
    vocab.leavesMakers.map(l => priors += ((l.nodeType, Some(l.head)) -> roundValue(-log2(probMap((l.nodeType, Some(l.head)))))))
    vocab.nodeMakers.map(l => priors += ((l.nodeType, None) -> roundValue(-log2(probMap((l.nodeType, None))))))
    priors
  }

  def createProbMap(vocab: VocabFactory): mutable.Map[(Class[_], Option[Any]), Double] = {
    val uniform = 1.0 / (vocab.leavesMakers.length + vocab.nonLeaves().length)
    vocab.leavesMakers.map(l => probMap += ((l.nodeType, Some(l.head)) -> uniform))
    vocab.nodeMakers.map(l => probMap += ((l.nodeType, None) -> uniform))
    probMap
  }
}