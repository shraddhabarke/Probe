package enumeration

import java.io.{File, FileOutputStream}

import ast._
import sygus.SygusFileTask
import scala.collection.mutable

object ProbUpdate {
  var fos = new FileOutputStream("overview-ex.txt", true)
  var phaseChange: Boolean = false
  var newPrior = 0.0
  var fitSet = mutable.Map[Set[Any], List[ASTNode]]()
  var fitCost = mutable.Map[Set[Any], Double]()
  var fitProgs: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  var fitMap = mutable.Map[(Class[_],Option[Any]), Double]()
  var priors = mutable.Map[(Class[_], Option[Any]), Int]()

  def getAllNodeTypes(program: ASTNode): Set[(Class[_], Option[Any])] = {
    val recurseValue = if (program.isInstanceOf[StringLiteral] || program.isInstanceOf[IntLiteral] || program.isInstanceOf[StringVariable]
    || program.isInstanceOf[IntVariable] || program.isInstanceOf[StringLiteral] || program.isInstanceOf[BoolLiteral] || program.isInstanceOf[BoolVariable])
      (program.getClass -> Some(program.code)) else (program.getClass -> None)
      program.children.flatMap(c => getAllNodeTypes(c)).toSet + recurseValue
  }

  def updateFit(fitsMap: mutable.Map[(Class[_], Option[Any]), Double], currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask): mutable.Map[(Class[_], Option[Any]), Double] = {
    fitMap = fitsMap
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0) {
        val examplesPassed = task.fitExs(program)
        if (!fitCost.contains(examplesPassed) || (fitCost(examplesPassed) > program.cost) && !fitProgs.contains(program.code)) {
          fitCost += (examplesPassed -> program.cost)
          fitProgs += program.code
          val changed: Set[(Class[_], Option[Any])] = getAllNodeTypes(program)
          for (changedNode <- changed) {
            if (!fitMap.contains(changedNode) || fitMap(changedNode) > (1 - fit))
              fitMap += (changedNode -> (1 - fit))
          }
          Console.withOut(fos) { println(program.code, examplesPassed, program.cost) }
        }
      }
    }
    fitMap
  }

  def updatePriors(fitMap: mutable.Map[(Class[_], Option[Any]), Double]): Unit = {
    fitMap.foreach(d => priors += (d._1 -> roundValue(d._2 * priors(d._1))))
    Console.withOut(fos) { println(priors) }
  }

  def getRootPrior(node: ASTNode): Int = if (node.isInstanceOf[StringLiteral] || node.isInstanceOf[StringVariable] || node.isInstanceOf[IntVariable]
                                              || node.isInstanceOf[IntLiteral] || node.isInstanceOf[BoolVariable] || node.isInstanceOf[BoolLiteral]) {
                                        priors((node.getClass,Some(node.code)))
                                        } else priors((node.getClass, None))

  def roundValue(num: Double): Int = if (num < 1) 1 else if (num - num.toInt > 0.5) math.ceil(num).toInt else math.floor(num).toInt

  def resetPrior(): mutable.Map[(Class[_], Option[Any]), Int] = {
    priors.foreach(c => (c._1 -> 10))
    priors
  }

  def createPrior(vocab: VocabFactory): mutable.Map[(Class[_], Option[Any]), Int] = {
    vocab.leavesMakers.foreach(l => priors += ((l.nodeType, Some(l.head)) -> 10))
    vocab.nonLeaves().foreach(l => priors += ((l.nodeType, None) -> 10))
    priors
  }
}