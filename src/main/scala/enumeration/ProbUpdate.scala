package enumeration

import java.io.{File, FileOutputStream}

import ast._
import sygus.SygusFileTask
import trace.DebugPrints.dprintln

import scala.collection.mutable

object ProbUpdate {
  var fos = new FileOutputStream("output_p.txt", true)
  var phaseChange: Boolean = false
  var newPrior = 0.0
  var fitSet = mutable.Map[Set[Any], List[ASTNode]]()
  var fitCost = mutable.Map[Set[Any], Double]()
  var fitProgs: mutable.ArrayBuffer[String] = mutable.ArrayBuffer()
  var fitMap = mutable.Map[Class[_], Double]()

  def getAllNodeTypes(program: ASTNode): Set[Class[_]] = program.children.flatMap(c => getAllNodeTypes(c)).toSet + program.getClass

  def updateFit(fitsMap: mutable.Map[Class[_], Double], currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask): mutable.Map[Class[_], Double] = {
    fitMap = fitsMap
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0) {
        val examplesPassed = task.fitExs(program)
        if (!fitCost.contains(examplesPassed) || (fitCost(examplesPassed) > program.cost) && !fitProgs.contains(program.code)) {
          fitCost += (examplesPassed -> program.cost)
          fitProgs += program.code
          val changed: Set[Class[_]] = getAllNodeTypes(program)
          for (changedNode <- changed) {
            if (!fitMap.contains(changedNode) || fitMap(changedNode) > (1 - fit))
              fitMap += (changedNode -> (1 - fit))
          }
        }
      }
    }
    fitMap
  }

  def updatePriors(fitMap: mutable.Map[Class[_], Double]): Unit = {
    fitMap.foreach(d => priors += (d._1 -> roundValue(d._2 * priors(d._1))))
    //Console.withOut(fos) {
    //  dprintln(priors)
    //}
  }

  def getRootPrior(node: ASTNode): Int = priors(node.getClass)

  def roundValue(num: Double): Int = if (num == 0) 1 else if (num - num.toInt > 0.5) math.ceil(num).toInt else math.floor(num).toInt

  var priors = mutable.Map[Class[_], Int](
    classOf[StringConcat] -> 10,
    classOf[StringAt] -> 10,
    classOf[IntAddition] -> 10,
    classOf[IntSubtraction] -> 10,
    classOf[IntLessThanEq] -> 10,
    classOf[IntEquals] -> 10,
    classOf[PrefixOf] -> 10,
    classOf[SuffixOf] -> 10,
    classOf[Contains] -> 10,
    classOf[StringLiteral] -> 10,
    classOf[IntLiteral] -> 10,
    classOf[BoolLiteral] -> 10,
    classOf[StringReplace] -> 10,
    classOf[StringITE] -> 10,
    classOf[IntITE] -> 10,
    classOf[Substring] -> 10,
    classOf[IndexOf] -> 10,
    classOf[IntToString] -> 10,
    classOf[StringToInt] -> 10,
    classOf[StringLength] -> 10,
    classOf[StringVariable] -> 10,
    classOf[IntVariable] -> 10,
    classOf[BoolVariable] -> 10,
  )

}