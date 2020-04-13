package enumeration

import java.io.{File, FileOutputStream}

import ast._
import sygus.SygusFileTask
import trace.DebugPrints.dprintln

import scala.collection.mutable

object ProbUpdate {
  val fos = new FileOutputStream(new File("out_prog.txt"))
  var fitSet = Set[Set[Any]]()
  var phaseChange: Boolean = false
  var newPrior = 0.0
  var fitMap = mutable.Map[Class[_], Double]()

  def getAllNodeTypes(program: ASTNode): Set[Class[_]] = program.children.flatMap(c => getAllNodeTypes(c)).toSet + program.getClass

  def updateFit(fitsMap: mutable.Map[Class[_], Double],fitSoFar: Set[Set[Any]], currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask, phaseChangeCheck: Boolean): mutable.Map[Class[_], Double] = {
    fitSet = fitSoFar
    fitMap = fitsMap
    phaseChange = phaseChangeCheck
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0.2) {
        val examplesPassed = task.fitExs(program)
        val union = fitSet + examplesPassed
        if (fitSet.isEmpty || !fitSet.contains(examplesPassed)) { // first shortest programs that covers a given subset of examples
          fitSet = union
          val changed: Set[Class[_]] = getAllNodeTypes(program)
          for (changedNode <- changed) {
            if (!fitMap.contains(changedNode) || fitMap(changedNode) > (1 - fit))
              fitMap += (changedNode -> (1 - fit))
          }
        }
      }
    }
    phaseChange = !fitMap.isEmpty || phaseChangeCheck
    fitMap
  }

  //newPrior = (1.0 - fit) * priors(changedNode)
  //diff += (changedNode -> roundValue(newPrior))

  def updatePriors(fitMap: mutable.Map[Class[_], Double]): Unit = {
    fitMap.foreach(d => priors += (d._1 -> roundValue(d._2 * priors(d._1))))
    Console.withOut(fos) {
      dprintln(priors)
    }
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
