package enumeration

import java.io.{File, FileOutputStream}

import ast._
import sygus.SygusFileTask
import trace.DebugPrints.dprintln

import scala.collection.mutable


object ProbUpdate {
  val fos = new FileOutputStream(new File("out_prog.txt"))

  def getAllNodeTypes(program: ASTNode): Set[Class[_]] = program.children.flatMap(c => getAllNodeTypes(c)).toSet + program.getClass

  var maximumFit: Double = 0
  var fitExamples = Set[Set[Any]]()
  var newPrior = 0.0

  def updatePriors(fits: Set[Set[Any]], currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask): Boolean = {
    fitExamples = fits
    var diff = mutable.Map[Class[_], Int]()
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0.2) {
        val examplesPassed = task.fitExs(program)
        val union = fitExamples + examplesPassed
        if (fitExamples.isEmpty || !fitExamples.contains(examplesPassed)) {
          fitExamples = union
          val changed: Set[Class[_]] = getAllNodeTypes(program)
          for (changedNode <- changed) {
            newPrior = (1.0 - fit) * priors(changedNode)
            if (!diff.contains(changedNode) || diff(changedNode) > newPrior)
              diff += (changedNode -> roundValue(newPrior))
          }
          Console.withOut(fos) { dprintln(fit, program.code, examplesPassed) }
        }
      }
    }
    diff.foreach(d => priors += d) //update the priors
    Console.withOut(fos) {
      dprintln(priors)
    }
    !diff.isEmpty
  }

  def getRootPrior(node: ASTNode): Int = priors(node.getClass)

  def roundValue(num: Double): Int = if (num == 0) 1 else if (num - num.toInt > 0.5) math.ceil(num).toInt else math.floor(num).toInt

  val priors = mutable.Map[Class[_], Int](
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
