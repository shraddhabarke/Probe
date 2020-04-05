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

  def updatePriors(maxFit: Double, currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask): Boolean = {
    maximumFit = maxFit
    var diff = mutable.Map[Class[_], Double]()
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      if (exampleFit._1 > 0) {
        val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
        if (maximumFit < fit) {
          Console.withOut(fos) {dprintln(fit, program.code)}
          val changed: Set[Class[_]] = getAllNodeTypes(program)

          for (changedNode <- changed) {
            val newPrior = (1 - fit) * priors(changedNode)
            if (!diff.contains(changedNode) || diff(changedNode) > newPrior) //TODO: is this the right direction? Always get smaller?
              diff += (changedNode -> newPrior)
          }
          maximumFit = fit
        }
      }
    }

    diff.foreach(d => priors += d) //update the priors
    Console.withOut(fos) {dprintln(priors)}
    !diff.isEmpty
  }

  def getRootPrior(node: ASTNode): Double = priors(node.getClass)

  val priors = mutable.Map[Class[_], Double](
    classOf[StringConcat] -> 1,
    classOf[StringAt] -> 1,
    classOf[IntAddition] -> 1,
    classOf[IntSubtraction] -> 1,
    classOf[IntLessThanEq] -> 1,
    classOf[IntEquals] -> 1,
    classOf[PrefixOf] -> 1,
    classOf[SuffixOf] -> 1,
    classOf[Contains] -> 1,
    classOf[StringLiteral] -> 0.0625,
    classOf[IntLiteral] -> 1,
    classOf[BoolLiteral] -> 1,
    classOf[StringReplace] -> 0.25,
    classOf[StringITE] -> 1,
    classOf[IntITE] -> 1,
    classOf[Substring] -> 1,
    classOf[IndexOf] -> 1,
    classOf[IntToString] -> 1,
    classOf[StringToInt] -> 1,
    classOf[StringLength] -> 1,
    classOf[StringVariable] -> 0.5,
    classOf[IntVariable] -> 1,
    classOf[BoolVariable] -> 1,
  )

}
