package enumeration

import ast._
import sygus.SygusFileTask

import scala.collection.mutable


object ProbUpdate {

  def getAllNodeTypes(program: ASTNode): Set[Class[_]] = program.children.flatMap(c => getAllNodeTypes(c)).toSet + program.getClass

  def updatePriors(currLevelProgs: mutable.ArrayBuffer[ASTNode], prevMap: mutable.Map[ast.VocabMaker, Double], task: SygusFileTask): Boolean = {
    var diff = mutable.Map[Class[_], Double]()
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      if (exampleFit._1 > 2) {
        val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
        val changed: Set[Class[_]] = getAllNodeTypes(program)

        for(changedNode <- changed) {
          val newPrior = fit * priors(changedNode)
          if (!diff.contains(changedNode) || diff(changedNode) > newPrior) //TODO: is this the right direction? Always get smaller?
            diff += (changedNode -> newPrior)
        }
      }
     }
    diff.foreach(d => priors += d) //update the priors
    !diff.isEmpty
  }

  def getRootPrior(node: ASTNode): Double = priors(node.getClass)
  val priors = mutable.Map[Class[_],Double](
    classOf[StringConcat] -> 1,
    classOf[StringAt] -> 1,
    classOf[IntAddition] -> 1,
    classOf[IntSubtraction] -> 1,
    classOf[IntLessThanEq] -> 1,
    classOf[IntEquals] -> 1,
    classOf[PrefixOf] -> 1,
    classOf[SuffixOf] -> 1,
    classOf[Contains] -> 1,
    classOf[StringLiteral] -> 1,
    classOf[IntLiteral] -> 1,
    classOf[BoolLiteral] -> 1,
    classOf[StringReplace] -> 1,
    classOf[StringITE] -> 1,
    classOf[IntITE] -> 1,
    classOf[Substring] -> 1,
    classOf[IndexOf] -> 1,
    classOf[IntToString] -> 1,
    classOf[StringToInt] -> 1,
    classOf[StringLength] -> 1,
    classOf[StringVariable] -> 1,
    classOf[IntVariable] -> 1,
    classOf[BoolVariable] -> 1,
  )

}
