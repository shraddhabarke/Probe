package enumeration

import java.io.{File, FileOutputStream}

import ast._
import sygus.SygusFileTask
import trace.DebugPrints.dprintln

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

object ProbUpdate {
  val fos = new FileOutputStream(new File("out.txt"))
  var phaseChange: Boolean = false
  var newPrior = 0.0
  var fitMap = mutable.Map[Set[Any], ArrayBuffer[ASTNode]]()

  def getAllNodeTypes(program: ASTNode): Set[Class[_]] = program.children.flatMap(c => getAllNodeTypes(c)).toSet + program.getClass

  def groupFit(currLevelProgs: mutable.ArrayBuffer[ASTNode], task: SygusFileTask, phaseChangeCheck: Boolean): mutable.Map[Set[Any], ArrayBuffer[ASTNode]] = {
    phaseChange = phaseChangeCheck
    for (program <- currLevelProgs) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      if (fit > 0.2) {
        val examplesPassed = task.fitExs(program)
        if (!fitMap.contains(examplesPassed))
          fitMap(examplesPassed) = ArrayBuffer(program)
        else
          fitMap(examplesPassed) += program
        Console.withOut(fos) {
          dprintln(fitMap.map(c => (c._1, c._2.toList.map(c => c.code))))
        }
      }
    }
    phaseChange = !fitMap.isEmpty || phaseChangeCheck
    fitMap
  }

  def clusterAndPick(fitMap: mutable.Map[Set[Any], ArrayBuffer[ASTNode]]): ArrayBuffer[ASTNode] = {
    var pickedPrograms = ArrayBuffer[ASTNode]()
    for (group <- fitMap) {
      val groupIterator = group._2.iterator
      var compareWith = ArrayBuffer[ASTNode]()
      compareWith = ArrayBuffer(groupIterator.next())
      val compareWithBackup = compareWith
      while (groupIterator.hasNext) { // if there are more than one programs
        val nextProgram = groupIterator.next()
        if (compareWith.iterator.hasNext) {
          val nextCompare = compareWith.iterator.next()
          if (SimilarityMetric.compute(nextCompare, nextProgram).toFloat / nextCompare.terms < 0.5)
            compareWith = compareWithBackup ++ Iterator(nextProgram)
        }
      }
      pickedPrograms ++= compareWith
    }
    pickedPrograms
  }

  def updatePriors(fitMap: mutable.Map[Set[Any], ArrayBuffer[ASTNode]], task: SygusFileTask) = {
    var diff = mutable.Map[Class[_], Int]()
    val pickedPrograms = clusterAndPick(fitMap)
    for (program <- pickedPrograms) {
      val exampleFit = task.fit(program)
      val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
      val changed: Set[Class[_]] = getAllNodeTypes(program)
      for (changedNode <- changed) {
        val newPrior = (1 - fit) * priors(changedNode)
        if (!diff.contains(changedNode) || diff(changedNode) > newPrior) //TODO: is this the right direction? Always get smaller?
          diff += (changedNode -> roundValue(newPrior))
      }
    }
    diff.foreach(d => priors += d)
    Console.withOut(fos) {dprintln(priors)}

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
