package enumeration

import ast.{ASTNode, VocabMaker}
import org.apache.commons.lang3.StringUtils
import sygus.SygusFileTask

import scala.collection.mutable
import scala.io.Source._

object ProbUpdate {

  def getUpdate(currLevelProgs: mutable.ListBuffer[ASTNode], prevMap: mutable.Map[ast.VocabMaker, Double], task: SygusFileTask, bank: mutable.Map[Double,List[ASTNode]]): mutable.Map[ast.VocabMaker, Double] = {
    var diff = mutable.Map[VocabMaker, Double]()
    val programIterator = currLevelProgs.iterator
    val mapKeys = prevMap.keys
    while (programIterator.hasNext) {
      val program = programIterator.next()
      val exampleFit = task.fit(program)
      if (exampleFit._1 > 2) {
        val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
        val changed = program.code.replaceAll("\\)","").replaceAll("\\(","").split(" ").toList
        val update = mapKeys.toList.filter(c => changed.contains(c.head))
        update.map(c => diff(c) = fit * prevMap(c))
      }
     }
    diff
  }
}
