package enumeration

import ast.{ASTNode, VocabFactory, VocabMaker}
import trace.DebugPrints.dprintln
import java.io.{File, FileOutputStream}

import sygus.SygusFileTask

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class ProbEnumerator(val vocab: VocabFactory, val oeManager: OEValuesManager, val task: SygusFileTask) extends Iterator[ASTNode] {
  override def toString(): String = "enumeration.Enumerator"

  var nextProgram: Option[ASTNode] = None

  override def hasNext: Boolean = if (!nextProgram.isEmpty) true
  else {
    nextProgram = getNextProgram()
    !nextProgram.isEmpty
  }

  override def next(): ASTNode = {
    if (nextProgram.isEmpty) {
      nextProgram = getNextProgram()
    }
    val res = nextProgram.get
    nextProgram = None
    res
  }

  var currIter: Iterator[VocabMaker] = vocab.leaves()
  var childrenIterator: Iterator[List[ASTNode]] = null
  var rootMaker: VocabMaker = currIter.next()
  var prevLevelProgs: mutable.ArrayBuffer[ASTNode] = mutable.ArrayBuffer()
  var currLevelProgs: mutable.ArrayBuffer[ASTNode] = mutable.ArrayBuffer()
  var bank = scala.collection.mutable.Map[Int, mutable.ArrayBuffer[ASTNode]]()
  val fos = new FileOutputStream(new File("out.txt"))
  var maxFit: Double = 0
  var costLevel = 10
  resetEnumeration()

  def resetEnumeration():  Unit = {
    childrenIterator = Iterator.single(Nil)
    prevLevelProgs.clear()
    currLevelProgs.clear()
    oeManager.clear()
    bank.clear()
    maxFit = 0
  }

  def advanceRoot(): Boolean = {
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    val rootCost = rootMaker.rootCost
    if (rootMaker.arity == 0 && rootCost == costLevel)
      childrenIterator = Iterator.single(Nil)
    else if (rootMaker.arity == 0 && rootCost > costLevel) {
      if (!currIter.hasNext) {
        currIter = vocab.leaves()
        costLevel += 1
        advanceRoot() }
      else advanceRoot()
    }
    else if (rootCost < costLevel) {
      val childrenCost = costLevel - rootCost
      childrenIterator = new ProbChildrenIterator(prevLevelProgs.toList, rootMaker.childTypes, childrenCost, bank)
    }
    true
  }

  def changeLevel(): Boolean = {
    currIter = vocab.nonLeaves.toList.sortBy(_.rootCost).toIterator
    val changed = ProbUpdate.updatePriors(maxFit, currLevelProgs, task)
    prevLevelProgs ++= currLevelProgs
    if (changed) {
      resetEnumeration()
      currIter = vocab.leaves()
      costLevel = 0
    }
    maxFit = ProbUpdate.maximumFit
    costLevel += 1
    currLevelProgs.clear()
    advanceRoot()
  }

  def getNextProgram(): Option[ASTNode] = {
    var res: Option[ASTNode] = None
    while (res.isEmpty) {
      if (childrenIterator.hasNext) {
        val children = childrenIterator.next()
        if (rootMaker.canMake(children)) {
          val prog = rootMaker(children, task.examples.map(_.input))
          if (oeManager.isRepresentative(prog))
            res = Some(prog)
        }
      }
      else if (currIter.hasNext) {
        if (!advanceRoot())
          return None
      }
      else {
        if (!changeLevel())
          return None
      }
    }
    currLevelProgs += res.get
    if (!bank.contains(res.get.cost))
      bank(res.get.cost) = ArrayBuffer(res.get)
    else
      bank(res.get.cost) += res.get
    Console.withOut(fos) { dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(",")) }
    //dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(","))
    res
  }
}

