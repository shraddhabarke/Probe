package enumeration

import ast.{ASTNode, VocabFactory, VocabMaker}
import trace.DebugPrints.dprintln
import java.io.{File, FileOutputStream}

import scala.collection.mutable

class ProbEnumerator(val vocab: VocabFactory, val oeManager: OEValuesManager, val contexts: List[Map[String, Any]]) extends Iterator[ASTNode] {
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

  var currIter = vocab.leaves()
  var childrenIterator: Iterator[List[ASTNode]] = Iterator.single(Nil)
  var rootMaker: VocabMaker = currIter.next()
  var prevLevelProgs: mutable.ListBuffer[ASTNode] = mutable.ListBuffer()
  var currLevelProgs: mutable.ListBuffer[ASTNode] = mutable.ListBuffer()
  var bank = scala.collection.mutable.Map[Int,List[ASTNode]]()
  val fos = new FileOutputStream(new File("out_prog.txt"))

  def advanceRoot(): Boolean = {
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    if (rootMaker.prob > costLevel) return false
    else if (rootMaker.arity == 0 && rootMaker.prob == costLevel)
      childrenIterator = Iterator.single(Nil)
    else if (rootMaker.prob < costLevel ) {
      val childrenCost = costLevel - rootMaker.prob
      childrenIterator = new ProbChildrenIterator(prevLevelProgs.toList, rootMaker.childTypes, childrenCost, bank)
    }
    true
  }

  var costLevel = 3
  def changeLevel(): Boolean = {
    currIter = vocab.nonLeaves
    costLevel += 3
    prevLevelProgs ++= currLevelProgs
    bank += ((currLevelProgs.head.cost) -> currLevelProgs.toList)
    currLevelProgs.clear()
    advanceRoot()
  }

  def getNextProgram(): Option[ASTNode] = {
    var res : Option[ASTNode] = None
    while(res.isEmpty) {
        if (childrenIterator.hasNext) {
          val children = childrenIterator.next()
            if (rootMaker.canMake(children)) {
              val prog = rootMaker(children, contexts)
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
    Console.withOut(fos) { dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(",")) }
    dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(","))
    res
  }
}
