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

  var currIter = vocab.leaves() //production rules without parameters
  var childrenIterator: Iterator[List[ASTNode]] = Iterator.single(Nil)
  var rootMaker: VocabMaker = currIter.next()
  var prevLevelProgs: mutable.ListBuffer[ASTNode] = mutable.ListBuffer()
  var currLevelProgs: mutable.ListBuffer[ASTNode] = mutable.ListBuffer()
  var bank = scala.collection.mutable.Map[Int,List[ASTNode]]()
  val fos = new FileOutputStream(new File("out_prog.txt"))

  def advanceRoot(): Boolean = {
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    if (computeCost(rootMaker) > costLevel) return false
    else if (rootMaker.arity == 0 && computeCost(rootMaker) == costLevel)
      childrenIterator = Iterator.single(Nil)
    else if (computeCost(rootMaker) < costLevel ) {
      val childrenCost = costLevel - computeCost(rootMaker)
      childrenIterator = new ProbChildrenIterator(prevLevelProgs.toList, rootMaker.childTypes, childrenCost, bank)
    }
    true
  }
  var costLevel = 3
  def changeLevel(): Boolean = {
    currIter = vocab.nonLeaves
    costLevel += 3
    prevLevelProgs ++= currLevelProgs
    currLevelProgs.clear()
    advanceRoot()
  }

  def computeProgramCost(ast: ASTNode): Int = {
    var cost = ast.cost
    if (ast.children.size > 0) {
      for (c <- ast.children)
        cost += computeProgramCost(c)
    }
    cost
  }
  def computeCost(vocab: VocabMaker): Int = vocab.prob

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
    if (!bank.contains(computeProgramCost(res.get)))
      bank(computeProgramCost(res.get)) = List(res.get)
    else
      bank(computeProgramCost(res.get)) = bank(computeProgramCost(res.get)) :+ res.get
    Console.withOut(fos) { dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(",")) }
    dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(","))
    res
  }
}
