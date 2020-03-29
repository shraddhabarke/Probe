package enumeration

import ast.{ASTNode, VocabFactory, VocabMaker}
import trace.DebugPrints.dprintln
import java.io.{File, FileOutputStream}

import sygus.SygusFileTask

import scala.collection.mutable

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
  var childrenIterator: Iterator[List[ASTNode]] = Iterator.single(Nil)
  var rootMaker: VocabMaker = currIter.next()
  var prevLevelProgs: mutable.ListBuffer[ASTNode] = mutable.ListBuffer()
  var currLevelProgs: mutable.ListBuffer[ASTNode] = mutable.ListBuffer()
  var bank = scala.collection.mutable.Map[Int,List[ASTNode]]()
  var costMap = scala.collection.mutable.Map[VocabMaker, Int]()
  val vocabList = vocab.nonLeaves().toList ++ vocab.leaves().toList
  vocabList.map(c => costMap(c) = 1)

  //TODO: makeup phase - adds all newly cheap programs to the bank
  // and moves existing programs to different buckets based on the cost.
  //TODO: The above TODO would involve figuring out how to propagate the cost from VocabMaker to ASTNode

  val fos = new FileOutputStream(new File("out_prog.txt"))

  def advanceRoot(): Boolean = {
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    if (costMap(rootMaker) > costLevel) return false
    else if (rootMaker.arity == 0 && costMap(rootMaker) == costLevel) //TODO: account for quantization here
      childrenIterator = Iterator.single(Nil)
    else if (costMap(rootMaker) < costLevel ) {
      val childrenCost = costLevel - costMap(rootMaker)
      childrenIterator = new ProbChildrenIterator(prevLevelProgs.toList, rootMaker.childTypes, childrenCost, bank)
    }
    true
  }

  var costLevel = 1
  def changeLevel(): Boolean = {
    currIter = vocab.nonLeaves
    costLevel += 1
    prevLevelProgs ++= currLevelProgs
    //costMap = ProbUpdate.getUpdate(currLevelProgs, costMap, task)
    //TODO: update function

    bank += ((currLevelProgs.head.cost) -> currLevelProgs.toList)
    //TODO: update the previous level programs
    //TODO: start enumeration from scratch? set costLevel to 0?
    currLevelProgs.clear()
    advanceRoot()
  }

  def getNextProgram(): Option[ASTNode] = {
    var res : Option[ASTNode] = None
    while(res.isEmpty) {
        if (childrenIterator.hasNext) {
          val children = childrenIterator.next()
            if (rootMaker.canMake(children)) {
              val prog = rootMaker(children, task.examples.map(_.input),costMap(rootMaker))
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
