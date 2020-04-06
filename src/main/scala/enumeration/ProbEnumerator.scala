package enumeration

import ast.{ASTNode, VocabFactory, VocabMaker}
import trace.DebugPrints.dprintln
import java.io.{File, FileOutputStream}

import sygus.SygusFileTask

import scala.annotation.tailrec
import scala.collection.Searching.{Found, InsertionPoint, SearchResult}
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
  var childrenIterator: Iterator[List[ASTNode]] = Iterator.single(Nil)
  var rootMaker: VocabMaker = currIter.next()
  var prevLevelProgs: mutable.ArrayBuffer[ASTNode] = mutable.ArrayBuffer()
  var currLevelProgs: mutable.ArrayBuffer[ASTNode] = mutable.ArrayBuffer()
  var bank = scala.collection.mutable.Map[Int, List[ASTNode]]()
  //val fos = new FileOutputStream(new File("out_prog.txt"))
  var maxFit: Double = 0

  def advanceRoot(): Boolean = {
    val rootCost = rootMaker.rootCost
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    if (rootCost > costLevel) return false
    if (rootMaker.arity == 0 && rootCost == costLevel)
      childrenIterator = Iterator.single(Nil)
    else if (rootCost < costLevel) {
      val childrenCost = costLevel - rootCost
      childrenIterator = new ProbChildrenIterator(prevLevelProgs.toList, rootMaker.childTypes, childrenCost, bank)
    }
    true
  }

  var costLevel = 10

  def changeLevel(): Boolean = {
    currIter = vocab.nonLeaves
    val changed = ProbUpdate.updatePriors(maxFit, currLevelProgs, task)
    maxFit = ProbUpdate.maximumFit
    prevLevelProgs ++= currLevelProgs
    if (changed) prevLevelProgs.map(p => renewBank(p))
    costLevel += 1
    currLevelProgs.clear()
    advanceRoot()
  }

  def renewBank(p: ASTNode): Unit = {
      p.renewCost()
      if (!bank.contains(p.cost))
        bank(p.cost) = List(p) //if it's a new cost.
      else {
        val prevKey = bank.find(_._2 == p).map(_._1) //remove it from previous cost bucket.
        if (prevKey != None && !bank(p.cost).contains(p) && p.cost != prevKey.get) {
          //if it's not a new program and if it's not in the correct cost bucket,
          //remove it from the previous bucket and later add to the new bucket.
          bank(prevKey.get) = bank(prevKey.get).filter(_ != p)
        }
        bank(p.cost) = bank(p.cost) :+ p
      }
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
      bank(res.get.cost) = List(res.get)
    else
      bank(res.get.cost) = bank(res.get.cost) :+ res.get
    //Console.withOut(fos) { dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(",")) }
    dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(","))
    res
  }
}

