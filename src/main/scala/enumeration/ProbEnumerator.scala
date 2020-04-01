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
  val fos = new FileOutputStream(new File("out_prog.txt"))

  def advanceRoot(): Boolean = {
    val rootCost = rootMaker.rootCost
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    if (rootCost > costLevel) return false
    if (rootMaker.arity == 0 && rootCost == costLevel)
      childrenIterator = Iterator.single(Nil)
    else if (rootCost < costLevel) {
      val childrenCost = costLevel - rootCost
      childrenIterator = new ProbChildrenIterator(prevLevelProgs.toList, rootMaker.childTypes, childrenCost)
    }
    true
  }

  var costLevel = 1.0

  def searchBy[A,B](list: ArrayBuffer[A], elem: A, f: A => B)(implicit ord: Ordering[B]): SearchResult =
    binarySearch(list, elem, 0, list.length,f)(ord)
  @tailrec
  private def binarySearch[A,B](list: ArrayBuffer[A], elem: A, from: Int, to: Int, f: A => B)
                                  (implicit ord: Ordering[B]): SearchResult = {
    if (to == from) InsertionPoint(from) else {
      val idx = from+(to-from-1)/2
      math.signum(ord.compare(f(elem), f(list(idx)))) match {
        case -1 => binarySearch(list, elem, from, idx, f)(ord)
        case  1 => binarySearch(list, elem, idx + 1, to, f)(ord)
        case  _ => Found(idx)
      }
    }
  }
  def changeLevel(): Boolean = {
    currIter = vocab.nonLeaves
    val changed = ProbUpdate.updatePriors(currLevelProgs, task)
    //this should probably happen all at once in the sorted insertion
    val oldPrev = prevLevelProgs
    prevLevelProgs = new ArrayBuffer()
    def sortedInsert(p: ASTNode) = {
      searchBy[ASTNode,Double](prevLevelProgs,p,prog => prog.cost) match {
        case Found(foundIndex) => {
          //val numEqual = prevLevelProgs.drop(foundIndex).zipWithIndex.takeWhile(p2 => p2._1.cost <= p.cost).last._2 + 1
          prevLevelProgs.insert(foundIndex /*+ numEqual*/,p)
        }
        case InsertionPoint(insertionPoint) => prevLevelProgs.insert(insertionPoint,p)
      }
    }

    for (p <- currLevelProgs) {
      if (changed) p.renewCost()
      sortedInsert(p)
    }

    for (p <- oldPrev) {
      if (changed) p.renewCost()
      sortedInsert(p)
    }

    costLevel += 1
    currLevelProgs.clear()
    Console.withOut(fos) { dprintln(ProbUpdate.priors) }
    advanceRoot()
  }

  def getNextProgram(): Option[ASTNode] = {
    var res : Option[ASTNode] = None
    while(res.isEmpty) {
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
    Console.withOut(fos) { dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(",")) }
    dprintln(currLevelProgs.takeRight(4).map(_.code).mkString(","))
    res
  }
}

