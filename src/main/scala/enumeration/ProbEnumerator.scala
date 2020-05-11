package enumeration

import ast.{ASTNode, VocabFactory, VocabMaker}
import trace.DebugPrints.dprintln
import java.io.{File, FileOutputStream}

import sygus.{ParseJson, SygusFileTask}

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class ProbEnumerator(val preLearned: Boolean, val filename: String, val vocab: VocabFactory, val oeManager: OEValuesManager, val task: SygusFileTask, val probBased: Boolean) extends Iterator[ASTNode] {
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

  var jsonMap: scala.collection.mutable.Map[String, Map[Class[_],Double]] = null
  jsonMap = ParseJson.parseMap()
  var currIter: Iterator[VocabMaker] = null
  var childrenIterator: Iterator[List[ASTNode]] = null
  var currLevelProgs: mutable.ArrayBuffer[ASTNode] = mutable.ArrayBuffer()
  var bank = scala.collection.mutable.Map[Int, mutable.ArrayBuffer[ASTNode]]()
  var fos = new FileOutputStream("check.txt", true)
  var phaseCounter : Int = 0
  var fitsMap = mutable.Map[Class[_], Double]()
  var preLearnedMap = mutable.Map[Class[_], Double]()
  preLearnedMap = jsonMap(filename.replace("src/test/benchmarks/euphony/","")).to(collection.mutable.Map)
  var costLevel = 10
  resetEnumeration()
  if (preLearned) { ProbUpdate.updatePriors(preLearnedMap) }
  var rootMaker: VocabMaker = currIter.next()

  def resetEnumeration():  Unit = {
    currIter = vocab.leaves().toList.sortBy(_.rootCost).toIterator
    childrenIterator = Iterator.single(Nil)
    currLevelProgs.clear()
    oeManager.clear()
    bank.clear()
    fitsMap.clear
    phaseCounter = 0
  }

  def advanceRoot(): Boolean = {
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    val rootCost = rootMaker.rootCost
    if (rootMaker.arity == 0)
      childrenIterator = Iterator.single(Nil)
    else if (rootCost < costLevel) {
      val childrenCost = costLevel - rootCost
      childrenIterator = new ProbChildrenIterator(rootMaker.childTypes, childrenCost, bank)
    }
    true
  }

  def updateBank(program: ASTNode): Unit = {
    if (!bank.contains(program.cost))
      bank(program.cost) = ArrayBuffer(program)
    else
      bank(program.cost) += program
  }

  def changeLevel(): Boolean = {
    currIter = vocab.nonLeaves.toList.sortBy(_.rootCost).toIterator
    for (p <- currLevelProgs) updateBank(p)
    if (probBased) {
      fitsMap = ProbUpdate.updateFit(fitsMap, currLevelProgs, task)
      if (phaseCounter == 30) {
        phaseCounter = 0
        if (!fitsMap.isEmpty) {
          ProbUpdate.updatePriors(fitsMap)
          resetEnumeration()
          costLevel = 0
        }
      }
    }
    costLevel += 1
    phaseCounter += 1
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
    /**
    val exampleFit = task.fit(res.get)
    val fit: Double = (exampleFit._1.toFloat) / exampleFit._2
    if (fit > 0.2) {
      //Console.withOut(fos) {
        //println(res.get.code)
      }
    }**/
    Console.withOut(fos) { println(currLevelProgs.takeRight(1).map(c => (c.code, c.cost)).mkString(",")) }
    res
  }
}
