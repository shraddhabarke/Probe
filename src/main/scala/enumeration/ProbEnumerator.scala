package enumeration

import java.io.FileOutputStream

import ast.{ASTNode, VocabFactory, VocabMaker}
import sygus.SygusFileTask

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class ProbEnumerator(val filename: String, val vocab: VocabFactory, val oeManager: OEValuesManager, val task: SygusFileTask, val contexts: List[Map[String,Any]], val probBased: Boolean) extends Iterator[ASTNode] {
  override def toString(): String = "enumeration.Enumerator"

  var nextProgram: Option[ASTNode] = None

  override def hasNext: Boolean =
    if (nextProgram.isDefined) {
      true
    } else {
      nextProgram = getNextProgram()
      nextProgram.isDefined
    }

  override def next(): ASTNode = {
    if (nextProgram.isEmpty) {
      nextProgram = getNextProgram()
    }
    val res = nextProgram.get
    nextProgram = None
    res
  }

  var currIter: Iterator[VocabMaker] = null
  var childrenIterator: Iterator[List[ASTNode]] = null
  var currLevelProgs: mutable.ArrayBuffer[ASTNode] = mutable.ArrayBuffer()
  var bank = mutable.Map[Int, mutable.ArrayBuffer[ASTNode]]()
  var phaseCounter: Int = 0
  var fitsMap = mutable.Map[(Class[_], Option[Any]), Double]()
  var fos = new FileOutputStream("outpu.txt", true)
  ProbUpdate.probMap = ProbUpdate.createProbMap(task.vocab)
  ProbUpdate.priors = ProbUpdate.createPrior(task.vocab)
  var timeout = 3 * ProbUpdate.priors.head._2
  var costLevel = 0

  resetEnumeration()
  var rootMaker: Iterator[ASTNode] = currIter.next().probe_init(currLevelProgs.toList, vocab, costLevel, contexts, bank)

  def resetEnumeration():  Unit = {
    currIter = vocab.leaves().toList.sortBy(_.rootCost).toIterator
    rootMaker = currIter.next().probe_init(currLevelProgs.toList, vocab, costLevel, contexts, bank)
    childrenIterator = Iterator.single(Nil)
    currLevelProgs.clear()
    oeManager.clear()
    bank.clear()
    fitsMap.clear
    phaseCounter = 0
  }

  def advanceRoot(): Boolean = {
    rootMaker = null
    while (rootMaker == null || !rootMaker.hasNext) {
      if (!currIter.hasNext) return false
      val next = currIter.next()
      rootMaker = next.probe_init(currLevelProgs.toList, vocab, costLevel, contexts, bank)
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
    val sortedLeaves = vocab.leaves().toList.sortBy(_.rootCost)
    currIter = if (sortedLeaves.last.rootCost <= costLevel)
      vocab.nonLeaves.toList.sortBy(_.rootCost).toIterator else
      sortedLeaves.toIterator

    for (p <- currLevelProgs) updateBank(p)

    if (probBased) {
      fitsMap = ProbUpdate.update(fitsMap, currLevelProgs, task)
      if (phaseCounter == timeout) {
        phaseCounter = 0
        if (!fitsMap.isEmpty) {
          ProbUpdate.updatePriors(ProbUpdate.probMap)
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
      if (rootMaker.hasNext) {
        val prog = rootMaker.next

        if (oeManager.isRepresentative(prog)) {
          res = Some(prog)
        }
      }
      else if (currIter.hasNext) {
        if (!advanceRoot()) {
          if (!changeLevel()) changeLevel()
        }
      }
      else if (!changeLevel()) {
        changeLevel()
      }
    }
    currLevelProgs += res.get
    //Console.withOut(fos) { println(currLevelProgs.takeRight(1).map(c => (c.code, c.cost)).mkString(",")) }
    res
  }
}
