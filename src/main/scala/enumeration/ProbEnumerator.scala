package enumeration

import java.io.FileOutputStream

import ast.{ASTNode, VocabFactory, VocabMaker}
import sygus.SygusFileTask
import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer
import trace.DebugPrints.iprintln

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

  var fos = new FileOutputStream("results/probe-out/" + filename.drop(27) + ".iter", true)
  var currIter: Iterator[VocabMaker] = null
  val totalLeaves = vocab.leaves().toList ++ vocab.nonLeaves().toList
  var childrenIterator: Iterator[List[ASTNode]] = null
  var currLevelProgs: mutable.ArrayBuffer[ASTNode] = mutable.ArrayBuffer()
  var bank = mutable.Map[Int, mutable.ArrayBuffer[ASTNode]]()
  var phaseCounter: Int = 0
  var fitsMap = mutable.Map[(Class[_], Option[Any]), Double]()
  ProbUpdate.probMap = ProbUpdate.createProbMap(task.vocab)
  ProbUpdate.priors = ProbUpdate.createPrior(task.vocab)
  val sortedLeaves = vocab.leaves().toList.sortBy(_.rootCost)
  var timeout = 3 * ProbUpdate.priors.head._2
  var costLevel = 0
  //var reset = false

  resetEnumeration()
  var rootMaker: Iterator[ASTNode] = currIter.next().probe_init(currLevelProgs.toList, vocab, costLevel, contexts, bank)

  def resetEnumeration():  Unit = {
    currIter = vocab.leaves().toList.sortBy(_.rootCost).toIterator
    rootMaker = currIter.next().probe_init(currLevelProgs.toList, vocab, costLevel, contexts, bank)
    currLevelProgs.clear()
    oeManager.clear()
    bank.clear()
    fitsMap.clear
    phaseCounter = 0
  }

  def advanceRoot(): Boolean = {
    rootMaker = null
    while (rootMaker == null || !rootMaker.hasNext) {
      if (currIter.isEmpty) return false
      else if (!currIter.hasNext) return false
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
    currIter = if (totalLeaves.filter(c => c.rootCost <= costLevel + 1).isEmpty) Iterator.empty
      else totalLeaves.sortBy(_.rootCost).toIterator

    for (p <- currLevelProgs) updateBank(p)

    if (probBased) {
      fitsMap = ProbUpdate.update(fitsMap, currLevelProgs, task, fos)
      if (phaseCounter == 2 * timeout) {
        phaseCounter = 0
        if (!fitsMap.isEmpty) {
          //reset = true
          ProbUpdate.updatePriors(ProbUpdate.probMap, fos)
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
      if (rootMaker!= null && rootMaker.hasNext) {
        val prog = rootMaker.next

        if (oeManager.isRepresentative(prog)) {
          res = Some(prog)
        }
      }
      else if (currIter.hasNext) {
        if (!advanceRoot())
          changeLevel()
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
