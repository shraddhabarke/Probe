package enumeration

import sygus.SMTProcess
import ast.{ASTNode, BasicVocabMaker, VocabFactory, VocabMaker}
import enumeration.ProbUpdate.priors
import sygus.SygusFileTask

import scala.collection.mutable
import scala.collection.mutable.ArrayBuffer

class ProbEnumerator(val filename: String, val vocab: VocabFactory, val oeManager: OEValuesManager, var task: SygusFileTask, var contexts: List[Map[String,Any]], val probBased: Boolean) extends Iterator[ASTNode] {
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
  val source = scala.io.Source.fromFile(filename)
  val totalLeaves = vocab.leaves().toList ++ vocab.nonLeaves().toList
  var childrenIterator: Iterator[List[ASTNode]] = null
  var currLevelProgs: mutable.ArrayBuffer[ASTNode] = mutable.ArrayBuffer()
  var bank = mutable.Map[Int, mutable.ArrayBuffer[ASTNode]]()
  var phaseCounter: Int = 0
  val reset: Boolean = false //Change here for resetting cache
  var fitsMap = mutable.Map[(Class[_], Option[Any]), Double]()
  ProbUpdate.probMap = ProbUpdate.createProbMap(task.vocab)
  ProbUpdate.priors = ProbUpdate.createPrior(task.vocab)
  val round = priors.head._2
  var timeout = 3 * ProbUpdate.priors.head._2
  var costLevel = 0
  var solution: String = null
  var funcArgs: List[String] = null
  var smtOut: List[String] = null

  resetEnumeration()
  if (!task.isPBE) solverSetup()
  var rootMaker: Iterator[ASTNode] = currIter.next().probe_init(currLevelProgs.toList, vocab, costLevel, contexts, bank)

  def resetEnumeration(): Unit = {
    currIter = vocab.leaves().toList.sortBy(_.rootCost).toIterator
    contexts = task.examples.map(_.input)
    rootMaker = currIter.next().probe_init(currLevelProgs.toList, vocab, costLevel, contexts, bank)
    currLevelProgs.clear()
    oeManager.clear()
    bank.clear()
    fitsMap.clear()
    phaseCounter = 0
    costLevel = 0
  }

  def resetCache(): Unit = {
    ProbUpdate.cacheStrings.clear()
    ProbUpdate.cache.clear()
    ProbUpdate.cacheCost.clear()
    ProbUpdate.fitMap.clear()
    ProbUpdate.examplesCovered.clear()
    ProbUpdate.currBest = Set[Any]()
    ProbUpdate.probMap = ProbUpdate.createProbMap(task.vocab)
    ProbUpdate.priors = ProbUpdate.createPrior(task.vocab)
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

  def solverSetup(): Unit = {
    val out = SMTProcess.toSMT(source.mkString)
    smtOut = out._1
    solution = out._3
    funcArgs = out._2
  }

  def changeLevel(): Boolean = {
    currIter = totalLeaves.sortBy(_.rootCost).toIterator //todo: more efficient

    for (p <- currLevelProgs) updateBank(p)

    if (probBased) {
      if (!currLevelProgs.isEmpty) fitsMap = ProbUpdate.update(fitsMap, currLevelProgs, task)
      if (phaseCounter == 2 * timeout) {
        phaseCounter = 0
        if (!fitsMap.isEmpty) {
          ProbUpdate.priors = ProbUpdate.updatePriors(ProbUpdate.probMap, round)
          println(ProbUpdate.priors)
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
        //need the arity 0 case because initially cegis loop has empty set of points.
        if (oeManager.isRepresentative(prog) ||
          (task.examples.isEmpty && rootMaker.asInstanceOf[BasicVocabMaker].arity == 0)) {
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
    /** CEGIS Loop - If the current program satisfies the list of examples, CVC4 is invoked after converting
      * SyGuS to SMTLib format. If the solver outputs sat, the counterexample returned is added to the list
      * of examples and synthesis restarts.
      ***/

    if (!res.isEmpty && !task.isPBE && (res.get.nodeType == task.functionReturnType)) {
      if (task.examples.isEmpty ||
        (!task.examples.isEmpty && task.examples.zip(res.get.values).map(pair => pair._1.output == pair._2).forall(identity))) {
        //Solver is invoked if either the set of examples is empty or the program satisfies all current examples.
        val query = SMTProcess.getquery(res.get.code, smtOut)
        val solverOut = SMTProcess.invokeCVC(query.stripMargin, SMTProcess.cvc4_Smt)
        if (solverOut.head == "sat") { // counterexample added!
          val cex = SMTProcess.getCEx(task, funcArgs, solverOut, solution)
          task = task.updateContext(cex)
         // println(res.get.code, task.examples)
          resetEnumeration() //restart synthesis
          if (reset) resetCache()
          else {
            ProbUpdate.readjustCosts(task)
            ProbUpdate.priors = ProbUpdate.updatePriors(ProbUpdate.probMap, round)
          }
          //reset cache and start with uniform probability if running reset true else readjust weights.
        } else if (solverOut.head == "unsat") {
          res.get.unsat = true
        }
      }
    }
    //Console.withOut(fos) { println(currLevelProgs.takeRight(1).map(c => (c.code, c.cost)).mkString(",")) }
    res
  }
}
