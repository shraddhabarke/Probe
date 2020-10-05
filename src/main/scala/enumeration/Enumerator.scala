package enumeration

import java.io.FileOutputStream

import sygus.{Example, SMTProcess, SygusFileTask}
import ast.{ASTNode, VocabFactory, VocabMaker}
import trace.DebugPrints.dprintln

import scala.collection.mutable

class Enumerator(val filename: String, val vocab: VocabFactory, val oeManager: OEValuesManager, var task: SygusFileTask, var contexts: List[Map[String,Any]]) extends Iterator[ASTNode]{
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

  def solverSetup(): Unit = {
    val out = SMTProcess.toSMT(source.mkString)
    smtOut = out._1
    solution = out._3
    funcArgs = out._2
  }

  var currIter = vocab.leaves
  val source = scala.io.Source.fromFile(filename)
  var childrenIterator: Iterator[List[ASTNode]] = Iterator.single(Nil)
  var rootMaker: VocabMaker = currIter.next()
  var prevLevelProgs: mutable.ListBuffer[ASTNode] = mutable.ListBuffer()
  var currLevelProgs: mutable.ListBuffer[ASTNode] = mutable.ListBuffer()
  var height = 0
  var solution: String = null
  var funcArgs: List[String] = null
  var smtOut: List[String] = null
  if (!task.isPBE) solverSetup()

  def resetEnumeration(): Unit = {
    height = 0
    currIter = vocab.leaves
    contexts = task.examples.map(_.input)
    childrenIterator = Iterator.single(Nil)
    rootMaker = currIter.next()
    currLevelProgs.clear()
    prevLevelProgs.clear()
    oeManager.clear()
  }

  def advanceRoot(): Boolean = {
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    childrenIterator = if (rootMaker.arity == 0)
      Iterator.single(Nil)
    else new ChildrenIterator(prevLevelProgs.toList,rootMaker.childTypes,height)
    true
  }

  def changeLevel(): Boolean = {
    if (currLevelProgs.isEmpty) return false
    currIter = vocab.nonLeaves
    height += 1
    prevLevelProgs ++= currLevelProgs
    currLevelProgs.clear()
    advanceRoot()
  }

  def getNextProgram(): Option[ASTNode] = {
    var res : Option[ASTNode] = None
    while(res.isEmpty) {
      if (childrenIterator.hasNext) {
        val children = childrenIterator.next()
        if (rootMaker.canMake(children)) {
          val prog = rootMaker(children,contexts)
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
    if (!res.isEmpty && !task.isPBE && (res.get.nodeType == task.functionReturnType)) {
      if (contexts.isEmpty ||
        (!contexts.isEmpty && task.examples.zip(res.get.values).map(pair => pair._1.output == pair._2).forall(identity))) {
        //Solver is invoked if either the set of examples is empty or the program satisfies all current examples.
        val query = SMTProcess.getquery(res.get.code, smtOut)
        val solverOut = SMTProcess.invokeCVC(query.stripMargin, SMTProcess.cvc4_Smt)
        if (solverOut.head == "sat") { // counterexample added!
          val cex = SMTProcess.getCEx(task, funcArgs, solverOut, solution)
          task = task.updateContext(cex)
          resetEnumeration() //restart synthesis
        } else if (solverOut.head == "unsat") {
          res.get.unsat = true
        }
      }
    }
    //Console.withOut(fos) { println(currLevelProgs.takeRight(1).map(c => (c.code, c.height)).mkString(",")) }
    res
  }
}
