package enumeration

import ast.{ASTNode, VocabFactory, VocabMaker}
import trace.DebugPrints.dprintln
import java.io.{File, FileOutputStream}

import sygus.SygusFileTask

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

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
  var bank = scala.collection.mutable.Map[Double,List[ASTNode]]()
  var prevMap = scala.collection.mutable.Map[VocabMaker, Double]()
  var costMap = scala.collection.mutable.Map[VocabMaker, Double]()
  val vocabList = vocab.nonLeaves().toList ++ vocab.leaves().toList
  vocabList.map(c => costMap(c) = 1)

  val fos = new FileOutputStream(new File("out_prog.txt"))

  def advanceRoot(): Boolean = {
    if (!currIter.hasNext) return false
    rootMaker = currIter.next()
    //if (costMap(rootMaker) > costLevel) return false
    if (rootMaker.arity == 0 && costMap(rootMaker) == costLevel) //TODO: account for quantization here
      childrenIterator = Iterator.single(Nil)
    else if (costMap(rootMaker) < costLevel ) {
      val childrenCost = costLevel - costMap(rootMaker)
      childrenIterator = new ProbChildrenIterator(prevLevelProgs.toList, rootMaker.childTypes, childrenCost, bank)
    }
    true
  }

  var costLevel = 1.0
  def changeLevel(): Boolean = {
    currIter = vocab.nonLeaves
    prevLevelProgs ++= currLevelProgs
    costLevel += 0.5
    val diff = ProbUpdate.getUpdate(currLevelProgs, costMap, task, bank)
    if (diff.isEmpty) {}
    else {
      //TODO: start enumeration from scratch? set costLevel to 0?
      prevLevelProgs = renewCosts(diff, prevLevelProgs)
      renewBank(bank)
    }
    prevLevelProgs.map(p => updateBank(p))
    currLevelProgs.clear()
    advanceRoot()
  }

  def renewCosts(diff: scala.collection.mutable.Map[VocabMaker, Double], oldProgs: ListBuffer[ASTNode]): ListBuffer[ASTNode] = {
    val diffString = diff.keys.toList.map(d => d.head)
    val changedProgs = oldProgs.toList.filter(p => p.code.replaceAll("\\)", "").replaceAll("\\(", "").split(" ").toList.intersect(diffString).nonEmpty)
    val diffMap = diffString.zip(diff).toMap
    changedProgs.map(p => updateCost(p, diffMap))

    def updateCost(ast: ASTNode, diffMap: Map[String,(VocabMaker, Double)]): Unit = {
      val change = ast.code.replaceAll("\\)", "").replaceAll("\\(", "").split(" ").toList.head
      if(diffString.contains(change))
        ast.prior = diffMap(change)._2
      if (ast.children.size > 0) {
        ast.children.map(c => updateCost(c, diffMap))
      }
    }
    changedProgs.to(collection.mutable.ListBuffer)
    //TODO: Optimize this (the updated ASTNode value propagates)
  }

  def updateBank(program: ASTNode): Unit = {
    if (!bank.contains(program.cost))
      bank(program.cost) = List(program)
    else {
      val prevKey = bank.find(_._2 == program).map(_._1)
      if (prevKey == None && !bank(program.cost).contains(program)) {
        bank(program.cost) = bank(program.cost) :+ program
      }
      else if (!bank(program.cost).contains(program) && program.cost != prevKey.get) {
          bank(prevKey.get) = bank(prevKey.get).filter(_ != program)
          bank(program.cost) = bank(program.cost) :+ program
      }
    }
  }

  def renewBank(bank: mutable.Map[Double,List[ASTNode]]): mutable.Map[Double,List[ASTNode]] = {
    val programs = bank.values
    programs.map(p => p.distinct.map(c => updateBank(c)))
    bank
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

