package enumeration

import ast.ASTNode
import ast.Types.Types

import scala.collection.parallel.CollectionConverters._
import trace.DebugPrints.dprintln

class ProbChildrenIterator(val childrenCandidates: List[ASTNode], val childTypes: List[Types], val childrenCost: Int, val bank: scala.collection.mutable.Map[Int, List[ASTNode]]) extends Iterator[List[ASTNode]] {
  val costs = new ProbCostIterator(childrenCost, childrenCandidates, childTypes.size)
  var childrenLists =
    childTypes.zip(costs.next()).map { case (t, c) => bank(c).filter(c => c.nodeType == t) }
  var candidates = Array[Iterator[ASTNode]]()
  def resetIterators(cost: List[Int]): Unit = {
    childrenLists = childTypes.zip(cost).map { case (t, c) => bank(c).filter(c => c.nodeType == t) }
    candidates = if (childrenLists.exists(l => l.isEmpty)) childrenLists.map(l => Iterator.empty).toArray
                 else childrenLists.map(l => l.iterator).toArray
  }

  var next_child: Option[List[ASTNode]] = None
  val costsIterator = costs.iterator

  candidates = childrenLists.map(l => l.iterator).toArray
  val allExceptLast = candidates.dropRight(1).map(_.next()).toArray

  def getNextChild(): Option[List[ASTNode]] = {
    next_child = None
    if (!candidates.isEmpty) {
      while (next_child.isEmpty) {
        if (candidates.last.hasNext) {
          val children = allExceptLast.toList :+ candidates.last.next()
          return Some(children)
        }
        else { //roll
          val next = candidates.zipWithIndex.findLast { case (iter, idx) => iter.hasNext }
          if (next.isEmpty) return None
          else {
            val (iter, idx) = next.get
            allExceptLast.update(idx, iter.next)
            for (i <- idx + 1 until candidates.length - 1) {
              candidates.update(i, childrenLists(i).iterator)
              allExceptLast.update(i, candidates(i).next())
            }
          }
          candidates.update(candidates.length - 1, childrenLists.last.iterator)
        }
      }
    }
    None
  }

  def getChild(): Unit = {
    next_child = None
    while (next_child.isEmpty) {
      next_child = getNextChild()
      if (next_child.isEmpty) {
        if (!costsIterator.hasNext) return
        val newCost = costsIterator.next()
        resetIterators(newCost)
      }
    }
  }

  override def hasNext: Boolean = {
    if (next_child.isEmpty) getChild()
    !next_child.isEmpty
  }

  def computeCost(ast: ASTNode): Int = {
    var cost = ast.cost
    if (ast.children.size > 0) {
      for (c <- ast.children)
        cost += computeCost(c)
    }
    cost
  }

  override def next(): List[ASTNode] = {
    if (next_child.isEmpty) getChild()
    val res = next_child.get
    next_child = None
    res
  }
}