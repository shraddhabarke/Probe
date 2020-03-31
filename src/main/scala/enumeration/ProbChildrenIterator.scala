package enumeration

import ast.ASTNode
import ast.Types.Types

class ProbChildrenIterator(val childrenCandidates: List[ASTNode], val childTypes: List[Types], val childrenCost: Double) extends Iterator[List[ASTNode]] {
  var childrenLists : List[List[ASTNode]] = childTypes.map { t => childrenCandidates.filter(c => c.nodeType == t) }

  var candidates : Array[Iterator[ASTNode]] = if (childrenLists.exists(l => l.isEmpty)) childrenLists.map(l => Iterator.empty).toArray
                                              else childrenLists.map(l => l.iterator).toArray
  var allExceptLast : Array[ASTNode] = Array.empty
  if (!candidates.isEmpty && candidates(0).hasNext)
    allExceptLast = candidates.dropRight(1).map(_.next()).toArray

  var next_child: Option[List[ASTNode]] = None

  def getNextChild(): Option[List[ASTNode]] = {
    if (!candidates.isEmpty) {
      while (true) {
        if (candidates.last.hasNext) {
          val children = allExceptLast.toList :+ candidates.last.next()
          if (children.map(_.cost).sum <= childrenCost)
            return Some(children)
          else candidates.update(candidates.length - 1,Iterator.empty) //bump last to end, force roll
        }
        else { //roll
          val next = candidates.zipWithIndex.findLast { case (iter, idx) => iter.hasNext }
          if (next.isEmpty) return None
          else {
            val (iter, idx) = next.get
            val nextVal = iter.next
            allExceptLast.update(idx, nextVal)
            for (i <- idx + 1 until candidates.length - 1) {
              candidates.update(i, childrenLists(i).iterator)
              allExceptLast.update(i, candidates(i).next())
            }
          }
          if (allExceptLast.map(_.cost).sum > childrenCost) { //doomed, force roll the next one
            val idx = next.get._2
            if (idx == 0) return None
            candidates.update(idx,Iterator.empty)
            candidates.update(candidates.length - 1,Iterator.empty)
          } else candidates.update(candidates.length - 1, childrenLists.last.iterator)
        }
      }
    }
    None
  }

  override def hasNext: Boolean = {
    if (next_child.isEmpty)
      next_child = getNextChild()
    !next_child.isEmpty
  }

  override def next(): List[ASTNode] = {
    if (next_child.isEmpty)
      next_child = getNextChild()
    val res = next_child.get
    next_child = None
    res
  }
}