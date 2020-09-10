package enumeration

import ast.ASTNode
import ast.Types.Types
import scala.collection._

class ChildrenIterator(val childrenCandidates: List[ASTNode], val childTypes: List[Types], val currHeight: Int) extends Iterator[List[ASTNode]]{
  var childrenLists : List[List[ASTNode]] = Nil
  var candidates = Array[Iterator[ASTNode]]()
  var allExceptLast : Array[ASTNode] = Array.empty

  childrenLists = childTypes.map(t => childrenCandidates.filter(c => c.nodeType == t))
  candidates = if (childrenLists.exists(l => l.isEmpty)) childrenLists.map(_ => Iterator.empty).toArray
  else childrenLists.map(l => l.iterator).toArray
  if (!candidates.isEmpty && candidates(0).hasNext)
    allExceptLast = candidates.dropRight(1).map(_.next())
  var next_child: Option[List[ASTNode]] = None
  def getNextChild(): Unit = {
    next_child = None
    while (next_child.isEmpty) {
      if (candidates.last.hasNext) {
        val children = allExceptLast.toList :+ candidates.last.next()
        if (children.exists(child => child.height == currHeight - 1))
          next_child = Some(children)
      }
      else { //roll
        val next = candidates.zipWithIndex.filter{case (iter,_) => iter.hasNext}.lastOption
        if (next.isEmpty) return
        else {
          val (iter,idx) = next.get
          allExceptLast.update(idx,iter.next)
          for (i <- idx + 1 until candidates.length - 1) {
            candidates.update(i,childrenLists(i).iterator)
            allExceptLast.update(i,candidates(i).next())
          }
          candidates.update(candidates.length - 1,childrenLists.last.iterator)
        }
      }
    }
  }
  override def hasNext: Boolean = {
    if (next_child.isEmpty) getNextChild()
    !next_child.isEmpty
  }
  override def next(): List[ASTNode] = {
    if (next_child.isEmpty) getNextChild()
    val res = next_child.get
    next_child = None
    res
  }
}