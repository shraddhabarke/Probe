package enumeration

import ast.ASTNode

class ProbCostIterator(val childrenCost: Int, val candidateChildren: List[ASTNode], val childrenArity: Int) extends Iterator[List[Int]] {
  val childrenCosts = candidateChildren.map(c => computeCost(c))
  var candidateCosts = List[List[Int]]()
  var next_cost : List[Int] = Nil

  val combinations = childrenCosts.combinations(childrenArity).toList.filter(c => c.sum== childrenCost)
  candidateCosts = combinations.map(c => c.permutations.toList).flatten
  candidateCosts = candidateCosts.distinct
  var candidates = candidateCosts.iterator

  def getCost(): List[Int] = {
    if (candidates.hasNext)
      next_cost = candidates.next()
    next_cost
  }

  override def hasNext: Boolean = {
    if (next_cost.isEmpty) getCost()
    !next_cost.isEmpty
  }

  override def next(): List[Int] = {
    if (next_cost.isEmpty) getCost()
    val res = next_cost
    next_cost = Nil
    res
  }

  def computeCost(ast: ASTNode): Int = {
    var cost = ast.cost
    if (ast.children.size > 0) {
      for (c <- ast.children)
        cost += computeCost(c)
    }
    cost
  }
}
