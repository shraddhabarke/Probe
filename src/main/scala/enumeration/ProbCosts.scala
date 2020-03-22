package enumeration

import ast.ASTNode

object ProbCosts{
  def getCosts(childrenCost: Int, candidateChildren: List[ASTNode], childrenArity: Int): List[List[Int]] = {
    val childrenCosts = candidateChildren.map(c => computeCost(c))
    var candidateCosts = List[List[Int]]()
    var next_cost : List[Int] = Nil

    val combinations = childrenCosts.combinations(childrenArity).toList.filter(c => c.sum== childrenCost)
    candidateCosts = combinations.map(c => c.permutations.toList).flatten
    candidateCosts = candidateCosts.distinct
    candidateCosts
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
