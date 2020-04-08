package enumeration

import ast.ASTNode

object ProbCosts{
  def getCosts(childrenCost: Double, candidateChildren: List[ASTNode], childrenArity: Int): List[List[Int]] = {
    val childrenCosts = candidateChildren.map(c => c.cost)
    var candidateCosts = List[List[Int]]()

    val combinations = childrenCosts.toList.combinations(childrenArity).toList.filter(c => c.sum == childrenCost)
    candidateCosts = combinations.map(c => c.permutations.toList).flatten
    candidateCosts = candidateCosts.distinct
    candidateCosts
  }

}
