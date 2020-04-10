package enumeration

object ProbCosts{
  def getCosts(childrenCost: Double, childrenCosts: List[Int], childrenArity: Int): List[List[Int]] = {
    var candidateCosts = List[List[Int]]()

    val combinations = (childrenCosts ++ childrenCosts ++ childrenCosts).combinations(childrenArity).filter(c => c.sum == childrenCost)
    candidateCosts = combinations.flatMap(c => c.permutations).toList
    candidateCosts = candidateCosts.distinct
    candidateCosts
  }
}
