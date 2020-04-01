package ast

import enumeration.ProbUpdate

trait ASTNode {
  val nodeType: Types.Types
  val values: List[Any]
  val code: String
  val height: Int
  val terms: Int
  val children: Iterable[ASTNode]
  def includes(varName: String): Boolean
  //var prior: Double
  private var _cost : Option[Double] = None
  def cost: Double = {
    if (_cost.isEmpty) renewCost()
    _cost.get
  }
  def renewCost(): Unit = {
    children.foreach(_.renewCost)
    _cost = Some(ProbUpdate.getRootPrior(this) + children.map(c => c.cost).sum)
  }
}

trait StringNode extends ASTNode {
  override val values: List[String]
  override val nodeType = Types.String
}

trait IntNode extends ASTNode {
  override val values: List[Int]
  override val nodeType = Types.Int
}

trait BoolNode extends ASTNode {
  override val values: List[Boolean]
  override val nodeType = Types.Bool
}