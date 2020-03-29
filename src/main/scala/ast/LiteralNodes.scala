package ast

abstract class LiteralNode[T](numContexts: Int) extends ASTNode{
  assert(numContexts > 0)
  val height = 0
  val terms = 1
  val value: T
  val values: List[T] = List.fill(numContexts)(value)
  override val children: Iterable[ASTNode] = Iterable.empty
  def includes(varName: String): Boolean = false
}
class StringLiteral(val value: String, numContexts: Int, var prior: Int = 0) extends LiteralNode[String](numContexts) with StringNode{
  override lazy val code: String = '"' + value + '"' //escape?
  override def cost: Int = prior + children.toList.map(c => c.cost).sum}

class IntLiteral(val value: Int, numContexts: Int, var prior: Int = 0) extends LiteralNode[Int](numContexts) with IntNode{
  override lazy val code: String = value.toString
  override def cost: Int = prior + children.toList.map(c => c.cost).sum}

class BoolLiteral(val value: Boolean, numContexts: Int, var prior: Int = 0) extends LiteralNode[Boolean](numContexts) with BoolNode {
  override lazy val code: String = value.toString
  override def cost: Int = prior + children.toList.map(c => c.cost).sum}