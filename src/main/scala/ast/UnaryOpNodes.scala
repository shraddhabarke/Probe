package ast

trait UnaryOpNode[T] extends ASTNode{
  val arg: ASTNode
  def doOp(x: Any): T
  override lazy val values : List[T] = arg.values.map(doOp)
  override val height = 1 + arg.height
  override val terms: Int = 1 + arg.terms
  override val children: Iterable[ASTNode] = Iterable(arg)
  def includes(varName: String): Boolean = arg.includes(varName)
}

class IntToString(val arg: IntNode) extends UnaryOpNode[String] with StringNode {
  override def doOp(x: Any): String = if (x.asInstanceOf[Int] >= 0) x.asInstanceOf[Int].toString else ""

  override lazy val code: String = "(int.to.str " + arg.code + ")"

}

class StringToInt(val arg: StringNode) extends UnaryOpNode[Int] with IntNode {
  override def doOp(x: Any): Int = {
    val str = x.asInstanceOf[String]
    if (!str.isEmpty && str.forall(c => c.isDigit)) str.toInt
    else -1
  }

  override lazy val code: String = "(str.to.int " + arg.code + ")"

}

class StringLength(val arg: StringNode) extends UnaryOpNode[Int] with IntNode {
  override def doOp(x: Any): Int = x.asInstanceOf[String].length

  override lazy val code: String = "(str.len " + arg.code + ")"

}

case class BVNot(val arg: BVNode) extends UnaryOpNode[Long] with BVNode {
  override def doOp(x: Any): Long = {
    val bv = x.asInstanceOf[Long]
    ~bv
  }

  override lazy val code: String = "(bvnot " + arg.code + ")"
}

case class BVNeg(val arg: BVNode) extends UnaryOpNode[Long] with BVNode {
  override def doOp(x: Any): Long = -x.asInstanceOf[Long]

  override val code: String = "(bvneg " + arg.code + ")"
}

case class LNot(val arg: BoolNode) extends UnaryOpNode[Boolean] with BoolNode {
  override def doOp(x: Any): Boolean = !x.asInstanceOf[Boolean]

  override val code: String = "(not " + arg.code + ")"
}

class BVRedor(val arg: BVNode) extends UnaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any): Boolean = {
    val lhsNode = l.asInstanceOf[Long]
    if (lhsNode == 0) false
    else true
  }
  override lazy val code: String = "(bvredor " + arg.code + ")"
}
