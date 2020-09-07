package ast

trait BinaryOpNode[T] extends ASTNode{
  val lhs: ASTNode
  val rhs: ASTNode
  override val height: Int = 1 + Math.max(lhs.height,rhs.height)
  override val terms: Int = 1 + lhs.terms + rhs.terms
  assert(lhs.values.length == rhs.values.length)
  def doOp(l: Any, r: Any): T
  lazy val values : List[T] =
    lhs.values.zip(rhs.values).map(pair => doOp(pair._1,pair._2)).toList
  override val children: Iterable[ASTNode] = Iterable(lhs,rhs)
  def includes(varName: String): Boolean = lhs.includes(varName) || rhs.includes(varName)
}

class StringConcat(val lhs: StringNode, val rhs: StringNode) extends BinaryOpNode[String] with StringNode {
  override def doOp(l: Any, r: Any): String = {
    val strLhs = l.asInstanceOf[String]
    val strRhs = r.asInstanceOf[String]
    strLhs + strRhs
  }
  override lazy val code: String = "(str.++ " + lhs.code + " " + rhs.code + ")"
  }

class StringAt(val lhs: StringNode, val rhs: IntNode) extends BinaryOpNode[String] with StringNode {
  override def doOp(l: Any, r: Any): String = {
    val str = l.asInstanceOf[String]
    val idx = r.asInstanceOf[Int]
    if (idx < 0 || idx >= str.length) ""
    else str(idx).toString
  }

  override lazy val code: String = "(str.at " + lhs.code + " " + rhs.code + ")"
  }

class IntAddition(val lhs: IntNode, val rhs: IntNode) extends BinaryOpNode[Int] with IntNode {
  override def doOp(l: Any, r: Any): Int = l.asInstanceOf[Int] + r.asInstanceOf[Int]

  override lazy val code: String = "(+ " + lhs.code + " " + rhs.code + ")"

}

class IntSubtraction(val lhs: IntNode, val rhs: IntNode)extends BinaryOpNode[Int] with IntNode {
  override def doOp(l: Any, r: Any): Int = l.asInstanceOf[Int] - r.asInstanceOf[Int]

  override lazy val code: String = "(- " + lhs.code + " " + rhs.code + ")"

}

class IntLessThanEq(val lhs: IntNode, val rhs: IntNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Int] <= r.asInstanceOf[Int]

  override lazy val code: String = "(<= " + lhs.code + " " + rhs.code + ")"

}

class IntEquals(val lhs: IntNode, val rhs: IntNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Int] == r.asInstanceOf[Int]

  override lazy val code: String = "(= " + lhs.code + " " + rhs.code + ")"

}

class BoolEquals(val lhs: BoolNode, val rhs: BoolNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Boolean] == r.asInstanceOf[Boolean]

  override lazy val code: String = "(= " + lhs.code + " " + rhs.code + ")"

}

class PrefixOf(val lhs: StringNode, val rhs: StringNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = r.asInstanceOf[String].startsWith(l.asInstanceOf[String])

  override lazy val code: String = "(str.prefixof " + lhs.code + " " + rhs.code + ")"

}

class SuffixOf(val lhs: StringNode, val rhs: StringNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = r.asInstanceOf[String].endsWith(l.asInstanceOf[String])

  override lazy val code: String = "(str.suffixof " + lhs.code + " " + rhs.code + ")"


}

class Contains(val lhs: StringNode, val rhs: StringNode) extends  BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[String].contains(r.asInstanceOf[String])

  override lazy val code: String = "(str.contains " + lhs.code + " " + rhs.code + ")"

}

class BVAnd(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = {
    val lhsNode = l.asInstanceOf[Long]
    val rhsNode = r.asInstanceOf[Long]
    lhsNode & rhsNode
  }
  override lazy val code: String = "(bvand " + lhs.code + " " + rhs.code + ")"
}

class BVOr(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = {
    val lhsNode = l.asInstanceOf[Long]
    val rhsNode = r.asInstanceOf[Long]
    lhsNode | rhsNode
  }
  override lazy val code: String = "(bvor " + lhs.code + " " + rhs.code + ")"
}

class BVXor(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = {
    val lhsNode = l.asInstanceOf[Long]
    val rhsNode = r.asInstanceOf[Long]
    lhsNode ^ rhsNode
  }
  override lazy val code: String = "(bvxor " + lhs.code + " " + rhs.code + ")"
}

class BVShiftLeft(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = {
    val lhsNode = l.asInstanceOf[Long]
    val rhsNode = r.asInstanceOf[Long]
    if (rhsNode >= 64 || rhsNode < 0) 0
    else lhsNode << rhsNode
  }
  override lazy val code: String = "(bvshl " + lhs.code + " " + rhs.code + ")"
}

class BVAdd(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = {
    val lhsNode = l.asInstanceOf[Long]
    val rhsNode = r.asInstanceOf[Long]
    lhsNode + rhsNode
  }
  override lazy val code: String = "(bvadd " + lhs.code + " " + rhs.code + ")"
}

class BVSub(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = {
    val lhsNode = l.asInstanceOf[Long]
    val rhsNode = r.asInstanceOf[Long]
    lhsNode - rhsNode
  }

  override val code: String = "(bvsub " + lhs.code + " " + rhs.code + ")"
}

class BVSDiv(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = l.asInstanceOf[Long] / r.asInstanceOf[Long]

  override val code: String = "(bvsdiv " + lhs.code + " " + rhs.code + ")"
}

class BVUDiv(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = java.lang.Long.divideUnsigned(l.asInstanceOf[Long],r.asInstanceOf[Long])

  override val code: String = "(bvudiv " + lhs.code + " " + rhs.code + ")"
}

class BVMul(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = l.asInstanceOf[Long] * r.asInstanceOf[Long]

  override val code: String = "(bvmul " + lhs.code + " " + rhs.code + ")"
}

class BVShrLogical(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = {
    val lhsNode = l.asInstanceOf[Long]
    val rhsNode = r.asInstanceOf[Long]
    if (rhsNode >= 64 || rhsNode < 0) 0
    else lhsNode >>> rhsNode
  }
  override lazy val code: String = "(bvlshr " + lhs.code + " " + rhs.code + ")"
}

class BVShrArithmetic(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = {
    val lhsNode = l.asInstanceOf[Long]
    val rhsNode = r.asInstanceOf[Long]
    if ((rhsNode >= 64 || rhsNode < 0) && lhsNode >= 0) 0
    else lhsNode >> rhsNode
  }
  override lazy val code: String = "(bvashr " + lhs.code + " " + rhs.code + ")"
}

class BVEquals(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Long] == r.asInstanceOf[Long]

  override val code: String = "(= " + lhs.code + " " + rhs.code + ")"
}

class BVSlt(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Long] < r.asInstanceOf[Long]

  override val code: String = "(bvslt " + lhs.code + " " + rhs.code + ")"
}

class BVSle(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Long] <= r.asInstanceOf[Long]

  override val code: String = "(bvsle " + lhs.code + " " + rhs.code + ")"
}

class BVUlt(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean
  = java.lang.Long.compareUnsigned(l.asInstanceOf[Long], r.asInstanceOf[Long]) < 0

  override val code: String = "(bvult " + lhs.code + " " + rhs.code + ")"
}

class BVUle(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean
    = java.lang.Long.compareUnsigned(l.asInstanceOf[Long], r.asInstanceOf[Long]) <= 0

    override val code: String = "(bvule " + lhs.code + " " + rhs.code + ")"
}

class BVUgt(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean
  = java.lang.Long.compareUnsigned(l.asInstanceOf[Long], r.asInstanceOf[Long]) > 0

  override val code: String = "(bvugt " + lhs.code + " " + rhs.code + ")"
}

class LAnd(val lhs: BoolNode, val rhs: BoolNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Boolean] && r.asInstanceOf[Boolean]

  override val code: String = "(and " + lhs.code + " " + rhs.code + ")"
}

class LOr(val lhs: BoolNode, val rhs: BoolNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Boolean] || r.asInstanceOf[Boolean]

  override val code: String = "(or " + lhs.code + " " + rhs.code + ")"
}

class LXor(val lhs: BoolNode, val rhs: BoolNode) extends BinaryOpNode[Boolean] with BoolNode {
  override def doOp(l: Any, r: Any): Boolean = l.asInstanceOf[Boolean] ^ r.asInstanceOf[Boolean]

  override val code: String = "(xor " + lhs.code + " " + rhs.code + ")"
}

class BVSRem(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = l.asInstanceOf[Long] % r.asInstanceOf[Long]

  override val code: String = "(bvsrem " + lhs.code + " " + rhs.code + ")"
}

class BVURem(val lhs: BVNode, val rhs: BVNode) extends BinaryOpNode[Long] with BVNode {
  override def doOp(l: Any, r: Any): Long = java.lang.Long.remainderUnsigned(l.asInstanceOf[Long], r.asInstanceOf[Long])

  override val code: String = "(bvurem " + lhs.code + " " + rhs.code + ")"
}