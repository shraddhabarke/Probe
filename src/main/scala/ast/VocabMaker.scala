package ast

import ast.Types.Types
import enumeration.ProbUpdate

trait VocabMaker {
  val arity: Int
  val childTypes: List[Types]
  val returnType: Types
  val head: String
  val nodeType: Class[_ <: ASTNode]
  def rootCost: Int = if (nodeType == classOf[IntLiteral] || nodeType == classOf[StringLiteral] || nodeType == classOf[BoolLiteral]
    || nodeType == classOf[StringVariable] || nodeType == classOf[BoolVariable] || nodeType == classOf[IntVariable])
    ProbUpdate.priors(nodeType, Some(head)) else ProbUpdate.priors(nodeType, None)
  def canMake(children: List[ASTNode]): Boolean = children.length == arity && children.zip(childTypes).forall(pair => pair._1.nodeType == pair._2)
  def apply(children: List[ASTNode], contexts: List[Map[String,Any]]): ASTNode
}

class VocabFactory(val leavesMakers: List[VocabMaker], val nodeMakers: List[VocabMaker]) {
  def leaves(): Iterator[VocabMaker] = leavesMakers.iterator
  def nonLeaves(): Iterator[VocabMaker] = nodeMakers.iterator
}

object VocabFactory{
  def apply(vocabMakers: Seq[VocabMaker]): VocabFactory = {
    val (leavesMakers, nodeMakers) = vocabMakers.toList.partition(m => m.arity == 0)
    new VocabFactory(leavesMakers,nodeMakers)
  }
}