package ast

import ast.Types.Types
import enumeration.ProbUpdate

import scala.collection.mutable

class VocabFactory(val leavesMakers: List[VocabMaker], val nodeMakers: List[VocabMaker]) {
  def leaves(): Iterator[VocabMaker] = leavesMakers.iterator
  def nonLeaves(): Iterator[VocabMaker] = nodeMakers.iterator
}

object VocabFactory {
  def apply(vocabMakers: Seq[VocabMaker]): VocabFactory = {
    val (leavesMakers, nodeMakers) = vocabMakers.toList.partition(m => m.arity == 0)
    new VocabFactory(leavesMakers, nodeMakers)
  }
}

trait VocabMaker {
  val arity: Int
  val childTypes: List[Types]
  val nodeType: Class[_ <: ASTNode]
  val head: String
  val returnType: Types
  def apply(children: List[ASTNode], contexts: List[Map[String,Any]]): ASTNode
  def canMake(children: List[ASTNode]): Boolean = children.length == arity && children.zip(childTypes).forall(pair => pair._1.nodeType == pair._2)

  def rootCost: Int = if (nodeType == classOf[IntLiteral] || nodeType == classOf[StringLiteral] || nodeType == classOf[BoolLiteral]
    || nodeType == classOf[StringVariable] || nodeType == classOf[BoolVariable] || nodeType == classOf[IntVariable]
    || nodeType == classOf[BVLiteral] || nodeType == classOf[BVVariable])

    ProbUpdate.priors(nodeType, Some(head)) else ProbUpdate.priors(nodeType, None)
  def init(progs: List[ASTNode], contexts : List[Map[String, Any]], vocabFactory: VocabFactory, height: Int) : Iterator[ASTNode]
  def probe_init(progs: List[ASTNode],
                 vocabFactory: VocabFactory, costLevel: Int, contexts: List[Map[String,Any]], bank: mutable.Map[Int, mutable.ArrayBuffer[ASTNode]]) : Iterator[ASTNode]
}

