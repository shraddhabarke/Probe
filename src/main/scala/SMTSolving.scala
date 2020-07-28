package sygus

import ast._
import org.bitbucket.franck44.scalasmt.configurations.SMTInit
import org.bitbucket.franck44.scalasmt.interpreters.{Resources, SMTSolver}
import org.bitbucket.franck44.scalasmt.parser.SMTLIB2Syntax.{Raw, Term}
import org.bitbucket.franck44.scalasmt.theories._
import org.bitbucket.franck44.scalasmt.typedterms.{Commands, QuantifiedTerm}
import org.bitbucket.franck44.scalasmt.theories.{BVTerm, BoolTerm, IntTerm}
import org.bitbucket.franck44.scalasmt.typedterms.TypedTerm

object SMTSolving extends Core
  with IntegerArithmetics
  with QuantifiedTerm
  with Resources
  with Commands
  with ArrayExBool
  with ArrayExOperators
  with BitVectors {

  //  val defaultSolver = "CVC4"
  val defaultSolver = "Z3"

  implicit private var solverObject: SMTSolver = null

  // create solver and assert axioms
  solverObject = new SMTSolver(defaultSolver, new SMTInit())
  for (cmd <- prelude) { solverObject.eval(Raw(cmd)) }

  trait SetTerm
  type SMTBoolTerm = TypedTerm[BoolTerm, Term]
  type SMTIntTerm = TypedTerm[IntTerm, Term]
  type SMTBVTerm = TypedTerm[BVTerm, Term]

  // Commands to be executed before solving starts
  def prelude : List[String] = ???

  /** Translating expression into SMT  */
  case class SMTUnsupportedExpr(e: ASTNode)
    extends Exception(s"Cannot convert expression ${e.code} to an equivalent SMT representation.")

  case class SolverUnsupportedExpr(solver: String)
    extends Exception(s"Unsupported solver: $solver.")

  private def convertFormula(phi: ASTNode): SMTBoolTerm = convertBoolExpr(phi)

  private def convertIntExpr(e: ASTNode): SMTIntTerm = e match {
    case IntLiteral(value: Int, _) => Ints(value)
    case IntAddition(lhs: ASTNode, rhs: ASTNode) => {
      val l = convertIntExpr(lhs)
      val r = convertIntExpr(rhs)
      l + r }
    case IntSubtraction(lhs: ASTNode, rhs: ASTNode) => {
      val l = convertIntExpr(lhs)
      val r = convertIntExpr(rhs)
      l - r }

    case _ => throw SMTUnsupportedExpr(e)
    }

  private def convertBoolExpr(e: ASTNode): SMTBoolTerm = e match {
    case BoolLiteral(value, _) => Bools(value)
    case BoolVariable(value, _) => Bools(value)
    case IntLessThanEq(lhs, rhs) => {
      val l = convertIntExpr(lhs)
      val r = convertIntExpr(rhs)
      l <= r }
    case IntEquals(lhs, rhs) => {
      val l = convertIntExpr(lhs)
      val r = convertIntExpr(rhs)
      l == r }
    case LAnd(lhs, rhs) => {
      val l = convertBoolExpr(lhs)
      val r = convertBoolExpr(rhs)
      l & r }
    case LOr(lhs, rhs) => {
      val l = convertBoolExpr(lhs)
      val r = convertBoolExpr(rhs)
      l | r }
    case LNot(lhs) => {
      val l = convertBoolExpr(lhs)
      !l }
    case BVEquals(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l == r
    }
    case _ => throw SMTUnsupportedExpr(e)
  }

  private def convertBVExpr(e: ASTNode): SMTBVTerm = e match {
    case BVVariable(value, _) => BVs(value)
    case BVLiteral(value, _) => BVs(f"#x$value%016x")
    case BVAnd(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l and r
    }
    case BVOr(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l or r
    }
    case BVXor(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l xor r
    }
    case BVShiftLeft(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l << r
    }
    case BVAdd(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l + r
    }
    case BVSub(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l - r
    }
    case BVSDiv(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l sdiv r
    }
    case BVUDiv(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l / r
    }
    case BVMul(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l * r
    }
    case BVShrLogical(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l >> r
    }
    case BVSRem(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l srem r
    }
    case BVURem(lhs, rhs) => {
      val l = convertBVExpr(lhs)
      val r = convertBVExpr(rhs)
      l  % r
    }
    case _ => throw SMTUnsupportedExpr(e)
  }
}

