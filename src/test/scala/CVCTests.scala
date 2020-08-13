import org.scalatest.{BeforeAndAfterAll, FunSuite}
import sygus.SygusFileTask
import org.junit.Assert._

class CVCTests extends FunSuite with BeforeAndAfterAll {

  test("Parsing sygus to SMTlib") {
    val synthConvert = SMTProcess.toSMT(
      """(set-logic BV)
        |
        |(define-fun hd14 ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64) (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)))
        |
        |(synth-fun f ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64)
        |    ((Start (BitVec 64) ((bvlshr Start Start)
        |						 (bvxor Start Start)
        |						 (bvadd Start Start)
        |						 (bvand Start Start)
        |						 x
        |						 y
        |						 #x0000000000000001))))
        |
        |(declare-var x (BitVec 64))
        |(declare-var y (BitVec 64))
        |(constraint (= (hd14 x y) (f x y)))
        |(check-synth)""".stripMargin)
    val synthRes = SMTProcess.invokeCVC(synthConvert.stripMargin, SMTProcess.cvc4_Smt)
    assert(synthRes == List("sat", "((x (_ bv18446744073709551615 64)) (y (_ bv18446744073709551615 64)))"))
  }

  test("Getting cex from query output") {
    val synthRes = SMTProcess.getCEx(List("x", "y"),
      List("sat", "((x (_ bv18446744073709551615 64)) (y (_ bv18446744073709551615 64)))"))
    assert(synthRes == List(Map("x" -> "18446744073709551615", "y" -> "18446744073709551615")))
  }

  test("Parsing SMT2 format LIA") {
    val synthRes = SMTProcess.invokeCVC(
      """(set-option :print-success false)
        |(set-option :produce-models true)
        |(set-logic QF_LIA)
        |(declare-const x Int)
        |(declare-const y Int)
        |(assert (not (= (- x y) 0)))
        |(check-sat)
        |(get-model)
        |""".stripMargin, SMTProcess.cvc4_Smt)
    assert(synthRes == List("sat", "(model", "(define-fun x () Int (- 1))", "(define-fun y () Int 0)", ")"))
  }

  test("Parsing SMT2 format BV") {
    val synthRes = SMTProcess.invokeCVC(
      """(set-option :print-success false)
        |(set-option :produce-models true)
        |(set-logic ALL)
        |(declare-const x (_ BitVec 64))
        |(declare-const y (_ BitVec 64))
        |(declare-fun f ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
        |(assert (not (= (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)) (f x y))))
        |(check-sat)
        |(get-value (x y))""".stripMargin, SMTProcess.cvc4_Smt)
    assert(synthRes == List("sat", "((x (_ bv18446744073709551615 64)) (y (_ bv18446744073709551615 64)))"))
  }

  test("Parsing a synthesis fail") {
    val synthRes = SMTProcess.invokeCVC(
      """(set-logic BV)
        |
        |(define-fun hd14 ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64) (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)))
        |
        |(synth-fun f ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64)
        |    ((Start (BitVec 64) ((bvlshr Start Start)
        |						 (bvxor Start Start)
        |						 (bvadd Start Start)
        |						 (bvand Start Start)
        |						 x
        |						 y
        |						 #x0000000000000001))))
        |
        |(declare-var x (BitVec 64))
        |(declare-var y (BitVec 64))
        |(constraint (= (hd14 x y) (f x y)))
        |(check-synth)""".stripMargin, SMTProcess.cvc4_SyGus)
    assert(synthRes == List("(define-fun f ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64) (bvadd (bvand x y) (bvlshr (bvxor x y) #b0000000000000000000000000000000000000000000000000000000000000001)))"))
  }

}
