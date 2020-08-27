import org.scalatest.{BeforeAndAfterAll, FunSuite}
import sygus.{Example, SMTProcess, SygusFileTask}

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
    val query = SMTProcess.getquery("(bvadd (bvand x y) (bvlshr (bvor x y) #x0000000000000001))", synthConvert._1)
    val synthRes = SMTProcess.invokeCVC(query, SMTProcess.cvc4_Smt)
    assert(synthRes == List("sat", "((x #b1111111111110111111111111011111100001000000011000001000001101000) (y #b1111111111110111111111111011111100001100000000000001000001100000))"))
    assert(synthConvert._2 == List("x", "y"))
    assert(synthConvert._3 == "(bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001))")
  }

  test("Getting cex from query output") {
    val synthRes = SMTProcess.getCEx(new SygusFileTask("""(set-logic BV)
      |(define-fun hd14 ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64) (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)))
      |(synth-fun f ((x (BitVec 64)) (y (BitVec 64))) (BitVec 64)
      |((Start (BitVec 64) ((bvlshr Start Start)
		  |(bvxor Start Start)
		  |(bvadd Start Start)
			|(bvand Start Start)
			|x
			|y
		  |#x0000000000000001))))
      |
      |(declare-var x (BitVec 64))
      |(declare-var y (BitVec 64))
      |(constraint (= (hd14 x y) (f x y)))
       |(check-synth)""".stripMargin), List("x", "y"),
      List("sat", "((x #b1111111111110111111111111011111100001000000011000001000001101000) (y #b1111111111110111111111111011111100001100000000000001000001100000))"),
      "(bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001))")
      assert(synthRes == Example(Map("x" -> -2252078851551128L, "y" -> -2252078785228704L),-2252078818389916L))
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

  test("Checking unsat") {
    val synthRes = SMTProcess.invokeCVC(
      """(set-option :print-success false)
        |(set-option :produce-models true)
        |(set-logic ALL)
        |(declare-const x (_ BitVec 64))
        |(declare-const y (_ BitVec 64))
        |(declare-fun f ((_ BitVec 64) (_ BitVec 64)) (_ BitVec 64))
        |(assert (not (= (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)) (bvadd (bvand x y) (bvlshr (bvxor x y) #x0000000000000001)))))
        |(check-sat)""".stripMargin, SMTProcess.cvc4_Smt)
    assert(synthRes == List("unsat"))
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
