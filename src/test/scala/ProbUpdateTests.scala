import ast.{ASTNode}
import org.junit.Assert.assertEquals
import org.junit.Test
import org.scalatestplus.junit.JUnitSuite
import sygus.Main
import enumeration.ProbUpdate
import scala.collection.mutable

import scala.collection.mutable.ArrayBuffer

class ProbUpdateTests extends JUnitSuite{

@Test def clusterTest3: Unit = {
    val prog1 = "(str.substr (str.++ \" \" _arg_0) (str.indexof _arg_0 \".\" 1) (str.len _arg_0))"
    val prog2 = "(str.substr _arg_0 (+ (+ -1 (+ -1 -1)) (str.len _arg_0)) (str.len _arg_0))"
    val prog3 = "(str.substr (str.++ \" \" _arg_0) (str.indexof _arg_0 \".\" 1) (str.indexof _arg_0 \" \" 1))"

    val tree1: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog1).get._1
    val tree2: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog2).get._1
    val tree3: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog3).get._1

    val arrayBuffer1 = ArrayBuffer(tree1, tree2, tree3)
    val fitMap = mutable.Map[Set[Any], ArrayBuffer[ASTNode]]()
    fitMap(Set(5.1, 1.0)) = arrayBuffer1
    assertEquals(ArrayBuffer(tree1,tree2),ProbUpdate.clusterAndPick(fitMap))
  }

  @Test def clusterTest0: Unit = {
    val prog1 = "(str.substr (str.++ \" \" _arg_0) (str.indexof _arg_0 \".\" 1) (str.len _arg_0))"
    val prog2 = "(str.substr _arg_0 (+ (+ -1 (+ -1 -1)) (str.len _arg_0)) (str.len _arg_0))"
    val prog3 = "(str.substr (str.++ \" \" _arg_0) (str.indexof _arg_0 \".\" 1) (str.indexof _arg_0 \" \" 1))"

    val tree1: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog1).get._1
    val tree2: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog2).get._1
    val tree3: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog3).get._1

    val arrayBuffer1 = ArrayBuffer(tree1, tree2)
    val arrayBuffer2 = ArrayBuffer(tree3)
    var fitMap = mutable.Map[Set[Any], ArrayBuffer[ASTNode]]()
    fitMap(Set(5.1, 1.0)) = arrayBuffer1
    fitMap(Set((5.1, 1.0, 2.6))) = arrayBuffer2
    assertEquals(ArrayBuffer(tree3,tree1,tree2),ProbUpdate.clusterAndPick(fitMap)) //since tree3 is in it's own group
  }

  @Test def clusterTest2: Unit = {
    val prog1 = "(str.substr (str.++ \" \" _arg_0) (str.indexof _arg_0 \".\" 1) (str.len _arg_0))"
    val prog2 = "(str.substr _arg_0 (+ (+ -1 (+ -1 -1)) (str.len _arg_0)) (str.len _arg_0))"

    val tree1: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog1).get._1
    val tree2: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog2).get._1

    val arrayBuffer = ArrayBuffer(tree1, tree2)
    var fitMap = mutable.Map[Set[Any], ArrayBuffer[ASTNode]]()
    fitMap(Set(5.1, 1.0)) = arrayBuffer
    assertEquals(ArrayBuffer(tree1,tree2),ProbUpdate.clusterAndPick(fitMap))
  }

  @Test def clusterTest1: Unit = {
    val prog1 = "(str.substr (str.++ \" \" _arg_0) (str.indexof _arg_0 \".\" 1) (str.len _arg_0))"
    val prog2 = "(str.substr _arg_0 (+ (+ -1 (+ -1 -1)) (str.len _arg_0)) (str.len _arg_0))"

    val tree1: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog1).get._1
    val tree2: ASTNode = Main.interpret("src/test/benchmarks/too-hard/11604909.sl",prog2).get._1

    val arrayBuffer = ArrayBuffer(tree1)
    var fitMap = mutable.Map[Set[Any], ArrayBuffer[ASTNode]]()
    fitMap(Set(5.1, 1.0)) = arrayBuffer
    assertEquals(ArrayBuffer(tree1),ProbUpdate.clusterAndPick(fitMap))
  }
}
