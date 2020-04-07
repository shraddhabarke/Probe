package enumeration
import ast.ASTNode
import scala.collection.mutable

trait OEValuesManager {
  def isRepresentative(program: ast.ASTNode): Boolean
  def clear(): Unit
}
class InputsValuesManager extends OEValuesManager {
  val classValues = mutable.HashSet[List[Any]]()
  override def isRepresentative(program: ASTNode): Boolean = {
    try {
      val results: List[Any] = program.values
      classValues.add(results)
    }
    catch {
      case ex: Exception => false
    }
  }

  override def clear(): Unit = classValues.clear()
}
