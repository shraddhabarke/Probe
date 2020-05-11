package sygus
import ast.{ASTNode, BoolLiteral, BoolVariable, Contains, IndexOf, IntAddition, IntEquals, IntITE, IntLiteral, IntSubtraction, IntToString, IntVariable, PrefixOf, StringAt, StringConcat, StringITE, StringLength, StringLiteral, StringReplace, StringToInt, StringVariable, Substring, SuffixOf}
import enumeration.ProbUpdate
import org.apache
import spray.json.{JsArray, JsBoolean, JsNumber, JsObject, JsString}

import scala.language.postfixOps
import spray.json._

import scala.collection.mutable

object ParseJson{

  var parsedMap = scala.collection.mutable.Map[String, Map[Class[_], Double]]()
  var convertMap = scala.collection.mutable.Map[String,Class[_]]()
  convertMap += ("(+ ntInt ntInt)" -> classOf[IntAddition],
    "(= ntInt ntInt)" -> classOf[IntEquals],
    "(- ntInt ntInt)" -> classOf[IntSubtraction],
    "(int.to.str ntInt)" -> classOf[IntToString],
    "(ite ntBool ntInt ntInt)" -> classOf[IntITE],
    "(ite ntBool ntString ntString)" -> classOf[StringITE] ,
    "(str.++ ntString ntString)" -> classOf[StringConcat],
    "(str.at ntString ntInt)" -> classOf[StringAt] ,
    "(str.contains ntString ntString)" -> classOf[Contains],
    "(str.indexof ntString ntString ntInt)" -> classOf[IndexOf],
    "(str.len ntString)" -> classOf[StringLength],
    "(str.prefixof ntString ntString)" -> classOf[PrefixOf],
    "(str.replace ntString ntString ntString)" -> classOf[StringReplace],
    "(str.substr ntString ntInt ntInt)" -> classOf[Substring],
    "(str.suffixof ntString ntString)" -> classOf[SuffixOf],
    "(str.to.int ntString)" -> classOf[StringToInt],
    "<bool_arg>" -> classOf[BoolVariable],
    "<bool_const>" -> classOf[BoolLiteral],
    "<int_arg>" -> classOf[IntVariable],
    "<int_const>" -> classOf[IntLiteral],
    "<str_arg>" -> classOf[StringVariable],
    "<str_const>" -> classOf[StringLiteral])

  def parseMap(): scala.collection.mutable.Map[String, Map[Class[_], Double]] = {
    val jsonified = scala.io.Source.fromFile("C:\\Users\\shrad\\Desktop\\partialcorrectness\\src\\main\\scala\\scores_CNN_generated_scaled.json").mkString.parseJson
    for ((key, value) <- jsonified.asInstanceOf[JsObject].fields) {
      val temp = value.asJsObject.fields.map {
        case (name, value) =>
          val scalaValue = value match {
            case n: JsNumber => (1 - n.value.toDouble)
            case b: JsBoolean => b.value
            case s: JsString => convertMap(s.value)
          }
          (name, scalaValue)
      }.toMap

      parsedMap = parsedMap.addOne(key.toString, temp.map(c => (convertMap(c._1), c._2.asInstanceOf[Double])))
    }
    parsedMap
  }

  var jsonMap: scala.collection.mutable.Map[String, Map[Class[_],Double]] = null
  jsonMap = ParseJson.parseMap()

}