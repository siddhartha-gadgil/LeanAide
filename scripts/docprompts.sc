import $ivy.`com.lihaoyi::upickle:1.6.0`
import $ivy.`com.lihaoyi::os-lib:0.8.0`
import scala.util.matching.Regex

val regex = "\ue000([^\ue001]*)\ue001([^\ue002]*)\ue002".r

def clean(s: String): String = regex.replaceAllIn(s, _.group(2))

import ujson._
val filename = "decls200.json"
lazy val fullSource = os.read(os.pwd / "rawdata" / "export.json")
lazy val fullDecls = ujson.read(fullSource)("decls")
val jsSource = os.read(os.pwd / "data" / filename)
val decls = ujson.read(jsSource).arr
def exprString(js: Value): String =
  js.strOpt.map(s => clean(s).replace("\n", " ")).getOrElse {
    val arr = js.arr
    val head = arr.head.str
    head match {
      case "c" => exprString(arr(1)) + exprString(arr(2))
      case "n" =>
        // println(arr(1))
        exprString(arr(1))
    }
  }

def nameArgsType(obj: Obj) = {
  val name = obj("name").str
  val args = obj("args").arr.map(js => exprString(js("arg")))
  val typeExpr = exprString(obj("type"))
  (name, args, typeExpr)
}

def nameArgTypes(arr: Value) = arr.arr.map(js => nameArgsType(js.obj))

def nameArgStrings(arr: Value) = nameArgTypes(arr).map {
  case (name, args, typeExpr) =>
    name + " " + args.mkString(" ") + " : " + typeExpr
}

def promptJs(js: Value): Value = {
  val obj = js.obj
  val name = obj("name").str.replace("\n", " ")
  val argSeq = obj("args").arr.toVector.map(js => exprString(js("arg")))
  val args = argSeq.mkString(" ")
  val typeExpr = exprString(obj("type"))
  val statement =
    s"theorem ${name} ${args} : ${typeExpr}"
  Obj(
    "doc_string" -> obj("doc_string").str,
    "statement" -> statement,
    "name" -> name,
    "args" -> args,
    "type" -> typeExpr
  )
}

def allPrompts(js: Value) = {
  val promptSeq = js.arr.toVector
    .filter(js => js("kind").str == "theorem" && js("doc_string").str.nonEmpty)
    .map(promptJs)
  Arr(promptSeq: _*)
}

def writeFull(): Unit = {
  val fullJs = allPrompts(fullDecls)
  println(
    s"Writing ${fullJs.arr.length} full declarations to ${os.pwd / "data" / "fulldecls.json"}"
  )
  os.write.over(os.pwd / "data" / "prompts.json", ujson.write(fullJs, 2))
}
