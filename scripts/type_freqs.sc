import $ivy.`com.lihaoyi::upickle:1.6.0`
import $ivy.`com.lihaoyi::os-lib:0.8.0`
import scala.util.matching.Regex

val tokenR = "[a-zA-Z_#/][0-9a-zA-Z#/._]+".r
val blob = os.read(os.pwd / "data" / "clean_prompts.json")
val data = upickle.default.read[Vector[Map[String, String]]](blob)
def tokens(m: Map[String, String]) = {
  val argTokens = tokenR.findAllIn(m("args")).toSet
  tokenR.findAllIn(m("type")).toVector.filterNot(argTokens.contains(_))
}
val allTokens = data.flatMap(tokens)
val tokenCount =
  allTokens.groupBy(identity).mapValues(_.size).toVector.sortBy(_._2).reverse
val tokenJs = tokenCount.map { case (n, c) =>
  ujson.Obj("name" -> n, "count" -> c)
}
val out = ujson.write(tokenJs, 2)
os.write(os.pwd / "data" / "freqs_in_types.json", out)
