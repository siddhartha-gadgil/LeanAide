def idPairs(js: ujson.Value) =
  js("ids").arr.toVector.map(js => (js.arr(0).str, js.arr(1).num))
def topWeight(pairs: Vector[(String, Double)]) =
  pairs.groupMapReduce(_._1)(_._2)(math.min).toVector.sortBy(_._2).map(_._1)
def idString(js: ujson.Value) = topWeight(idPairs(js)).take(64).mkString("; ")
def idPredData(js: ujson.Value) = ujson.Obj(
  "theorem" -> (js("context").str + " : " + js("type").str),
  "ids" -> idString(js)
)

def shrink(s: String): String =
  s.replace("( ", "(")
    .replace(" )", ")")
    .replace("{ ", "{")
    .replace(" }", "}")
    .replace("[ ", "[")
    .replace(" ]", "]")
    .trim()
    .replace("  ", " ")
val turnstile = "\u22A2"

// No longer used as context not included
def termView(js: ujson.Value): (String, Double) = {
  val value = js("value").str
  val ctx = js("context").arr.map(_.str)
  val size = js("size").num + (3 * ctx.size)
  (
    if (ctx.isEmpty) shrink(value)
    else shrink(ctx.mkString("", " ", " " + turnstile + " " + value)),
    size
  )
}

import scala.collection.mutable

lazy val idV: Vector[(String, Int)] = {
  val id_js = os.read.lines.stream(os.pwd / "rawdata" / "def_ids.jsonl")
  val js = id_js.map(s => upickle.default.read[ujson.Obj](s))
  val ids = js.map(_("ids").arr)
  val idCount: mutable.Map[String, Int] = mutable.Map()
  def addId(id: String): Unit = { idCount(id) = idCount.getOrElse(id, 0) + 1 }
  ids.foreach { idL => idL.arr.foreach(id => addId(id.str)) }
  idCount.toVector.sortBy(_._2)
}

lazy val idCount: Map[String, Int] = idV.toMap

lazy val idThmFull: Map[String, String] = {
  val m = mutable.Map[String, String]()
  val id_js = os.read.lines.stream(os.pwd / "rawdata" / "def_ids.jsonl")
  val js = id_js.map(s => upickle.default.read[ujson.Obj](s))
  id_js.foreach { s =>
    val js = upickle.default.read[ujson.Obj](s)
    if (js("is_prop").bool) {
      m(js("name").str) = js("type").str
    }
  }
  m.toMap
}

lazy val idThm =
  idThmFull.filterKeys((id: String) => idCount.getOrElse(id, 10) < 3)

def idProps(js: ujson.Value) = {
  val ids = js("ids").arr.map(_(0).str).distinct
  ids.flatMap(id => idThm.get(id))
}

def allTerms(js: ujson.Value) =
  js("terms").arr.map(js => (js("value").str, js("size").num)).sortBy(_._2)
def totalBound[A](l: List[(A, Double)], bound: Double)(
    a: A
): List[(A, Double)] = l
  .scanLeft((a, 0.0)) { case ((h, t), (a, w)) => (a, t + w) }
  .tail
  .takeWhile(_._2 < bound)
def topTerms(js: ujson.Value) =
  totalBound(allTerms(js).toList, 128)("").map(_._1).mkString("; ")
def prop(js: ujson.Value) =
  (shrink(js("prop").str), js("propSize").num)
def propVerbose(js: ujson.Value) =
  (
    js("context").arr
      .map(s => shrink(s.str))
      .mkString("", " ", s" : ${shrink(js("prop").str)}"),
    3 * js("context").arr.size + js("propSize").num
  )
def props(js: ujson.Value) =
  js("propProofs").arr.map(prop).sortBy(_._2).distinctBy(_._1)

def topProps(js: ujson.Value): String =
  (totalBound(props(js).toList, 128)("").map(_._1) ++ idProps(js))
    .mkString("; ")

var count: Int = 0

def predData(js: ujson.Value) = ujson.Obj(
  "theorem" -> js("context").arr
    .map(s => shrink(s.str))
    .mkString("", " ", s" : ${shrink(js("type").str)}"),
  "ids" -> idString(js),
  "lemmas" -> topProps(js),
  "terms" -> topTerms(js)
)

lazy val train_js =
  os.read.lines.stream(os.pwd / "rawdata" / "train_premises.jsonl")
def writeTrainingData(): Unit = {
  os.write.over(os.pwd / "rawdata" / "train_ids.jsonl", "")
  train_js.foreach { s =>
  val js = upickle.default.read[ujson.Obj](s)
  count = count + 1
  if (count % 1000 == 0) println(count)
  os.write.append(
    os.pwd / "rawdata" / "train_ids.jsonl",
    ujson.write(predData(js)) + "\n"
  )
}
}

def writeTestData(): Unit = {
  count = 0
  val test_js = os.read.lines.stream(os.pwd / "rawdata" / "test_premises.jsonl")
  val test_id_file = os.pwd / "rawdata" / "test_ids.jsonl"
  os.write.over(test_id_file, "")
  test_js.foreach { s =>
    val js = upickle.default.read[ujson.Obj](s)
    count = count + 1
    if (count % 1000 == 0) println(count)
    os.write.append(test_id_file, ujson.write(predData(js)) + "\n")
  }
}
