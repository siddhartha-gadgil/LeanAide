import scala.util.matching.Regex
import $ivy.`org.scala-lang.modules::scala-parallel-collections:1.0.4`
import scala.collection.parallel.CollectionConverters._

def wordMatch(w: String) = new Regex(
  "(?<![a-zA-Z\\._]+)" + w + "(?![a-zA-Z\\._]+)"
)
def segmentMatch(w: String) = new Regex(
  "(?<![a-zA-Z_]+)" + w + "(?![a-zA-Z_\u2093]+)"
)
def dotMatch(w: String) = new Regex("(?<=\\.)" + w + "(?![a-zA-Z\\._]+)")

def capSegments(s: String) = {
  val pieces = "[A-Z]+[a-z0-9]*".r.findAllIn(s).toVector
  if (pieces.mkString("") == s) pieces
  else if (pieces.nonEmpty && s.endsWith(pieces.mkString("")))(s.dropRight(
    pieces.map(_.length()).sum
  )) +: pieces
  else Vector(s)
}

def segments(s: String) = s
  .split("_")
  .toVector
  .flatMap(capSegments)
  .map(_.toLowerCase)

def segmentsNoIs(s: String) = s
  .split("_")
  .toVector
  .flatMap(capSegments)
  .map(_.toLowerCase.replace("\u2093", ""))
  .filterNot(s => Set("is", "has").contains(s))

def equalSegments(s1: String, s2: String) = {
  val s1s = segmentsNoIs(s1)
  val s2s = segmentsNoIs(s2)
  s1s == s2s
}

def equalTokens(s1: String, s2: String) = {
  val s1s = s1.split("\\.").toVector
  val s2s = s2.split("\\.").toVector
  s1s.zip(s2s).forall { case (a, b) => equalSegments(a, b) }
}

def piecesSegments(s: String) = s.split("\\.").toVector.map(segments(_))

def piecesSegmentsNoIs(s: String) = s.split("\\.").toVector.map(segmentsNoIs(_))

def segmentMap(ss: Vector[String]) = ss
  .map(s => piecesSegmentsNoIs(s) -> s)
  .toMap ++ ss.map(s => piecesSegments(s) -> s).toMap

def piecesMap(ss: Vector[String]) =
  ss.map(s => segmentsNoIs(s) -> s).toMap ++ ss.map(s => segments(s) -> s).toMap

lazy val binNames = os.read.lines(os.pwd / "data" / "binport_names.txt")
lazy val allNames = os.read.lines(os.pwd / "data" / "all_names.txt")
lazy val allNamesPieces = allNames.flatMap(_.split("\\.")).distinct
lazy val allNamePieceSegs = piecesMap(allNamesPieces.toVector)
lazy val binNamesPieces = binNames.flatMap(_.split("\\.")).distinct
lazy val binSegs = segmentMap(binNames.toVector)
lazy val nameMatch = allNames.flatMap(s1 =>
  binSegs
    .get(piecesSegments(s1))
    .orElse(binSegs.get(piecesSegmentsNoIs(s1)))
    .map(s2 => s1 -> s2)
)
lazy val binPieces = binNames.flatMap(_.split("\\.")).distinct
lazy val binPieceSegs = piecesMap(binPieces.toVector)
lazy val namePieceMatch = allNamesPieces.flatMap(s1 =>
  binPieceSegs
    .get(segments(s1))
    .orElse(binPieceSegs.get(segmentsNoIs(s1)))
    .map(s2 => s1 -> s2)
)
lazy val nameMatchAll = (namePieceMatch ++ nameMatch).distinct

import $ivy.`com.lihaoyi::upickle:1.6.0`
lazy val reps =
  nameMatch.filter { case (a, b) => a != b && b != "" && b != "type" }.map {
    case (a, b) =>
      ujson.Obj("snakecase" -> a, "camelcase" -> b)
  }
lazy val jsreps = ujson.write(reps, 2)

lazy val xxNames =
  binNames.filter(w => w.endsWith("\u2093\u2093") && !w.contains("."))
lazy val xNames = binNames.filter(w =>
  w.endsWith("\u2093") && !w.contains(".") && !xxNames.contains(w)
)

lazy val dotPairs = nameMatch
  .filter(_._2.contains("."))
  .map { case (a, b) => (a.split("\\.").last, b.split("\\.").last) }
  .groupMap(_._1)(_._2)
  .map { case (a, v) => a -> v.toVector.distinct.filterNot(_ == a) }
  .filterNot(_._2.isEmpty)

lazy val dotPairVector = dotPairs.toVector.sortBy(_._1.length()).reverse

def withAppend(t: Int)(accum: Vector[String], rep: String): Vector[String] = {
  val r = segmentMatch(rep.dropRight(t))
  accum.flatMap(s => Vector(s, r.replaceAllIn(s, rep)).distinct)
}

def withDotMatch(s: String): Vector[String] = {
  dotPairVector.foldLeft(Vector(s)) {
    case (accum, (a, bs)) => accum.flatMap(w => (w +: bs.map(b => dotMatch(a).replaceAllIn(w, b))).distinct).distinct
  }
}

def withXRep(s: String) : Vector[String] = xNames.foldLeft(Vector(s))(withAppend(1))

def withXXRep(s: String) : Vector[String] = xxNames.foldLeft(Vector(s))(withAppend(2))

lazy val blob = os.read(os.pwd / "data" / "output.json")

lazy val jsBlob = upickle.default.read[ujson.Arr](blob)

lazy val dictBlob = os.read(os.pwd / "data" / "case_dictionary.json")
lazy val dictJson = upickle.default.read[Vector[ujson.Obj]](dictBlob)
lazy val dictMapper = dictJson
  .map(obj => (wordMatch(obj("snakecase").str), obj("camelcase").str))
  .filter(_._2.length() > 1)
  .sortBy(_._1.toString.length())
  .reverse
def mapDict(s: String) = dictMapper.foldLeft(s) { case (accum, (r, out)) =>
  r.replaceAllIn(accum, out)
}

def cleanOutput(jsBlob: ujson.Arr): Unit = {
  for {
    i <- 0 until jsBlob.value.size
    j <- 0 until jsBlob(i)("outputs").arr.value.size
  } {
    val prev = jsBlob(i)("outputs")(j)
    val newVal = mapDict(prev.str.replace("\n", " "))
    println(s"group: $i; output: $j")
    jsBlob(i)("outputs")(j) = ujson.Str(newVal)
  }
}

def cleanOutputExtend(jsBlob: ujson.Arr): Unit = {
  for { i <- 0 until jsBlob.value.size } {
    val prevs = jsBlob(i)("outputs").arr.toVector.par
    val newVals = prevs.map { prev =>
      mapDict(prev.str.replace("\n", " "))
    }
    val mappedNewval = newVals.flatMap(withXRep(_))
    val mappedNewval2 = mappedNewval.flatMap(withXXRep(_))
    val mappedNewval3 = mappedNewval2.map(ujson.Str(_))
    println(s"group: $i, size: ${mappedNewval3.size}")
    jsBlob(i)("outputs") = ujson.Arr(mappedNewval3.seq: _*)
  }
}

def polyMap(s: String) : Vector[String]= {
  val ss : String = mapDict(s)
  val x = withXRep(ss).toVector
  val xx = x.flatMap(withXXRep(_))
  (ss +: (x ++ xx)).distinct.toVector
}

def lastPiecesMap(ss: Vector[String]) = ss
  .filter(_.split("\\.").size == 2)
  .map(s => segmentsNoIs(s.split("\\.").last) -> s)
  .toMap ++ ss
  .filter(_.split("\\.").size == 2)
  .map(s => segments(s.split("\\.").last) -> s)
  .toMap

lazy val lastPieceSegs = lastPiecesMap(binNames.toVector)

lazy val pureNames = allNames.filterNot(_.contains("."))

lazy val lastPiecesMatch = pureNames
  .flatMap(s1 =>
    lastPieceSegs
      .get(segments(s1))
      .orElse(lastPieceSegs.get(segmentsNoIs(s1)))
      .map(s2 => s1 -> s2)
  )
  .toVector
  .filter(_._1 != "Type")

lazy val repsLonger = lastPiecesMatch.filter { case (a, b) => a != b }.map {
  case (a, b) => ujson.Obj("snakecase" -> a, "camelcase" -> b)
}

lazy val jsrepsLonger = ujson.write(repsLonger, 2)

def seeOut(): Unit = {
  val blob = os.read(os.pwd / "data" / "output.json")
  val jsBlob = upickle.default.read[ujson.Arr](blob)
  for {
    i <- 0 until jsBlob.value.size
    j <- 0 until jsBlob(i)("outputs").arr.value.size
  }
    println(jsBlob(i)("outputs")(j))
}

lazy val dictBlobExt = os.read(os.pwd / "data" / "case_dictionary_extend.json")
lazy val dictJsonExt = upickle.default.read[Vector[ujson.Obj]](dictBlobExt)
lazy val dictMapperExt = dictJsonExt.map(obj =>
  (wordMatch(obj("snakecase").str), obj("camelcase").str)
)
def mapDictExt(s: String) = dictMapperExt.foldLeft(s) {
  case (accum, (r, out)) => r.replaceAllIn(accum, out)
}

def identifiers(blob: String) = {
  val regex = "unknown identifier ('[^']*')".r
  val finds = regex.findAllIn(blob).toVector
  finds.map(s => s.drop(20).dropRight(1)).distinct
}.filter(_.size > 1)

def identifiersMult(blob: String) = {
  val regex = "unknown identifier ('[^']*')".r
  val finds = regex.findAllIn(blob).toVector
  finds
    .map(s => s.drop(20).dropRight(1))
    .filter(_.size > 1)
    .groupBy(identity)
    .mapValues(_.size)
    .toVector
    .sortBy(_._2)
    .reverse
}

@main
def caseMap(path: os.Path = os.pwd / "data") : Unit = {
  val blob = os.read(path / "output.json")
  val jsBlob = upickle.default.read[ujson.Arr](blob)
  cleanOutputExtend(jsBlob)
  os.write.over(path / "output_casemap.json", ujson.write(jsBlob, 2))
}