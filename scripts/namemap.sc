import scala.util.matching.Regex
def wordMatch(w: String) = new Regex("(?<![a-zA-Z\\.]+)" + w + "(?![a-zA-Z\\.]+)")
def capSegments(s: String) = {
  val pieces = "[A-Z]+[a-z0-9]+".r.findAllIn(s).toVector
  if (pieces.mkString("") == s) pieces else 
  if (pieces.nonEmpty && s.endsWith(pieces.mkString(""))) (s.dropRight(pieces.map(_.length()).sum)) +: pieces
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
  .map(_.toLowerCase)
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

val binNames = os.read.lines(os.pwd / "data" / "binport_names.txt")
val allNames = os.read.lines(os.pwd / "data" / "all_names.txt")
val allNamesPieces = allNames.flatMap(_.split("\\.")).distinct
val allNamePieceSegs = piecesMap(allNamesPieces.toVector)
val binNamesPieces = binNames.flatMap(_.split("\\.")).distinct
val binSegs = segmentMap(binNames.toVector)
val nameMatch = allNames.flatMap(s1 =>
  binSegs
    .get(piecesSegments(s1))
    .orElse(binSegs.get(piecesSegmentsNoIs(s1)))
    .map(s2 => s1 -> s2)
)
val binPieces = binNames.flatMap(_.split("\\.")).distinct
val binPieceSegs = piecesMap(binPieces.toVector)
val namePieceMatch = allNamesPieces.flatMap(s1 =>
  binPieceSegs
    .get(segments(s1))
    .orElse(binPieceSegs.get(segmentsNoIs(s1)))
    .map(s2 => s1 -> s2)
)
val nameMatchAll = (namePieceMatch ++ nameMatch).distinct

import $ivy.`com.lihaoyi::upickle:1.6.0`
val reps = nameMatch.filter { case (a, b) => a != b  && b!= "" && b!= "type"}.map { case (a, b) =>
  ujson.Obj("snakecase" -> a, "camelcase" -> b)
}
val jsreps = ujson.write(reps, 2)

def lastPiecesMap(ss: Vector[String]) = ss
  .filter(_.split("\\.").size == 2)
  .map(s => segmentsNoIs(s.split("\\.").last) -> s)
  .toMap ++ ss
  .filter(_.split("\\.").size == 2)
  .map(s => segments(s.split("\\.").last) -> s)
  .toMap

val lastPieceSegs = lastPiecesMap(binNames.toVector)

val pureNames = allNames.filterNot(_.contains("."))

val lastPiecesMatch = pureNames
  .flatMap(s1 =>
    lastPieceSegs
      .get(segments(s1))
      .orElse(lastPieceSegs.get(segmentsNoIs(s1)))
      .map(s2 => s1 -> s2)
  )
  .toVector
  .filter(_._1 != "Type")

val repsLonger = lastPiecesMatch.filter { case (a, b) => a != b }.map {
  case (a, b) => ujson.Obj("snakecase" -> a, "camelcase" -> b)
}

val jsrepsLonger = ujson.write(repsLonger, 2)

def seeOut(): Unit = {
  val blob = os.read(os.pwd / "data" / "output.json")
  val jsBlob = upickle.default.read[ujson.Arr](blob)
  for {i <- 0 until jsBlob.value.size
     j <- 0 until jsBlob(i)("outputs").arr.value.size}
   println (jsBlob(i)("outputs")(j))
}

val dictBlob = os.read(os.pwd / "data" / "case_dictionary.json")
val dictJson = upickle.default.read[Vector[ujson.Obj]](dictBlob)
val dictMapper = dictJson.map(obj => (wordMatch(obj("snakecase").str), obj("camelcase").str)).filter(_._2.length() > 1).sortBy(_._1.toString.length()).reverse
def mapDict(s: String) = dictMapper.foldLeft(s){case (accum, (r,out)) => r.replaceAllIn(accum, out)}

def cleanOutput(jsBlob : ujson.Arr) : Unit = {
  for {i <- 0 until jsBlob.value.size
     j <- 0 until jsBlob(i)("outputs").arr.value.size}
   {val prev = jsBlob(i)("outputs")(j)
    val newVal = mapDict(prev.str.replace("\n", " "))
    println (s"group: $i; output: $j")
    jsBlob(i)("outputs")(j) = ujson.Str(newVal)}
}

val dictBlobExt = os.read(os.pwd / "data" / "case_dictionary_extend.json")
val dictJsonExt = upickle.default.read[Vector[ujson.Obj]](dictBlobExt)
val dictMapperExt = dictJsonExt.map(obj => (wordMatch(obj("snakecase").str), obj("camelcase").str))
def mapDictExt(s: String) = dictMapperExt.foldLeft(s){case (accum, (r,out)) => r.replaceAllIn(accum, out)}


def identifiers(blob: String) = {
  val regex = "unknown identifier ('[^']*')".r 
  val finds= regex.findAllIn(blob).toVector
  finds.map(s => s.drop(20).dropRight(1)).distinct
  }.filter(_.size > 1)

def identifiersMult(blob: String) = {
  val regex = "unknown identifier ('[^']*')".r 
  val finds= regex.findAllIn(blob).toVector
  finds.map(s => s.drop(20).dropRight(1)).filter(_.size > 1).groupBy(identity).mapValues(_.size).toVector.sortBy(_._2).reverse
  }
  
  