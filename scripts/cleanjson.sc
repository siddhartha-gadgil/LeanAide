case class CleanJson(name: String) {
  val file = os.pwd / "rawdata" / name
  val text = os.read(file)
  val jsVec = upickle.default.read[Vector[ujson.Obj]](text)
  def jsonBlock(s: String) =
    if (s.contains("```json")) s.split("```json")(1).split("```")(0).trim
    else if (s.contains("```")) s.split("```")(1).split("```")(0).trim
    else s.trim
  def getJson(s: String): ujson.Value =
    upickle.default.read[ujson.Value](jsonBlock(s).replace("\\", "\\\\"))
  import scala.util._
  def getJsonSafe(s: String): ujson.Value =
    Try(getJson(s)) match {
      case Failure(exception) =>
        println("Failed to parse: " + s)
        println("Error: " + exception.getMessage())
        ujson.Str(s)
      case Success(value) =>
        value
    }
    // Try(getJson(s)).getOrElse{
    //    println("Failed to parse: " + s)
    //    ujson.Str(s)
    // }
  lazy val cleaned =
    jsVec.map { js =>
      val clean = js("structured").arr.toVector.map(_.str).map(getJsonSafe)
      js("structured") = ujson.Arr(clean: _*)
      js
    }
  lazy val cleanedText = ujson.write(cleaned, indent = 2)
  def save(): Unit =
    os.write.over(file, cleanedText)
}
