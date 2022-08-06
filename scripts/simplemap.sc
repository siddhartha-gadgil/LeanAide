import $file.namemap, namemap._
import $ivy.`com.lihaoyi::upickle:1.6.0`

def polyText(objs: ujson.Value) : ujson.Arr =
    {
        val entries = objs.arr.toVector.flatMap{obj =>
            val text = obj.obj("text").str
            val alts = polyMap(text)
            val transforms = alts.map{s =>
                val js = ujson.copy(obj)
                js("text") = s
                js
            }
            transforms
        }

        ujson.Arr(entries : _*)
    }

@main def transformText(path: os.Path = os.pwd / "web_serv" / "tmp.json") : Unit = {
    val inp = os.read(path)
    val js = upickle.default.read[ujson.Value](inp)
    val out = polyText(js)
    println(ujson.write(out, 2))
}