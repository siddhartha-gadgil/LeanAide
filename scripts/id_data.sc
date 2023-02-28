def idPairs(js: ujson.Value) = js("ids").arr.toVector.map(js => (js.arr(0).str, js.arr(1).num))
def topWeight(pairs : Vector[(String, Double)]) = pairs.groupMapReduce(_._1)(_._2)(math.min).toVector.sortBy(_._2).map(_._1)
def idString(js: ujson.Value) = topWeight(idPairs(js)).take(64).mkString("; ")
def idPredData (js: ujson.Value) = ujson.Obj("theorem" -> (js("context").str + " : " + js("type").str), "ids" -> idString(js))

var count = 0
val train_js = os.read.lines.stream(os.pwd / "rawdata" / "train_premises.jsonl")
train_js.foreach{s =>
val js = upickle.default.read[ujson.Obj](s)
count = count + 1
if (count % 1000 == 0) println (count)
os.write.append(train_id_file, ujson.write(idPredData(js))+"\n")
} 
count = 0
val test_js = os.read.lines.stream(os.pwd / "rawdata" / "test_premises.jsonl")
val test_id_file = os.pwd/ "rawdata" / "test_ids.jsonl"
test_js.foreach{s =>
val js = upickle.default.read[ujson.Obj](s)
count = count + 1
if (count % 1000 == 0) println (count)
os.write.append(test_id_file, ujson.write(idPredData(js))+"\n")
} 

