import Cache.IO
import LeanAide.Aides
open Lean Cache.IO


unsafe def main (args: List String) : IO UInt32 := do
  let picklePath ← picklePath "docString"
  if (← picklePath.pathExists) &&
    !(args.get? 0 == some "--force") then
    IO.eprintln s!"Embeddings already present at {picklePath}, use --force to redownload."
    return 1
  IO.eprintln "Fetching embeddings ..."
  let out ← runCurl #["--output", picklePath.toString, "-s",  s!"https://math.iisc.ac.in/~gadgil/data/{picklePath.fileName.get!}"]
  IO.eprintln "Fetched embeddings"
  IO.eprintln out
  return 0
