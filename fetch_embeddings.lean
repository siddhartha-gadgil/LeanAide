import Cache.IO
import LeanAide.Aides
open Lean Cache.IO


unsafe def main (args: List String) : IO UInt32 := do
  let descField := args.getD 0 "docString"
  let picklePath ← picklePath descField
  if (← picklePath.pathExists) &&
    (args.all <| fun x => x != "--force") then
    IO.eprintln s!"Embeddings already present at {picklePath}, use --force to redownload."
    return 1
  IO.eprintln "Fetching embeddings ..."
  IO.eprintln s!"https://storage.googleapis.com/leanaide_data/{picklePath.fileName.get!}"
  let out ← runCurl #["--output", picklePath.toString,   s!"https://storage.googleapis.com/leanaide_data/{picklePath.fileName.get!}"]
  IO.eprintln "Fetched embeddings"
  IO.eprintln out
  return 0
