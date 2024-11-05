import Cache.IO
import LeanAide.Aides
open Lean Cache.IO

unsafe def fetchEmbedding (descField : String) (force: Bool) : IO UInt32 := do
  let picklePath ← picklePath descField
  if (← picklePath.pathExists) && !force then
    IO.eprintln s!"Embeddings already present at {picklePath}, use --force to redownload."
  IO.eprintln "Fetching embeddings ..."
  IO.eprintln s!"https://storage.googleapis.com/leanaide_data/{picklePath.fileName.get!}"
  let out ← runCurl #["--output", picklePath.toString,   s!"https://storage.googleapis.com/leanaide_data/{picklePath.fileName.get!}"]
  IO.eprintln "Fetched embeddings"
  IO.eprintln out
  return 0


unsafe def main (args: List String) : IO UInt32 := do
  let force := args.any (· == "--force")
  for descField in ["docString", "description", "concise-description"] do
    let res ← fetchEmbedding descField force
    if res != 0 then return res
  return 0
