import Cache.IO
import LeanAide.Aides
open Lean Cache.IO

unsafe def fetchEmbedding (descField : String) (force: Bool) : IO UInt32 := do
  let picklePath ← picklePath descField
  if (← picklePath.pathExists) && !force then
    IO.eprintln s!"Embeddings already present at {picklePath}, use --force to redownload."
  IO.eprintln "Fetching embeddings ..."
  IO.eprintln s!"https://storage.googleapis.com/leanaide_data/{picklePath.fileName.get!}"
  let out ← IO.Process.output {cmd:= "curl", args:=#["--output", picklePath.toString,   s!"https://storage.googleapis.com/leanaide_data/{picklePath.fileName.get!}"]}
  IO.eprintln "Fetched embeddings"
  if out.exitCode != 0 then
    IO.eprintln s!"Failed to fetch embeddings: {out.stderr}"
  else
    IO.eprintln s!"Fetched embeddings: {out.stdout}"
  return out.exitCode


unsafe def main (args: List String) : IO UInt32 := do
  let force := args.any (· == "--force")
  for descField in ["docString", "description", "concise-description"] do
    let res ← fetchEmbedding descField force
    if res != 0 then return res
  return 0
