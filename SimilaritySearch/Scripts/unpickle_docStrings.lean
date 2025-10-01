-- Unpickles the docStrings at `.lake/build/lib/`
-- Writes it into dir `docStrings`

import Lean
import Batteries.Util.Pickle
import LeanAideCore.Aides

def writeAllEmbedData (filename : String) (content : EmbedData) : IO Unit := do
  let handle ← IO.FS.Handle.mk filename IO.FS.Mode.write
  let arrJs := content.map (fun data : (String × String × Bool × String) × FloatArray =>
    match data with
    | ((doc,thm,isProp,name),_) =>
      Lean.Json.mkObj <| [
        ("docString", Lean.Json.str doc),
        ("type", Lean.Json.str thm),
        ("isProp", Lean.Json.bool isProp),
        ("name", Lean.Json.str name)
      ])
  let jsArr := Lean.Json.arr arrJs
  handle.putStrLn jsArr.compress
  handle.flush
  IO.println s!"Content successfully written to {filename}"

unsafe def readAndWrite (args : List String) : IO Unit := do
  let x ← unpickle (EmbedData) (args.getD 0
    ".lake/build/lib/mathlib4-concise-description-embeddings-v4.22.0.olean")
  writeAllEmbedData (args.getD 1 "TestEmbeddings/unpickled1.txt") (x.1)


--#eval readAndWrite [".lake/build/lib/mathlib4-concise-description-embeddings-v4.22.0.olean", "SimilaritySearch/docStrings/concise_desc_emb.json"]

--#eval readAndWrite [".lake/build/lib/mathlib4-description-embeddings-v4.22.0.olean", "SimilaritySearch/docStrings/desc_emb.json"]

--#eval readAndWrite [".lake/build/lib/mathlib4-prompts-embeddings-v4.22.0.olean", "SimilaritySearch/docStrings/prompt_emb.json"]
