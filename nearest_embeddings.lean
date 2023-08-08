import LeanCodePrompts.Embeddings
import LeanAide.Aides
import Lean.Data.Json
import Mathlib.Util.Pickle
open Lean

-- A dummy function
def nearestDocsToDoc' (data : Array (String × FloatArray)) (doc : String) (k : Nat) : 
  IO (Array (String × String)) := pure #[
    ("/-- Fermat's Last theorem -/", "∀ x y z n : ℕ, n > 2 → x^ + y^n = z^n → x*y*z=0"),
    ("/-- There are infinitely many odd numbers -/", "∀ n : ℕ, ∃ m : ℕ, m > n ∧ Odd m")
  ]

unsafe def main (args : List String) : IO Unit := do
  let [arg] := args | IO.throwServerError "Expected exactly one argument."
  let k := arg.toNat!

  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  unless ← picklePath.pathExists do
    IO.println "Fetching embeddings ..."
    let out ← IO.Process.run {
      cmd := "curl",
      args := #["-O", "https://math.iisc.ac.in/~gadgil/data/mathlib4-thms-embeddings.olean"],
      cwd := "./rawdata/"
    }
    IO.println out

  withUnpickle picklePath <| fun data ↦
    showNearestDocs stdin stdout k data

where
  picklePath : System.FilePath := "./rawdata/mathlib4-thms-embeddings.olean"
  
  showNearestDocs (stdin stdout : IO.FS.Stream) (k : ℕ) (data : Array (String × FloatArray)): IO Unit := do
    let doc ← stdin.getLine
    IO.println s!"Received {doc}"
    let embs ← nearestDocsToDoc' data doc k
    let out : Lean.Json := .arr <| embs.map fun (docstr, thm) ↦ .mkObj [("docstring", docstr), ("theorem", thm)]
    stdout.putStrLn out.compress
    showNearestDocs stdin stdout k data