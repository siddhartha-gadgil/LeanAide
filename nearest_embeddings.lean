import Lean
open Lean

-- A dummy function
def nearestDocsToDoc' (doc : String) (k : Nat) : 
  IO (Array (String × String)) := pure #[
    ("/-- Fermat's Last theorem -/", "∀ x y z n : ℕ, n > 2 → x^ + y^n = z^n → x*y*z=0"),
    ("/-- There are infinitely many odd numbers -/", "∀ n : ℕ, ∃ m : ℕ, m > n ∧ Odd m")
  ]

unsafe def main (args : List String) : IO Unit := do
  let [arg] := args | IO.throwServerError "Expected exactly one argument."
  let k := arg.toNat!

  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "Nearest `mathlib` embeddings\n"
  showNearestDocs stdin stdout k

where  
  showNearestDocs (stdin stdout : IO.FS.Stream) (k : Nat) : IO Unit := do
    let doc ← stdin.getLine
    let embs ← nearestDocsToDoc' doc k
    let out : Lean.Json := .arr <| embs.map fun (docstr, thm) ↦ .mkObj [("docstring", docstr), ("theorem", thm)]
    stdout.putStrLn out.compress
    showNearestDocs stdin stdout k