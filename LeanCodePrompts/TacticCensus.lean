import LeanCodePrompts.FirstTacticData
import LeanCodePrompts.FirstTacticDataExamples
import Lean
open Lean Meta

def countAndSave (p: String) : MetaM Nat := do
  let mut count := 0
  let files ← leanFiles [p]
  let censusFile := System.mkFilePath ["data", "tactic-census.txt"]
  let h ← IO.FS.Handle.mk censusFile IO.FS.Mode.append
  for f in files do
    let blob : String ←  
      try 
        IO.FS.readFile f
      catch e =>
        logWarning m!"{f} {e.toMessageData}" 
        pure ""
    let blocks ← parseTacticBlocks blob
    for arr in blocks do
      for tac in arr do
        h.putStrLn tac
        count := count + 1
  return count

def mathlib4path := "/home/gadgil/dev/mathlib4"

def mathlib3path := "/home/gadgil/code/mathlib3port"

#eval leanFiles [mathlib4path]

-- #eval countAndSave mathlib3path