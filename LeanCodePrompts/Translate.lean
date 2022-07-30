import Lean
import Lean.Meta
import Lean.Parser
import LeanCodePrompts.CheckParse
import LeanCodePrompts.ParseJson

open Lean Elab Parser Command

def egPrompt:= "Every prime number is either `2` or odd."

def egOut := #["{p : ℕ} (hp : Nat.Prime p) :  p = 2 ∨ p % 2 = 1 ",
   "(p : ℕ) :  Nat.Prime p ↔ p = 2 ∨ p % 2 = 1 ",
   "{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 ",
   "(n : ℕ) (hp : Nat.Prime n) : n = 2 ∨ n % 2 = 1 ",
   "{p : ℕ} (hp : Nat.Prime p) : p = 2 ∨ p % 2 = 1 ",
   "Nonsense output to test filtering"]

#check Bool.true

def textToExpr (s: String) : TermElabM Expr := do
  -- logInfo m!"text: {s}"
  let output := egOut
  let elaborated ← output.filterM  <| 
      fun s => do
        let chk ← elabThm s
        return chk.toBool
  logInfo m!"elaborated: {elaborated.size} out of {output.size}"
  if elaborated.isEmpty then do
    logWarning m!"No elaborated output found"
    for out in output do
      logWarning m!"{out}"
    throwError "No valid output from codex"  
  let groupSorted ← groupThms elaborated
  let topStr := groupSorted[0][0]
  let thmExc ← elabThm topStr
  let thm := thmExc.toOption.get!
  return thm

elab "/---" cb:commentBody : term => do
  let s := cb.getAtomVal!
  let s := s.dropRight 2
  let e ← textToExpr s
  logInfo m!"{e}"
  return e

