import LeanAide.AesopSearch
import LeanAide.Aides
import LeanAide.TheoremElab
import LeanAide.RunAsync
import Lean
import Mathlib
open Lean Meta Elab Parser Tactic

def powerTactics := #["gcongr", "ring", "linarith", "norm_num", "positivity", "polyrith"]

def errLog := IO.FS.Handle.mk (System.mkFilePath ["data",
    s!"elab-errors.log"]) IO.FS.Mode.append

-- should eventually use premises
def proofSearchM (thm: String) : TermElabM <| Bool × Bool := 
  withoutModifyingState do
  let type? ← elabThm thm 
  let errs ← errLog 
  -- IO.println "Trying to prove"
  -- IO.println thm
  -- IO.println type?
  -- IO.println ""
  match type? with
  | Except.ok type => 
    let goal ← mkFreshExprMVar type
    let mvarId := goal.mvarId! 
    try 
      let goals ←
        runAesop 0.5 #[] #[] #[] powerTactics mvarId
      let proved := goals.isEmpty
      -- let stx ← `(tacticSeq|aesop?) 
      -- if proved then
      --   let (pfScript, _) ← getMsgTacticD stx 
      --   IO.println s!"Proof:"
      --   let tacs := getTactics pfScript  
      --   for tac in tacs do
      --     let fmt ← PrettyPrinter.formatTactic tac 
      --     IO.println fmt.pretty
      -- else
      --   IO.println "Failed"
      return (true, proved)
    catch _ =>
      return (true, false)
  | Except.error err =>
    errs.putStrLn thm 
    errs.putStrLn err
    errs.putStrLn ""
    return (false, false)

def batchProofSearchM (thms: Array String) : TermElabM <| Array <| String × Bool × Bool := 
  thms.mapM fun thm => do
    let pair ← proofSearchM thm
    let (elaborated, proved) := pair
    return (thm, elaborated, proved)

def proofSearchCore (thm: String) : CoreM <| Bool × Bool  := 
  (proofSearchM thm).run'.run'

def batchProofSearchCore (thms: Array String) : CoreM <| Array <| String × Bool × Bool := 
  (batchProofSearchM thms).run'.run'