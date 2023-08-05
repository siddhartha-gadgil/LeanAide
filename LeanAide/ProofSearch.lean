import LeanAide.AesopSearch
import LeanAide.Aides
import LeanAide.TheoremElab
import LeanAide.RunAsync
import Lean
import Mathlib
open Lean Meta Elab Parser Tactic Core

def powerTactics := #["gcongr", "ring", "linarith", "norm_num", "positivity"]

def errLog := IO.FS.Handle.mk (System.mkFilePath ["data",
    s!"elab-errors.log"]) IO.FS.Mode.append

def getMsgTactic?  : CoreM <| Option <| (TSyntax ``tacticSeq) × Format := do
  let msgLog ← Core.getMessageLog  
  let msgs := msgLog.toList
  let mut tac? : Option <| TSyntax ``tacticSeq := none
  let mut fmt? : Option Format := none
  for msg in msgs do
    let msg := msg.data
    let msg' := (← msg.format).pretty 
    match msg'.dropPrefix? "Try this:" with
    | none => 
      pure ()
    | some msg'' => do
      let parsedMessage := 
        parseAsTacticSeq (←getEnv) msg''.toString
      match parsedMessage with
      | Except.ok tac' => 
        resetMessageLog
        tac?:= some  tac'
        fmt? := some <| ← msg.format
      | _ =>
        logInfo m!"failed to parse tactic ({msg''.toString})"
        pure ()
  return tac?.bind (fun tac => 
    fmt?.map fun fmt => (tac, fmt))

-- should eventually use premises
def proofSearchM (thm: String) : TermElabM <| Bool × Bool := 
  withoutModifyingState do
  let type? ← elabThm thm 
  IO.println s!"Elaborated"
  let errs ← errLog 
  match type? with
  | Except.ok type => 
    let goal ← mkFreshExprMVar type
    let mvarId := goal.mvarId! 
    try 
      let goals ←
        runAesop 0.5 #[] #[] #[] powerTactics mvarId
      let proved := goals.isEmpty
      if proved then
        let pair? ← getMsgTactic?
        match pair? with
        | none => IO.println "could not extract proof"
        | some (pfScript, fmt) =>
          IO.println s!"Proof:"
          IO.println fmt.pretty
          let tacs := getTactics pfScript  
          IO.println s!"Number of tactics: {tacs.size}"
          for tac in tacs do
            let fmt ← PrettyPrinter.ppTactic tac 
            IO.println fmt.pretty
      else
        IO.println "Failed"
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