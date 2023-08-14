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
def proofSearchM (thm: String)(tacs: Array String := powerTactics) : TermElabM <| Bool × Bool × (Option String) := 
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
        runAesop 0.5 #[] #[] #[] tacs mvarId
      let proved := goals.isEmpty
      let (code: String) ← 
        if proved 
        then
          let pair? ← getMsgTactic?
          match pair? with
          | none => 
            pure "sorry -- could not extract proof"
          | some (pfScript, _) =>
            let pfScript:= 
              (← PrettyPrinter.ppCategory `tacticSeq pfScript).pretty
            pure pfScript
        else 
            pure "sorry"
      IO.println s!"example: {← ppExpr type} := by\n{code}\n\n"
      return (true, proved, some code)
    catch _ =>
      return (true, false, none)
  | Except.error err =>
    errs.putStrLn thm 
    errs.putStrLn err
    errs.putStrLn ""
    return (false, false, none)

def batchProofSearchM (thms: Array String) : TermElabM <| Array <| String × Bool × Bool × (Option String) := 
  thms.mapM fun thm => do
    let pair ← proofSearchM thm
    let (elaborated, proved) := pair
    return (thm, elaborated, proved)

def proofSearchCore (thm: String)(tacs: Array String := powerTactics) : CoreM <| Bool × Bool × (Option String)  := 
  (proofSearchM thm tacs).run'.run'

def batchProofSearchCore (thms: Array String) : CoreM <| Array <| String × Bool × Bool × Option (String) := 
  (batchProofSearchM thms).run'.run'