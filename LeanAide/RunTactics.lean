import Lean
import LeanAide.Aides
import LeanAide.SimpleFrontend

open Lean Meta Elab Term PrettyPrinter

namespace LeanAide

open Parser.Tactic
-- TODO: add errors and warnings
def runForSingleGoal (mvarId : MVarId) (tacticCode : TSyntax ``tacticSeq) : TermElabM <| Option MVarId :=
    mvarId.withContext do
  -- let tacticCode ← `(tacticSeq| skip)
  let s₀ ← saveState
  try
    let ctx ← read
    let (mvars, s) ←
      withoutErrToSorry do
      Elab.runTactic mvarId tacticCode {ctx with mayPostpone := false, errToSorry := false, declName? := some `_tacticCode}
        {}  (s:= ← get)
    match mvars with
    | [] =>
      set s
      return none
    | [mvar] =>
      set s
      return mvar
    | _ =>
      s₀.restore
      return none
  catch e =>
    IO.eprintln s!"Tactics failed on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {← e.toMessageData.toString}"
    IO.eprintln s!"Tactic code: \n{← ppCategory ``tacticSeq tacticCode}"
    IO.eprintln s!"Tactics:"
    let tacs := getTactics tacticCode
    for tac in tacs do
      IO.eprintln s!"{← ppTactic tac}"
      IO.eprintln ""
    IO.eprintln s!"Assignment: {← mvarId.isAssigned}; {← PrettyPrinter.ppExpr <| mkMVar mvarId} "
    s₀.restore
    return mvarId

-- Actually not useful, need to integrate with `getCode`.
def runTacticSeqList (mvarId : MVarId) (tacticCodeList : List <| TSyntax ``tacticSeq) : TermElabM <| Option MVarId :=
    mvarId.withContext do
  match tacticCodeList with
  | [] =>
    return none
  | head :: tail =>
    let mvar ← runForSingleGoal mvarId head
    match mvar with
    | none =>
      return none
    | some mvarId' =>
      runTacticSeqList mvarId' tail

def runAndGetMVars (mvarId : MVarId) (tacs : Array Syntax.Tactic)
    (n: Nat)(allowClosure: Bool := false):TermElabM <| List MVarId :=
    mvarId.withContext do
  let tacticCode ← `(tacticSeq| $tacs*)
  -- let tacticCode ← `(tacticSeq| skip)
  try
    let ctx ← read
    let (mvars, s) ←
      withoutErrToSorry do
      Elab.runTactic mvarId tacticCode {ctx with mayPostpone := false, errToSorry := false, declName? := some `_tacticCode}
        {}  (s:= ← get)
    if allowClosure && mvars.isEmpty then
      set s
      IO.eprintln s!"Tactics returned no goals on {← PrettyPrinter.ppExpr <| ← mvarId.getType}"
      IO.eprintln s!"Assignment: {← mvarId.isAssigned}; {← PrettyPrinter.ppExpr <| mkMVar mvarId} "
      for tac in tacs do
        IO.eprintln s!"Tactic: {← ppTactic tac}"
      return mvars
    unless mvars.length == n do
      IO.eprintln s!"Tactics returned wrong number of goals on {← mvarId.getType}: {mvars.length} instead of {n}"
      for tac in tacs do
        IO.eprintln s!"Tactic: {← ppTactic tac}"
      return List.replicate n mvarId
    set s
    -- IO.eprintln s!"Tactics succeeded on {← PrettyPrinter.ppExpr <| ← mvarId.getType}"
    return mvars
  catch e =>
    IO.eprintln s!"Tactics failed on {← PrettyPrinter.ppExpr <| ← mvarId.getType}: {← e.toMessageData.toString}"
    IO.eprintln s!"Tactic code: {← ppCategory ``tacticSeq tacticCode}"
    for tac in tacs do
      IO.eprintln s!"Tactic: {← ppTactic tac}"
    return List.replicate n mvarId

def runTacticsAndGetMessages (mvarId : MVarId) (tactics : Array Syntax.Tactic): TermElabM <| MessageLog  :=
    mvarId.withContext do
  -- IO.eprintln s!"Running tactics on {← PrettyPrinter.ppExpr <| ← mvarId.getType} to get messages in context:"
  let lctx ← getLCtx
  let mut vars : Array Syntax.Term := #[]
  for decl in lctx do
    unless decl.isImplementationDetail || decl.isLet do
      let name := decl.userName
      let term ← if !name.isInternal then
        let id := mkIdent name
        `($id)
      else
        `(_)
      vars := vars.push term
    -- IO.eprintln s!"Declaration: {decl.userName} (internal: {decl.userName.isInternal}) : {← PrettyPrinter.ppExpr decl.type}"
  -- vars := vars[1:]
  let targetType ← relLCtx' mvarId
  let typeView ← PrettyPrinter.ppExpr targetType
  logInfo m!"Target type: {typeView}"
  let introTac ← `(tactic| intro $vars*)
  let tactics := if vars.isEmpty then tactics else  #[introTac] ++ tactics
  let tacticCode ← `(tacticSeq| $tactics*)
  let termView ← PrettyPrinter.ppTerm <| ← `(by $tacticCode)
  logInfo m!"Tactic proof: {termView}"
  let egCode := s!"example : {typeView} := {termView}"
  -- let code := topCode ++ egCode
  let (_, msgs') ← runFrontendM egCode
  -- IO.eprintln s!"Ran frontend, Messages:"
  -- for msg in msgs'.toList do
  --   IO.eprintln s!"{← msg.data.toString}"
  return msgs'

def getTacticsFromMessage? (msg: Message) :
    MetaM <| Option (Array Syntax.Tactic) := do
  let s ← msg.data.toString
  let s := s.trim
  if s.startsWith "Try this:" then
    let s' := s.drop 10 |>.trim
    match Parser.runParserCategory (← getEnv) `term ("by\n  " ++ s') with
    | Except.ok term => do
      match term with
      | `(by $[$t]*) =>
        -- IO.eprintln "Parsed tactics:"
        return t
      | _ =>
        IO.eprintln s!"Message: {s} starts with Try this:, but failed to parse {"by\n  " ++ s'} as a tactic sequence"
        return none
    | Except.error e => do
      IO.eprintln s!"Message: {s} starts with Try this:, but failed to parse {s'} with error {e}"
      return none
  else
    -- IO.eprintln s!"Message: {s} does not start with Try this:"
    return none

def runTacticsAndGetTryThis? (goal : Expr) (tactics : Array Syntax.Tactic): TermElabM <| Option (Array Syntax.Tactic) :=
    withoutModifyingState do
  let mvar ← mkFreshExprMVar goal
  let msgs ←
    runTacticsAndGetMessages mvar.mvarId! tactics
  -- IO.eprintln "Messages:"
  -- for msg in msgs.toList do
  --   IO.eprintln s!"Message: {← msg.data.toString}"
  msgs.toList.findSomeM?
    fun msg => getTacticsFromMessage? msg

def getExactTactics? (goal: Expr) : TermElabM <| Option (TSyntax ``tacticSeq) := do
  let tactics? ← runTacticsAndGetTryThis? goal #[(← `(tactic| exact?))]
  match tactics? with
  | none => return none
  | some tacs =>
    if tacs.isEmpty then
      return none
    else
      let tacticCode ←  `(tacticSeq| $tacs*)
      return some tacticCode

elab "#exact? " goal:term : command => Command.liftTermElabM do
  let goal ← elabTerm goal none
  let tacticCode? ← getExactTactics? goal
  match tacticCode? with
  | none => logWarning "exact? tactic failed to find any tactics"
  | some tacticCode =>
    logInfo m!"exact? tactic found tactics: {← ppCategory ``tacticSeq tacticCode}"

-- #exact? ∀ (n m : Nat), n + m = m + n

open PrettyPrinter
def runTacticsAndGetTryThisI (goal : Expr) (tactics : Array Syntax.Tactic): TermElabM <|  (Array Syntax.Tactic) := do
  let tacs? ← runTacticsAndGetTryThis? goal tactics
  -- IO.eprintln s!"Tactics for goal: {← PrettyPrinter.ppExpr goal}"
  -- if let some tacs := tacs? then
  --   let view ← ppCategory ``tacticSeq <| ← `(tacticSeq|$tacs*)
  --   IO.eprintln s!"Tactics:\n {view}"
  -- else
  --   IO.eprintln "No tactics found"
  return tacs?.getD #[(←  `(tactic| sorry))]

def extractIntros (goal: MVarId) (maxDepth : Nat) (accum: List Name := []) :
    MetaM <| MVarId × List Name := do
  match maxDepth, ← goal.getType with
  | 0, _ =>
    return (goal, accum)
  | k + 1, Expr.forallE n _ _ _ => do
    let n := if n.isInternal then n.components[0]! else n
    let (_, goal') ← goal.intro n
    extractIntros goal' k (accum ++ [n])
  | _, _ => do
    return (goal, accum)


end LeanAide
