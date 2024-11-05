import Lean
import LeanAide.Aides
import Lean.Meta.Tactic.TryThis
import Aesop

open Lean Meta Elab Term Tactic Core Parser Tactic
open Lean.Meta.Tactic

/-!
# Asynchronous tactic execution

We provide methods for executing tactics asynchronously. These are modelled on the `checkpoint` tactic.

* We run tactics and store resulting states in a cache.
* We use a more robust key than that for checkpoints.

## Indexing

We index by

* the current goal
* the current local context converted into lists

## Running tactics

We have a function of type `TacticM Unit` which

* executes the tactic
* stores the resulting states in the cache

## Fetching results

* We fetch final states based on the current goal and local context.
* We then restore these states.
-/

register_option aided_by.delay : Nat :=
  { defValue := 50
    group := "aided_by"
    descr := "Time to wait after launching a task." }

def isSorry (tacticCode: TSyntax `tactic) : TermElabM Bool := do
  let goal ← mkFreshExprMVar (mkConst ``False)
  try
    let (goals, _) ← Elab.runTactic  goal.mvarId! tacticCode
    return goals.isEmpty
  catch _ =>
    return false

deriving instance BEq, Hashable, Repr for LocalDecl

structure GoalKey where
  goal : Expr
  lctx : List <| Option LocalDecl
deriving BEq, Hashable, Repr

structure ProofState where
  core   : Core.State
  meta   : Meta.State
  term?  : Option Term.State
  script : TSyntax ``tacticSeq
  messages : List Message

def GoalKey.get : TacticM GoalKey := do
  let lctx ← getLCtx
  let goal ← getMainTarget
  pure { goal := goal, lctx := lctx.decls.toList }

section Caches

initialize tacticCache : IO.Ref (Std.HashMap GoalKey ProofState)
        ← IO.mkRef ∅

initialize spawnedKeys :
  IO.Ref (Std.HashSet <| GoalKey)
        ← IO.mkRef  ∅

def isSpawned (key : GoalKey) : IO Bool := do
  let m ← spawnedKeys.get
  return m.contains key

def markSpawned (key : GoalKey)  : IO Unit := do
  spawnedKeys.modify fun m => m.insert key

def putTactic (key : GoalKey) (s : ProofState) : MetaM Unit := do
  tacticCache.modify fun m => m.insert key s

def getStates (key : GoalKey) : TacticM (Option ProofState) := do
  let m ← tacticCache.get
  return m.get? key

def clearCache : IO Unit := do
  tacticCache.modify fun _ => ∅
  spawnedKeys.modify fun _ => ∅

end Caches

def getMsgTacticD (default : TSyntax ``tacticSeq)  : CoreM <| (TSyntax ``tacticSeq) × (List Message) := do
  let msgLog ← Core.getMessageLog
  let msgs := msgLog.toList
  let mut tac : TSyntax ``tacticSeq := default
  for msg in msgs do
    let msg := msg.data
    let msg ← msg.toString
    match msg.dropPrefix? "Try this:" with
    | none =>
      pure ()
    | some msg => do
      let parsedMessage :=
        parseAsTacticSeq (←getEnv) msg.toString.trimLeft
      match parsedMessage with
      | Except.ok tac' =>
        resetMessageLog
        tac:=  tac'
      | _ =>
        logInfo m!"failed to parse tactic ({msg.toString})"
        pure ()
  return (tac, msgs)



def runAndCacheM (tacticCode : TSyntax ``tacticSeq)
  (goal: MVarId) (target : Expr)  : MetaM Unit :=
  goal.withContext do
    let lctx ← getLCtx
    let key : GoalKey := { goal := target, lctx := lctx.decls.toList }
    if ←isSpawned key then
      return ()
    markSpawned key
    let core₀ ← getThe Core.State
    let meta₀ ← getThe Meta.State
    try
      let (goals, ts) ← runTactic  goal tacticCode
      unless goals.isEmpty do
        throwError m!"Tactic not finishing, remaining goals:\n{goals}"
      let (code, msgs) ← getMsgTacticD tacticCode
      let s : ProofState := {
        core   := (← getThe Core.State)
        meta   := (← getThe Meta.State)
        term?   := some ts
        script := code
        messages := msgs
        }
      putTactic key s
    catch _ =>
    set core₀
    set meta₀

def runAndCacheIO (tacticCode : TSyntax ``tacticSeq) (goal: MVarId) (target : Expr)
  (mctx : Meta.Context) (ms : Meta.State)
  (cctx : Core.Context) (cs: Core.State) : IO Unit :=
  let eio :=
  (runAndCacheM tacticCode goal target).run' mctx ms |>.run' cctx cs
  let res := eio.runToIO'
  res

def fetchProof  : TacticM ProofState :=
  focus do
  let key ← GoalKey.get
  let goal ← getMainGoal
  match (← getStates key) with
  | none => throwTacticEx `fetch goal  m!"No cached result found for the goal : {← ppExpr <| key.goal }."
  | some s => do
    return s


syntax (name := autoTacs) "aided_by" ("from_by")? tacticSeq "do" (tacticSeq)? : tactic

macro "by#" tacs:tacticSeq : term =>
  `(by
  aided_by from_by aesop? do $tacs)

macro "by#"  : term =>
  `(by
  aided_by from_by aesop? do)


@[tactic autoTacs] def autoStartImpl : Tactic := fun stx =>
withMainContext do
match stx with
| `(tactic| aided_by from_by $auto? do $tacticCode) =>
    autoStartImplAux stx auto? tacticCode true
| `(tactic| aided_by $auto? do $tacticCode) =>
    autoStartImplAux stx auto? tacticCode false
| `(tactic| aided_by from_by $auto? do) => do
    autoStartImplAux' stx auto? true
| `(tactic| aided_by $auto? do) => do
    autoStartImplAux' stx auto? false
| _ => throwUnsupportedSyntax
where
  initialSearch (stx: Syntax)
    (autoCode : TSyntax `Lean.Parser.Tactic.tacticSeq)(fromBy: Bool) : TacticM Unit :=
    withMainContext do
    if (← getUnsolvedGoals).isEmpty then
        return ()
    let ioSeek : IO Unit := runAndCacheIO
      autoCode  (← getMainGoal) (← getMainTarget)
              (← readThe Meta.Context) (← getThe Meta.State )
              (← readThe Core.Context) (← getThe Core.State)
    let _ ← ioSeek.asTask
    try
      let delay  := aided_by.delay.get (← getOptions)
      dbgSleep delay.toUInt32 fun _ => do
        let pf ← fetchProof
        let script := pf.script
        if fromBy then
          TryThis.addSuggestion stx (← `(by $script))
        else
          TryThis.addSuggestion stx script
    catch _ =>
      pure ()
  autoStartImplAux (stx: Syntax)
  (autoCode : TSyntax `Lean.Parser.Tactic.tacticSeq)
  (tacticCode : TSyntax ``tacticSeq)(fromBy: Bool) : TacticM Unit :=
  withMainContext do
    initialSearch stx autoCode fromBy
    let allTacs := getTactics tacticCode
    let mut cumTacs :  Array (TSyntax `tactic) := #[]
    for tacticCode in allTacs do
      evalTactic tacticCode
      if ← isSorry tacticCode then
        return ()
      cumTacs := cumTacs.push tacticCode
      if (← getUnsolvedGoals).isEmpty then
        unless tacticCode.raw.reprint.get!.trim.endsWith "sorry" do
          if fromBy then
            TryThis.addSuggestion stx (← `(by $[$cumTacs]*))
          else
            TryThis.addSuggestion stx (← `(tacticSeq|$[$cumTacs]*))
        return ()
      let ioSeek : IO Unit := runAndCacheIO
        autoCode  (← getMainGoal) (← getMainTarget)
                (← readThe Meta.Context) (← getThe Meta.State )
                (← readThe Core.Context) (← getThe Core.State)
      let _ ← ioSeek.asTask
      try
        let delay  := aided_by.delay.get (← getOptions)
        dbgSleep delay.toUInt32 fun _ => do
          let pf ← fetchProof
          let allTacs ←  appendTactics' cumTacs pf.script
          if fromBy then
            TryThis.addSuggestion stx (← `(by $allTacs))
          else
            TryThis.addSuggestion stx allTacs
          return ()
      catch _ =>
        pure ()
  autoStartImplAux' (stx: Syntax)
    (autoCode : TSyntax `Lean.Parser.Tactic.tacticSeq)(fromBy: Bool) : TacticM Unit :=
    withMainContext do
    initialSearch stx autoCode fromBy
    if (← getUnsolvedGoals).isEmpty then
        return ()


namespace leanaide.auto

scoped macro (priority := high) "by" tacs?:(tacticSeq)? : term =>
  match tacs? with
  | none => `(by aided_by from_by aesop? do)
  | some tacs => `(by aided_by from_by aesop? do $tacs)

end leanaide.auto
