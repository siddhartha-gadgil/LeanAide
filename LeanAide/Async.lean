import Lean
import LeanAide.Aides
import Std.Tactic.TryThis
import Aesop

open Lean Meta Elab Term Tactic Core Parser Tactic
open Std.Tactic

/-!
A cleaner version is in `RunAsync`.

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

deriving instance BEq, Hashable, Repr for LocalDecl

structure GoalKey where
  goal : Expr
  lctx : List <| Option LocalDecl
deriving BEq, Hashable, Repr

structure ProofState where
  core   : Core.State
  meta   : Meta.State
  term?  : Option Term.State
  preScript : Option String
  script : TSyntax ``tacticSeq
  tailPos? : Option String.Pos

def GoalKey.get : TacticM GoalKey := do
  let lctx ← getLCtx
  let goal ← getMainTarget
  pure { goal := goal, lctx := lctx.decls.toList }

section Caches

initialize tacticCache : IO.Ref (HashMap GoalKey ProofState)
        ← IO.mkRef ∅

initialize tacticPosCache : IO.Ref (HashMap CacheKey ProofState)
        ← IO.mkRef ∅

initialize spawnedKeys :
  IO.Ref (HashSet <| GoalKey × Option String.Pos × Option String.Pos)
        ← IO.mkRef  ∅

def isSpawned (key : GoalKey) (pos? tailPos? : Option String.Pos) : IO Bool := do
  let m ← spawnedKeys.get
  return m.contains (key, pos?, tailPos?)

def markSpawned (key : GoalKey) (pos? tailPos? : Option String.Pos) : IO Unit := do
  spawnedKeys.modify fun m => m.insert (key, pos?, tailPos?)

def putTactic (key : GoalKey) (s : ProofState) : MetaM Unit := do
  tacticCache.modify fun m => m.insert key s

def putPosTactic (key : CacheKey) (s : ProofState) : MetaM Unit := do
  tacticPosCache.modify fun m => m.insert key s


def getStates (key : GoalKey) : TacticM (Option ProofState) := do
  let m ← tacticCache.get
  return m.find? key

end Caches

abbrev PolyTacticM :=  MVarId →
  (MetaM <| (Option Term.State) × TSyntax ``tacticSeq)

/- Abstracted to possibly replace by Aesop search -/
def runTacticCode (tacticCode : TSyntax ``tacticSeq)  : PolyTacticM := fun goal ↦
  withoutModifyingState do
    let (goals, ts) ← runTactic goal tacticCode
    unless goals.isEmpty do
        throwError m!"Tactic not finishing, remaining goals:\n{goals}"
    pure (some ts, tacticCode)


def getMsgTacticD (default : TSyntax ``tacticSeq)  : CoreM <| TSyntax ``tacticSeq := do
  let msgLog ← Core.getMessageLog
  let msgs := msgLog.toList
  let mut tac : TSyntax ``tacticSeq := default
  for msg in msgs do
    let msg := msg.data
    let msg ← msg.toString
    match msg.dropPrefix? "Try this: " with
    | none =>
      pure ()
    | some msg => do
      let parsedMessage :=
        parseAsTacticSeq (←getEnv) msg.toString
      match parsedMessage with
      | Except.ok tac' =>
        resetMessageLog
        tac:=  tac'
      | _ =>
        logInfo m!"failed to parse tactic ({msg.toString})"
        pure ()
  return tac

def runTacticCodeMsg (tacticCode : TSyntax ``tacticSeq)  : PolyTacticM :=
  fun goal ↦ do
    -- let mut msgs ←
    --   modifyGetThe Core.State fun st => (st.messages, { st with messages := {} })
    let (goals, ts) ← runTactic  goal tacticCode
    unless goals.isEmpty do
        -- msgs := msgs ++ (← getThe Core.State).messages
        -- modifyThe Core.State fun st => { st with messages := msgs }
        throwError m!"Tactic not finishing, remaining goals:\n{goals}"
    let code ← getMsgTacticD tacticCode
    pure (some ts, code)

def PolyTacticM.ofTactic (tacticCode : TSyntax ``tacticSeq) : PolyTacticM := runTacticCodeMsg tacticCode


def runAndCacheM (polyTac : PolyTacticM) (goal: MVarId) (target : Expr) (pos? tailPos? : Option String.Pos)(preScript: Option String) : MetaM Unit :=
  goal.withContext do
    let lctx ← getLCtx
    let key : GoalKey := { goal := target, lctx := lctx.decls.toList }
    if ←isSpawned key pos? tailPos? then
      return ()
    markSpawned key pos? tailPos?
    let core₀ ← getThe Core.State
    let meta₀ ← getThe Meta.State
    try
      let (ts?, script) ← polyTac goal
      let s : ProofState := {
      core   := (← getThe Core.State)
      meta   := (← getThe Meta.State)
      term?   := ts?
      preScript := preScript
      script := script
      tailPos? := tailPos?
      }
      putTactic key s
      match pos? with
      | none => pure ()
      | some pos =>
        let ckey : CacheKey := { pos := pos, mvarId := goal}
        putPosTactic ckey s
    catch _ =>
    set core₀
    set meta₀

-- #check MetaM.run'

def runAndCacheIO (polyTac : PolyTacticM) (goal: MVarId) (target : Expr) (pos? tailPos?: Option String.Pos)(preScript: Option String)
  (mctx : Meta.Context) (ms : Meta.State)
  (cctx : Core.Context) (cs: Core.State) : IO Unit :=
  let eio :=
  (runAndCacheM polyTac goal target pos? tailPos? preScript).run' mctx ms |>.run' cctx cs
  let res := eio.runToIO'
  res

syntax (name := launchTactic) "launch" tacticSeq : tactic

@[tactic launchTactic] def elabLaunchTactic : Tactic := fun stx =>
  withMainContext do
  focus do
  match stx with
  | `(tactic| launch $tacticCode) => do
    let s ← saveState
    let ts ← getThe Term.State
    let stx' := stx.copyHeadTailInfoFrom .missing
    let ioSeek := runAndCacheIO
      (PolyTacticM.ofTactic tacticCode)  (← getMainGoal) (← getMainTarget)
              stx.getPos? stx.getTailPos?
              (some <| stx'.reprint.get! |>.replace "  " " ")
              (← readThe Meta.Context) (← getThe Meta.State )
              (← readThe Core.Context) (← getThe Core.State)
    let _ ← ioSeek.asTask
    set ts
    s.restore
  | _ => throwUnsupportedSyntax

syntax (name := bgTactic) "bg" tacticSeq : tactic

@[tactic bgTactic] def elabBgTactic : Tactic := fun stx =>
  withMainContext do
  focus do
  match stx with
  | stx@`(tactic| bg $tacticCode) => do
    let s ← saveState
    let ts ← getThe Term.State
    let stx' := stx.copyHeadTailInfoFrom .missing
    let ioSeek : IO Unit := runAndCacheIO
      (PolyTacticM.ofTactic tacticCode)  (← getMainGoal) (← getMainTarget)
              stx.getPos? stx.getTailPos?
              (some <| stx'.reprint.get! |>.replace "  " " ")
              (← readThe Meta.Context) (← getThe Meta.State )
              (← readThe Core.Context) (← getThe Core.State)
    let _ ← ioSeek.asTask
    set ts
    s.restore
    admitGoal <| ← getMainGoal
  | _ => throwUnsupportedSyntax

def fetchProof  : TacticM (TSyntax `Lean.Parser.Tactic.tacticSeq) :=
  focus do
  let key ← GoalKey.get
  let goal ← getMainGoal
  match (← getStates key) with
  | none => throwTacticEx `fetch goal  m!"No cached result found for the goal : {← ppExpr <| key.goal }."
  | some s => do
    set s.core
    set s.meta
    match s.term? with
    | none => pure ()
    | some ts =>
      set ts
    setGoals []
    return s.script

elab "fetch_proof" : tactic => do
  discard fetchProof

-- macro "auto?" : tactic => do
--   `(tactic|aesop?)

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
  autoStartImplAux (stx: Syntax)
  (autoCode : TSyntax `Lean.Parser.Tactic.tacticSeq)
  (tacticCode : TSyntax ``tacticSeq)(fromBy: Bool) : TacticM Unit :=
  withMainContext do
    let allTacs := getTactics tacticCode
    let mut cumTacs :  Array (TSyntax `tactic) := #[]
    for tacticCode in allTacs do
      cumTacs := cumTacs.push tacticCode
      try
        let script ← fetchProof
        logWarningAt tacticCode m!"proof complete before: {tacticCode}"
        let allTacs ←  appendTactics' cumTacs script
        if fromBy then
           TryThis.addSuggestion stx (← `(by $allTacs))
        else
           TryThis.addSuggestion stx allTacs
      catch _ =>
        if (← getUnsolvedGoals).isEmpty then
          return ()
      evalTactic tacticCode
      if (← getUnsolvedGoals).isEmpty then
        logInfoAt tacticCode m!"Goals accomplished!! 🎉"
        return ()
      let ioSeek : IO Unit := runAndCacheIO
        (PolyTacticM.ofTactic autoCode)  (← getMainGoal) (← getMainTarget)
                none none none
                (← readThe Meta.Context) (← getThe Meta.State )
                (← readThe Core.Context) (← getThe Core.State)
      let _ ← ioSeek.asTask
      try
        dbgSleep 50 fun _ => do
          let script ← fetchProof
          let allTacs ←  appendTactics' cumTacs script
          if fromBy then
            TryThis.addSuggestion stx (← `(by $allTacs))
          else
            TryThis.addSuggestion stx allTacs
      catch _ =>
        pure ()
  autoStartImplAux' (stx: Syntax)
    (autoCode : TSyntax `Lean.Parser.Tactic.tacticSeq)(fromBy: Bool) : TacticM Unit :=
    withMainContext do
    -- let tacticCode ← `(tactic|auto?)
    if (← getUnsolvedGoals).isEmpty then
        logInfoAt stx m!"Goals accomplished!! 🎉"
        return ()
    let ioSeek : IO Unit := runAndCacheIO
      (PolyTacticM.ofTactic autoCode)  (← getMainGoal) (← getMainTarget)
              none none none
              (← readThe Meta.Context) (← getThe Meta.State )
              (← readThe Core.Context) (← getThe Core.State)
    let _ ← ioSeek.asTask
    try
      dbgSleep 50 fun _ => do
        let script ← fetchProof
        if fromBy then
          TryThis.addSuggestion stx (← `(by $script))
        else
          TryThis.addSuggestion stx script
    catch _ =>
      pure ()
    if (← getUnsolvedGoals).isEmpty then
        return ()


elab "check_auto" : tactic => withMainContext do
  if (← getUnsolvedGoals).isEmpty then
        logInfo m!"No more goals to solve"
        return ()
  let lctx ← getLCtx
  let target ← getMainTarget
  let key : GoalKey := { goal := target, lctx := lctx.decls.toList }
  logInfo m!"Checking for cached result for the goal : {← ppExpr <| key.goal }"
  let cache : HashMap GoalKey ProofState ← tacticCache.get
  logInfo m!"Cache size : {cache.size}"
  logInfo m!"Cache keys"
  for (k, _) in cache.toList do
    logInfo m!"{← ppExpr k.goal}"

namespace leanaide.auto

scoped macro (priority := high) "by" tacs?:(tacticSeq)? : term =>
  match tacs? with
  | none => `(by aided_by from_by aesop? do)
  | some tacs => `(by aided_by from_by aesop? do $tacs)

end leanaide.auto
