import Lean
import LeanCodePrompts.Utils
open Lean Meta Elab Term Tactic Core

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

deriving instance BEq for LocalDecl
deriving instance Hashable for LocalDecl
deriving instance Repr for LocalDecl


structure GoalKey where
  goal : Expr
  lctx : List <| Option LocalDecl
deriving BEq, Hashable, Repr

structure ProofState where
  core   : Core.State
  meta   : Meta.State
  term   : Option Term.State
  preScript : String
  script: Syntax
  tailPos? : Option String.Pos

def GoalKey.get : TacticM GoalKey := do
  let lctx ← getLCtx
  let goal ← getMainTarget
  pure { goal := goal, lctx := lctx.decls.toList }

initialize tacticCache : IO.Ref (HashMap GoalKey ProofState) 
        ← IO.mkRef <| HashMap.empty

initialize tacticPosCache : IO.Ref (HashMap CacheKey ProofState) 
        ← IO.mkRef <| HashMap.empty

def putTactic (key : GoalKey) (s : ProofState) : MetaM Unit := do
  tacticCache.modify fun m => m.insert key s

def putPosTactic (key : CacheKey) (s : ProofState) : MetaM Unit := do
  tacticPosCache.modify fun m => m.insert key s


def getStates (key : GoalKey) : TacticM (Option ProofState) := do  
  let m ← tacticCache.get
  return m.find? key

/- Abstracted to possibly replace by Aesop search -/
def runTacticCode (goal: MVarId) (tacticCode : Syntax)  : 
  MetaM <| (Option Term.State) × Syntax := do
    let (goals, ts) ← runTactic  goal tacticCode 
    unless goals.isEmpty do
        throwError m!"Tactic not finishing, remaining goals:\n{goals}"
    pure (some ts, tacticCode)

def runAndCacheM (tacticCode : Syntax) (goal: MVarId) (target : Expr) (pos? tailPos? : Option String.Pos)(preScript: String) : MetaM Unit := 
  goal.withContext do 
    let lctx ← getLCtx
    let key : GoalKey := { goal := target, lctx := lctx.decls.toList }
    let core₀ ← getThe Core.State
    let meta₀ ← getThe Meta.State
    try
      let (ts, script) ← runTacticCode  goal tacticCode 
      let s : ProofState := {
      core   := (← getThe Core.State)
      meta   := (← getThe Meta.State)
      term   := ts
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

def runAndCacheIO (tacticCode : Syntax) (goal: MVarId) (target : Expr) (pos? tailPos?: Option String.Pos)(preScript: String) 
  (mctx : Meta.Context) (ms : Meta.State) 
  (cctx : Core.Context) (cs: Core.State) : IO Unit :=
  let eio := 
  (runAndCacheM tacticCode goal target pos? tailPos? preScript).run' mctx ms |>.run' cctx cs
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
    -- runAndCache tacticCode
    let mctx ← readThe Meta.Context
    let ms ← getThe Meta.State 
    let cctx ← readThe Core.Context
    let cs ← getThe Core.State 
    -- runAndCacheM tacticCode (← getMainGoal) (← getMainTarget) tk
    let ioSeek := runAndCacheIO 
      tacticCode (← getMainGoal) (← getMainTarget) 
              stx.getPos? stx.getTailPos? stx.reprint.get!  mctx ms cctx cs
    let _ ← ioSeek.asTask
    set ts
    s.restore
  | _ => throwUnsupportedSyntax

syntax (name := bgTactic) "bg" tacticSeq : tactic

@[tactic bgTactic] def elabBgTactic : Tactic := fun stx => 
  withMainContext do
  focus do
  match stx with
  | `(tactic| bg $tacticCode) => do
    let s ← saveState
    let ts ← getThe Term.State
    -- runAndCache tacticCode
    let mctx ← readThe Meta.Context
    let ms ← getThe Meta.State 
    let cctx ← readThe Core.Context
    let cs ← getThe Core.State 
    -- runAndCacheM tacticCode (← getMainGoal) (← getMainTarget) tk
    let ioSeek := runAndCacheIO 
      tacticCode (← getMainGoal) (← getMainTarget) 
              stx.getPos? stx.getTailPos? stx.reprint.get!  mctx ms cctx cs
    let _ ← ioSeek.asTask
    set ts
    s.restore
    let goal ← getMainGoal
    let s ←  mkSyntheticSorry (← getMainTarget)
    goal.assign s 
  | _ => throwUnsupportedSyntax

elab "fetch_proof" : tactic => 
  focus do
  let key ← GoalKey.get
  let goal ← getMainGoal
  match (← getStates key) with
  | none => throwTacticEx `fetch goal  m!"No cached result found for the goal : {← ppExpr <| key.goal }."
  | some s => do
    set s.core
    set s.meta
    match s.term with
    | none => pure ()
    | some ts =>
      set ts 
    setGoals []
    logInfo m!"Try this: {indentD s.script}"

example : 1 = 1 := by checkpoint rfl
