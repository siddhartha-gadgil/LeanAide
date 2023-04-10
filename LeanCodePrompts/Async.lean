import Lean
open Lean Meta Elab Term Tactic

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

def GoalKey.get : TacticM GoalKey := do
  let lctx ← getLCtx
  let goal ← getMainTarget
  pure { goal := goal, lctx := lctx.decls.toList }

initialize tacticCache : IO.Ref (HashMap GoalKey Tactic.Snapshot) 
        ← IO.mkRef <| HashMap.empty

def putTactic (key : GoalKey) (s : Tactic.Snapshot) : TacticM Unit := do
  tacticCache.modify fun m => m.insert key s

def getSnap (key : GoalKey) : TacticM (Option Tactic.Snapshot) := do  
  let m ← tacticCache.get
  return m.find? key

def runAndCache (tacticCode : Syntax) : TacticM Unit := 
  withMainContext do
  let s₀ : Snapshot := {
      stx    := tacticCode
      core   := (← getThe Core.State)
      meta   := (← getThe Meta.State)
      term   := (← getThe Term.State)
      tactic := (← get)
    }
  try
    let key ← GoalKey.get     
    evalTactic tacticCode
    let s : Snapshot := {
      stx    := tacticCode
      core   := (← getThe Core.State)
      meta   := (← getThe Meta.State)
      term   := (← getThe Term.State)
      tactic := (← get)
    }     
    putTactic key s
    logInfo m!"Stored tactic result for {repr key}"
  catch ex =>
    logError ex.toMessageData
    logError m!"Error while running tactic {repr tacticCode}, {ex.toMessageData}"
  set s₀.core
  set s₀.meta
  set s₀.term
  set s₀.tactic

syntax (name := launchTactic) "launch" tacticSeq : tactic

@[tactic launchTactic] def elabLaunchTactic : Tactic := fun stx => 
  withMainContext do
  match stx with
  | `(tactic| launch $tacticCode) => do
    runAndCache tacticCode
  | _ => throwUnsupportedSyntax

elab "fetch" : tactic => do
  let key ← GoalKey.get
  let goal ← getMainGoal
  match (← getSnap key) with
  | none => throwTacticEx `fetch goal  m!"No cached result found for this goal; key : {repr key}."
  | some s => do
    set s.core
    set s.meta
    set s.term
    set s.tactic

example : 1 = 1 := by checkpoint rfl