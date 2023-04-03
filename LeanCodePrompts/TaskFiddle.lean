import Lean
import LeanCodePrompts.AesopSearch

open Lean Meta Elab Tactic Parser 

#eval 3

def slowFibIO : Nat → IO Nat
| 0 => pure 0
| 1 => pure 1
| n + 2 => do return (← slowFibIO (n)) + (←  slowFibIO (n + 1))   

elab "run_io_task" : tactic => do
  let _  ← (IO.asTask <| 
    do 
      setFib s!"Computed: {← slowFibIO 37} at {← IO.monoMsNow}"
    ).toIO
  return ()

example : 3 = 3 := by
  run_io_task
  rfl

#eval getFib

#check Core.CoreM.run -- {α : Type} → CoreM α → Core.Context → Core.State → EIO Exception (α × Core.State)
#check Meta.MetaM.run /-{α : Type} →
  MetaM α →
    optParam Meta.Context
        {...} →
      optParam Meta.State
          {...} →
        CoreM (α × Meta.State)
-/
#check Elab.runTactic /- MVarId →
  Syntax →
    optParam Term.Context
        {...} →
      optParam Term.State
          { levelNames := [], syntheticMVars := ∅, pendingMVars := ∅, mvarErrorInfos := ∅, letRecsToLift := [] } →
        MetaM (List MVarId × Term.State)-/
#check IO.asTask /- {α : Type} → IO α → optParam Task.Priority Task.Priority.default → BaseIO (Task (Except IO.Error α)) -/
#check evalTactic
