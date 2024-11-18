import Lean
import Plausible
import Plausible.Testable
import Plausible.Attr
import Plausible.Tactic

open Lean Meta Elab Tactic Plausible

/-- Run a test suite for `p` in `BaseIO` using the global RNG in `stdGenRef`. -/
def Plausible.Testable.checkDirect (p : Prop) [Testable p] (cfg : Configuration := {})(defaultSeed : Nat) : TestResult p :=
  let seed := cfg.randomSeed.getD defaultSeed
  let suite : RandT Id (TestResult p) := Testable.runSuite p cfg
  let res := runRandWith seed suite
  res.run


def getProof? (p e: Expr) : MetaM <| Option Expr := do
  let p ← instantiateMVars p
  let n ← mkFreshExprMVar <| mkConst ``Nat
  let s ← mkFreshExprMVar <| ← mkAppM ``List #[mkConst ``String]
  let np ← mkAppM ``Not #[p]
  let contra ← mkFreshExprMVar np
  let fExpr ← mkAppOptM ``TestResult.failure #[p, contra, s, n]
  if ← isDefEq e fExpr then
    return some contra
  else
    return none

#check Plausible.TestResult.failure

def findDisproof (p: Expr) : MetaM <| Option Expr := do
  try
    let inst ← synthInstance (← mkAppM ``Testable #[p])
    -- logInfo m!"Found instance"
    let cfg : Configuration := {}
    let cfg : Configuration := {cfg with
    traceDiscarded := cfg.traceDiscarded || (← isTracingEnabledFor `plausible.discarded),
    traceSuccesses := cfg.traceSuccesses || (← isTracingEnabledFor `plausible.success),
    traceShrink := cfg.traceShrink || (← isTracingEnabledFor `plausible.shrink.steps),
    traceShrinkCandidates := cfg.traceShrinkCandidates
      || (← isTracingEnabledFor `plausible.shrink.candidates) }
    let defaultSeed ← IO.rand 0 1000000
    let testResult ← mkAppOptM ``Testable.checkDirect #[p, inst, toExpr cfg, toExpr defaultSeed]
    let testResult ← reduce testResult
    getProof? p testResult
  catch _ =>
    return none

elab "find_disproof" type:term : term => do
  let p ← Term.elabType type
  -- logInfo m!"Finding disproof of {p}"
  let disproof ← findDisproof p
  match disproof with
  | some contra =>
    -- logInfo m!"Found disproof: {contra}"
    return contra
  | none =>
    logWarning m!"No disproof found"
    return mkConst ``False

#check find_disproof ((2 : Nat) < 3)
