import Lean
import Plausible

open Lean Meta Elab Tactic Plausible

def Plausible.Testable.checkDirect (p : Prop) [Testable p] (cfg : Configuration := {})(defaultSeed : Nat) : TestResult p :=
  let seed := cfg.randomSeed.getD defaultSeed
  let suite : RandT Id (TestResult p) := Testable.runSuite p cfg
  let res := runRandWith seed suite
  res.run


def getProof? (p e: Expr) : MetaM <| Option Expr := do
  let n ← mkFreshExprMVar <| mkConst ``Nat
  let s ← mkFreshExprMVar <| ← mkAppM ``List #[mkConst ``String]
  let np ← mkAppM ``Not #[p]
  let contra ← mkFreshExprMVar np
  let fExpr ← mkAppOptM ``TestResult.failure #[p, contra, s, n]
  if ← isDefEq e fExpr then
    return some contra
  else
    return none

def findDisproof? (p: Expr) : MetaM <| Option Expr := do
  try
    unless ← isProp p do
      return none
    let p' ← Decorations.addDecorations p
    let inst ← synthInstance (← mkAppM ``Testable #[p'])
    let cfg : Configuration := {}
    let cfg : Configuration := {cfg with
    traceDiscarded := cfg.traceDiscarded || (← isTracingEnabledFor `plausible.discarded),
    traceSuccesses := cfg.traceSuccesses || (← isTracingEnabledFor `plausible.success),
    traceShrink := cfg.traceShrink || (← isTracingEnabledFor `plausible.shrink.steps),
    traceShrinkCandidates := cfg.traceShrinkCandidates
      || (← isTracingEnabledFor `plausible.shrink.candidates) }
    let defaultSeed ← IO.rand 0 1000000
    let testResult ← mkAppOptM ``Testable.checkDirect #[p, inst, toExpr cfg, toExpr defaultSeed]
    let testResult ← reduce testResult -- crashes
    getProof? p testResult
  catch e =>
    logWarning m!"Failed to find disproof: {e.toMessageData}"
    return none

def proveVacuous? (p: Expr) : MetaM <| Option Expr := do
  match p with
  | .forallE n d b bi =>
    withLocalDecl n bi d fun x => do
      let b := b.instantiate1 x
      let contra? ← findDisproof? d -- proof of ¬d
      match contra? with
      | some contra =>
        let pfFalse ← mkAppM' contra #[x]
        let pfBody ← mkAppOptM ``False.elim #[b, pfFalse]
        mkLambdaFVars #[x] pfBody
      | none =>
        return none
  | _ =>
    return none

elab "find_disproof" type:term : term => do
  let p ← Term.elabType type
  -- logInfo m!"Finding disproof of {p}"
  let disproof ← findDisproof? p
  match disproof with
  | some contra =>
    -- logInfo m!"Found disproof: {contra}"
    return contra
  | none =>
    logWarning m!"No disproof found"
    return mkConst ``False

#check find_disproof ((2 : Nat) < 1)

elab "prove_vacuous" type:term : term => do
  let p ← Term.elabType type
  let vacuous ← proveVacuous? p
  match vacuous with
  | some pf =>
    return pf
  | none =>
    logWarning m!"No vacuous proof found"
    return mkConst ``False

/-
fun a => False.elim (Nat.not_le_of_not_ble_eq_true (fun h => Bool.noConfusion h) a) : 2 < 1 → 1 ≤ 3
-/
#check prove_vacuous ((2 : Nat) < 1) → 1 ≤ 3

-- #check find_disproof (∀ n: Nat, n < (4: Nat))
