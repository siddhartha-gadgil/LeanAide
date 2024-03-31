import Lean
import Mathlib

open Lean Meta Elab Term PrettyPrinter Tactic

@[aesop unsafe 10% tactic]
def myRing : TacticM Unit := do
  evalTactic (← `(tactic|ring))

attribute [aesop simp] Real.sin_two_mul

open Real
example : ∀(x: ℝ), (x + sin x + cos (tan x)) * 2 =
  2 * cos (tan x) + 2 * x + sin x + sin x := by
  aesop


example : ∀(x: ℝ), ((x + sin x + cos (tan x)) * 2)/ (x + 1) =
  (2 * cos (tan x) + 2 * x + sin x + sin x)/ (x + 1) := by
  intro x
  ring

example : ∀ x: ℝ, (x + sin (2 * (cos x))) / (tan x + 1) =
  (sin (cos x) * cos (cos x) + x)/(tan x + 1) +
  (cos (cos x) * sin (cos x))/ (tan x + 1) := by
  aesop

#check HasDerivAt

#check deriv -- 0 if the function is not differentiable at x.

-- code of Adam Topaz
def parseFloat (s : String) : Except String Float :=
  match Lean.Json.parse s with
    | .ok (.num t) => .ok t.toFloat
    | _ => throw "Failed to parse as float."

#eval parseFloat "25.123651"

def checkTermType (s: String) (type: Expr) : TermElabM Bool := do
  let termStx := Parser.runParserCategory (← getEnv) `term s
  match termStx with
  | Except.ok termStx =>
    withoutErrToSorry do
      try
        let _ ← elabTermEnsuringType termStx type
        return true
      catch err =>
        logWarning m!"{err.toMessageData}"
        return false
  | Except.error err =>
    logWarning m!"{err}"
    return false

def checkTermNat (s: String) : TermElabM Bool := do
  let type :=  Lean.mkConst `Nat
  checkTermType s type

#eval checkTermNat "3" -- true
#eval checkTermNat "3 + 4" -- true
#eval checkTermNat "3 + 4 + 5" -- true
#eval checkTermNat "3 + 4 + 5 + six" -- false
#eval checkTermNat "Nat" -- false

def diffNat (n: Nat)(m: Nat := n) : Nat :=
  n - m

#eval diffNat 4 3

#eval diffNat 4

opaque P : Prop

axiom p_eq_true : P = True

example  : P := by
  aesop (add unsafe (by rw [p_eq_true]))

example : MetaM Syntax := do
  let stx ← `(rule_expr|(by rw [p_eq_true]))
  let stx' ← `(rule_expr| apply Nat.add)
  `(tactic| aesop (add unsafe [$stx, $stx']))
