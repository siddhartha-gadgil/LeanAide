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
