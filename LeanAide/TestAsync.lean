import LeanAide.RunAsync
import Aesop
import Mathlib.Tactic
import Lean.Meta.Tactic.TryThis

-- Solving in the background
/--
info: Try this: by simp_all only [Nat.reduceLE]
---
warning: declaration uses 'sorry'
-/
example : 2 ≤ 3 := by#
  sorry

/--
info: Try this: simp_all only [le_refl]
---
warning: declaration uses 'sorry'
-/
example : 2 ≤ 2 := by
  aided_by aesop? do
  sorry


-- Solving as soon as `aesop?` can complete the proof
opaque sillyN : Nat

axiom silly : sillyN = 2

/--
warning: declaration uses 'sorry'
-/
example : sillyN ≤ 3 := by#
  sorry

/--
info: Try this: by
  rw [silly]
  simp_all only
---
warning: declaration uses 'sorry'
-/
example : sillyN ≤ 4 := by#
  rw [silly]
  sorry

-- Ensuring reset of the cache
#eval clearCache

-- Showing that the task runs in the background
set_option aided_by.delay 0 in
/--
info: Try this: by
  skip
  sleep 100
  simp_all only
---
warning: declaration uses 'sorry'
-/
example : 2 ≤ 3 := by#
  skip
  sleep 100
  sorry

-- Messages tried after each steps
/--
info: Try this: by simp_all only
---
info: Try this: by
  skip
  simp_all only
---
warning: declaration uses 'sorry'
-/
example : 2 ≤ 2 := by#
   skip
   sorry

-- Using `apply?` in place of `aesop?`
macro "by!" tacs:tacticSeq : term =>
  `(by
  aided_by from_by apply? do $tacs)

macro "by!"  : term =>
  `(by
  aided_by from_by apply? do)

-- Added to make sure that the discriminant tree is loaded.
example : 2 ≤ 3 := by apply?

set_option aided_by.delay 200

/--
info: Try this: by exact Nat.le_of_ble_eq_true rfl
---
warning: declaration uses 'sorry'
-/
example : 2 ≤ 4 := by!
  sorry


def prop := 2 ≤ 3

example : prop := by
  rw [prop]
  exact Nat.AtLeastTwo.prop

example : 1 = 1 := by!
  sorry

/--
info: Try this: by
  rw [silly]
  simp_all only
---
warning: declaration uses 'sorry'
-/
example : sillyN ≤ 4 := by#
  rw [silly]
  sorry

example : 1 = 1 := by#
  skip
  sorry

example : 1 = 1 := by
  simp?

def sum : ℕ → ℕ
| 0 => 0
| n + 1 => n + 1 + sum n


-- Using `linarith`, tried after each step.
set_option aided_by.delay 600

/--
info: Try this:
  simp [sum]
  linarith
---
warning: declaration uses 'sorry'
-/
theorem sum_formula (n: ℕ) :  sum n = (n * (n + 1) : ℚ) / 2  := by
  induction n with
  | zero => rfl
  | succ n ih =>
    aided_by linarith do
    simp [sum]
    sorry
