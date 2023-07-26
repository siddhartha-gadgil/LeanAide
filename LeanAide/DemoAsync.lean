import LeanAide.RunAsync
import Mathlib.Tactic

example : 3 ≤4 := by simp_all only

example : 3 ≤5 := by
  simp_all only
  
opaque sillyN : Nat

axiom silly : sillyN = 2

example : sillyN ≤ 3 := by
  rw [silly]
  simp_all only

example : sillyN ≤ 4 := by simp [silly]

macro "by!" tacs:tacticSeq : term =>
  `(by 
  aided_by from_by apply? do $tacs)

macro "by!"  : term =>
  `(by 
  aided_by from_by apply? do)

example : 3 ≤ 5 := by apply?

example : 3 ≤6 := by
  skip
  exact Nat.le_of_ble_eq_true rfl 
   

def sum : ℕ → ℕ
| 0 => 0
| n + 1 => n + 1 + sum n

theorem sum_formula (n: ℕ) :  sum n = (n * (n + 1) : ℚ) / 2  := by 
  induction n with
  | zero => rfl
  | succ n ih => 
      simp
      simp [sum]
      linarith