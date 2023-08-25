import Mathlib

example (x : ℝ) : ‖x‖ = 0 := sorry

example (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) : ‖x + y‖^2 + ‖x - y‖^2 = 2*‖x‖ ^2 + 2*‖y‖^2 := by sorry

example : forall {R : Type u} [inst : CommRing R] {n : Type w} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),  Polynomial.aeval M (Matrix.charpoly M) = 0 := by sorry

#check Complex.abs

open BigOperators
example (n : ℕ) (f : ℕ → ℂ) : Complex.abs (∑ i in Finset.range n, f i) ≤ ∑ i in Finset.range n, Complex.abs (f i) := by sorry

example : 1 = 1 := by
  let c := 1
  show c = 1
  rfl

example : ∀ x: ℕ, x + 3 = 3 + x := by
  conv =>
    enter [x, 2]
    rw [Nat.add_comm]
  intro _ 
  rfl
   
example (f g : ℕ → ℕ): f = g → ∀ x: ℕ, f (x + 3) = g (3 + x) := by
  conv =>
    intro eqn x
    arg 1
    rw [eqn]
    arg 1    
    rw [Nat.add_comm]
  simp

example (f g : ℕ → ℕ): f = g → ∀ x: ℕ, f (x + 3) = g (3 + x) := by
  conv =>
    enter [eqn, x, 2]
    rw [← eqn]
  conv => 
    enter [eqn, x, 1]
    rw [Nat.add_comm]
  simp

example (f g : ℕ →   ℕ → ℕ): f = g → ∀ x: ℕ, 
    f (x + 3) (4 + x) = g (3 + x) (x + 4) := by
  conv => 
    intro
    enter [x, 1, 2]
    rw [Nat.add_comm]
  conv => 
    intro
    enter [x, 1, 1]
    rw [Nat.add_comm]
  conv =>
    enter [eqn, x, 2]
    rw [← eqn]
  simp

example : 1 = 1 := by
  let _ := 3
  rfl