import Mathlib

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