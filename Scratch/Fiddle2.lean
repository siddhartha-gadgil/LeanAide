import Mathlib

#check List.sum

#eval 3 ∣ 4 

#reduce (3: Nat)
set_option pp.all true in
#reduce Nat.succ <| Nat.succ Nat.zero
set_option pp.all true in
#reduce (0 : Nat)
#check String
example (n: Nat): (instOfNatNat n).1 = n := rfl

#print ULift.up
#print ULift.down
#check False.elim
#print False.elim
#check @False.rec -- (motive : False → Sort u_1) → (t : False) → motive t
#check False
#check @And.rec
#check @Or.rec

#check @True.rec

#check Fin.mk -- {n : ℕ} → (val : ℕ) → val < n → Fin n

example : forall {a : ℝ} {f : ℝ → ℝ} {M₀ M₁ M₂ : ℝ},  Differentiable ℝ f → Differentiable ℝ (deriv f) →    (∀ x, a < x → abs (f x) ≤ M₀) →      (∀ x, a < x → abs (deriv f x) ≤ M₁) →        (∀ x, a < x → abs (deriv^[2] f x) ≤ M₂) → M₁ ^ 2 ≤ 4 * M₀ * M₂ := by sorry

example : ∀ {M : Type u_1} [inst : MetricSpace M],  ∃ (f : Set M → Set M), (∀ (U : Set M), IsOpen U → IsClosed (f U)) ∧ (∀ (K : Set M), IsClosed K → IsOpen (f K)) ∧    (∀ (U₁ U₂ : Set M), IsOpen U₁ → IsOpen U₂ → f U₁ = f U₂ → U₁ = U₂) ∧    (∀ (K₁ K₂ : Set M), IsClosed K₁ → IsClosed K₂ → f K₁ = f K₂ → K₁ = K₂) := by sorry

example (x : ℝ) : ‖x‖ = 0 := sorry

example (n : ℕ) (x y : EuclideanSpace ℝ (Fin n)) : ‖x + y‖^2 + ‖x - y‖^2 = 2*‖x‖ ^2 + 2*‖y‖^2 := by sorry

example : ∀ {G : Type u_1} {H : Type u_2} [inst : Group G] [inst_1 : Group H],  Monoid.IsTorsionFree (G × H) → Monoid.IsTorsionFree G ∧ Monoid.IsTorsionFree H := by sorry

example  (G : Type*) (H : Type*) [Group G] [Group H] (gh_torsion_free : ∀ g : G × H, g ≠ 1 → ∃ n : ℤ, g ^ n ≠ 1) : (∀ (g : G), g ≠ 1 → ∃ n : ℤ, g ^ n ≠ 1) ∧ (∀ (h : H), h ≠ 1 → ∃ n : ℤ, h ^ n ≠ 1) := by sorry

example : PythagoreanTriple 3 4 5 := by sorry

example : ∀ {α : Type u} [t : MetricSpace α] [inst : TopologicalSpace.SeparableSpace α] {s : Set α},  IsClosed s → ∃ t₁ t₂, Perfect t₁ ∧ Set.Countable t₂ ∧ s = t₁ ∪ t₂ := by sorry

example : forall {α : Type u} [inst : PseudoMetricSpace α] [inst_1 : CompleteSpace α] {f : ℕ → Set α},  (∀ n, IsOpen (f n)) → (∀ n, Dense (f n)) → Set.Nonempty (⋂ n, f n)   := by sorry

example : ∀ {Y : Type u_1} [inst : TopologicalSpace Y] [inst_1 : NormalSpace Y] {s : Set Y} (f : C(↑s, ℝ)),  IsClosed s → ∃ g, ContinuousMap.restrict s g = f  := by sorry

example: forall {Y : Type u_1} [inst : TopologicalSpace Y] [inst_1 : NormalSpace Y] {E : Set Y} (f : C(↑E, ℝ)),  IsClosed E → ∃ g, ContinuousMap.restrict E g = f := by sorry

#check Complex.abs

example : ∀ {n : ℕ}, n * n % 2 = 0 → n % 2 = 0 := by sorry

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

example : (n: ℕ) → let m := n + 1 ; n + 1 = m := by simp 

#check Eq.mp