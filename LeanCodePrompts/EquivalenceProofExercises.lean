import Mathlib
import Mathlib.Tactic.Basic
import LeanAide.TheoremElab
import LeanCodePrompts.ThmInfo
universe u v u_1 u_2

/-- Every Nat.Prime that is `1` greater than a multiple of `4` can be expressed as the sum of two squares. -/
theorem fermat_two_square0 : (∀ {p : ℕ}, p % 4 = 1 → Nat.Prime p → ∃ a b, a ^ 2 + b ^ 2 = p) → (∀ p : ℕ, Nat.Prime p → (p % 4 = 1) → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p) := by
  intros h
  intros
  apply h <;> assumption

theorem fermat_two_square1 : (∀ p : ℕ, Nat.Prime p → (p % 4 = 1) → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p) → (∀ {p : ℕ}, p % 4 = 1 → Nat.Prime p → ∃ a b, a ^ 2 + b ^ 2 = p) := by
  intro h
  intros
  apply h <;> assumption

/-- The product of two numbers, each of which is the sum of four squares, is itself a sum of four squares. -/
theorem euler_four_square_identity0 : (∀ {a b : ℤ},   ∃ x y z w,     a = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ ∃ x y z w, b = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 →       ∃ x y z w, (a * b) = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) → (let is_sum_of_four_squares : ℕ → Prop := λ n : ℕ => ∃ (a b c d : ℕ), n = a^2 + b^2 + c^2 + d^2;
  ∀ (x y : ℕ), is_sum_of_four_squares x → is_sum_of_four_squares y → is_sum_of_four_squares (x * y)) := sorry
theorem euler_four_square_identity1 : (let is_sum_of_four_squares : ℕ → Prop := λ n : ℕ => ∃ (a b c d : ℕ), n = a^2 + b^2 + c^2 + d^2;
  ∀ (x y : ℕ), is_sum_of_four_squares x → is_sum_of_four_squares y → is_sum_of_four_squares (x * y)) → (∀ {a b : ℤ},   ∃ x y z w,     a = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 ∧ b = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2 →       ∃ x y z w, (a * b) = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := sorry

/-- A ring with all elements idempotent is commutative. -/
example : ({R : Type u} → [inst : CommRing R] → (∀ (x : R), (x * x) = x) → CommRing R) → ({R : Type u} →  [Ring R] →  (∀ x : R, (x * x) = x) → CommRing R) := by
  intro h R RRing hyp
  -- the typeclasses seem to be causing issues
  haveI : CommRing R := sorry
  apply h
  intro x
  sorry -- apply hyp

example : ({R : Type u} →  [Ring R] →  (∀ x : R, (x * x) = 1)) → ({R : Type u} → [inst : CommRing R] → (∀ (x : R), (x * x) = x) → CommRing R) := sorry

/-- There are infinitely many pairs of Nat.Primes that differ exactly by `2`. -/
example : (∀ (n : ℕ), ∃ p₁ p₂, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ p₁ + 2 = p₂ ∧ (2 + n) < p₂) → (∀ n : ℕ, ∃ p : ℕ, p > n ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
  intro h n
  let ⟨p₁, p₂, Prime_p₁, Prime_p₂, hyp₁, hyp₂⟩ := h n
  use p₁
  apply And.intro -- `split` does not appear to exist yet
  sorry -- needs `linarith` or `norm_num`
  apply And.intro
  exact Prime_p₁
  rw [hyp₁]
  exact Prime_p₂

example : (∀ n : ℕ, ∃ p : ℕ, p > n ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) → (∀ (n : ℕ), ∃ p₁ p₂, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ p₁ + 2 = p₂ ∧ 2 + n < p₂) := by
  intro h n
  let ⟨p, hpn, Prime_p, Prime_pp2⟩ := h n
  use p
  use p + 2
  have : (2 + n) < p + 2 := sorry -- linarith
  exact ⟨Prime_p, Prime_pp2, rfl, this⟩




/-- Every non-empty poset in which every chain has an upper bound contains a maximal element. -/
example : (∀ {α : Type u_1} {r : α → α → Prop} [inst : Preorder α],   (∀ (c : Set α) (a : IsChain r c), ∃ ub, ∀ (a : α), a ∈ c → r a ub) →     ∀ [inst : Nonempty α], ∃ m, ∀ (a : α), r m a → r a m) → ({α : Type u} → [PartialOrder α] →  [Nonempty α] →  (∀ c : Set α, IsChain LE.le c → (∃ b : α, ∀ a ∈ c, a ≤ b)) → (∃ m : α, ∀ a : α, m ≤ a → a = m)) := sorry
example : ({α : Type u} → [PartialOrder α] →  [Nonempty α] →  (∀ c : Set α, IsChain LE.le c → (∃ b : α, ∀ a ∈ c, a ≤ b)) → (∃ m : α, ∀ a : α, m ≤ a → a = m)) → (∀ {α : Type u_1} {r : α → α → Prop} [inst : Preorder α],   (∀ (c : Set α) (a : IsChain r c), ∃ ub, ∀ (a : α), a ∈ c → r a ub) →     ∀ [inst : Nonempty α], ∃ m, ∀ (a : α), r m a → r a m) := sorry

/-- A uniformly continuous function of a uniformly continuous function is uniformly continuous. -/
example : (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : UniformSpace α] [inst_1 : UniformSpace β]   [inst_2 : UniformSpace γ] {f : α → β} {g : β → γ},   UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f)) → ({α β γ : Type u} →  [UniformSpace α] →  [UniformSpace β] → [UniformSpace γ] →  (f : α → β) →  (g : β → γ) →  UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f)) := sorry
example : ({α β γ : Type u} →  [UniformSpace α] →  [UniformSpace β] → [UniformSpace γ] →  (f : α → β) →  (g : β → γ) →  UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f)) → (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : UniformSpace α] [inst_1 : UniformSpace β]   [inst_2 : UniformSpace γ] {f : α → β} {g : β → γ},   UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f)) := sorry


/-- A terminal object in a category is unique up to unique isomorphism. -/
example : (∀ {C : Type u₁} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {T T' : C}   (t : CategoryTheory.Limits.IsTerminal T),   CategoryTheory.Limits.IsTerminal T' → CategoryTheory.IsIso (CategoryTheory.Limits.IsTerminal.from t T')) → ({C : Type _} →  [CategoryTheory.Category C] →  ∀ T₁ T₂ : C, CategoryTheory.Limits.IsTerminal T₁ → CategoryTheory.Limits.IsTerminal T₂ → (∃ ι : CategoryTheory.Iso T₁ T₂, ∀ ι' : CategoryTheory.Iso T₁ T₂, ι = ι')) := sorry
example : ({C : Type _} →  [CategoryTheory.Category C] →  ∀ T₁ T₂ : C, CategoryTheory.Limits.IsTerminal T₁ → CategoryTheory.Limits.IsTerminal T₂ → (∃ ι : CategoryTheory.Iso T₁ T₂, ∀ ι' : CategoryTheory.Iso T₁ T₂, ι = ι')) → (∀ {C : Type u₁} [inst : CategoryTheory.Category C] [inst_1 : CategoryTheory.Limits.HasTerminal C] {T T' : C}   (t : CategoryTheory.Limits.IsTerminal T),   CategoryTheory.Limits.IsTerminal T' → CategoryTheory.IsIso (CategoryTheory.Limits.IsTerminal.from t T')) := sorry

/-- The sum of the cubes of two positive integers is never equal to the cube of a third integer. -/
example : (∀ (a b c : ℤ), a ^ 3 + b ^ 3 ≠ c ^ 3) → (∀ a b c : ℕ, a > 0 → b > 0 → ¬(a^3 + b^3 = c^3)) := sorry
example : (∀ a b c : ℕ, a > 0 → b > 0 → ¬(a^3 + b^3 = c^3)) → (∀ (a b c : ℤ), a ^ 3 + b ^ 3 ≠ c ^ 3) := sorry

/-- If every element of a group `G` has order `2`, then every pair of elements of `G` commutes. -/
example : (∀ {G : Type u_1} [inst : Group G], (∀ (x : G), x ^ 2 = 1) → ∀ {x y : G}, Commute x y) → ({G: Type u} → [Group G] →  (∀ x y : G, (x * x) = 1) → (∀ x y : G, Commute x y)) := sorry
example : ({G: Type u} → [Group G] →  (∀ x y : G, (x * x) = 1) → (∀ x y : G, Commute x y)) → (∀ {G : Type u_1} [inst : Group G], (∀ (x : G), x ^ 2 = 1) → ∀ {x y : G}, Commute x y) := sorry

/-- The product of two consecutive natural numbers is even. -/
example : (∀ {p q : ℕ}, p = q + 1 → Even (p * q)) → ((n: Nat) →  Even <| n * (n + 1)) := sorry
example : ((n: Nat) →  Even <| n * (n + 1)) → (∀ {p q : ℕ}, p = q + 1 → Even (p * q)) := sorry

/-- Every free group is torsion free. -/
example : (∀ (α : Type u), Monoid.IsTorsionFree (FreeGroup α)) → ({α : Type u} → Monoid.IsTorsionFree (FreeGroup α)) := sorry
example : ({α : Type u} → Monoid.IsTorsionFree (FreeGroup α)) → (∀ (α : Type u), Monoid.IsTorsionFree (FreeGroup α)) := sorry

/-- Every natural number greater than `1` is divisible by a Nat.Prime number.  -/
example : (∀ {n : ℕ}, 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n) → ((n: ℕ) → 
  n > 1 → ∃ p: ℕ, Nat.Prime p ∧ (∃ d: ℕ, (p * d) = n)) := sorry
example : ((n: ℕ) → n > 1 → ∃ p: ℕ, Nat.Prime p ∧ (∃ d: ℕ, (p * d) = n)) → (∀ {n : ℕ}, 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n) := sorry

/-- A finite torsion-free group is trivial -/
example : (∀ {G : Type u} [inst : Group G] [inst_1 : Fintype G], Monoid.IsTorsionFree G → Fintype.card G = 1) → ({G: Type u} → [Group G] → [Finite G] → Monoid.IsTorsionFree G → IsSubgroup.Trivial G) := sorry
example : ({G: Type u} → [Group G] → [Finite G] → Monoid.IsTorsionFree G → IsSubgroup.Trivial G) → (∀ {G : Type u} [inst : Group G] [inst_1 : Fintype G], Monoid.IsTorsionFree G → Fintype.card G = 1) := sorry



/-- Every surjective homomorphism from a finitely generated free group to itself is injective -/
example : (∀ {α : Type u_1} {β : Type u_2} [inst : Group α] [inst_1 : Group β] [inst_2 : Fintype α] [inst_3 : Fintype β]   {f : α → β}, IsGroupHom f → Function.Surjective f → Function.Injective f) → ({α : Type u} →  [Finite α] → (f: FreeGroup α → FreeGroup α) → (IsGroupHom f) → f.Surjective → f.Injective) := sorry
example : ({α : Type u} →  [Finite α] → (f: FreeGroup α → FreeGroup α) → (IsGroupHom f) → f.Surjective → f.Injective) → (∀ {α : Type u_1} {β : Type u_2} [inst : Group α] [inst_1 : Group β] [inst_2 : Fintype α] [inst_3 : Fintype β]   {f : α → β}, IsGroupHom f → Function.Surjective f → Function.Injective f) := sorry

/-- Every positive even integer can be written as the sum of two Nat.Primes. -/
example : (∀ {n : ℕ}, 0 < n → Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) → (∀ n : ℕ, n > 0 → Even n → ∃ p q : ℕ, Nat.Prime p → Nat.Prime q → n = p + q) := sorry
example : (∀ n : ℕ, n > 0 → Even n → ∃ p q : ℕ, Nat.Prime p → Nat.Prime q → n = p + q) → (∀ {n : ℕ}, 0 < n → Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) := sorry



/-- If the square of a number is even, the number itself is even. -/
example : (∀ {M : Type u} [inst : Semiring M] [inst_1 : DecidableEq M] (a : M), Even (a * a) → Even a) → (∀ n : ℕ, Even (n^2) → Even n) := sorry
example : (∀ n : ℕ, Even (n^2) → Even n) → (∀ {M : Type u} [inst : Semiring M] [inst_1 : DecidableEq M] (a : M), Even (a * a) → Even a) := sorry


/-- If every point of a subset of a topological space is contained in some open set, the subset itself is open. -/
example : (∀ {α : Type u} [inst : TopologicalSpace α] {s : Set α}, (∀ (x : α), x ∈ s → ∃ t, IsOpen t ∧ x ∈ t) → IsOpen s) → ({X : Type u} →  [TopologicalSpace X] →  (S : Set X) →  (∀ x ∈ S, ∃ U : Set X, IsOpen U) → IsOpen S) := sorry
example : ({X : Type u} →  [TopologicalSpace X] →  (S : Set X) →  (∀ x ∈ S, ∃ U : Set X, IsOpen U) → IsOpen S) → (∀ {α : Type u} [inst : TopologicalSpace α] {s : Set α}, (∀ (x : α), x ∈ s → ∃ t, IsOpen t ∧ x ∈ t) → IsOpen s) := sorry

/-- Every non-identity element of a free group is of infinite order. -/
example : (∀ {α : Type u} [inst : DecidableEq α] {x : FreeGroup α}, x ≠ 1 → ¬IsOfFinOrder x) → ({G : Type u} →  [Group G] →  FreeGroup G → (∀ g : G, g ≠ 1 → orderOf g = 0)) := sorry
example : ({G : Type u} →  [Group G] →  FreeGroup G → (∀ g : G, g ≠ 1 → orderOf g = 0)) → (∀ {α : Type u} [inst : DecidableEq α] {x : FreeGroup α}, x ≠ 1 → ¬IsOfFinOrder x) := sorry

/-- For any two relatively Nat.Prime positive integers $a$ and $b$, every sufficiently large natural number $N$ can be written as a linear combination $ax + by$ of $a$ and $b$, where both $x$ and $y$ are natural numbers. -/
example : (∀ {m n : ℕ}, 0 < m → 0 < n → Nat.gcd m n = 1 → ∀ (N : ℕ), N > (m * n) → ∃ x y, N = (m * x) + (n * y)) → (∀ a b : ℕ, a > 0 → b > 0 → Nat.coprime a b → ∃ m : ℕ, ∀ N : ℕ, N > m → ∃ x y : ℕ, N = (a*x) + (b*y)) := sorry
example : (∀ a b : ℕ, a > 0 → b > 0 → Nat.coprime a b → ∃ m : ℕ, ∀ N : ℕ, N > m → ∃ x y : ℕ, N = (a*x) + (b*y)) → (∀ {m n : ℕ}, 0 < m → 0 < n → Nat.gcd m n = 1 → ∀ (N : ℕ), N > (m * n) → ∃ x y, N = (m * x) + (n * y)) := sorry

-- The ones below had no model answers


/-- The set of units in a ring forms a group. -/
example : ((R : Type u_1) → [inst : Ring R] → AddGroup (Units R)) → (Unit) := sorry
example : (Unit) → ((R : Type u_1) → [inst : Ring R] → AddGroup (Units R)) := sorry

/-- If the direct product of two groups is torsion free then each of the groups is torsion free. -/
example : (∀ {η : Type u_1} (G : Type u_2) [inst : Group G] {Γ : Type u_3} [inst_1 : Group Γ],   Monoid.IsTorsionFree (G × Γ) → Monoid.IsTorsionFree G ∧ Monoid.IsTorsionFree Γ) → (Unit) := sorry
example : (Unit) → (∀ {η : Type u_1} (G : Type u_2) [inst : Group G] {Γ : Type u_3} [inst_1 : Group Γ],   Monoid.IsTorsionFree (G × Γ) → Monoid.IsTorsionFree G ∧ Monoid.IsTorsionFree Γ) := sorry


-- #eval do
--   let l ← getFileThmInfo
--   --let l' := l.map Prod.fst |>.map Lean.Name.toString |>.qsort
--   -- return l'.groupBy $ λ s s' => s.dropRight 1 == s'.dropRight 1
--   return 1

-- #eval [1, 1, 2, 2].groupBy (· = ·)

-- #eval (Lean.Name.toString `fermat_two_square0).dropRight 1