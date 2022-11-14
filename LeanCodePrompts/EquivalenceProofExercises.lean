import Mathbin.All
import Mathlib.Tactic.Basic
import LeanCodePrompts.CheckParse
import LeanCodePrompts.ThmInfo
universe u v u_1 u_2

/-- Every prime that is `1` greater than a multiple of `4` can be expressed as the sum of two squares. -/
theorem fermat_two_square0 : (∀ {p : ℕ}, p % 4 = 1 → Prime p → ∃ a b, a ^ 2 + b ^ 2 = p) → (∀ p : ℕ, Prime p → (p % 4 = 1) → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p) := by
  intros h
  intros
  apply h <;> assumption

theorem fermat_two_square1 : (∀ p : ℕ, Prime p → (p % 4 = 1) → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p) → (∀ {p : ℕ}, p % 4 = 1 → Prime p → ∃ a b, a ^ 2 + b ^ 2 = p) := by
  intro h
  intros
  apply h <;> assumption

/-- The product of two numbers, each of which is the sum of four squares, is itself a sum of four squares. -/
theorem euler_four_square_identity0 : (∀ {a b : ℤ},   (∃ x y z w, a = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) → (∃ x y z w, b = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) → ∃ x y z w, a * b = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) → 
  (let is_sum_of_four_squares : ℕ → Prop := λ n : ℕ => ∃ (a b c d : ℕ), n = a^2 + b^2 + c^2 + d^2;
  ∀ (x y : ℕ), is_sum_of_four_squares x → is_sum_of_four_squares y → is_sum_of_four_squares (x * y)) := by 
  let is_sum_of_four_squares_int : ℤ → Prop := λ n : ℤ => ∃ (a b c d : ℤ), n = a^2 + b^2 + c^2 + d^2
  intros h1 h2 x y hx hy
  suffices : ∀ (a : ℕ), is_sum_of_four_squares_int (a : ℤ) ↔ h2 a
  · rw [← this (x * y)] 
    rw [Nat.cast_mul]
    refine @h1 (x : ℤ) (y : ℤ) (by refine (this x).2 hx) (by refine (this y).2 hy)
  intro z
  refine ⟨λ h, by 
    rcases h with ⟨a, b, c, d, h⟩
    refine ⟨Int.natAbs a, Int.natAbs b, Int.natAbs c, Int.natAbs d, by 
      have hn : ∀ (n : ℤ), (Int.natAbs n : ℤ) ^ 2 = n ^ 2
      · intro n
        -- this is the issue
        have hpow : ∀ (z : ℤ) (n : ℕ), @HPow.hPow ℤ ℕ ℤ instHPow z n = @HPow.hPow ℤ ℕ ℤ Monoid.HPow z n
        · intros z n
          change Monoidₓ.npow n z = Int.pow z n
          induction n 
          · change Monoidₓ.npow Zero.zero z = 1
            rw [Monoidₓ.npow_zero' z]
            simp only
          · rw [Int.pow, Monoidₓ.npow_succ' _, _root_.mul_comm]
            refine congr_arg2 _ (by assumption) rfl
        simp_rw [← hpow]
        refine Int.nat_abs_eq_iff_sq_eq.1 (by 
          conv_rhs =>
          · rw [← Int.nat_abs_abs] 
          refine congr_arg _ (by 
            rw [Int.abs_eq_nat_abs]
            norm_num
            norm_cast ) )
      rw [← hn a, ← hn b, ← hn c, ← hn d] at h
      simp_rw [← Nat.cast_pow] at h
      simp_rw [← Nat.cast_add] at h
      norm_cast at h ⟩, 
    λ h, by 
    rcases h with ⟨a, b, c, d, h⟩
    refine ⟨(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ), by 
      rw [h]
      simp_rw [Nat.cast_add]
      simp_rw [Nat.cast_pow] ⟩ ⟩

  
theorem euler_four_square_identity1 : (let is_sum_of_four_squares : ℕ → Prop := λ n : ℕ => ∃ (a b c d : ℕ), n = a^2 + b^2 + c^2 + d^2;
  ∀ (x y : ℕ), is_sum_of_four_squares x → is_sum_of_four_squares y → is_sum_of_four_squares (x * y)) → (∀ {a b : ℤ}, 
  (∃ x_1 y z w, a = x_1 ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) → 
  (∃ x_2 y z w, b = x_2 ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) → 
  ∃ x y z w, a * b = x ^ 2 + y ^ 2 + z ^ 2 + w ^ 2) := by 
  intros h1 x y hx hy
  suffices nat_abs_eq : ∀ {z : ℤ} (hz : 0 ≤ z), (Int.natAbs z : ℤ) = z
  · have sum_of_four_squares_nonneg : ∀ (a b c d : ℤ), 0 ≤ a^2 + b^2 + c^2 + d^2 := sorry
    rcases hx with ⟨ax, bx, cx, dx, hx⟩
    rcases hy with ⟨ay, b'y, cy, dy, hy⟩
    have x_nonneg : 0 ≤ x := hx ▸ (sum_of_four_squares_nonneg _ _ _ _)
    have y_nonneg : 0 ≤ y := hy ▸ (sum_of_four_squares_nonneg _ _ _ _)
    rw [← nat_abs_eq x_nonneg] at hx
    rw [← nat_abs_eq y_nonneg] at hy
    have mul_nonneg : 0 ≤ x * y 
    · -- this should work but some typeclass instance error : refine Int.mul_le_mul_of_nonneg_left x_nonneg y_nonneg
      sorry
    rw [← nat_abs_eq mul_nonneg]
    -- copied from last proof
    have hn : ∀ (n : ℤ), (Int.natAbs n : ℤ) ^ 2 = n ^ 2
    · intro n
      -- this is the issue
      have hpow : ∀ (z : ℤ) (n : ℕ), @HPow.hPow ℤ ℕ ℤ instHPow z n = @HPow.hPow ℤ ℕ ℤ Monoid.HPow z n
      · intros z n
        change Monoidₓ.npow n z = Int.pow z n
        induction n 
        · change Monoidₓ.npow Zero.zero z = 1
          rw [Monoidₓ.npow_zero' z]
          simp only
        · rw [Int.pow, Monoidₓ.npow_succ' _, _root_.mul_comm]
          refine congr_arg2 _ (by assumption) rfl
      simp_rw [← hpow]
      refine Int.nat_abs_eq_iff_sq_eq.1 (by 
        conv_rhs =>
        · rw [← Int.nat_abs_abs] 
        refine congr_arg _ (by 
        rw [Int.abs_eq_nat_abs]
        norm_num
        norm_cast ) )
    rw [← hn ax, ← hn bx, ← hn cx, ← hn dx] at hx
    rw [← hn ay, ← hn b'y, ← hn cy, ← hn dy] at hy
    simp_rw [← Nat.cast_pow, ← Nat.cast_add] at hx
    simp_rw [← Nat.cast_pow, ← Nat.cast_add] at hy
    norm_cast at hx
    norm_cast at hy
    rw [Int.nat_abs_mul]
    specialize h1 (Int.natAbs x) (Int.natAbs y)
    simp only at h1
    obtain ⟨a, b, c, d, h⟩ := h1 ⟨Int.natAbs ax, Int.natAbs bx, Int.natAbs cx, Int.natAbs dx, hx⟩ ⟨Int.natAbs ay, Int.natAbs b'y, Int.natAbs cy, Int.natAbs dy, hy⟩
    refine ⟨(a : ℤ), (b : ℤ), (c : ℤ), (d : ℤ), h ▸ by norm_cast ⟩
  intros z hz
  rw [Int.natAbs]
  induction z
  · simp only
    norm_cast
  exfalso
  norm_cast at hz

/-- A ring with all elements idempotent is commutative. -/
example : ({R : Type u} → [inst : CommRing R] → (∀ (x : R), x * x = x) → CommRing R) → ({R : Type u} →  [Ring R] →  (∀ x : R, x * x = x) → CommRing R) := by
  intro h R RRing hyp
  -- the typeclasses seem to be causing issues
  haveI : CommRing R := sorry
  apply h
  intro x
  sorry -- apply hyp

example : ({R : Type u} →  [Ring R] →  (∀ x : R, x * x = 1)) → ({R : Type u} → [inst : CommRing R] → (∀ (x : R), x * x = x) → CommRing R) := sorry

/-- There are infinitely many pairs of primes that differ exactly by `2`. -/
example : (∀ (n : ℕ), ∃ p₁ p₂, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ p₁ + 2 = p₂ ∧ 2 * n < p₂) → (∀ n : ℕ, ∃ p : ℕ, p > n ∧ Nat.Prime p ∧ Nat.Prime (p + 2)) := by
  intro h n
  let ⟨p₁, p₂, prime_p₁, prime_p₂, hyp₁, hyp₂⟩ := h n
  use p₁
  apply And.intro -- `split` does not appear to exist yet
  sorry -- needs `linarith` or `norm_num`
  apply And.intro
  exact prime_p₁
  rw [hyp₁]
  exact prime_p₂

example : (∀ n : ℕ, ∃ p : ℕ, p > n → Prime p → Prime (p + 2)) → (∀ (n : ℕ), ∃ p₁ p₂, Nat.Prime p₁ ∧ Nat.Prime p₂ ∧ p₁ + 2 = p₂ ∧ 2 * n < p₂) := sorry

/-- Every finite division ring is a field. -/
example : ((K : Type u) → [inst : DivisionRing K] → Fintype K → Field K) → ({R : Type u} →  [DivisionRing R] →  [Finite R] →  Field R) := sorry
example : ({R : Type u} →  [DivisionRing R] →  [Finite R] →  Field R) → ((K : Type u) → [inst : DivisionRing K] → Fintype K → Field K) := sorry


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
example : (∀ {G : Type u_1} [inst : Group G], (∀ (x : G), x ^ 2 = 1) → ∀ {x y : G}, Commute x y) → ({G: Type u} → [Group G] →  (∀ x y : G, x * x = 1) → (∀ x y : G, Commute x y)) := sorry
example : ({G: Type u} → [Group G] →  (∀ x y : G, x * x = 1) → (∀ x y : G, Commute x y)) → (∀ {G : Type u_1} [inst : Group G], (∀ (x : G), x ^ 2 = 1) → ∀ {x y : G}, Commute x y) := sorry

/-- The product of two consecutive natural numbers is even. -/
example : (∀ {p q : ℕ}, p = q + 1 → Even (p * q)) → ((n: Nat) →  Even <| n * (n + 1)) := sorry
example : ((n: Nat) →  Even <| n * (n + 1)) → (∀ {p q : ℕ}, p = q + 1 → Even (p * q)) := sorry

/-- Every free group is torsion free. -/
example : (∀ (α : Type u), Monoidₓ.IsTorsionFree (FreeGroup α)) → ({α : Type u} → Monoidₓ.IsTorsionFree (FreeGroup α)) := sorry
example : ({α : Type u} → Monoidₓ.IsTorsionFree (FreeGroup α)) → (∀ (α : Type u), Monoidₓ.IsTorsionFree (FreeGroup α)) := sorry

/-- Every natural number greater than `1` is divisible by a prime number.  -/
example : (∀ {n : ℕ}, 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n) → ((n: ℕ) → 
  n > 1 → ∃ p: ℕ, Prime p ∧ (∃ d: ℕ, p * d = n)) := sorry
example : ((n: ℕ) → n > 1 → ∃ p: ℕ, Prime p ∧ (∃ d: ℕ, p * d = n)) → (∀ {n : ℕ}, 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n) := sorry

/-- A finite torsion-free group is trivial -/
example : (∀ {G : Type u} [inst : Groupₓ G] [inst_1 : Fintype G], Monoidₓ.IsTorsionFree G → Fintype.card G = 1) → ({G: Type u} → [Groupₓ G] → [Finite G] → Monoidₓ.IsTorsionFree G → IsSubgroup.Trivial G) := sorry
example : ({G: Type u} → [Groupₓ G] → [Finite G] → Monoidₓ.IsTorsionFree G → IsSubgroup.Trivial G) → (∀ {G : Type u} [inst : Groupₓ G] [inst_1 : Fintype G], Monoidₓ.IsTorsionFree G → Fintype.card G = 1) := sorry

/-- Every finite division ring is a field. -/
example : ((K : Type u) → [inst : DivisionRing K] → Fintype K → Field K) → ({R : Type u} →  [Ringₓ R] → [IsDomain R] →  [Finite R] →  Field R) := sorry
example : ({R : Type u} →  [Ringₓ R] → [IsDomain R] →  [Finite R] →  Field R) → ((K : Type u) → [inst : DivisionRing K] → Fintype K → Field K) := sorry


/-- Every surjective homomorphism from a finitely generated free group to itself is injective -/
example : (∀ {α : Type u_1} {β : Type u_2} [inst : Groupₓ α] [inst_1 : Groupₓ β] [inst_2 : Fintype α] [inst_3 : Fintype β]   {f : α → β}, IsGroupHom f → Function.Surjective f → Function.Injective f) → ({α : Type u} →  [Finite α] → (f: FreeGroup α → FreeGroup α) → (IsGroupHom f) → f.Surjective → f.Injective) := sorry
example : ({α : Type u} →  [Finite α] → (f: FreeGroup α → FreeGroup α) → (IsGroupHom f) → f.Surjective → f.Injective) → (∀ {α : Type u_1} {β : Type u_2} [inst : Groupₓ α] [inst_1 : Groupₓ β] [inst_2 : Fintype α] [inst_3 : Fintype β]   {f : α → β}, IsGroupHom f → Function.Surjective f → Function.Injective f) := sorry

/-- Every positive even integer can be written as the sum of two primes. -/
example : (∀ {n : ℕ}, 0 < n → Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) → (∀ n : ℕ, n > 0 → Even n → ∃ p q : ℕ, Prime p → Prime q → n = p + q) := sorry
example : (∀ n : ℕ, n > 0 → Even n → ∃ p q : ℕ, Prime p → Prime q → n = p + q) → (∀ {n : ℕ}, 0 < n → Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n) := sorry

/-- Every matrix satisfies its own characteristic polynomial. -/
example : (∀ {R : Type u} [inst : CommRingₓ R] [inst_1 : Nontrivial R] {n : Type w} [inst_2 : DecidableEq n] [inst_3 : Fintype n]   (M : Matrix n n R), AlgHom.toFun (Polynomial.aeval M) (Matrix.charpoly M) = 0) → ({R : Type u} →  [CommRingₓ R] →  {n : Type v} →  [DecidableEq n] →  [Fintype n] →  (M : Matrix n n R) → (Polynomial.aeval M) M.charpoly = 0) := sorry
example : ({R : Type u} →  [CommRingₓ R] →  {n : Type v} →  [DecidableEq n] →  [Fintype n] →  (M : Matrix n n R) → (Polynomial.aeval M) M.charpoly = 0) → (∀ {R : Type u} [inst : CommRingₓ R] [inst_1 : Nontrivial R] {n : Type w} [inst_2 : DecidableEq n] [inst_3 : Fintype n]   (M : Matrix n n R), AlgHom.toFun (Polynomial.aeval M) (Matrix.charpoly M) = 0) := sorry

/-- If the square of a number is even, the number itself is even. -/
example : (∀ {M : Type u} [inst : Semiring M] [inst_1 : DecidableEq M] (a : M), Even (a * a) → Even a) → (∀ n : ℕ, Even (n^2) → Even n) := sorry
example : (∀ n : ℕ, Even (n^2) → Even n) → (∀ {M : Type u} [inst : Semiring M] [inst_1 : DecidableEq M] (a : M), Even (a * a) → Even a) := sorry


/-- If every point of a subset of a topological space is contained in some open set, the subset itself is open. -/
example : (∀ {α : Type u} [inst : TopologicalSpace α] {s : Set α}, (∀ (x : α), x ∈ s → ∃ t, IsOpen t ∧ x ∈ t) → IsOpen s) → ({X : Type u} →  [TopologicalSpace X] →  (S : Set X) →  (∀ x ∈ S, ∃ U : Set X, IsOpen U) → IsOpen S) := sorry
example : ({X : Type u} →  [TopologicalSpace X] →  (S : Set X) →  (∀ x ∈ S, ∃ U : Set X, IsOpen U) → IsOpen S) → (∀ {α : Type u} [inst : TopologicalSpace α] {s : Set α}, (∀ (x : α), x ∈ s → ∃ t, IsOpen t ∧ x ∈ t) → IsOpen s) := sorry

/-- Every non-identity element of a free group is of infinite order. -/
example : (∀ {α : Type u} [inst : DecidableEq α] {x : FreeGroup α}, x ≠ 1 → ¬IsOfFinOrder x) → ({G : Type u} →  [Groupₓ G] →  FreeGroup G → (∀ g : G, g ≠ 1 → orderOf g = 0)) := sorry
example : ({G : Type u} →  [Groupₓ G] →  FreeGroup G → (∀ g : G, g ≠ 1 → orderOf g = 0)) → (∀ {α : Type u} [inst : DecidableEq α] {x : FreeGroup α}, x ≠ 1 → ¬IsOfFinOrder x) := sorry

/-- For any two relatively prime positive integers $a$ and $b$, every sufficiently large natural number $N$ can be written as a linear combination $ax + by$ of $a$ and $b$, where both $x$ and $y$ are natural numbers. -/
example : (∀ {m n : ℕ}, 0 < m → 0 < n → Nat.gcd m n = 1 → ∀ (N : ℕ), N > m * n → ∃ x y, N = m * x + n * y) → (∀ a b : ℕ, a > 0 → b > 0 → Nat.coprime a b → ∃ m : ℕ, ∀ N : ℕ, N > m → ∃ x y : ℕ, N = a*x + b*y) := sorry
example : (∀ a b : ℕ, a > 0 → b > 0 → Nat.coprime a b → ∃ m : ℕ, ∀ N : ℕ, N > m → ∃ x y : ℕ, N = a*x + b*y) → (∀ {m n : ℕ}, 0 < m → 0 < n → Nat.gcd m n = 1 → ∀ (N : ℕ), N > m * n → ∃ x y, N = m * x + n * y) := sorry

-- The ones below had no model answers

/-- Every field is a ring. -/
example : ({α : Type u_1} → [inst : Field α] → Ring α) → (Unit) := sorry
example : (Unit) → ({α : Type u_1} → [inst : Field α] → Ring α) := sorry

/-- The set of units in a ring forms a group. -/
example : ((R : Type u_1) → [inst : Ringₓ R] → AddGroup (Units R)) → (Unit) := sorry
example : (Unit) → ((R : Type u_1) → [inst : Ringₓ R] → AddGroup (Units R)) := sorry

/-- If the direct product of two groups is torsion free then each of the groups is torsion free. -/
example : (∀ {η : Type u_1} (G : Type u_2) [inst : Groupₓ G] {Γ : Type u_3} [inst_1 : Groupₓ Γ],   Monoidₓ.IsTorsionFree (G × Γ) → Monoidₓ.IsTorsionFree G ∧ Monoidₓ.IsTorsionFree Γ) → (Unit) := sorry
example : (Unit) → (∀ {η : Type u_1} (G : Type u_2) [inst : Groupₓ G] {Γ : Type u_3} [inst_1 : Groupₓ Γ],   Monoidₓ.IsTorsionFree (G × Γ) → Monoidₓ.IsTorsionFree G ∧ Monoidₓ.IsTorsionFree Γ) := sorry


#eval do
  let l ← getFileThmInfo
  --let l' := l.map Prod.fst |>.map Lean.Name.toString |>.qsort
  -- return l'.groupBy $ λ s s' => s.dropRight 1 == s'.dropRight 1
  return 1

#eval [1, 1, 2, 2].groupBy (· = ·)

#eval (Lean.Name.toString `fermat_two_square0).dropRight 1