import Mathlib

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

open Nat

/-
  Translation of 40 statements from `data/thm-prompts.txt`
  Using similarity search

  SUMMARY:

  Time:
  · Total time to translate 40 statements = 330.79
  · Avg time to translate one statement = 8.27

  Results:
  · Success = 40
  · Fallback = 0
-/

--Result: success
--Time: 12.12 s
/--If every proper closed subset of a topological space is compact, then the space itself is compact.-/
theorem t1 : ∀ {X : Type u} [inst : TopologicalSpace X], (∀ (s : Set X), IsClosed s → s ≠ Set.univ → IsCompact s) → CompactSpace X :=
  by sorry

--Result: success
--Time: 13.34 s
/--Every prime that is `1` greater than a multiple of `4` can be expressed as the sum of two squares.-/
theorem t2 : ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 → ∃ a b, a ^ 2 + b ^ 2 = p :=
  by sorry

--Result: success
--Time: 13.12 s
/--The product of two numbers, each of which is the sum of four squares, is itself a sum of four squares.-/
theorem t3 : ∀ {a b x₁ x₂ x₃ x₄ y₁ y₂ y₃ y₄ : ℕ},
  a = x₁ ^ 2 + x₂ ^ 2 + x₃ ^ 2 + x₄ ^ 2 →
    b = y₁ ^ 2 + y₂ ^ 2 + y₃ ^ 2 + y₄ ^ 2 → ∃ z₁ z₂ z₃ z₄, a * b = z₁ ^ 2 + z₂ ^ 2 + z₃ ^ 2 + z₄ ^ 2 :=
  by sorry

--Result: success
--Time: 7.85 s
/--A ring with all elements idempotent is commutative.-/
theorem t4 : {R : Type u_1} → [inst : Ring R] → (∀ (a : R), IsIdempotentElem a) → CommRing R :=
  by sorry

--Result: success
--Time: 8.48 s
/--There are infinitely many pairs of primes that differ exactly by `2`.-/
theorem t5 : {p | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite :=
  by sorry

--Result: success
--Time: 6.06 s
/--Every finite division ring is a field.-/
theorem t6 : (D : Type u_1) → [Finite D] → [inst : DivisionRing D] → Field D :=
  by sorry

--Result: success
--Time: 7.92 s
/--If each of two types can be mapped injectively into the other, then there is a bijection between them.-/
theorem t7 : ∀ {α : Type u} {β : Type v} (a : α ↪ β) (a : β ↪ α), Nonempty (α ≃ β) :=
  by sorry

--Result: success
--Time: 18.51 s
/--A finite graph in which every pair of vertices have precisely one common neighbour contains a vertex that is adjacent to all other vertices.-/
theorem t8 : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V],
  (∀ (v w : V), v ≠ w → ∃! x, G.Adj v x ∧ G.Adj w x) → ∃ v, ∀ (w : V), v ≠ w → G.Adj v w :=
  by sorry

--Result: success
--Time: 9.48 s
/--The number of partitions with odd parts is equal to the number of partitions with distinct parts.-/
theorem t9 : ∀ (n : ℕ), Fintype.card { p // ∀ x ∈ p.parts, x % 2 = 1 } = Fintype.card { p // p.parts.Nodup } :=
  by sorry

--Result: success
--Time: 9.07 s
/--Every non-empty poset in which every chain has an upper bound contains a maximal element.-/
theorem t10 : ∀ {α : Type u} [inst : PartialOrder α] [Nonempty α], ∃ m, ∀ (a : α), m ≤ a → a ≤ m :=
  by sorry

--Result: success
--Time: 6.26 s
/--A group whose automorphism group is cyclic is Abelian.-/
theorem t11 : {G : Type u_1} → [inst : Group G] → IsCyclic (MulAut G) → CommGroup G :=
  by sorry

--Result: success
--Time: 9.16 s
/--A uniformly continuous function of a uniformly continuous function is uniformly continuous.-/
theorem t12 : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [instα : UniformSpace α] [instβ : UniformSpace β]
  [instγ : UniformSpace γ] {f : α → β} {g : β → γ},
  UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f) :=
  by sorry

--Result: success
--Time: 0.04 s
/--A uniformly continuous function of a uniformly continuous function is uniformly continuous.-/
theorem t13 : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [instα : UniformSpace α] [instβ : UniformSpace β]
  [instγ : UniformSpace γ] {f : α → β} {g : β → γ},
  UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f) :=
  by sorry

--Result: success
--Time: 14.71 s
/--A topological space is normal if and only if any two disjoint closed subsets can be separated by a continuous function.-/
theorem t14 : ∀ {X : Type u} [inst : TopologicalSpace X],
  NormalSpace X ↔ ∀ (s t : Set X), IsClosed s → IsClosed t → Disjoint s t → ∃ f, Set.EqOn (⇑f) 0 s ∧ Set.EqOn (⇑f) 1 t :=
  by sorry

--Result: success
--Time: 7.83 s
/--If a function from the unit interval to itself has a point of period three, then it has points of all positive periods.-/
theorem t15 : ∀ {f : ℝ → ℝ},
  (∃ x ∈ Set.Icc 0 1, Function.IsPeriodicPt f 3 x) → ∀ (n : ℕ), 0 < n → ∃ y ∈ Set.Icc 0 1, Function.IsPeriodicPt f n y :=
  by sorry

--Result: success
--Time: 13.35 s
/--A terminal object in a category is unique up to unique isomorphism.-/
theorem t16 : {C : Type u} →
  [inst : CategoryTheory.Category.{v, u} C] →
    {X Y : C} → CategoryTheory.Limits.IsTerminal X → CategoryTheory.Limits.IsTerminal Y → Unique (X ≅ Y) :=
  by sorry

--Result: success
--Time: 6.34 s
/--The complement of the union of two sets is the intersection of their complements.-/
theorem t17 : ∀ {α : Type u} (s t : Set α), (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  by sorry

--Result: success
--Time: 8.68 s
/--The sum of the cubes of two positive integers is never equal to the cube of a third integer.-/
theorem t18 : ∀ {a b c : ℕ}, a > 0 → b > 0 → a ^ 3 + b ^ 3 ≠ c ^ 3 :=
  by sorry

--Result: success
--Time: 12.84 s
/--If every element of a group `G` has order `2`, then every pair of elements of `G` commutes.-/
theorem t19 : ∀ {G : Type u_1} [inst : Group G], (∀ (g : G), g ^ 2 = 1) → ∀ (a b : G), a * b = b * a :=
  by sorry

--Result: success
--Time: 5.07 s
/--The product of two consecutive natural numbers is even.-/
theorem t20 : ∀ (n : ℕ), Even (n * (n + 1)) :=
  by sorry

--Result: success
--Time: 7.19 s
/--Every index 2 subgroup of a group is normal.-/
theorem t21 : ∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, H.index = 2 → H.Normal :=
  by sorry

--Result: success
--Time: 6.59 s
/--Every free group is torsion free.-/
theorem t22 : ∀ {G : Type u_1} [inst : Group G] [IsFreeGroup G], Monoid.IsTorsionFree G :=
  by sorry

--Result: success
--Time: 7.59 s
/--Every natural number greater than `1` is divisible by a prime number.-/
theorem t23 : ∀ {n : ℕ}, n > 1 → ∃ p, Nat.Prime p ∧ p ∣ n :=
  by sorry

--Result: success
--Time: 7.17 s
/--A finite torsion-free group is trivial-/
theorem t24 : ∀ {G : Type u_1} [inst : Group G] [Fintype G], Monoid.IsTorsionFree G → Subsingleton G :=
  by sorry

--Result: success
--Time: 0.03 s
/--Every finite division ring is a field.-/
theorem t25 : (D : Type u_1) → [Finite D] → [inst : DivisionRing D] → Field D :=
  by sorry

--Result: success
--Time: 4.87 s
/--Every finite topological space is compact.-/
theorem t26 : ∀ {X : Type u} [inst : TopologicalSpace X] [Finite X], CompactSpace X :=
  by sorry

--Result: success
--Time: 14.53 s
/--Every surjective homomorphism from a finitely generated free group to itself is injective.-/
theorem t27 : ∀ {G : Type u_1} [inst : Group G] [inst_1 : IsFreeGroup G] [Finite (IsFreeGroup.Generators G)] (f : G →* G),
  Function.Surjective ⇑f → Function.Injective ⇑f :=
  by sorry

--Result: success
--Time: 6.40 s
/--Every positive even integer greater than $4$ can be written as the sum of two primes.-/
theorem t28 : ∀ (n : ℕ), n > 4 ∧ n % 2 = 0 → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q :=
  by sorry

--Result: success
--Time: 9.35 s
/--Every matrix satisfies its own characteristic polynomial.-/
theorem t29 : ∀ {R : Type u_1} [inst : CommRing R] {n : Type u_4} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),
  (Polynomial.aeval M) M.charpoly = 0 :=
  by sorry

--Result: success
--Time: 5.34 s
/--The square root of an irrational number is irrational.-/
theorem t30 : ∀ {x : ℝ}, Irrational x → Irrational √x :=
  by sorry

--Result: success
--Time: 5.71 s
/--If the square of a number is even, the number itself is even.-/
theorem t31 : ∀ {n : ℤ}, Even (n ^ 2) → Even n :=
  by sorry

--Result: success
--Time: 5.20 s
/--In a finite commutative ring, all prime ideals are maximal.-/
theorem t32 : ∀ {R : Type u_1} [inst : CommRing R] [Finite R] {I : Ideal R}, I.IsPrime → I.IsMaximal :=
  by sorry

--Result: success
--Time: 6.78 s
/--A topological space $X$ is Hausdorff if and only if the diagonal is a closed set in $X × X$.-/
theorem t33 : ∀ {X : Type u_1} [inst : TopologicalSpace X], T2Space X ↔ IsClosed (Set.diagonal X) :=
  by sorry

--Result: success
--Time: 9.42 s
/--If every point of a subset of a topological space is contained in some open set, the subset itself is open.-/
theorem t34 : ∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, (∀ x ∈ s, ∃ t, IsOpen t ∧ x ∈ t ∧ t ⊆ s) → IsOpen s :=
  by sorry

--Result: success
--Time: 8.56 s
/--Every non-identity element of a free group is of infinite order.-/
theorem t35 : ∀ {G : Type u_1} [inst : Group G] [IsFreeGroup G] (g : G), g ≠ 1 → ¬IsOfFinOrder g :=
  by sorry

--Result: success
--Time: 9.98 s
/--An element of a discrete valuation ring is a unit if and only if it has a valuation of zero.-/
theorem t36 : ∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : CommRing R] [inst_1 : IsDomain R] [IsDiscreteValuationRing R]
  [inst_2 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀) {x : R}, IsUnit x ↔ v x = 0 :=
  by sorry

--Result: success
--Time: 6.66 s
/--For any two relatively prime positive integers $a$ and $b$, every sufficiently large natural number $N$ can be written as a linear combination $ax + by$ of $a$ and $b$, where both $x$ and $y$ are natural numbers.-/
theorem t37 : ∀ {a b : ℕ}, a.Coprime b → 0 < a → 0 < b → ∀ (N : ℕ), ∃ x y, N ≥ a * x + b * y :=
  by sorry

--Result: success
--Time: 5.79 s
/--Every field is a ring.-/
theorem t38 : (K : Type u) → [inst : Field K] → Ring K :=
  by sorry

--Result: success
--Time: 6.17 s
/--The set of units in a ring forms a group.-/
theorem t39 : {R : Type u} → [inst : Ring R] → Group Rˣ :=
  by sorry

--Result: success
--Time: 7.20 s
/--If the direct product of two groups is torsion free then each of the groups is torsion free.-/
theorem t40 : ∀ {G H : Type u_1} [inst : Group G] [inst_1 : Group H],
  Monoid.IsTorsionFree (G × H) → Monoid.IsTorsionFree G ∧ Monoid.IsTorsionFree H :=
  by sorry
