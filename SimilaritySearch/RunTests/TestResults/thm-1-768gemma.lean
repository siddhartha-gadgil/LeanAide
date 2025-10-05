import Mathlib

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

open Nat

/-
  Translation of 40 statements from `data/thm-prompts.txt`
  Using similarity search

  SUMMARY:

  Time:
  · Total time to translate 40 statements = 275.57 s
  · Avg time to translate one statement = 6.89 s

  Results:
  · Success = 37
    · Without error = 31
    · With error = 6
  · Fallback = 3
  · Failures = 0
-/

--Result: success
--Time: 8.75 s
/--If every proper closed subset of a topological space is compact, then the space itself is compact.-/
theorem t1 : ∀ {X : Type u_1} [inst : TopologicalSpace X], (∀ (s : Set X), IsClosed s → s ≠ Set.univ → IsCompact s) → CompactSpace X :=
  by sorry

--Result: success
--Time: 7.16 s
/--Every prime that is `1` greater than a multiple of `4` can be expressed as the sum of two squares.-/
theorem t2 : ∀ {p : ℕ}, Nat.Prime p → p % 4 = 1 → ∃ a b, a ^ 2 + b ^ 2 = p :=
  by sorry

--Result: success
--Time: 7.23 s
/--The product of two numbers, each of which is the sum of four squares, is itself a sum of four squares.-/
theorem t3 : ∀ {a b w x y z : ℕ}, a = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 → ∃ p q r s, a * b = p ^ 2 + q ^ 2 + r ^ 2 + s ^ 2 :=
  by sorry

--Result: success
--Time: 9.96 s
/--A ring with all elements idempotent is commutative.-/
theorem t4 : ∀ {R : Type u} [inst : Ring R], (∀ (a : R), a * a = a) → ∀ (a b : R), a * b = b * a :=
  by sorry

--Result: success
--Time: 6.42 s
/--There are infinitely many pairs of primes that differ exactly by `2`.-/
theorem t5 : {p | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite :=
  by sorry

--Result: success
--Time: 6.06 s
/--Every finite division ring is a field.-/
theorem t6 : ∀ {D : Type u} [inst : DivisionRing D] [inst_1 : Fintype D], IsField D :=
  by sorry

--Result: success
--Time: 7.47 s
/--If each of two types can be mapped injectively into the other, then there is a bijection between them.-/
theorem t7 : ∀ {α : Type u_1} {β : Type u_2}, (∃ f, Function.Injective f) → (∃ g, Function.Injective g) → Nonempty (α ≃ β) :=
  by sorry

--Result: success
--Time: 8.52 s
/--A finite graph in which every pair of vertices have precisely one common neighbour contains a vertex that is adjacent to all other vertices.-/
theorem t8 : ∀ {V : Type u} (G : SimpleGraph V) [Fintype V], ∃ v, ∀ (w : V), v ≠ w → G.Adj v w :=
  by sorry

--Result: success
--Time: 7.16 s
/--The number of partitions with odd parts is equal to the number of partitions with distinct parts.-/
theorem t9 : ∀ (n : ℕ), Fintype.card { p // ∀ part ∈ p.parts, Odd part } = Fintype.card { p // p.parts.Nodup } :=
  by sorry

--Result: success
--Time: 7.00 s
/--Every non-empty poset in which every chain has an upper bound contains a maximal element.-/
theorem t10 : ∀ {α : Type u} [inst : PartialOrder α] [Nonempty α],
  (∀ (c : Set α), IsChain (fun x1 x2 => x1 ≤ x2) c → c.Nonempty → ∃ ub, ∀ a ∈ c, a ≤ ub) → ∃ m, ∀ (a : α), m ≤ a → a = m :=
  by sorry

--Result: success
--Time: 7.22 s
/--A group whose automorphism group is cyclic is Abelian.-/
theorem t11 : {G : Type u_1} → [inst : Group G] → IsCyclic (G ≃* G) → CommGroup G :=
  by sorry

--Result: success
--Time: 9.42 s
/--A uniformly continuous function of a uniformly continuous function is uniformly continuous.-/
theorem t12 : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : UniformSpace α] [inst_1 : UniformSpace β]
  [inst_2 : UniformSpace γ] {f : α → β} {g : β → γ},
  UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f) :=
  by sorry

--Result: success
--Time: 0.03 s
/--A uniformly continuous function of a uniformly continuous function is uniformly continuous.-/
theorem t13 : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : UniformSpace α] [inst_1 : UniformSpace β]
  [inst_2 : UniformSpace γ] {f : α → β} {g : β → γ},
  UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f) :=
  by sorry

--Result: success
--Time: 8.54 s
/--A topological space is normal if and only if any two disjoint closed subsets can be separated by a continuous function.-/
theorem t14 : ∀ {X : Type u} [inst : TopologicalSpace X],
  NormalSpace X ↔ ∀ (s t : Set X), IsClosed s → IsClosed t → Disjoint s t → ∃ f, ∀ x ∈ s, f x = 0 ∧ x ∈ t → f x = 1 :=
  by sorry

--Result: success
--Time: 6.94 s
/--If a function from the unit interval to itself has a point of period three, then it has points of all positive periods.-/
theorem t15 : ∀ {f : ℝ → ℝ} {x : ℝ},
  (∀ (x : ℝ), 0 ≤ x ∧ x ≤ 1 → 0 ≤ f x ∧ f x ≤ 1) →
    Function.IsPeriodicPt f 3 x → ∀ (n : ℕ), 0 < n → ∃ y, Function.IsPeriodicPt f n y :=
  by sorry

--Result: fallback
--Time: 10.07 s
/--A terminal object in a category is unique up to unique isomorphism.-/
theorem t16 : ∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C} (hX : CategoryTheory.Limits.IsTerminal X)
  (hY : CategoryTheory.Limits.IsTerminal Y), X ≅ Y :=
  by sorry

--Result: success
--Time: 6.61 s
/--The complement of the union of two sets is the intersection of their complements.-/
theorem t17 : ∀ {α : Type u_1} (s t : Set α), (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  by sorry

--Result: success
--Time: 6.84 s
/--The sum of the cubes of two positive integers is never equal to the cube of a third integer.-/
theorem t18 : ∀ (a b c : ℕ), a > 0 → b > 0 → a ^ 3 + b ^ 3 ≠ c ^ 3 :=
  by sorry

--Result: success
--Time: 9.26 s
/--If every element of a group `G` has order `2`, then every pair of elements of `G` commutes.-/
theorem t19 : ∀ {G : Type u_1} [inst : Group G], (∀ (x : G), x ^ 2 = 1) → ∀ (x y : G), x * y = y * x :=
  by sorry

--Result: success
--Time: 6.57 s
/--The product of two consecutive natural numbers is even.-/
theorem t20 : ∀ (n : ℕ), Even (n * (n + 1)) :=
  by sorry

--Result: success
--Time: 5.70 s
/--Every index 2 subgroup of a group is normal.-/
theorem t21 : ∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), H.index = 2 → H.Normal :=
  by sorry

--Result: success
--Time: 6.67 s
/--Every free group is torsion free.-/
theorem t22 : ∀ {G : Type u_1} [inst : Group G] [IsFreeGroup G], Monoid.IsTorsionFree G :=
  by sorry

--Result: success
--Time: 7.21 s
/--Every natural number greater than `1` is divisible by a prime number.-/
theorem t23 : ∀ {n : ℕ}, 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n :=
  by sorry

--Result: success
--Time: 5.23 s
/--A finite torsion-free group is trivial-/
theorem t24 : ∀ {G : Type u_1} [inst : Group G] [hF : Fintype G], Monoid.IsTorsionFree G → Subsingleton G :=
  by sorry

--Result: success
--Time: 0.04 s
/--Every finite division ring is a field.-/
theorem t25 : ∀ {D : Type u} [inst : DivisionRing D] [inst_1 : Fintype D], IsField D :=
  by sorry

--Result: success
--Time: 5.59 s
/--Every finite topological space is compact.-/
theorem t26 : ∀ {X : Type u} [inst : TopologicalSpace X] [Finite X], CompactSpace X :=
  by sorry

--Result: success
--Time: 7.42 s
/--Every surjective homomorphism from a finitely generated free group to itself is injective.-/
theorem t27 : ∀ {G : Type u} [inst : Group G] {n : ℕ} (f : FreeGroup (Fin n) →* G), Function.Surjective ⇑f → Function.Injective ⇑f :=
  by sorry

--Result: success
--Time: 6.24 s
/--Every positive even integer greater than $4$ can be written as the sum of two primes.-/
theorem t28 : ∀ {n : ℕ}, 4 < n → Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q :=
  by sorry

--Result: fallback
--Time: 10.43 s
/--Every matrix satisfies its own characteristic polynomial.-/
theorem t29 : ∀ {R : Type u} [inst : CommRing R] {n : Type u_1} [inst_1 : Fintype n] [inst_2 : DecidableEq n] (A : Matrix n n R),
  Aeval (Matrix.charpoly A) A = 0 :=
  by sorry

--Result: success
--Time: 5.34 s
/--The square root of an irrational number is irrational.-/
theorem t30 : ∀ {x : ℝ}, Irrational x → Irrational √x :=
  by sorry

--Result: success
--Time: 5.80 s
/--If the square of a number is even, the number itself is even.-/
theorem t31 : ∀ {n : ℕ}, Even (n ^ 2) → Even n :=
  by sorry

--Result: success
--Time: 6.70 s
/--In a finite commutative ring, all prime ideals are maximal.-/
theorem t32 : ∀ {R : Type u_1} [inst : CommRing R] [inst_1 : Fintype R] (P : Ideal R), P.IsPrime → P.IsMaximal :=
  by sorry

--Result: success
--Time: 6.09 s
/--A topological space $X$ is Hausdorff if and only if the diagonal is a closed set in $X × X$.-/
theorem t33 : ∀ {X : Type u_1} [inst : TopologicalSpace X], T2Space X ↔ IsClosed (Set.diagonal X) :=
  by sorry

--Result: success
--Time: 9.07 s
/--If every point of a subset of a topological space is contained in some open set, the subset itself is open.-/
theorem t34 : ∀ {α : Type u_1} [inst : TopologicalSpace α] {s : Set α}, (∀ x ∈ s, ∃ U, IsOpen U ∧ x ∈ U) → IsOpen s :=
  by sorry

--Result: success
--Time: 5.02 s
/--Every non-identity element of a free group is of infinite order.-/
theorem t35 : ∀ {G : Type u_1} [inst : Group G] [IsFreeGroup G] {g : G}, g ≠ 1 → orderOf g = 0 :=
  by sorry

--Result: fallback
--Time: 6.85 s
/--An element of a discrete valuation ring is a unit if and only if it has a valuation of zero.-/
theorem t36 : ∀ {R : Type u_1} [inst : DiscreteValuationRing R] {x : R}, IsUnit x ↔ DiscreteValuationRing.valuation x = 0 :=
  by sorry

--Result: success
--Time: 6.52 s
/--For any two relatively prime positive integers $a$ and $b$, every sufficiently large natural number $N$ can be written as a linear combination $ax + by$ of $a$ and $b$, where both $x$ and $y$ are natural numbers.-/
theorem t37 : ∀ {a b : ℕ}, a.Coprime b → 0 < a → 0 < b → ∃ N, ∀ n ≥ N, ∃ x y, n = a * x + b * y :=
  by sorry

--Result: success
--Time: 6.11 s
/--Every field is a ring.-/
theorem t38 : (K : Type u) → [inst : Field K] → Ring K :=
  by sorry

--Result: success
--Time: 7.48 s
/--The set of units in a ring forms a group.-/
theorem t39 : {R : Type u_1} → [inst : Ring R] → Group Rˣ :=
  by sorry

--Result: success
--Time: 8.82 s
/--If the direct product of two groups is torsion free then each of the groups is torsion free.-/
theorem t40 : ∀ {G H : Type u_1} [inst : Group G] [inst_1 : Group H],
  Monoid.IsTorsionFree (G × H) → Monoid.IsTorsionFree G ∧ Monoid.IsTorsionFree H :=
  by sorry
