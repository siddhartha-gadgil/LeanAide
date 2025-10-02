import Mathlib

/-
  Translation of 40 statements from `data/thm-prompts.txt`
  Using similarity search

  SUMMARY:

  Time:
  · Total time to translate 40 statements = 217.21 s
  · Avg time to translate one statement = 5.43 s

  Results:
  · Success = 33
    · Without error = 30
    · With error = 3
  · Fallback = 7
  · Failures = 0
-/

--Result: success
--Time: 11.41 s
/--If every proper closed subset of a topological space is compact, then the space itself is compact.-/
theorem t1 : ∀ {X : Type u} [inst : TopologicalSpace X], (∀ (s : Set X), IsClosed s → s ≠ Set.univ → IsCompact s) → CompactSpace X :=
  by sorry

--Result: success
--Time: 6.60 s
/--Every prime that is `1` greater than a multiple of `4` can be expressed as the sum of two squares.-/
theorem t2 : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)], p % 4 = 1 → ∃ a b, a ^ 2 + b ^ 2 = p :=
  by sorry

--Result: success
--Time: 8.70 s
/--The product of two numbers, each of which is the sum of four squares, is itself a sum of four squares.-/
theorem t3 : ∀ {a b w x y z u v s t : ℤ},
  a = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 →
    b = u ^ 2 + v ^ 2 + s ^ 2 + t ^ 2 → ∃ r₁ r₂ r₃ r₄, a * b = r₁ ^ 2 + r₂ ^ 2 + r₃ ^ 2 + r₄ ^ 2 :=
  by sorry

--Result: success
--Time: 5.40 s
/--A ring with all elements idempotent is commutative.-/
theorem t4 : ∀ {R : Type u_1} [inst : Ring R], (∀ (a : R), a * a = a) → ∀ (x y : R), x * y = y * x :=
  by sorry

--Result: success
--Time: 4.48 s
/--There are infinitely many pairs of primes that differ exactly by `2`.-/
theorem t5 : {p | Nat.Prime p ∧ Nat.Prime (p + 2)}.Infinite :=
  by sorry

--Result: success
--Time: 5.87 s
/--Every finite division ring is a field.-/
theorem t6 : ∀ (D : Type u_1) [inst : DivisionRing D] [inst_1 : Finite D], IsField D :=
  by sorry

--Result: success (with error)
--Time: 6.03 s
/--If each of two types can be mapped injectively into the other, then there is a bijection between them.-/
theorem t7 : ∀ {α : Type u} {β : Type v} (a : α ↪ β) (a : β ↪ α), ∃ f, True :=
  by sorry

--Result: success
--Time: 5.87 s
/--A finite graph in which every pair of vertices have precisely one common neighbour contains a vertex that is adjacent to all other vertices.-/
theorem t8 : ∀ {V : Type u_1} [inst : Fintype V] {G : SimpleGraph V} [inst_1 : DecidableRel G.Adj],
  (∀ (v w : V), v ≠ w → Fintype.card ↑(G.commonNeighbors v w) = 1) → ∃ v, ∀ (w : V), v ≠ w → G.Adj v w :=
  by sorry

--Result: success (with error)
--Time: 6.87 s
/--The number of partitions with odd parts is equal to the number of partitions with distinct parts.-/
theorem t9 : ∀ (n : ℕ), {p | ∀ x ∈ p.parts, x % 2 = 1}.card = {p | p.parts.Nodup}.card :=
  by sorry

--Result: success
--Time: 4.60 s
/--Every non-empty poset in which every chain has an upper bound contains a maximal element.-/
theorem t10 : ∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Nonempty α],
  (∀ (c : Set α), IsChain (fun x x_1 => x ≤ x_1) c → c.Nonempty → BddAbove c) → ∃ m, ∀ (a : α), m ≤ a → a = m :=
  by sorry

--Result: fallback
--Time: 4.78 s
/--A group whose automorphism group is cyclic is Abelian.-/
theorem t11 : ∀ {G : Type u} [Group G], IsCyclic (Group.Aut G) → CommGroup G :=
  by sorry

--Result: success
--Time: 6.64 s
/--A uniformly continuous function of a uniformly continuous function is uniformly continuous.-/
theorem t12 : ∀ {α : Type u} {β : Type v} {γ : Type w} [inst : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]
  {f : β → γ} {g : α → β}, UniformContinuous f → UniformContinuous g → UniformContinuous (f ∘ g) :=
  by sorry

--Result: success
--Time: 0.05 s
/--A uniformly continuous function of a uniformly continuous function is uniformly continuous.-/
theorem t13 : ∀ {α : Type u} {β : Type v} {γ : Type w} [inst : UniformSpace α] [inst_1 : UniformSpace β] [inst_2 : UniformSpace γ]
  {f : β → γ} {g : α → β}, UniformContinuous f → UniformContinuous g → UniformContinuous (f ∘ g) :=
  by sorry

--Result: success (with error)
--Time: 8.09 s
/--A topological space is normal if and only if any two disjoint closed subsets can be separated by a continuous function.-/
theorem t14 : ∀ {X : Type u} [inst : TopologicalSpace X],
  NormalSpace X ↔
    ∀ (s t : Set X), IsClosed s → IsClosed t → Disjoint s t → ∃ f, Continuous f ∧ Set.EqOn f 0 s ∧ Set.EqOn f 1 t :=
  by sorry

--Result: success
--Time: 6.02 s
/--If a function from the unit interval to itself has a point of period three, then it has points of all positive periods.-/
theorem t15 : ∀ {α : Type u_1} (f : α → α), (∃ x, Function.IsPeriodicPt f 3 x) → ∀ (n : ℕ), 0 < n → ∃ y, Function.IsPeriodicPt f n y :=
  by sorry

--Result: fallback
--Time: 5.96 s
/--A terminal object in a category is unique up to unique isomorphism.-/
theorem t16 : ∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {X Y : C},
  CategoryTheory.Limits.IsTerminal X → CategoryTheory.Limits.IsTerminal Y → (X ≅ Y) :=
  by sorry

--Result: success
--Time: 4.79 s
/--The complement of the union of two sets is the intersection of their complements.-/
theorem t17 : ∀ {α : Type u_1} (s t : Set α), (s ∪ t)ᶜ = sᶜ ∩ tᶜ :=
  by sorry

--Result: success
--Time: 5.20 s
/--The sum of the cubes of two positive integers is never equal to the cube of a third integer.-/
theorem t18 : ∀ {x y z : ℕ}, x > 0 → y > 0 → ¬x ^ 3 + y ^ 3 = z ^ 3 :=
  by sorry

--Result: success
--Time: 13.23 s
/--If every element of a group `G` has order `2`, then every pair of elements of `G` commutes.-/
theorem t19 : ∀ {G : Type u_1} [inst : Group G], (∀ (x : G), x ^ 2 = 1) → ∀ (x y : G), x * y = y * x :=
  by sorry

--Result: success
--Time: 4.30 s
/--The product of two consecutive natural numbers is even.-/
theorem t20 : ∀ (n : ℕ), Even (n * (n + 1)) :=
  by sorry

--Result: success
--Time: 4.51 s
/--Every index 2 subgroup of a group is normal.-/
theorem t21 : ∀ {G : Type u_1} [inst : Group G] {H : Subgroup G}, H.index = 2 → H.Normal :=
  by sorry

--Result: success
--Time: 4.35 s
/--Every free group is torsion free.-/
theorem t22 : ∀ {G : Type u_1} [inst : Group G] [hF : IsFreeGroup G], Monoid.IsTorsionFree G :=
  by sorry

--Result: success
--Time: 4.28 s
/--Every natural number greater than `1` is divisible by a prime number.-/
theorem t23 : ∀ {n : ℕ}, 1 < n → ∃ p, Nat.Prime p ∧ p ∣ n :=
  by sorry

--Result: success
--Time: 5.65 s
/--A finite torsion-free group is trivial-/
theorem t24 : ∀ {G : Type u_1} [inst : Group G] [hF : Finite G], Monoid.IsTorsionFree G → Subsingleton G :=
  by sorry

--Result: success
--Time: 0.02 s
/--Every finite division ring is a field.-/
theorem t25 : ∀ (D : Type u_1) [inst : DivisionRing D] [inst_1 : Finite D], IsField D :=
  by sorry

--Result: success
--Time: 4.86 s
/--Every finite topological space is compact.-/
theorem t26 : ∀ {X : Type u} [inst : TopologicalSpace X] [inst_1 : Finite X], CompactSpace X :=
  by sorry

--Result: success
--Time: 6.98 s
/--Every surjective homomorphism from a finitely generated free group to itself is injective.-/
theorem t27 : ∀ {ι : Type u_1} [inst : Finite ι] (f : FreeGroup ι →* FreeGroup ι), Function.Surjective ⇑f → Function.Injective ⇑f :=
  by sorry

--Result: success
--Time: 3.66 s
/--Every positive even integer greater than $4$ can be written as the sum of two primes.-/
theorem t28 : ∀ (n : ℕ), 4 < n ∧ Even n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q :=
  by sorry

--Result: success
--Time: 4.54 s
/--Every matrix satisfies its own characteristic polynomial.-/
theorem t29 : ∀ {R : Type u} [inst : CommRing R] {n : Type v} [inst_1 : DecidableEq n] [inst_2 : Fintype n] (M : Matrix n n R),
  (Polynomial.aeval M) M.charpoly = 0 :=
  by sorry

--Result: success
--Time: 3.15 s
/--The square root of an irrational number is irrational.-/
theorem t30 : ∀ {x : ℝ}, Irrational x → Irrational √x :=
  by sorry

--Result: success
--Time: 3.84 s
/--If the square of a number is even, the number itself is even.-/
theorem t31 : ∀ {n : ℤ}, Even (n ^ 2) → Even n :=
  by sorry

--Result: success
--Time: 5.68 s
/--In a finite commutative ring, all prime ideals are maximal.-/
theorem t32 : ∀ {R : Type u} [inst : CommRing R] [inst_1 : Finite R] (P : Ideal R), P.IsPrime → P.IsMaximal :=
  by sorry

--Result: success
--Time: 4.88 s
/--A topological space $X$ is Hausdorff if and only if the diagonal is a closed set in $X × X$.-/
theorem t33 : ∀ {X : Type u} [inst : TopologicalSpace X], T2Space X ↔ IsClosed (Set.diagonal X) :=
  by sorry

--Result: success
--Time: 4.34 s
/--If every point of a subset of a topological space is contained in some open set, the subset itself is open.-/
theorem t34 : ∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, (∀ x ∈ s, ∃ U, IsOpen U ∧ x ∈ U) → IsOpen s :=
  by sorry

--Result: fallback
--Time: 5.04 s
/--Every non-identity element of a free group is of infinite order.-/
theorem t35 : ∀ {G : Type u_1} [inst : Group G] [inst_1 : IsFreeGroup G] {x : G}, x ≠ 1 → orderOf x = ⊤ :=
  by sorry

--Result: fallback
--Time: 8.05 s
/--An element of a discrete valuation ring is a unit if and only if it has a valuation of zero.-/
theorem t36 : ∀ {R : Type u} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : DiscreteValuationRing R]
  (v : Valuation R (ValuationRing.ValueGroup R)) (x : R), IsUnit x ↔ v x = 0 :=
  by sorry

--Result: fallback
--Time: 5.22 s
/--For any two relatively prime positive integers $a$ and $b$, every sufficiently large natural number $N$ can be written as a linear combination $ax + by$ of $a$ and $b$, where both $x$ and $y$ are natural numbers.-/
theorem t37 : ∀ {a b : ℕ}, Nat.coprime a b → ∃ M, ∀ N, N ≥ M → ∃ x y : ℕ, N = a * x + b * y :=
  by sorry

--Result: fallback
--Time: 3.49 s
/--Every field is a ring.-/
theorem t38 : ∀ (K : Type u) [inst : Field K], Ring K :=
  by sorry

--Result: fallback
--Time: 4.18 s
/--The set of units in a ring forms a group.-/
theorem t39 : {R : Type u} → [inst : Ring R] → Group Rˣ :=
  by sorry

--Result: success
--Time: 5.58 s
/--If the direct product of two groups is torsion free then each of the groups is torsion free.-/
theorem t40 : ∀ {G H : Type u_1} [inst : Group G] [inst_1 : Group H],
  Monoid.IsTorsionFree (G × H) → Monoid.IsTorsionFree G ∧ Monoid.IsTorsionFree H :=
  by sorry
