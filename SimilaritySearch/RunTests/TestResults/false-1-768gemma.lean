import Mathlib

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

open Nat

/-
  Translation of 40 statements from `data/false-prompts.txt`
  Using similarity search

  SUMMARY:

  Time:
  · Total time to translate 40 statements = 337.75 s
  · Avg time to translate one statement = 8.44 s

  Results:
  · Success = 35
    · Without error = 31
    · With error = 4
  · Fallback = 5
  · Failures = 0
-/


--Result: success
--Time: 9.44 s
/--Every ring is a field.-/
theorem t1 : ∀ (R : Type u_1) [inst : Ring R], IsField R :=
  by sorry

--Result: success
--Time: 9.33 s
/--Every vector space is finite dimensional.-/
theorem t2 : ∀ {K V : Type u} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V], FiniteDimensional K V :=
  by sorry

--Result: success
--Time: 8.25 s
/--Every group is a torsion monoid.-/
theorem t3 : ∀ {G : Type u_1} [inst : Group G], Monoid.IsTorsion G :=
  by sorry

--Result: success
--Time: 8.06 s
/--Every finite simple group has prime order.-/
theorem t4 : ∀ {G : Type u_1} [inst : Group G] [Finite G] [IsSimpleGroup G], Nat.Prime (Nat.card G) :=
  by sorry

--Result: success
--Time: 7.46 s
/--Every finite group is simple.-/
theorem t5 : ∀ {G : Type u_1} [inst : Group G] [Fintype G], IsSimpleGroup G :=
  by sorry

--Result: fallback
--Time: 7.81 s
/--Every finite group has prime order.-/
theorem t6 : ∀ {G : Type u_1} [inst : Group G] [Fintype G], IsPrime (Fintype.card G) :=
  by sorry

--Result: success
--Time: 5.91 s
/--Every set has Lebesgue measure zero.-/
theorem t7 : ∀ (s : Set ℝ), MeasureTheory.volume s = 0 :=
  by sorry

--Result: success
--Time: 6.93 s
/--If a topological space is compact, then every subset is compact.-/
theorem t8 : ∀ {X : Type u_1} [inst : TopologicalSpace X], CompactSpace X → ∀ (s : Set X), IsCompact s :=
  by sorry

--Result: fallback
--Time: 17.70 s
/--Every set that is Lebesgue measurable but not Borel measurable has Lebesgue measure zero.-/
theorem t9 : ∀ {α : Type u_1} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] (s : Set α),
  MeasurableSet s ∧ ¬MeasurableSet[BorelSpace.toMeasurableSpace α] s → MeasureTheory.volume s = 0 :=
  by sorry

--Result: success
--Time: 8.46 s
/--A finitely-presented group containing a torsion element is finite.-/
theorem t10 : ∀ {G : Type u_1} [inst : Group G] [Group.FG G], (∃ g, g ≠ 1 ∧ ∃ n, 0 < n ∧ g ^ n = 1) → Finite G :=
  by sorry

--Result: success
--Time: 10.45 s
/--If every point of a subset of a topological space is contained in some closed set, the subset itself is closed.-/
theorem t11 : ∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, (∀ x ∈ s, ∃ C, IsClosed C ∧ x ∈ C) → IsClosed s :=
  by sorry

--Result: success
--Time: 11.96 s
/--A topological space $X$ is Hausdorff if and only if the diagonal map is an open map from $X$ to $X × X$.-/
theorem t12 : ∀ {X : Type u_1} [inst : TopologicalSpace X], T2Space X ↔ IsOpenMap fun x => (x, x) :=
  by sorry

--Result: success
--Time: 8.50 s
/--Any finite order element in a group is equal to the identity.-/
theorem t13 : ∀ {G : Type u} [inst : Group G] {g : G}, (∃ n, 0 < n ∧ g ^ n = 1) → g = 1 :=
  by sorry

--Result: success
--Time: 8.13 s
/--If a subgroup of a group is torsion-free, then the group itself is torsion free.-/
theorem t14 : ∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), Monoid.IsTorsionFree ↥H → Monoid.IsTorsionFree G :=
  by sorry

--Result: fallback
--Time: 8.11 s
/--Every injective homomorphism from a finitely generated free group to itself is surjective.-/
theorem t15 : ∀ {G : Type u_1} [inst : Group G] [FinitelyGenerated G] (f : G →* G), Function.Injective f → Function.Surjective f :=
  by sorry

--Result: success
--Time: 8.36 s
/--Every division ring is either a field or finite.-/
theorem t16 : ∀ {K : Type u} [inst : DivisionRing K], IsField K ∨ Finite K :=
  by sorry

--Result: success
--Time: 6.36 s
/--Every natural number is the product of two primes.-/
theorem t17 : ∀ (n : ℕ), ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q :=
  by sorry

--Result: success
--Time: 6.72 s
/--Every even number is the square of a natural number.-/
theorem t18 : ∀ (n : ℕ), Even n → ∃ m, n = m ^ 2 :=
  by sorry

--Result: success
--Time: 7.30 s
/--Every normal subgroup of a group has finite index.-/
theorem t19 : ∀ {G : Type u_1} [inst : Group G] (N : Subgroup G), N.Normal → N.FiniteIndex :=
  by sorry

--Result: success
--Time: 8.92 s
/--The characteristic polynomial of every matrix has real roots.-/
theorem t20 : ∀ {n : Type u} [inst : Fintype n] [inst_1 : DecidableEq n] (M : Matrix n n ℝ) (x : ℝ), x ∈ M.charpoly.roots.toFinset :=
  by sorry

--Result: success
--Time: 11.12 s
/--In a commutative ring, every prime ideal is contained in a unique maximal ideal.-/
theorem t21 : ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R) [P.IsPrime], ∃! M, M.IsMaximal ∧ P ≤ M :=
  by sorry

--Result: success
--Time: 0.68 s
/--Every continuous function is uniformly continuous.-/
theorem t22 : ∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : UniformSpace β] (f : α → β),
  Continuous f → UniformContinuous f :=
  by sorry

--Result: fallback
--Time: 10.17 s
/--Every uniformly continuous function is bounded above.-/
theorem t23 : ∀ {α : Type u} {β : Type v} [PseudoMetricSpace α] [PseudoMetricSpace β] {f : α → β},
  UniformContinuous f → BddAbove (Set.range f) :=
  by sorry

--Result: success
--Time: 8.62 s
/--If every compact subset of a topological space is closed, then the space is compact.-/
theorem t24 : ∀ {X : Type u} [inst : TopologicalSpace X], (∀ {K : Set X}, IsCompact K → IsClosed K) → CompactSpace X :=
  by sorry

--Result: success
--Time: 9.10 s
/--In a commutative ring, the sum of idempotent elements is idempotent.-/
theorem t25 : ∀ {R : Type u} [inst : CommRing R] {a b : R}, IsIdempotentElem a → IsIdempotentElem b → IsIdempotentElem (a + b) :=
  by sorry

--Result: fallback
--Time: 14.74 s
/--The number of partitions of a finite set is a prime number.-/
theorem t26 : ∀ {α : Type u_1} [Fintype α] [DecidableEq α], Nat.Prime (Fintype.card (Setoid α)) :=
  by sorry

--Result: success
--Time: 6.61 s
/--If a poset has a maximal element, then it has a unique minimal element.-/
theorem t27 : ∀ {α : Type u} [inst : PartialOrder α] [OrderTop α], ∃! m, ∀ (x : α), m ≤ x :=
  by sorry

--Result: success
--Time: 6.79 s
/--The automorphism group of an Abelian group is cyclic.-/
theorem t28 : ∀ (G : Type u_1) [inst : AddCommGroup G], IsCyclic (AddAut G) :=
  by sorry

--Result: success
--Time: 12.01 s
/--If a function from the unit interval to itself has a fixed point, then it has points of all positive periods.-/
theorem t29 : ∀ {f : ℝ → ℝ},
  (∃ x ∈ Set.Icc 0 1, Function.IsFixedPt f x) → ∀ (n : ℕ), 0 < n → ∃ x ∈ Set.Icc 0 1, Function.IsPeriodicPt f n x :=
  by sorry

--Result: success
--Time: 9.41 s
/--The complement of the union of two sets contains the union of their complements.-/
theorem t30 : ∀ {α : Type u_1} (s t : Set α), (s ∪ t)ᶜ ⊇ sᶜ ∪ tᶜ :=
  by sorry

--Result: success
--Time: 7.02 s
/--The square root of an rational number is rational.-/
theorem t31 : ∀ (a : ℚ), ∃ b, b ^ 2 = a :=
  by sorry

--Result: success
--Time: 7.96 s
/--If a module over a ring is free, then the ring is commutative.-/
theorem t32 : {R : Type u} →
  {M : Type v} → [inst : Ring R] → [inst_1 : AddCommMonoid M] → [inst_2 : Module R M] → [Module.Free R M] → CommRing R :=
  by sorry

--Result: success
--Time: 6.98 s
/--If the set of units of a ring forms a group then the ring is commutative.-/
theorem t33 : {R : Type u_1} → [inst : Ring R] → Group Rˣ → CommRing R :=
  by sorry

--Result: success
--Time: 6.84 s
/--Every natural number larger than `10` is the sum of a square and a prime.-/
theorem t34 : ∀ {n : ℕ}, n > 10 → ∃ a p, Nat.Prime p ∧ n = a ^ 2 + p :=
  by sorry

--Result: success
--Time: 7.90 s
/--The initial object of a category is isomorphic to its terminal object.-/
theorem t35 : {C : Type u} →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasInitial C] → [inst_2 : CategoryTheory.Limits.HasTerminal C] → ⊥_ C ≅ ⊤_ C :=
  by sorry

--Result: success
--Time: 8.21 s
/--If the composition of two functions is continuous, then each of them is continuous.-/
theorem t36 : ∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  [inst_2 : TopologicalSpace Z] {f : X → Y} {g : Y → Z}, Continuous (g ∘ f) → Continuous f ∧ Continuous g :=
  by sorry

--Result: success
--Time: 7.80 s
/--If `a` commutes with `b` and `b` commutes with `c` then `a` commutes with `c`.-/
theorem t37 : ∀ {S : Type u_3} [inst : Mul S] {a b c : S}, Commute a b → Commute b c → Commute a c :=
  by sorry

--Result: success
--Time: 9.22 s
/--If an element maps to zero under a ring homomorphism, then it is zero.-/
theorem t38 : ∀ {R : Type u_1} {S : Type u_2} [inst : NonAssocSemiring R] [inst_1 : NonAssocSemiring S] (f : R →+* S) {x : R},
  f x = 0 → x = 0 :=
  by sorry

--Result: success
--Time: 5.24 s
/--Implication `→` is symmetric. If `P → Q` then `Q → P`.-/
theorem t39 : ∀ {P Q : Prop}, (P → Q) → Q → P :=
  by sorry

--Result: success
--Time: 7.17 s
/--Two natural numbers are equal if and only if they are both divisible by some prime number.-/
theorem t40 : ∀ {m n : ℕ}, (∃ p, Nat.Prime p ∧ p ∣ m ∧ p ∣ n) ↔ m = n :=
  by sorry
