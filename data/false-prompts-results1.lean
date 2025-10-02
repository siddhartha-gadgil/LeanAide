import Mathlib

/-
  Translation of 40 statements from `data/false-prompts.txt`
  Using similarity search

  SUMMARY:

  Time:
  · Total time to translate 40 statements = 318.60 s
  · Avg time to translate one statement = 7.97 s

  Results:
  · Success = 32
    · Without error = 31
    · With error = 1
  · Fallback = 8
  · Failures = 0
-/

--Result: success
--Time: 14.63 s
/--Every ring is a field.-/
theorem t1 : ∀ (R : Type u) [inst : Ring R], IsField R :=
  by sorry

--Result: success
--Time: 16.50 s
/--Every vector space is finite dimensional.-/
theorem t2 : ∀ {K : Type u} {V : Type v} [inst : DivisionRing K] [inst_1 : AddCommGroup V] [inst_2 : Module K V],
  FiniteDimensional K V :=
  by sorry

--Result: success
--Time: 7.45 s
/--Every group is a torsion monoid.-/
theorem t3 : ∀ {G : Type u_1} [inst : Group G], Monoid.IsTorsion G :=
  by sorry

--Result: success
--Time: 10.67 s
/--Every finite simple group has prime order.-/
theorem t4 : ∀ {G : Type u} [inst : Group G] [inst_1 : Fintype G], IsSimpleGroup G → ∃ p, Nat.Prime p ∧ Fintype.card G = p :=
  by sorry

--Result: success
--Time: 9.87 s
/--Every finite group is simple.-/
theorem t5 : ∀ {G : Type u} [inst : Group G] [inst_1 : Fintype G], IsSimpleGroup G :=
  by sorry

--Result: success
--Time: 10.30 s
/--Every finite group has prime order.-/
theorem t6 : ∀ {G : Type u} [inst : Group G] [inst_1 : Fintype G], ∃ p, Nat.Prime p ∧ Fintype.card G = p :=
  by sorry

--Result: fallback
--Time: 8.00 s
/--Every set has Lebesgue measure zero.-/
theorem t7 : ∀ {α : Type u_1} [inst : MeasurableSpace α]
  [inst_1 : MeasureTheory.IsFiniteMeasure (MeasureTheory.volume : MeasureTheory.Measure α)] (s : Set α),
  ↑↑MeasureTheory.volume s = 0 :=
  by sorry

--Result: success
--Time: 9.22 s
/--If a topological space is compact, then every subset is compact.-/
theorem t8 : ∀ {X : Type u} [inst : TopologicalSpace X] [inst_1 : CompactSpace X] {s : Set X}, IsCompact s :=
  by sorry

--Result: fallback
--Time: 13.62 s
/--Every set that is Lebesgue measurable but not Borel measurable has Lebesgue measure zero.-/
theorem t9 : ∀ {α : Type u_1} [inst : MeasurableSpace α] [inst_1 : TopologicalSpace α] {μ : MeasureTheory.Measure α}
  [inst_2 : MeasureTheory.Measure.IsOpenPosMeasure μ] [inst_3 : BorelSpace α] (s : Set α),
  MeasureTheory.Measure.IsComplete μ → MeasurableSet s ∧ ¬MeasurableSet[MeasureTheory.borel α] s → ↑↑μ s = 0 :=
  by sorry

--Result: fallback
--Time: 14.56 s
/--A finitely-presented group containing a torsion element is finite.-/
theorem t10 : ∀ {G : Type u_1} [inst : Group G] [h : Group.FinitelyPresented G],
  (∃ g : G, g ≠ 1 ∧ ∃ n : ℕ, 0 < n ∧ g ^ n = 1) → Fintype G :=
  by sorry

--Result: success
--Time: 11.77 s
/--If every point of a subset of a topological space is contained in some closed set, the subset itself is closed.-/
theorem t11 : ∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, (∀ x ∈ s, ∃ t, IsClosed t ∧ x ∈ t ∧ t ⊆ s) → IsClosed s :=
  by sorry

--Result: success (with error)
--Time: 21.90 s
/--A topological space $X$ is Hausdorff if and only if the diagonal map is an open map from $X$ to $X × X$.-/
theorem t12 : ∀ {X : Type u_1} [inst : TopologicalSpace X], T2Space X ↔ IsOpenMap fun x => (x, x) :=
  by sorry

--Result: success
--Time: 11.35 s
/--Any finite order element in a group is equal to the identity.-/
theorem t13 : ∀ {G : Type u_1} [inst : Group G] {x : G}, IsOfFinOrder x → x = 1 :=
  by sorry

--Result: success
--Time: 21.18 s
/--If a subgroup of a group is torsion-free, then the group itself is torsion free.-/
theorem t14 : ∀ {G : Type u_1} [inst : Group G], (∀ (H : Subgroup G), Monoid.IsTorsionFree ↥H) → Monoid.IsTorsionFree G :=
  by sorry

--Result: success
--Time: 9.72 s
/--Every injective homomorphism from a finitely generated free group to itself is surjective.-/
theorem t15 : ∀ {G : Type u_1} [inst : Group G] [inst_1 : IsFreeGroup G] [inst_2 : Group.FG G] (f : G →* G),
  Function.Injective ⇑f → Function.Surjective ⇑f :=
  by sorry

--Result: success
--Time: 5.03 s
/--Every division ring is either a field or finite.-/
theorem t16 : ∀ (D : Type u_1) [inst : DivisionRing D], IsField D ∨ ¬Finite D :=
  by sorry

--Result: success
--Time: 7.34 s
/--Every natural number is the product of two primes.-/
theorem t17 : ∀ (n : ℕ), ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q :=
  by sorry

--Result: success
--Time: 6.62 s
/--Every even number is the square of a natural number.-/
theorem t18 : ∀ {n : ℕ}, Even n → ∃ m, n = m ^ 2 :=
  by sorry

--Result: success
--Time: 3.75 s
/--Every normal subgroup of a group has finite index.-/
theorem t19 : ∀ {G : Type u_1} [inst : Group G] {N : Subgroup G} [nN : N.Normal], N.FiniteIndex :=
  by sorry

--Result: success
--Time: 4.36 s
/--The characteristic polynomial of every matrix has real roots.-/
theorem t20 : ∀ {R : Type u} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : Algebra R ℝ] {n : Type v} [inst_3 : DecidableEq n]
  [inst_4 : Fintype n] (M : Matrix n n R), Polynomial.Splits (algebraMap R ℝ) M.charpoly :=
  by sorry

--Result: success
--Time: 3.84 s
/--In a commutative ring, every prime ideal is contained in a unique maximal ideal.-/
theorem t21 : ∀ {R : Type u} [inst : CommRing R] {P : Ideal R} [hP : P.IsPrime], ∃! M, M.IsMaximal ∧ P ≤ M :=
  by sorry

--Result: success
--Time: 0.21 s
/--Every continuous function is uniformly continuous.-/
theorem t22 : ∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},
  Continuous f → UniformContinuous f :=
  by sorry

--Result: fallback
--Time: 8.40 s
/--Every uniformly continuous function is bounded above.-/
theorem t23 : ∀ {α : Type u_1} {β : Type u_2} [inst : UniformSpace α] [inst_1 : MetricSpace β] {f : α → β},
  UniformContinuous f → BddAbove (Set.range f) :=
  by sorry

--Result: success
--Time: 4.62 s
/--If every compact subset of a topological space is closed, then the space is compact.-/
theorem t24 : ∀ {X : Type u} [inst : TopologicalSpace X], (∀ (s : Set X), IsCompact s → IsClosed s) → CompactSpace X :=
  by sorry

--Result: success
--Time: 6.42 s
/--In a commutative ring, the sum of idempotent elements is idempotent.-/
theorem t25 : ∀ {R : Type u_1} [inst : CommRing R] {a b : R}, IsIdempotentElem a → IsIdempotentElem b → IsIdempotentElem (a + b) :=
  by sorry

--Result: fallback
--Time: 6.35 s
/--The number of partitions of a finite set is a prime number.-/
theorem t26 : ∀ {α : Type u} [Fintype α], Nat.Prime (Fintype.card (Set.Partition α)) :=
  by sorry

--Result: success
--Time: 4.03 s
/--If a poset has a maximal element, then it has a unique minimal element.-/
theorem t27 : ∀ {α : Type u} [inst : PartialOrder α], (∃ m, ∀ (a : α), m ≤ a → a = m) → ∃! b, ∀ (a : α), b ≤ a :=
  by sorry

--Result: success
--Time: 3.25 s
/--The automorphism group of an Abelian group is cyclic.-/
theorem t28 : ∀ {G : Type u} [inst : CommGroup G], IsCyclic (G ≃* G) :=
  by sorry

--Result: success
--Time: 7.18 s
/--If a function from the unit interval to itself has a fixed point, then it has points of all positive periods.-/
theorem t29 : ∀ {f : ℝ → ℝ},
  (∀ x ∈ Set.Icc 0 1, f x ∈ Set.Icc 0 1) →
    (∃ x ∈ Set.Icc 0 1, f x = x) → ∀ n > 0, ∃ x ∈ Set.Icc 0 1, Function.IsPeriodicPt f n x :=
  by sorry

--Result: success
--Time: 3.82 s
/--The complement of the union of two sets contains the union of their complements.-/
theorem t30 : ∀ {α : Type u_1} (s t : Set α), (s ∪ t)ᶜ ⊇ sᶜ ∪ tᶜ :=
  by sorry

--Result: success
--Time: 4.36 s
/--The square root of an rational number is rational.-/
theorem t31 : ∀ {q : ℚ}, ∃ r, r * r = q → ↑r = √↑q :=
  by sorry

--Result: fallback
--Time: 6.40 s
/--If a module over a ring is free, then the ring is commutative.-/
theorem t32 : ∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : Module R M] [inst_3 : Module.Free R M],
  CommRing R :=
  by sorry

--Result: fallback
--Time: 4.95 s
/--If the set of units of a ring forms a group then the ring is commutative.-/
theorem t33 : ∀ {R : Type u_1} [inst : Ring R], Group Rˣ → CommRing R :=
  by sorry

--Result: success
--Time: 5.50 s
/--Every natural number larger than `10` is the sum of a square and a prime.-/
theorem t34 : ∀ {n : ℕ}, 10 < n → ∃ a p, Nat.Prime p ∧ a ^ 2 + p = n :=
  by sorry

--Result: fallback
--Time: 8.69 s
/--The initial object of a category is isomorphic to its terminal object.-/
theorem t35 : ∀ {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Limits.HasInitial C]
  [inst_2 : CategoryTheory.Limits.HasTerminal C], (⊥_ C ≅ ⊤_ C) :=
  by sorry

--Result: success
--Time: 5.30 s
/--If the composition of two functions is continuous, then each of them is continuous.-/
theorem t36 : ∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  [inst_2 : TopologicalSpace Z] {f : X → Y} {g : Y → Z}, Continuous (g ∘ f) → Continuous f ∧ Continuous g :=
  by sorry

--Result: success
--Time: 4.37 s
/--If `a` commutes with `b` and `b` commutes with `c` then `a` commutes with `c`.-/
theorem t37 : ∀ {S : Type u_2} [inst : Semigroup S] {a b c : S}, Commute a b → Commute b c → Commute a c :=
  by sorry

--Result: success
--Time: 5.54 s
/--If an element maps to zero under a ring homomorphism, then it is zero.-/
theorem t38 : ∀ {R : Type u} {S : Type v} [inst : Semiring R] [inst_1 : Semiring S] {f : R →+* S} {r : R}, f r = 0 → r = 0 :=
  by sorry

--Result: success
--Time: 3.68 s
/--Implication `→` is symmetric. If `P → Q` then `Q → P`.-/
theorem t39 : ∀ {p q : Prop}, (p → q) → q → p :=
  by sorry

--Result: success
--Time: 3.87 s
/--Two natural numbers are equal if and only if they are both divisible by some prime number.-/
theorem t40 : ∀ {m n : ℕ}, (∃ p, Nat.Prime p ∧ p ∣ m ∧ p ∣ n) ↔ m = n :=
  by sorry
