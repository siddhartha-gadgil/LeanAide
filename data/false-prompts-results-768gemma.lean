import Mathlib

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

open Nat

/-
  Translation of 40 statements from `data/false-prompts.txt`
  Using similarity search

  SUMMARY:

  Time:
  · Total time to translate 40 statements = 463.92 s
  · Avg time to translate one statement = 11.60 s

  Results:
  · Success = 33
    · Without error = 32
    · With error = 1
  · Fallback = 7
  · Failures = 0
-/

--Result: success
--Time: 13.89 s
/--Every ring is a field.-/
theorem t1 : ∀ {R : Type u_1} [inst : Ring R], IsField R :=
  by sorry

--Result: success
--Time: 11.65 s
/--Every vector space is finite dimensional.-/
theorem t2 : ∀ (K : Type u) (V : Type v) [inst : Field K] [inst_1 : AddCommGroup V] [inst_2 : Module K V], FiniteDimensional K V :=
  by sorry

--Result: success
--Time: 7.57 s
/--Every group is a torsion monoid.-/
theorem t3 : ∀ {G : Type u_1} [inst : Group G], Monoid.IsTorsion G :=
  by sorry

--Result: success
--Time: 6.18 s
/--Every finite simple group has prime order.-/
theorem t4 : ∀ {α : Type u_1} [inst : Group α] [inst_1 : Fintype α] [IsSimpleGroup α], Nat.Prime (Fintype.card α) :=
  by sorry

--Result: success
--Time: 5.90 s
/--Every finite group is simple.-/
theorem t5 : ∀ {G : Type u_1} [inst : Group G] [Fintype G], (∀ (H : Subgroup G), H = ⊥ ∨ H = ⊤) → IsSimpleGroup G :=
  by sorry

--Result: fallback
--Time: 8.37 s
/--Every finite group has prime order.-/
theorem t6 : I'm sorry, but this statement is incorrect. Not every finite group has prime order. A finite group can have composite order as well. If you have a different statement to translate or need further assistance, please let me know. :=
  by sorry

--Result: success
--Time: 6.46 s
/--Every set has Lebesgue measure zero.-/
theorem t7 : ∀ {α : Type u_1} [inst : MeasureTheory.MeasureSpace α] (s : Set α), MeasureTheory.volume s = 0 :=
  by sorry

--Result: success
--Time: 6.52 s
/--If a topological space is compact, then every subset is compact.-/
theorem t8 : ∀ {X : Type u} [inst : TopologicalSpace X], CompactSpace X → ∀ (s : Set X), IsCompact s :=
  by sorry

--Result: fallback
--Time: 9.47 s
/--Every set that is Lebesgue measurable but not Borel measurable has Lebesgue measure zero.-/
theorem t9 : ∀ {α : Type u_1} [MeasurableSpace α] [TopologicalSpace α] [BorelSpace α] {s : Set α},
  MeasureTheory.MeasureSpace.volume s ≠ ⊤ →
    MeasurableSet s ∧ ¬BorelMeasurable s → MeasureTheory.MeasureSpace.volume s = 0 :=
  by sorry

--Result: fallback
--Time: 7.76 s
/--A finitely-presented group containing a torsion element is finite.-/
theorem t10 : ∀ {G : Type u_1} [inst : Group G], Group.FinitelyPresented G → (∃ g : G, g ≠ 1 ∧ ∃ n : ℕ, n ≠ 0 ∧ g ^ n = 1) → Fintype G :=
  by sorry

--Result: success
--Time: 8.37 s
/--If every point of a subset of a topological space is contained in some closed set, the subset itself is closed.-/
theorem t11 : ∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, (∀ x ∈ s, ∃ C, IsClosed C ∧ x ∈ C ∧ C ⊆ s) → IsClosed s :=
  by sorry

--Result: success
--Time: 6.72 s
/--A topological space $X$ is Hausdorff if and only if the diagonal map is an open map from $X$ to $X × X$.-/
theorem t12 : ∀ {X : Type u_1} [inst : TopologicalSpace X], T2Space X ↔ IsOpenMap fun x => (x, x) :=
  by sorry

--Result: success
--Time: 6.24 s
/--Any finite order element in a group is equal to the identity.-/
theorem t13 : ∀ {G : Type u} [inst : Group G] {g : G}, (∃ n, 0 < n ∧ g ^ n = 1) → g = 1 :=
  by sorry

--Result: success
--Time: 6.88 s
/--If a subgroup of a group is torsion-free, then the group itself is torsion free.-/
theorem t14 : ∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), Monoid.IsTorsionFree ↥H → Monoid.IsTorsionFree G :=
  by sorry

--Result: success
--Time: 6.98 s
/--Every injective homomorphism from a finitely generated free group to itself is surjective.-/
theorem t15 : ∀ {G : Type u} [inst : Group G] [Fintype G] (f : G →* G), Function.Injective ⇑f → Function.Surjective ⇑f :=
  by sorry

--Result: success
--Time: 8.32 s
/--Every division ring is either a field or finite.-/
theorem t16 : ∀ {K : Type u_1} [inst : DivisionRing K], IsField K ∨ Finite K :=
  by sorry

--Result: success
--Time: 5.86 s
/--Every natural number is the product of two primes.-/
theorem t17 : ∀ (n : ℕ), 1 < n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q :=
  by sorry

--Result: success
--Time: 5.51 s
/--Every even number is the square of a natural number.-/
theorem t18 : ∀ (n : ℕ), Even n → ∃ m, n = m ^ 2 :=
  by sorry

--Result: success
--Time: 9.24 s
/--Every normal subgroup of a group has finite index.-/
theorem t19 : ∀ {G : Type u_1} [inst : Group G] (H : Subgroup G), H.Normal → H.FiniteIndex :=
  by sorry

--Result: success
--Time: 9.23 s
/--The characteristic polynomial of every matrix has real roots.-/
theorem t20 : ∀ {n : Type u} [inst : Fintype n] [inst_1 : DecidableEq n] (M : Matrix n n ℝ), ∃ r, r ∈ M.charpoly.roots :=
  by sorry

--Result: success
--Time: 7.41 s
/--In a commutative ring, every prime ideal is contained in a unique maximal ideal.-/
theorem t21 : ∀ {R : Type u_1} [inst : CommRing R] {P : Ideal R} [P.IsPrime], ∃! M, M.IsMaximal ∧ P ≤ M :=
  by sorry

--Result: success
--Time: 1.13 s
/--Every continuous function is uniformly continuous.-/
theorem t22 : ∀ {X : Type u_1} {Y : Type u_2} [inst : UniformSpace X] [inst_1 : UniformSpace Y] (f : X → Y),
  Continuous f → UniformContinuous f :=
  by sorry

--Result: fallback
--Time: 8.64 s
/--Every uniformly continuous function is bounded above.-/
theorem t23 : ∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] {f : α → β},
  UniformContinuous f → BddAbove (Set.range f) :=
  by sorry

--Result: success
--Time: 7.72 s
/--If every compact subset of a topological space is closed, then the space is compact.-/
theorem t24 : ∀ {X : Type u} [inst : TopologicalSpace X], (∀ (K : Set X), IsCompact K → IsClosed K) → CompactSpace X :=
  by sorry

--Result: success
--Time: 6.16 s
/--In a commutative ring, the sum of idempotent elements is idempotent.-/
theorem t25 : ∀ {R : Type u} [inst : CommRing R] {a b : R}, a * a = a → b * b = b → (a + b) * (a + b) = a + b :=
  by sorry

--Result: fallback
--Time: 8.60 s
/--The number of partitions of a finite set is a prime number.-/
theorem t26 : ∀ {α : Type u_1} [Fintype α], Nat.Prime (Fintype.card (Set.Partition α)) :=
  by sorry

--Result: success
--Time: 5.89 s
/--If a poset has a maximal element, then it has a unique minimal element.-/
theorem t27 : ∀ {α : Type u} [inst : PartialOrder α] [OrderTop α], ∃! x, ∀ (y : α), x ≤ y :=
  by sorry

--Result: success
--Time: 5.51 s
/--The automorphism group of an Abelian group is cyclic.-/
theorem t28 : ∀ {G : Type u_1} [inst : CommGroup G], IsCyclic (MulAut G) :=
  by sorry

--Result: success
--Time: 10.10 s
/--If a function from the unit interval to itself has a fixed point, then it has points of all positive periods.-/
theorem t29 : ∀ {f : ℝ → ℝ},
  (∀ (x : ℝ), 0 ≤ x ∧ x ≤ 1 → 0 ≤ f x ∧ f x ≤ 1) →
    (∃ c, 0 ≤ c ∧ c ≤ 1 ∧ f c = c) → ∀ (n : ℕ), 0 < n → ∃ x, 0 ≤ x ∧ x ≤ 1 ∧ Function.IsPeriodicPt f n x :=
  by sorry

--Result: success
--Time: 169.79 s
/--The complement of the union of two sets contains the union of their complements.-/
theorem t30 : ∀ {α : Type u} (s t : Set α), (s ∪ t)ᶜ ⊇ sᶜ ∪ tᶜ :=
  by sorry

--Result: success
--Time: 6.13 s
/--The square root of an rational number is rational.-/
theorem t31 : ∀ (a : ℚ), ∃ b, b * b = a → b = Rat.sqrt a :=
  by sorry

--Result: fallback
--Time: 10.78 s
/--If a module over a ring is free, then the ring is commutative.-/
theorem t32 : ∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : Module R M],
  Module.Free R M → CommRing R :=
  by sorry

--Result: fallback
--Time: 8.11 s
/--If the set of units of a ring forms a group then the ring is commutative.-/
theorem t33 : ∀ {R : Type u} [inst : Ring R], Group Rˣ → CommRing R :=
  by sorry

--Result: success
--Time: 7.56 s
/--Every natural number larger than `10` is the sum of a square and a prime.-/
theorem t34 : ∀ {n : ℕ}, 10 < n → ∃ a p, Nat.Prime p ∧ n = a ^ 2 + p :=
  by sorry

--Result: success
--Time: 6.93 s
/--The initial object of a category is isomorphic to its terminal object.-/
theorem t35 : ∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasInitial C]
  [inst_2 : CategoryTheory.Limits.HasTerminal C], CategoryTheory.IsIso (CategoryTheory.Limits.initial.to (⊤_ C)) :=
  by sorry

--Result: success
--Time: 10.61 s
/--If the composition of two functions is continuous, then each of them is continuous.-/
theorem t36 : ∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y]
  [inst_2 : TopologicalSpace Z] {f : X → Y} {g : Y → Z}, Continuous (g ∘ f) → Continuous f ∧ Continuous g :=
  by sorry

--Result: success
--Time: 5.97 s
/--If `a` commutes with `b` and `b` commutes with `c` then `a` commutes with `c`.-/
theorem t37 : ∀ {S : Type u_3} [inst : Semigroup S] {a b c : S}, Commute a b → Commute b c → Commute a c :=
  by sorry

--Result: success
--Time: 8.33 s
/--If an element maps to zero under a ring homomorphism, then it is zero.-/
theorem t38 : ∀ {α : Type u_2} {β : Type u_3} [inst : NonAssocSemiring α] [inst_1 : NonAssocSemiring β] (f : α →+* β) {x : α},
  f x = 0 → x = 0 :=
  by sorry

--Result: success
--Time: 5.06 s
/--Implication `→` is symmetric. If `P → Q` then `Q → P`.-/
theorem t39 : ∀ {P Q : Prop}, (P → Q) → Q → P :=
  by sorry

--Result: success
--Time: 6.34 s
/--Two natural numbers are equal if and only if they are both divisible by some prime number.-/
theorem t40 : ∀ {m n : ℕ}, (∃ p, Nat.Prime p ∧ p ∣ m ∧ p ∣ n) ↔ m = n :=
  by sorry
