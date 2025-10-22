import Mathlib

universe u v w u_1 u_2 u_3 u₁ u₂ u₃

open Nat

/-
  Translation of 40 statements from `data/false-prompts.txt`
  Using similarity search

  SUMMARY:

  Time:
  · Total time to translate 40 statements = 306.85
  · Avg time to translate one statement = 7.67

  Results:
  · Success = 36
  · Fallback = 4
-/

--Result: success
--Time: 11.24 s
/--Every ring is a field.-/
theorem t1 : (R : Type u) → [inst : Ring R] → Field R :=
  by sorry

--Result: fallback
--Time: 9.13 s
/--Every vector space is finite dimensional.-/
theorem t2 : This theorem is generally false in the context of vector spaces, as not all vector spaces are finite-dimensional. Hence, there is no corresponding Lean 4 code for this statement as a universally true theorem. If you have specific conditions or a context under which this holds, please provide further details. :=
  by sorry

--Result: success
--Time: 5.25 s
/--Every group is a torsion monoid.-/
theorem t3 : ∀ {G : Type u_1} [inst : Group G], Monoid.IsTorsion G :=
  by sorry

--Result: success
--Time: 9.61 s
/--Every finite simple group has prime order.-/
theorem t4 : ∀ {G : Type u_1} [inst : Group G] [Finite G], IsSimpleGroup G → ∃ p, Nat.Prime p ∧ Nat.card G = p :=
  by sorry

--Result: success
--Time: 6.64 s
/--Every finite group is simple.-/
theorem t5 : ∀ {G : Type u_1} [inst : Group G] [Finite G], IsSimpleGroup G :=
  by sorry

--Result: success
--Time: 8.53 s
/--Every finite group has prime order.-/
theorem t6 : ∀ {G : Type u_1} [Group G] [Finite G], ∃ p, Nat.Prime p ∧ Nat.card G = p :=
  by sorry

--Result: success
--Time: 5.70 s
/--Every set has Lebesgue measure zero.-/
theorem t7 : ∀ {s : Set ℝ}, MeasureTheory.volume s = 0 :=
  by sorry

--Result: success
--Time: 7.07 s
/--If a topological space is compact, then every subset is compact.-/
theorem t8 : ∀ {X : Type u} [inst : TopologicalSpace X] [CompactSpace X] (s : Set X), IsCompact s :=
  by sorry

--Result: fallback
--Time: 7.36 s
/--Every set that is Lebesgue measurable but not Borel measurable has Lebesgue measure zero.-/
theorem t9 : ∀ {α : Type u_1} [inst : MeasurableSpace α] [inst_1 : MeasureTheory.Measure α] (s : Set α),
  MeasurableSet s ∧ ¬BorelMeasurable s → inst_1 s = 0 :=
  by sorry

--Result: fallback
--Time: 8.94 s
/--A finitely-presented group containing a torsion element is finite.-/
theorem t10 : ∀ {G : Type u_1} [inst : Group G] [Group.FinitelyPresented G], (∃ g : G, g ≠ 1 ∧ g ^ n = 1) → Finite G :=
  by sorry

--Result: success
--Time: 9.62 s
/--If every point of a subset of a topological space is contained in some closed set, the subset itself is closed.-/
theorem t11 : ∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}, (∀ x ∈ s, ∃ t, IsClosed t ∧ x ∈ t) → IsClosed s :=
  by sorry

--Result: success
--Time: 10.05 s
/--A topological space $X$ is Hausdorff if and only if the diagonal map is an open map from $X$ to $X × X$.-/
theorem t12 : ∀ {X : Type u_1} [inst : TopologicalSpace X], T2Space X ↔ IsOpenMap fun x => (x, x) :=
  by sorry

--Result: success
--Time: 5.39 s
/--Any finite order element in a group is equal to the identity.-/
theorem t13 : ∀ {G : Type u_1} [inst : Group G] {x : G}, IsOfFinOrder x → orderOf x = 1 → x = 1 :=
  by sorry

--Result: success
--Time: 7.15 s
/--If a subgroup of a group is torsion-free, then the group itself is torsion free.-/
theorem t14 : ∀ {G : Type u_1} [inst : Group G], (∃ H, Monoid.IsTorsionFree ↥H) → Monoid.IsTorsionFree G :=
  by sorry

--Result: success
--Time: 6.82 s
/--Every injective homomorphism from a finitely generated free group to itself is surjective.-/
theorem t15 : ∀ {G : Type u_1} [inst : Group G] [inst_1 : IsFreeGroup G] [Group.FG G] (f : G →* G),
  Function.Injective ⇑f → Function.Surjective ⇑f :=
  by sorry

--Result: success
--Time: 7.78 s
/--Every division ring is either a field or finite.-/
theorem t16 : ∀ {K : Type u} [inst : DivisionRing K], IsField K ∨ Nonempty (Fintype K) :=
  by sorry

--Result: success
--Time: 7.72 s
/--Every natural number is the product of two primes.-/
theorem t17 : ∀ (n : ℕ), 2 ≤ n → ∃ p q, Nat.Prime p ∧ Nat.Prime q ∧ n = p * q :=
  by sorry

--Result: success
--Time: 8.03 s
/--Every even number is the square of a natural number.-/
theorem t18 : ∀ (n : ℕ), Even n → ∃ m, n = m ^ 2 :=
  by sorry

--Result: success
--Time: 6.88 s
/--Every normal subgroup of a group has finite index.-/
theorem t19 : ∀ {G : Type u_1} [inst : Group G] {N : Subgroup G} [N.Normal], N.FiniteIndex :=
  by sorry

--Result: success
--Time: 7.56 s
/--The characteristic polynomial of every matrix has real roots.-/
theorem t20 : ∀ {R : Type u} [inst : CommRing R] [IsDomain R] {n : Type v} [inst_1 : Fintype n] [inst_2 : DecidableEq n]
  (M : Matrix n n ℝ), ∃ r, M.charpoly.IsRoot r :=
  by sorry

--Result: success
--Time: 7.28 s
/--In a commutative ring, every prime ideal is contained in a unique maximal ideal.-/
theorem t21 : ∀ {R : Type u_1} [inst : CommRing R] {P : Ideal R}, P.IsPrime → ∃! M, M.IsMaximal ∧ P ≤ M :=
  by sorry

--Result: success
--Time: 0.04 s
/--Every continuous function is uniformly continuous.-/
theorem t22 : ∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},
  Continuous f → UniformContinuous f :=
  by sorry

--Result: success
--Time: 7.40 s
/--Every uniformly continuous function is bounded above.-/
theorem t23 : ∀ {α : Type u} {β : Type v} [inst : UniformSpace α] [inst_1 : LinearOrder β] [TopologicalSpace β]
  [inst_3 : PseudoMetricSpace β] {f : α → β}, UniformContinuous f → BddAbove (Set.range f) :=
  by sorry

--Result: success
--Time: 5.78 s
/--If every compact subset of a topological space is closed, then the space is compact.-/
theorem t24 : ∀ {X : Type u} [inst : TopologicalSpace X], (∀ {s : Set X}, IsCompact s → IsClosed s) → CompactSpace X :=
  by sorry

--Result: success
--Time: 6.32 s
/--In a commutative ring, the sum of idempotent elements is idempotent.-/
theorem t25 : ∀ {R : Type u_1} [inst : CommRing R] {a b : R}, IsIdempotentElem a → IsIdempotentElem b → IsIdempotentElem (a + b) :=
  by sorry

--Result: fallback
--Time: 6.57 s
/--The number of partitions of a finite set is a prime number.-/
theorem t26 : ∀ {α : Type u} [Fintype α] [DecidableEq α], Nat.Prime (Fintype.card (Setoid.Partitions (Finset.univ : Finset α))) :=
  by sorry

--Result: success
--Time: 8.44 s
/--If a poset has a maximal element, then it has a unique minimal element.-/
theorem t27 : ∀ {α : Type u_1} [inst : PartialOrder α] {s : Set α}, (∃ a ∈ s, ∀ x ∈ s, x ≤ a) → ∃! a, a ∈ s ∧ ∀ x ∈ s, a ≤ x :=
  by sorry

--Result: success
--Time: 6.60 s
/--The automorphism group of an Abelian group is cyclic.-/
theorem t28 : ∀ {A : Type u_1} [inst : AddCommGroup A], IsCyclic (AddAut A) :=
  by sorry

--Result: success
--Time: 11.51 s
/--If a function from the unit interval to itself has a fixed point, then it has points of all positive periods.-/
theorem t29 : ∀ {f : ℝ → ℝ}, Function.IsFixedPt f 0 → ∀ (n : ℕ), 0 < n → ∃ x, Function.IsPeriodicPt f n x :=
  by sorry

--Result: success
--Time: 16.12 s
/--The complement of the union of two sets contains the union of their complements.-/
theorem t30 : ∀ {α : Type u_1} (s t : Set α), (s ∪ t)ᶜ ⊇ sᶜ ∪ tᶜ :=
  by sorry

--Result: success
--Time: 5.39 s
/--The square root of an rational number is rational.-/
theorem t31 : ∀ {q : ℚ}, ∃ r, r ^ 2 = q → ↑r = √↑q :=
  by sorry

--Result: success
--Time: 7.51 s
/--If a module over a ring is free, then the ring is commutative.-/
theorem t32 : {R : Type u_1} →
  {M : Type u_2} → [inst : Ring R] → [inst_1 : AddCommMonoid M] → [inst_2 : Module R M] → Module.Free R M → CommRing R :=
  by sorry

--Result: success
--Time: 5.24 s
/--If the set of units of a ring forms a group then the ring is commutative.-/
theorem t33 : {R : Type u} → [inst : Ring R] → Group Rˣ → CommRing R :=
  by sorry

--Result: success
--Time: 4.64 s
/--Every natural number larger than `10` is the sum of a square and a prime.-/
theorem t34 : ∀ (n : ℕ), 10 < n → ∃ a p, a ^ 2 + p = n ∧ Nat.Prime p :=
  by sorry

--Result: success
--Time: 14.30 s
/--The initial object of a category is isomorphic to its terminal object.-/
theorem t35 : {C : Type u} →
  [inst : CategoryTheory.Category.{v, u} C] →
    [inst_1 : CategoryTheory.Limits.HasInitial C] → [inst_2 : CategoryTheory.Limits.HasTerminal C] → ⊥_ C ≅ ⊤_ C :=
  by sorry

--Result: success
--Time: 10.90 s
/--If the composition of two functions is continuous, then each of them is continuous.-/
theorem t36 : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]
  [inst_2 : TopologicalSpace γ] {f : α → β} {g : β → γ}, Continuous (g ∘ f) → Continuous f ∧ Continuous g :=
  by sorry

--Result: success
--Time: 6.17 s
/--If `a` commutes with `b` and `b` commutes with `c` then `a` commutes with `c`.-/
theorem t37 : ∀ {S : Type u_3} [inst : Mul S] {a b c : S}, Commute a b → Commute b c → Commute a c :=
  by sorry

--Result: success
--Time: 7.73 s
/--If an element maps to zero under a ring homomorphism, then it is zero.-/
theorem t38 : ∀ {R : Type u} {S : Type v} [inst : Semiring R] [inst_1 : Semiring S] {f : R →+* S},
  Function.Injective ⇑f → ∀ {r : R}, f r = 0 → r = 0 :=
  by sorry

--Result: success
--Time: 6.71 s
/--Implication `→` is symmetric. If `P → Q` then `Q → P`.-/
theorem t39 : ∀ {P Q : Prop}, (P → Q) → Q → P :=
  by sorry

--Result: success
--Time: 5.71 s
/--Two natural numbers are equal if and only if they are both divisible by some prime number.-/
theorem t40 : ∀ {m n : ℕ}, (∃ p, Nat.Prime p ∧ p ∣ m ∧ p ∣ n) ↔ m = n :=
  by sorry
