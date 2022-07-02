import Mathbin.All

/-
If every proper closed set of a topological space is compact, then the space itself is compact.
-/
theorem compact_if_all_proper_compact {α : Type _} [TopologicalSpace α] : (∀ (s : Set α), (s ≠ Set.univ) → IsCompact s) → CompactSpace α := sorry

/-
Every prime that is one greater than a multiple of four can be expressed as the sum of two squares.
-/
theorem fermat_two_square : ∀ p : ℕ, Prime p → (p % 4 = 1) → ∃ a b : ℕ, a ^ 2 + b ^ 2 = p := sorry

/-
For every subset of the Euclidean plane, there is a line segment of unit length whose endpoints are either both inside the subset or both outside it.
-/
theorem unit_line_in_or_out_of_euclidean_plane_subset : ∀ (S : Set $ EuclideanSpace ℝ (Finₓ 2)), ∃ (x y : EuclideanSpace ℝ (Finₓ 2)), (∥x - y∥ = (1 : ℝ)) → (x ∈ S ∧ y ∈ S) ∨ (x ∉ S ∧ y ∉ S) := sorry

/-
The product of two numbers, each of which is the sum of four squares, is itself a sum of four squares.
-/
theorem euler_four_square_identity : let is_sum_of_four_squares : ℕ → Prop := λ n : ℕ => ∃ (a b c d : ℕ), n = a^2 + b^2 + c^2 + d^2;
  ∀ (x y : ℕ), is_sum_of_four_squares x → is_sum_of_four_squares y → is_sum_of_four_squares (x * y) := sorry

/-
A ring with all elements idempotent is commutative.
-/
theorem all_idempotent_implies_commutative {R : Type _} [Ring R] : (∀ x : R, x * x = 1) → CommRing R := sorry

/-
There are infinitely many pairs of primes that differ exactly by two.
-/
theorem twin_prime_conjecture : ∀ n : ℕ, ∃ p : ℕ, p > n → Prime p → Prime (p + 2) := sorry

/-
If `I` is a collection of intervals of real numbers with lengths that sum to less than one, then the union of the intervals cannot be all of the unit interval.
-/


/-
Every finite division ring is a field.
-/
theorem fin_div_ring_is_field {R : Type _} [DivisionRing R] [Finite R] : Field R := sorry

/-
The product of two positive numbers is at most the square of their average.
-/
theorem am_gm_ineq : ∀ (a b : ℝ), a > 0 → b > 0 → a * b ≤ ((a + b)/(1 + 1))^2 := sorry

/-
In any configuration of points on the plane, not all on a line, there is a line which contains exactly two of the points.
-/
theorem sylvester_gallai {P L : Type _} [HasMem P L] [Membership P L] [Configuration.Nondegenerate P L] : ∃ (l : L) (p q : P), p ∈ l → q ∈ l → (∀ r : P, r ∈ l → r = p ∨ r = q) := sorry

/-
If each of two types can be mapped injectively into the other, then there is a bijection between them.
-/
theorem cantor_schroeder_bernstein {α β : Type _} (f : α → β) (g : β → α) : Function.Injective f → Function.Injective g → (∃ h : α → β, Function.Bijective h) := sorry

/-
A finite graph in which every two vertices have precisely one common neighbour contains a vertex that is adjacent to all other vertices.
-/
theorem graph_unique_common_neighbour_implies_universal_adjacent_vertex {V : Type _} [Finite V] (G : SimpleGraph V) : (∀ v w : V, ∃! x : V, G.Adj v x ∧ G.Adj w x) → (∃ c : V, ∀ v : V, G.Adj c v) := sorry

/-
The number of partitions with odd parts is equal to the number of partitions with distinct parts.
-/
theorem partition_odd_distincts : ∀ n : ℕ, Finset.card (Nat.Partition.odds n) = Finset.card (Nat.Partition.distincts n) := sorry

/-
Every non-empty poset in which every chain has an upper bound contains a maximal element.
-/
lemma zorn {α : Type _} [PartialOrder α] [Nonempty α] : (∀ c : Set α, IsChain LE.le c → (∃ b : α, ∀ a ∈ c, a ≤ b)) → (∃ m : α, ∀ a : α, m ≤ a → a = m) := sorry

/-
A group whose automorphism group is cyclic is Abelian.
-/


/-
A uniformly continuous function of a uniformly continuous function is uniformly continuous.
-/


/-
The image of a union of sets is the union of the images.
-/
theorem image_union (f : α → β) (S : Set (Set α)) : (f <$> (⋃₀ S)) = (⋃₀ ((Functor.map f) <$> S)) := sorry

/-
A topological space is normal if and only if any two disjoint closed subsets can be separated by a continuous function.
-/
-- lemma urysohn {X : Type _} [TopologicalSpace X] [NormalSpace X] {S T : Set X} : IsClosed S → IsClosed T → Disjoint S T →
--  (∃ f : X → ℝ, Continuous f → ):= sorry

/-
The only field automorphism of the reals is the identity.
-/
theorem real_field_aut_trivial : ∀ (f : ℝ ≃+* ℝ), (∀ x : ℝ, f x = x) := sorry

/-
If a function from the unit interval to itself has a point of period three, then it has points of all positive periods.
-/
theorem period_three_implies_chaos : ∀ f : Set.Icc 0 1 → Set.Icc 0 1, (∃ x : Set.Icc 0 1, Function.IsPeriodicPt f 3 x) → (∀ n : ℕ, n > 0 → ∃ y : Set.Icc 0 1, Function.IsPeriodicPt f n y) := sorry

/-
A terminal object in a category is unique up to unique isomorphism.
-/

/-
A finitely-presented group containing a torsion element is finite.
-/

/-
The complement of the union of two sets is the intersection of their complements.
-/
theorem compl_union {α : Type _} (S T : Set α) : (S ∪ T).compl = S.compl ∩ T.compl := sorry

/-
The sum of the cubes of two positive integers is never equal to the cube of a third integer.
-/
theorem flt_3 : ∀ a b c : ℕ, a > 0 → b > 0 → ¬(a^3 + b^3 = c^3) := sorry

#check Nonempty