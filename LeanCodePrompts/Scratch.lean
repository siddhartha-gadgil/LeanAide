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
theorem aut_group_cyclic_implies_abelian {G : Type _} [Groupₓ G] : CategoryTheory.Aut G → CommGroup G := sorry

/-
A uniformly continuous function of a uniformly continuous function is uniformly continuous.
* This translation may be incorrect
-/
theorem uniformcts_of_uniformcts {α β γ : Type _} [UniformSpace α] [UniformSpace β] [UniformSpace γ] (f : α → β) (g : β → γ) : UniformContinuous f → UniformContinuous g → UniformContinuous (g ∘ f) := sorry

/-
The image of a union of sets is the union of the images.
-/
theorem image_union (f : α → β) (S : Set (Set α)) : (f <$> (⋃₀ S)) = (⋃₀ ((Functor.map f) <$> S)) := sorry

/-
A topological space is normal if and only if any two disjoint closed subsets can be separated by a continuous function.
-/
lemma urysohn {X : Type _} [TopologicalSpace X] [TopologicalSpace ℝ] : NormalSpace X ↔ ( ∀ {S T : Set X}, IsClosed S → IsClosed T → Disjoint S T →
 (∃ f : X → ℝ, Continuous f → (∀ x ∈ S, f x = 0) ∧ (∀ x ∈ T, f x = 1)) ) := sorry

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
theorem terminal_unique_iso {C : Type _} [CategoryTheory.Category C] : ∀ T₁ T₂ : C, CategoryTheory.Limits.IsTerminal T₁ → CategoryTheory.Limits.IsTerminal T₂ → (∃ ι : CategoryTheory.Iso T₁ T₂, ∀ ι' : CategoryTheory.Iso T₁ T₂, ι = ι') := sorry

/-
A finitely-presented group containing a torsion element is finite.
-/
theorem torsion_in_fg_group_implies_finite {G : Type _} [Groupₓ G] : Groupₓ.Fg G → Finite G := sorry

/-
The complement of the union of two sets is the intersection of their complements.
-/
theorem compl_union {α : Type _} (S T : Set α) : (S ∪ T).compl = S.compl ∩ T.compl := sorry

/-
The sum of the cubes of two positive integers is never equal to the cube of a third integer.
-/
theorem flt_3 : ∀ a b c : ℕ, a > 0 → b > 0 → ¬(a^3 + b^3 = c^3) := sorry


/-
If every element of a group `G` has order two, then every pair of elements of `G` commutes.
-/
theorem elems_order_two_implies_commutative {G: Type _}[Group G] : (∀ x y : G, x * x = 1) → (∀ x y : G, Commute x y) := sorry

/-
Every prime number is either `2` or odd.
-/
theorem prime_eq_two_or_odd {n: Nat} : Prime n → n = 2 ∨ Odd n := sorry

/-
Every odd degree polynomial over `ℝ` has a zero
-/
theorem poly_odd_degree_has_zero {α : Type _} [Field α] (p : Polynomial α) : Odd (p.degree) → ∃ x, p.IsRoot x := sorry

/-
The product of two consequitive natural numbers is odd
-/
theorem product_conseq_odd (n: Nat): Odd <| n * (n + 1) := sorry

/-
Every constant function `f x = c` from real numbers to real numbers is differentiable.
-/
theorem constant_is_differentiable 
  {f: ℝ → ℝ}: ∃ c: ℝ, (∀ x : ℝ, f x = c) → Differentiable ℝ f := sorry 

/-
Every index 2 subgroup of a group is free
-/
theorem index_two_subgroup {G : Type _} [Groupₓ G] (H : Subgroup G): 
      H.index = 2 → Subgroup.Normal H := sorry

/-
Every subgroup of a free group is free
-/
theorem subgpFree {G : Type _} [Groupₓ G] : 
      (K : Subgroup G) → Σ β, FreeGroup β ≃* ↥K := sorry

/-
Every free group is torsion free
-/
theorem free_group_torsion_free {α : Type} :
  Monoidₓ.IsTorsionFree (FreeGroup α) := sorry

/-
Every non-empty subgroup of `ℤ` is isomorphic to `ℤ`
-/
theorem integer_subgroups (H : AddSubgroup ℤ) :
    H.Carrier.Nonempty  →   ↥H ≃+ ℤ := sorry

/- If the coefficients of a polynomial over rationals are integral, every rational root is integral.-/
theorem int_poly_rat_zeros_int (p: Polynomial ℚ) :
  ∀ n: ℕ, IsIntegral ℚ (p.coeff n) →  
  ∀ x: ℚ, p.IsRoot x →  IsIntegral ℚ x := sorry

/-
Every natural number greater than `1` is divisible by a prime number. 
-/
theorem has_prime_factor(n: ℕ) :
  n > 1 → ∃ p: ℕ, Prime p ∧ (∃ d: ℕ, p * d = n) := sorry

/-
Six is not the sum of two prime numbers.
-/
theorem six_not_prime_sum : 
  ¬ (∃ n m: Nat, Prime n ∧ Prime m ∧ n ≠ m ∧ 6 = n + m) := sorry

/-
A finite torsion-free group is trivial
-/
theorem fin_torsionfree {G: Type _}[Groupₓ G][Finite G] :
  Monoidₓ.IsTorsionFree G → IsSubgroup.Trivial G := sorry

/-
Any homomorphism from the additive group of rational numbers to `ℤ` is trivial
-/
theorem hom_rat_Z_trivial (f : ℚ → ℤ) : 
  IsAddGroupHom f →  ∀ x: ℚ, f x = 0 := sorry

/-
Every finite division ring is a field.
-/
theorem fin_int_domain_ring_is_field 
    {R : Type _} [Ringₓ R][IsDomain R] [Finite R] : Field R := sorry

/-
Every finite topological space is compact
-/
theorem finite_space_compact{X : Type _}[TopologicalSpace X][Finite X] :
  CompactSpace X := sorry

/-
Every surjective homomorphism from a finitely generated free group to itself is injective
-/
theorem freegroup_hopfian {α : Type _} [Finite α]: (f: FreeGroup α → FreeGroup α) → (IsGroupHom f) → f.Surjective → f.Injective := sorry

/-
Every polynomial of positive degree over reals is unbounded.
-/
theorem polys_unbounded(p: Polynomial ℝ) : p.degree > 0 → 
    ∀ m: ℝ, ∃ x: ℝ, p.eval x  > m ∨ p.eval x < -m  := sorry

/-
A homomorphism between fields is either injective or trivial.
-/
theorem field_hom_inj_or_trivial {F F' : Type _} [Field F] [Field F'] : ∀ ϕ : F →+* F', ϕ.toFun.Injective ∨ (∀ x : F, ϕ x = 0) := sorry

/-
Any homomorphism from a group $G$ to an Abelian group factors through the Abelianisation of $G$.
-/
-- typeclass difficulties
--theorem abelianisation_factor {G : Type _} [Groupₓ G] [NonAssocSemiringₓ G] {A : Type _} [CommGroup A] [NonAssocSemiringₓ A] [NonAssocSemiringₓ (Abelianization G)] : ∀ ϕ : G →+* A, ∃! (ϕ' : Abelianization G →+* A), ϕ = ϕ' ∘ (@Abelianization.of G _) := sorry

/-
Every ascending chain of sub-modules of a Noetherian module eventually stabilises.
-/
theorem noetherian_implies_ascending_chain_condition {R M : Type _} [Ringₓ R] [AddCommMonoidₓ M] [Module R M] : IsNoetherian R M → ∀ (f : ℕ →o Submodule R M), ∃ n : ℕ, ∀ m : ℕ, n < m → f n = f m := sorry

/-
Differentiability implies continuity.
-/
theorem differentiability_implies_continuity [TopologicalSpace ℝ] : ∀ f : ℝ → ℝ, Differentiable ℝ f → Continuous f := sorry

/-
Left adjoint functors preserve colimits.
-/
open CategoryTheory in
theorem left_adjoints_preserve_colimits {C D J : Type _} [Category C] [Category D] [Category J] (F : Functor C D) [IsLeftAdjoint F] (K : Functor J C) :
∀ c : Limits.Cocone K, Limits.IsColimit c → ( Limits.IsColimit $ Functor.mapCocone F c) := sorry

/-
The angles of a triangle add up to two right angles.
-/
theorem angle_sum_pi {p q r : EuclideanSpace ℝ (Finₓ 2)} : EuclideanGeometry.angle p q r + EuclideanGeometry.angle q r p + EuclideanGeometry.angle r p q = Real.pi := sorry

/-
Every Lebesgue measurable function is equal almost everywhere to a Borel measurable function.
-/


/-
For any prime divisor $p$ of the order of a finite group $G$, there is a subgroup of $G$ whose order is $p$.
-/
-- theorem cauchy {G : Type _} [Groupₓ G] [Fintype G] : ∀ p : ℕ, Prime p → (Fintype.card G % p = 0) → ∃ H : Subgroup G, Monoidₓ.exponent (↥H) = p := sorry

/-
Any locally-small category $C$ can be embedded into the category of contravariant functors from $C$ to $Set$.
-/


/-
Every positive even integer can be written as the sum of two primes.
-/
theorem goldbach : ∀ n : ℕ, n > 0 → Even n → ∃ p q : ℕ, Prime p → Prime q → n = p + q := sorry

/-
A complex function that is once differentiable is infinitely differentiable.
-/


/-
The elements of any finite distributive lattice can be represented as finite sets, in such a way that the meet and join lattice operations correspond to unions and intersections of sets.
-/

/-
Every matrix satisfies its own characteristic polynomial.
-/
theorem cayley_hamilton {R : Type _} [CommRingₓ R] {n : Type _} [DecidableEq n] [Fintype n] (M : Matrix n n R) : (Polynomial.aeval M) M.charpoly = 0 := sorry

/-
The square root of an irrational number is irrational.
-/
theorem sqrt_of_irrat_irrat (x : ℝ) : Irrational x → Irrational (Real.sqrt x) := sorry

/-
Among all rectangles of a given area $A$, the square of side √A has the smallest perimeter.
-/

/-
If each strongly-connected component of a graph is contracted to a single vertex, the resulting graph is a directed acyclic graph.
-/

/-
If $n$ infinitely long straight lines are lying on a plane such that no two lines are parallel and no three lines intersect at a single point, then the lines divide the plane into $(n^2 + n + 2)/2$ regions.
-/

/-
The tangent bundle of the circle is trivial.
-/

/-
The number of binary strings of length $n$ with no consecutive zeros is equal to the $n+2$th Fibonacci number.
-/

/-
If a sub-sequence of a Cauchy sequence in a metric space converges to a point, then the full sequence also converges to the same point.
-/

/-
Every finite Abelian group is isomorphic to the product of cyclic groups.
-/

/-
If the square of a number is even, the number itself is even.
-/
theorem sq_even_implies_num_even : ∀ n : ℕ, Even (n^2) → Even n := sorry

/-
In a finite commutative ring, all prime ideals are maximal.
-/
theorem finite_ring_prime_implies_maximal {R : Type _} [CommRingₓ R] [Fintype R] : ∀ (Idl : Ideal R), Idl.IsPrime → Idl.IsMaximal := sorry

/-
An integer polynomial with a root in the integers has a root modulo every prime.
-/

/-
The number of Sylow-2 subgroups of a dihedral group is equal to the largest odd number dividing the order of the group.
-/

/-
A topological space $X$ is Hausdorff if and only if the diagonal is a closed set in $X × X$.
-/
theorem hausdorff_iff_diag_closed {X : Type _} [TopologicalSpace X] : T2Space X ↔ IsClosed (Set.Diagonal X) := sorry

/-
If every point of a subset of a topological space is contained in some open set, the subset itself is open.
-/
theorem open_iff_open_nhd_all_pt {X : Type _} [TopologicalSpace X] (S : Set X) : (∀ x ∈ S, ∃ U : Set X, IsOpen U) → IsOpen S := sorry

/-
The product of a complex number with its conjugate is a real number.
-/
theorem complex_conj_prod_real : ∀ z : ℂ, ∃ r : ℝ, z * (starRingEnd ℂ $ z) = (r : ℂ) := sorry

/-
Every non-identity element of a free group is of infinite order.
-/
theorem non_id_implies_infinite_order {G : Type _} [Groupₓ G] : FreeGroup G → (∀ g : G, g ≠ 1 → orderOf g = 0) := sorry

/-
Any sub-ring of a field that contains the identity is an integral domain.
-/
theorem sub_ring_field_with_id_is_int_domain {F : Type _} [Field F] : ∀ R : Subring F, 1 ∈ R.Carrier → IsDomain ↥R := sorry

/-
An element of a discrete valuation ring is a unit if and only if it has a valuation of zero.
-/
theorem dvr_unit_iff_val_zero {R : Type _} [CommRingₓ R] [IsDomain R] [DiscreteValuationRing R] : ∀ r : R, IsUnit r → DiscreteValuationRing.addVal R r = 0 := sorry

/-
Every automorphism of a tree fixes a vertex or an edge.
-/

/-
If $e$ is an idempotent in a commutative ring $R$ with identity, the $R$ is isomorphic to the product of the ideals generated by $e$ and $1-e$.
-/

/-
The number of leaves in any tree is at least the maximum degree.
-/

/-
The exponential function is convex.
-/
theorem exp_convex : ConvexOn ℝ Set.univ Real.exp := sorry

/-
For every natural number $k$, there is a natural number $n$ such that any partition of the first $n$ natural numbers into $k$ sets has a set containing numbers $x, y, z$ such that $x + y = z$.
-/

/-
No non-constant polynomial of a complex variable can take imaginary values only.
-/

/-
For any two relatively prime positive integers $a$ and $b$, every sufficiently large natural number $N$ can be written as a linear combination $ax + by$ of $a$ and $b$, where both $x$ and $y$ are natural numbers.
-/
theorem coprime_integer_span_sylvester_coin : ∀ a b : ℕ, a > 0 → b > 0 → Nat.coprime a b → ∃ m : ℕ, ∀ N : ℕ, N > m → ∃ x y : ℕ, N = a*x + b*y := sorry

/-
An integer-valued polynomial need not have all integer coefficients.
-/

/-
For a module $M$, if a sub-module $N$ and the quotient $M/N$ are both finitely generated, then so is $M$.
-/
-- theorem module_fg_if_sub_and_quot_fg {M R : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] : ∀ N : Submodule R M, N.Fg → (N.Quotient.Module.Fg) → M.Fg := sorry

/-
If $ϕ$ is a linear transformation from a finite dimensional vector space to itself, there is an integer $m$ such that the intersection of the image of $ϕ^m$ with the kernel of $ϕ^m$ is trivial.
-/

/-
The eigenvalues of an orthogonal matrix have absolute value $1$.
-/

/-
In a commutative ring with prime characteristic $p$, the $p$th power of the sum of two elements is equal to the sum of the $p$th powers of the elements.
-/
theorem frobenius_pow_sum_eq_sum_pow {R : Type _} [CommRingₓ R] : (p : ℕ) → Prime p → CharP R p → ∀ a b : R, (a + b)^p = a^p + b^p := sorry

/-
Every alternating $n$ tensor over a vector space of dimension $n$ is a scalar multiple of the determinant.
-/

/-
An absolutely convergent sequence is convergent.
-/

/-
The combinator (S K K) is equal to the identity combinator.
-/
-- Library/Init/Core.lean not yet ported
-- theorem combinator_I_derivable_from_S_K : Combinator.S Combinator.K Combinator.K = Combinator.I := sorry

#check Function.Injective

#check AddGroup
#print AddGroupₓ
#print AddGroup
