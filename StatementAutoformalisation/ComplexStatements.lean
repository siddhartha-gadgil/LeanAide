import Mathlib

/-!
This file has example prompts for complex statements in Lean.
-/

/- Theorem 1 statement (field theory) : A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some natural number `m`. Prove that the degree of a separable contraction divides the degree, as a function of the exponential characteristic of the field. -/

variable {F : Type*} [CommSemiring F] (q : ℕ)
/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
def IsSeparableContraction (f : F[X]) (g : F[X]) : Prop :=
  g.Separable ∧ ∃ m : ℕ, expand F (q ^ m) g = f

/-- The condition of having a separable contraction. -/
def HasSeparableContraction (f : F[X]) : Prop :=
  ∃ g : F[X], IsSeparableContraction q f g

variable {q} {f : F[X]} (hf : HasSeparableContraction q f)

/-- A choice of a separable contraction. -/
def HasSeparableContraction.contraction : F[X] :=
  Classical.choose hf

/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
def HasSeparableContraction.degree : ℕ :=
  hf.contraction.natDegree

theorem HasSeparableContraction.dvd_degree' : ∃ m : ℕ, hf.degree * q ^ m = f.natDegree := sorry

/- Thm 2 statement (linear algebra) : Consider the category of modules with an associated quadratic form. Any two of these modules have an underlying isometry. Given modules $M, N$ and $U$ in this category, and functions $f : M → N$ and $g : N → U$, show that the isometry corresponding to $f ∘ g$ is the same as the composition of the isometry corresponding to f with the isometry corresponding to g. -/

variable (R : Type u) [CommRing R]

/-- The category of quadratic modules; modules with an associated quadratic form-/
structure QuadraticModuleCat extends ModuleCat.{v} R where
  /-- The quadratic form associated with the module. -/
  form : QuadraticForm R carrier

variable {R}
/-- A type alias for `QuadraticForm.LinearIsometry` to avoid confusion between the categorical and
algebraic spellings of composition. -/
@[ext]
structure Hom (V W : QuadraticModuleCat.{v} R) :=
  /-- The underlying isometry -/
  toIsometry : V.form →qᵢ W.form

@[simp] theorem toIsometry_comp {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toIsometry = g.toIsometry.comp f.toIsometry := sorry

/-- Theorem 3 statement (measure theory) : The topological Besicovitch covering theorem ensures that, in a nice metric space, there exists a
number `N` such that, from any family of balls with bounded radii, one can extract `N` families,
each made of disjoint balls, covering together all the centers of the initial family.

By "nice metric space", we mean a technical property stated as follows: there exists no satellite
configuration of `N + 1` points (with a given parameter `τ > 1`). Such a configuration is a family
of `N + 1` balls, where the first `N` balls all intersect the last one, but none of them contains
the center of another one and their radii are controlled. This property is for instance
satisfied by finite-dimensional real vector spaces.

Prove the topological Besicovitch covering theorem. -/

/-- A satellite configuration is a configuration of `N+1` points that shows up in the inductive
construction for the Besicovitch covering theorem. It depends on some parameter `τ ≥ 1`.

This is a family of balls (indexed by `i : Fin N.succ`, with center `c i` and radius `r i`) such
that the last ball intersects all the other balls (condition `inter`),
and given any two balls there is an order between them, ensuring that the first ball does not
contain the center of the other one, and the radius of the second ball can not be larger than
the radius of the first ball (up to a factor `τ`). This order corresponds to the order of choice
in the inductive construction: otherwise, the second ball would have been chosen before.
This is the condition `h`.

Finally, the last ball is chosen after all the other ones, meaning that `h` can be strengthened
by keeping only one side of the alternative in `hlast`.
-/
structure Besicovitch.SatelliteConfig (α : Type*) [MetricSpace α] (N : ℕ) (τ : ℝ) where
  c : Fin N.succ → α
  r : Fin N.succ → ℝ
  rpos : ∀ i, 0 < r i
  h : ∀ i j, i ≠ j → r i ≤ dist (c i) (c j) ∧ r j ≤ τ * r i ∨ r j ≤ dist (c j) (c i) ∧ r i ≤ τ * r j
  hlast : ∀ i < last N, r i ≤ dist (c i) (c (last N)) ∧ r (last N) ≤ τ * r i
  inter : ∀ i < last N, dist (c i) (c (last N)) ≤ r i + r (last N)

variable {α : Type*} [MetricSpace α] {N : ℕ} {τ : ℝ} (a : SatelliteConfig α N τ)

/-- A ball package is a family of balls in a metric space with positive bounded radii. -/
structure BallPackage (β : Type*) (α : Type*) where
  c : β → α
  r : β → ℝ
  rpos : ∀ b, 0 < r b
  r_bound : ℝ
  r_le : ∀ b, r b ≤ r_bound

/-- The topological Besicovitch covering theorem: there exist finitely many families of disjoint
balls covering all the centers in a package. More specifically, one can use `N` families if there
are no satellite configurations with `N+1` points. -/
theorem exist_disjoint_covering_families {N : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (hN : IsEmpty (SatelliteConfig α N τ)) (q : BallPackage β α) :
    ∃ s : Fin N → Set β,
      (∀ i : Fin N, (s i).PairwiseDisjoint fun j => closedBall (q.c j) (q.r j)) ∧
        range q.c ⊆ ⋃ i : Fin N, ⋃ j ∈ s i, ball (q.c j) (q.r j) := sorry
