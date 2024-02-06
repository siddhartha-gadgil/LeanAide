import Mathlib

/-!
This file has example prompts for complex statements in Lean.
-/

/- Theorem 1 statement (Field Theory) : A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some natural number `m`. Prove that the degree of a separable contraction divides the degree, as a function of the exponential characteristic of the field. -/
namespace One
noncomputable section
open Classical Polynomial
variable {F : Type*} [CommSemiring F] (q : ℕ)
/-- A separable contraction of a polynomial `f` is a separable polynomial `g` such that
`g(x^(q^m)) = f(x)` for some `m : ℕ`.-/
def IsSeparableContraction (f : F[X]) (g : F[X]) : Prop :=
  g.Separable ∧ ∃ m : ℕ, expand F (q ^ m) g = f

/-- The condition of having a separable contraction. -/
def HasSeparableContraction' (f : F[X]) : Prop :=
  ∃ g : F[X], IsSeparableContraction q f g

variable {q} {f : F[X]} (hf : HasSeparableContraction q f)

/-- A choice of a separable contraction. -/
def HasSeparableContraction.contraction : F[X] :=
  Classical.choose hf

/-- The separable degree of a polynomial is the degree of a given separable contraction. -/
def HasSeparableContraction.degree : ℕ :=
  hf.contraction.natDegree

theorem HasSeparableContraction.dvd_degree' : ∃ m : ℕ, hf.degree * q ^ m = f.natDegree := sorry
end
end One

/- Theorems 2 and 3 statements (linear algebra) : Consider the space of modules with an associated quadratic form. Any two of these modules have an underlying isometry. Show that this space of modules forms a category. Given modules $M, N$ and $U$ in this category, and functions $f : M → N$ and $g : N → U$, show that the isometry corresponding to $f ∘ g$ is the same as the composition of the isometry corresponding to f with the isometry corresponding to g. -/
namespace Two
open CategoryTheory
universe v u
variable (R : Type u) [CommRing R]

/-- The category of quadratic modules; modules with an associated quadratic form. -/
structure QuadraticModuleCat extends ModuleCat.{v} R where
  /-- The quadratic form associated with the module. -/
  form : QuadraticForm R carrier

variable {R}
open QuadraticForm

/-- The algebraic composition. -/
@[ext]
structure Hom (V W : QuadraticModuleCat.{v} R) :=
  /-- The underlying isometry -/
  toIsometry : V.form →qᵢ W.form

instance category : Category (QuadraticModuleCat.{v} R) where
  Hom M N := Hom M N
  id M := ⟨Isometry.id M.form⟩
  comp f g := ⟨QuadraticForm.Isometry.comp g.toIsometry f.toIsometry⟩
  id_comp g := sorry
  comp_id f := sorry
  assoc f g h := sorry

@[simp] theorem toIsometry_comp {M N U : QuadraticModuleCat.{v} R} (f : M ⟶ N) (g : N ⟶ U) :
    (f ≫ g).toIsometry = g.toIsometry.comp f.toIsometry := sorry
end Two

/- Theorem 4 statement (Measure Theory) : The topological Besicovitch covering theorem ensures that, in a "nice metric space", there exists a
number `N` such that, from any family of balls with bounded radii, one can extract `N` families,
each made of disjoint balls, covering together all the centers of the initial family.

By "nice metric space", we mean a technical property stated as follows: there exists no satellite
configuration of `N + 1` points (with a given parameter `τ > 1`).

A satellite configuration is a configuration of `N+1` balls such
that:
1) The last ball intersects all the other balls.
2) Given any two distinct balls, there is an order between them, ensuring that the first ball does not
contain the center of the other one, and the radius of the second ball can not be larger than
the radius of the first ball, up to a factor `τ`.
3) Finally, none of the balls except the last ball must contain the center of the last ball, and the radius of the last ball can not be larger than
the radius of any of the other balls, up to a factor `τ`.

Prove the topological Besicovitch covering theorem. -/

namespace Four
noncomputable section
open Metric Set Filter Fin MeasureTheory TopologicalSpace

open scoped Topology Classical BigOperators ENNReal MeasureTheory NNReal
/-- A satellite configuration is a configuration of `N+1` balls that shows up in the inductive
construction for the Besicovitch covering theorem. It depends on some parameter `τ ≥ 1`.
This is a family of balls such
that:
1) The last ball intersects all the other balls.
2) Given any two distinct balls, there is an order between them, ensuring that the first ball does not
contain the center of the other one, and the radius of the second ball can not be larger than
the radius of the first ball, up to a factor `τ`.
3) Finally, none of the balls except the last ball must contain the center of the last ball, and the radius of the last ball can not be larger than
the radius of any of the other balls, up to a factor `τ`. -/
structure Besicovitch.SatelliteConfig (α : Type*) [MetricSpace α] (N : ℕ) (τ : ℝ) where
  c : Fin N.succ → α
  r : Fin N.succ → ℝ
  rpos : ∀ i, 0 < r i
  h : ∀ i j, i ≠ j → (r i ≤ dist (c i) (c j) ∧ r j ≤ τ * r i) ∨ (r j ≤ dist (c j) (c i) ∧ r i ≤ τ * r j)
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

open Besicovitch
/-- The topological Besicovitch covering theorem: If there
are no satellite configurations with `N+1` points, given a ball package, there exist finitely many families of disjoint balls covering all the centers in the package. -/
theorem exist_disjoint_covering_families {N : ℕ} {τ : ℝ} (hτ : 1 < τ)
    (hN : IsEmpty (SatelliteConfig α N τ)) (q : BallPackage β α) :
    ∃ s : Fin N → Set β,
      (∀ i : Fin N, (s i).PairwiseDisjoint fun j => closedBall (q.c j) (q.r j)) ∧
        range q.c ⊆ ⋃ i : Fin N, ⋃ j ∈ s i, ball (q.c j) (q.r j) := sorry
end
end Four

/- Theorem 5 statement (combinatorics) : A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) any two lines have at most one intersection point.
  If a nondegenerate configuration has at least as many points as lines, then prove that there exists
  an injective function from lines to points, such that the image of a line does not lie on itself. -/
namespace Five
variable (P L : Type*) [Membership P L]

/-- A configuration is nondegenerate if:
  1) there does not exist a line that passes through all of the points,
  2) there does not exist a point that is on all of the lines,
  3) there is at most one line through any two points,
  4) any two lines have at most one intersection point. -/
class Nondegenerate : Prop where
  exists_point : ∀ l : L, ∃ p, p ∉ l
  exists_line : ∀ p, ∃ l : L, p ∉ l
  eq_or_eq : ∀ {p₁ p₂ : P} {l₁ l₂ : L}, p₁ ∈ l₁ → p₂ ∈ l₁ → p₁ ∈ l₂ → p₂ ∈ l₂ → p₁ = p₂ ∨ l₁ = l₂

variable {P L}

/-- If a nondegenerate configuration has at least as many points as lines, then there exists
  an injective function `f` from lines to points, such that `f l` does not lie on `l`. -/
theorem Nondegenerate.exists_injective_of_card_le [Nondegenerate P L] [Fintype P] [Fintype L]
    (h : Fintype.card L ≤ Fintype.card P) : ∃ f : L → P, Function.Injective f ∧ ∀ l, f l ∉ l := sorry
end Five

/- Theorem 6 statement (Manifolds) : Prove that the `n` times continuously differentiable
sections of a smooth vector bundle over a manifold `M` is a module. -/
namespace Six
open Bundle Filter Function

open scoped Bundle Manifold
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H : Type*}
  [TopologicalSpace H] {H' : Type*} [TopologicalSpace H'] (I : ModelWithCorners 𝕜 E H)
  (I' : ModelWithCorners 𝕜 E' H') {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] {E'' : Type*} [NormedAddCommGroup E'']
  [NormedSpace 𝕜 E''] {H'' : Type*} [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M''] [SmoothManifoldWithCorners I M]

variable (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  -- `F` model fiber
  (n : ℕ∞)
  (V : M → Type*) [TopologicalSpace (TotalSpace F V)]
  -- `V` vector bundle
  [∀ x, AddCommGroup (V x)]
  [∀ x, Module 𝕜 (V x)]

variable [∀ x : M, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle 𝕜 F V]
  [SmoothVectorBundle F V I]

/-- Bundled `n` times continuously differentiable sections of a vector bundle. -/
structure ContMDiffSection where
  toFun : ∀ x, V x
  contMDiff_toFun : ContMDiff I (I.prod 𝓘(𝕜, F)) n fun x ↦
    TotalSpace.mk' F x (toFun x)

variable {I F V n}

-- notice that we get an error for the instance below if this is not given
instance : AddCommMonoid (ContMDiffSection I F n V) := sorry

instance instModule : Module 𝕜 (ContMDiffSection I F n V) := sorry
end Six

/- Theorems 7 and 8 statements (Differential geometry) : The stereographic projection is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It takes `x` in `E` to its orthogonal projection in the subspace orthogonal to `v` scaled by `2 / ((1 : ℝ) - <v, x>)`, where `<v, x>` denotes the inner product of `v` and `x`. Another function takes `w` to the vector `(‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)` in `E`. Prove that every point in the image of this function lies in the unit sphere. We can now use this function to create an inverse to the stereographic projection, which is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. Use this to prove that the stereographic projection is a homeomorphism when restricted to the complement of the singleton set composed of a unit vector `v`. -/
namespace Seven
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (v : E)
open Metric FiniteDimensional Function
open scoped Manifold
/-- Stereographic projection, forward direction. This is a map from an inner product space `E` to
the orthogonal complement of an element `v` of `E`. It takes `x` in `E` to its orthogonal projection in the subspace orthogonal to `v` scaled by `2 / ((1 : ℝ) - <v, x>)`, where `<v, x>` denotes the inner product of `v` and `x`. -/
def stereoToFun (x : E) : (ℝ ∙ v)ᗮ :=
  (2 / ((1 : ℝ) - innerSL ℝ v x)) • orthogonalProjection (ℝ ∙ v)ᗮ x

/-- Auxiliary function for the construction of the reverse direction of the stereographic
projection. It takes `w : E` to the vector `(‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)` in `E`. -/
def stereoInvFunAux (w : E) : E :=
  (‖w‖ ^ 2 + 4)⁻¹ • ((4 : ℝ) • w + (‖w‖ ^ 2 - 4) • v)

variable {v}
theorem stereoInvFunAux_mem (hv : ‖v‖ = 1) {w : E} (hw : w ∈ (ℝ ∙ v)ᗮ) :
    stereoInvFunAux v w ∈ sphere (0 : E) 1 := sorry

/-- Stereographic projection, reverse direction.  This is a map from the orthogonal complement of a
unit vector `v` in an inner product space `E` to the unit sphere in `E`. -/
def stereoInvFun (hv : ‖v‖ = 1) (w : (ℝ ∙ v)ᗮ) : sphere (0 : E) 1 :=
  ⟨stereoInvFunAux v (w : E), stereoInvFunAux_mem hv w.2⟩

/-- Stereographic projection from the unit sphere in `E`, centred at a unit vector `v` in `E`; this
is the version as a local homeomorphism. -/
def stereographic (hv : ‖v‖ = 1) : PartialHomeomorph (sphere (0 : E) 1) (ℝ ∙ v)ᗮ where
  toFun := stereoToFun v ∘ (↑)
  invFun := stereoInvFun hv
  source := {⟨v, sorry⟩}ᶜ
  target := Set.univ
  map_source' := sorry
  map_target' {w} _ := sorry
  left_inv' x hx := sorry
  right_inv' w _ := sorry
  open_source := sorry
  open_target := sorry
  continuousOn_toFun := sorry
  continuousOn_invFun := sorry
end
end Seven

/- Theorem 9 statement (algebraic geometry) : We know that a morphism `α` of presheafed spaces `X` and `Y` induces a morphism of stalks, given by the composition of the pushforward with `α`. Prove that this morphism of stalks is in fact invertible. -/ --rewrite!
namespace Nine
noncomputable section
open Opposite CategoryTheory CategoryTheory.Category CategoryTheory.Functor CategoryTheory.Limits
  AlgebraicGeometry TopologicalSpace
variable {C : Type u} [Category.{v} C] [HasColimits C]
open TopCat.Presheaf
/-- The stalk at `x` of a `PresheafedSpace`. -/
abbrev stalk (X : PresheafedSpace C) (x : X) : C := X.presheaf.stalk x

/-- A morphism of presheafed spaces induces a morphism of stalks. -/
def stalkMap {X Y : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) (x : X) :
    Y.stalk (α.base x) ⟶ X.stalk x :=
  (stalkFunctor C (α.base x)).map α.c ≫ X.presheaf.stalkPushforward C α.base x

instance isIso {X Y : PresheafedSpace.{_, _, v} C} (α : X ⟶ Y) [IsIso α] (x : X) : IsIso (stalkMap α x) where
  out := sorry
end
end Nine

/- Theorem 10 statement (Topology) : A trivial fiber bundle with fiber `F` over a base `B` is a space `Z` projecting on `B` for which there exists a homeomorphism to `B × F` such that the projection on to the first coordinate of the homeomorphism is the same as the projection of `Z` to `B`. Prove that the first and second projections in a product are trivial fiber bundles. -/
namespace Ten
variable {B : Type*} (F : Type*) {Z : Type*} [TopologicalSpace B] [TopologicalSpace F] [TopologicalSpace Z]

/-- A trivial fiber bundle with fiber `F` over a base `B` is a space `Z`
projecting on `B` for which there exists a homeomorphism to `B × F` that sends `proj`
to `Prod.fst`. -/
def IsHomeomorphicTrivialFiberBundle (proj : Z → B) : Prop :=
  ∃ e : Z ≃ₜ B × F, ∀ x, (e x).1 = proj x

/-- The projections in a product are trivial fiber bundles. -/
theorem isHomeomorphicTrivialFiberBundle_fst_and_snd :
    IsHomeomorphicTrivialFiberBundle F (Prod.fst : B × F → B) ∧ IsHomeomorphicTrivialFiberBundle F (Prod.snd : F × B → B) := sorry
end Ten

/- Theorem 11 and 12 statements (Topology) : We define the one point extension of an arbitrary space `X` to be `X` along with an extra point. We call this extra point `∞`. If `X` is a non-compact space, then prove that `∞` is not an isolated point of the one point extension of `X`.
Every element of `X` can easily be identified with an element of the one-point extension. Suppose `X` is a topological space. The one-point extension of `X` can then be made a topogical space in the following manner : a subset `s` of the one-point extension is open if its preimage in `X` is open and additionally, its preimage is compact if `s` contains `∞`. Prove that, for a given subset `s`, if `s` does not contain `∞`, then it is closed if and only if its preimage in `X` is closed and compact. -/
namespace Eleven
open Set Filter Topology
variable {X : Type*}

/-- The OnePoint extension of an arbitrary space `X` -/
def OnePoint (X : Type*) := Option X

/-- The point at infinity -/
@[match_pattern] def infty : OnePoint X := none

@[inherit_doc]
scoped notation "∞" => OnePoint.infty

variable [TopologicalSpace X]
/-- If `X` is a non-compact space, then `∞` is not an isolated point of `OnePoint X`. -/
instance nhdsWithin_compl_infty_neBot [NoncompactSpace X] : NeBot (𝓝[≠] (∞ : OnePoint X)) := sorry

/-- Coercion from `X` to `OnePoint X`. -/
@[coe, match_pattern] def some : X → OnePoint X := Option.some

instance : CoeTC X (OnePoint X) := ⟨some⟩

instance : TopologicalSpace (OnePoint X) where
  IsOpen s := (∞ ∈ s → IsCompact (((↑) : X → OnePoint X) ⁻¹' s)ᶜ) ∧
    IsOpen (((↑) : X → OnePoint X) ⁻¹' s)
  isOpen_univ := sorry
  isOpen_inter s t := sorry
  isOpen_sUnion S ho := sorry

theorem isClosed_iff_of_not_mem {s : Set (OnePoint X)} (h : ∞ ∉ s) :
    IsClosed s ↔ IsClosed ((↑) ⁻¹' s : Set X) ∧ IsCompact ((↑) ⁻¹' s : Set X) := sorry
end Eleven

/- Theorem statement 13 (Number Theory) : Let `Γ(N)` denote the full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity modulo `N`. Let `Γ₀(N)` denote the congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. Let `Γ₁'(N)` denote the congruence subgroup (as a subgroup of `Γ₀(N)`) of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. Let `Γ₁(N)` denote the congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. Fix an `N`. Prove that `γ` is a member of `Γ₁(N)` if and only if the upper triangle of `γ` is congruent to the identity matrix modulo `N`. -/ --not sure if this is correct wording
namespace Thirteen
local notation "SL(" n ", " R ")" => Matrix.SpecialLinearGroup (Fin n) R
local notation:1024 "↑ₘ" A:1024 => ((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
variable (N : ℕ)
local notation "SLMOD(" N ")" =>
  @Matrix.SpecialLinearGroup.map (Fin 2) _ _ _ _ _ _ (Int.castRingHom (ZMod N))

/-- The full level `N` congruence subgroup of `SL(2, ℤ)` of matrices that reduce to the identity modulo `N`.-/
def Gamma : Subgroup SL(2, ℤ) := SLMOD(N).ker

/-- The congruence subgroup of `SL(2, ℤ)` of matrices whose lower left-hand entry reduces to zero
modulo `N`. -/
def Gamma0 (N : ℕ) : Subgroup SL(2, ℤ) where
  carrier := { g : SL(2, ℤ) | ((↑ₘg 1 0 : ℤ) : ZMod N) = 0 }
  one_mem' := sorry
  mul_mem' := sorry
  inv_mem' := sorry

/-- The congruence subgroup `Gamma1` (as a subgroup of `Gamma0`) of matrices whose bottom
row is congruent to `(0,1)` modulo `N`.-/
def Gamma1' (N : ℕ) : Subgroup (Gamma0 N) :=
  (Gamma0Map N).ker

/-- The congruence subgroup `Gamma1` of `SL(2, ℤ)` consisting of matrices whose bottom
row is congruent to `(0,1)` modulo `N`. -/
def Gamma1 (N : ℕ) : Subgroup SL(2, ℤ) :=
  Subgroup.map ((Gamma0 N).subtype.comp (Gamma1' N).subtype) ⊤

theorem Gamma_mem (γ : SL(2, ℤ)) : γ ∈ Gamma N ↔ ((↑ₘγ 0 0 : ℤ) : ZMod N) = 1 ∧ ((↑ₘγ 0 1 : ℤ) : ZMod N) = 0 ∧ ((↑ₘγ 1 0 : ℤ) : ZMod N) = 0 ∧ ((↑ₘγ 1 1 : ℤ) : ZMod N) = 1 := sorry

/-
/- Honorable mention Theorem statement (combinatorics) : Pigeonhole principles

Given pigeons (possibly infinitely many) in pigeonholes, the
pigeonhole principle states that, if there are more pigeons than
pigeonholes, then there is a pigeonhole with two or more pigeons. -/

variable {α : Type u} {β : Type v} {M : Type w} [DecidableEq β]

open Nat

open BigOperators

namespace Finset

variable {s : Finset α} {t : Finset β} {f : α → β} {w : α → M} {b : M} {n : ℕ}
variable [LinearOrderedCancelAddCommMonoid M]
variable [LinearOrderedCommSemiring M]
variable [Fintype α] [Fintype β] (f : α → β) {w : α → M} {b : M} {n : ℕ}
--variable [LinearOrderedCancelAddCommMonoid M]

/-- The pigeonhole principle for finitely many pigeons of different weights, non-strict inequality
version: there is a pigeonhole with the total weight of pigeons in it less than or equal to `b`
provided that the total number of pigeonholes times `b` is greater than or equal to the total weight
of all pigeons. -/
theorem exists_sum_fiber_le_of_sum_le_nsmul [Nonempty β] (hb : ∑ x, w x ≤ card β • b) : ∃ y, ∑ x in univ.filter fun x => f x = y, w x ≤ b := sorry
-/

end Thirteen
