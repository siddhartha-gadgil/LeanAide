/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Sébastien Gouëzel, Heather Macbeth
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.Analysis.NormedSpace.PiLp

/-!
# `L²` inner product space structure on finite products of inner product spaces

The `L²` norm on a finite product of inner product spaces is compatible with an inner product
$$
\langle x, y\rangle = \sum \langle x_i, y_i \rangle.
$$
This is recorded in this file as an inner product space instance on `pi_Lp 2`.

This file develops the notion of a finite dimensional Hilbert space over `𝕜 = ℂ, ℝ`, referred to as
`E`. We define an `orthonormal_basis 𝕜 ι E` as a linear isometric equivalence
between `E` and `euclidean_space 𝕜 ι`. Then `std_orthonormal_basis` shows that such an equivalence
always exists if `E` is finite dimensional. We provide language for converting between a basis
that is orthonormal and an orthonormal basis (e.g. `basis.to_orthonormal_basis`). We show that
orthonormal bases for each summand in a direct sum of spaces can be combined into an orthonormal
basis for the the whole sum in `direct_sum.submodule_is_internal.subordinate_orthonormal_basis`. In
the last section, various properties of matrices are explored.

## Main definitions

- `euclidean_space 𝕜 n`: defined to be `pi_Lp 2 (n → 𝕜)` for any `fintype n`, i.e., the space
  from functions to `n` to `𝕜` with the `L²` norm. We register several instances on it (notably
  that it is a finite-dimensional inner product space).

- `orthonormal_basis 𝕜 ι`: defined to be an isometry to Euclidean space from a given
  finite-dimensional innner product space, `E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι`.

- `basis.to_orthonormal_basis`: constructs an `orthonormal_basis` for a finite-dimensional
  Euclidean space from a `basis` which is `orthonormal`.

- `orthonormal.exists_orthonormal_basis_extension`: provides an existential result of an
  `orthonormal_basis` extending a given orthonormal set

- `exists_orthonormal_basis`: provides an orthonormal basis on a finite dimensional vector space

- `std_orthonormal_basis`: provides an arbitrarily-chosen `orthonormal_basis` of a given finite
  dimensional inner product space

For consequences in infinite dimension (Hilbert bases, etc.), see the file
`analysis.inner_product_space.l2_space`.

-/


open Real Set Filter IsROrC

open BigOperators uniformity TopologicalSpace Nnreal Ennreal ComplexConjugate DirectSum

noncomputable section

variable {ι : Type _} {ι' : Type _}

variable {𝕜 : Type _} [IsROrC 𝕜] {E : Type _} [InnerProductSpace 𝕜 E]

variable {E' : Type _} [InnerProductSpace 𝕜 E']

variable {F : Type _} [InnerProductSpace ℝ F]

variable {F' : Type _} [InnerProductSpace ℝ F']

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-
 If `ι` is a finite type and each space `f i`, `i : ι`, is an inner product space,
then `Π i, f i` is an inner product space as well. Since `Π i, f i` is endowed with the sup norm,
we use instead `pi_Lp 2 f` for the product space, which is endowed with the `L^2` norm.
-/
instance PiLp.innerProductSpace {ι : Type _} [Fintype ι] (f : ι → Type _) [∀ i, InnerProductSpace 𝕜 (f i)] :
    InnerProductSpace 𝕜 (PiLp 2 f) where
  inner := fun x y => ∑ i, inner (x i) (y i)
  norm_sq_eq_inner := by
    intro x
    have h₂ : 0 ≤ ∑ i : ι, ∥x i∥ ^ (2 : ℝ) := Finset.sum_nonneg fun j hj => rpow_nonneg_of_nonneg (norm_nonneg (x j)) 2
    simp only [← norm, ← AddMonoidHom.map_sum, norm_sq_eq_inner, ← one_div]
    rw [← rpow_nat_cast ((∑ i : ι, ∥x i∥ ^ (2 : ℝ)) ^ (2 : ℝ)⁻¹) 2, ← rpow_mul h₂]
    norm_num
  conj_sym := by
    intro x y
    unfold inner
    rw [RingHom.map_sum]
    apply Finset.sum_congr rfl
    rintro z -
    apply inner_conj_sym
  add_left := fun x y z =>
    show (∑ i, inner (x i + y i) (z i)) = (∑ i, inner (x i) (z i)) + ∑ i, inner (y i) (z i) by
      simp only [← inner_add_left, ← Finset.sum_add_distrib]
  smul_left := fun x y r =>
    show (∑ i : ι, inner (r • x i) (y i)) = conj r * ∑ i, inner (x i) (y i) by
      simp only [← Finset.mul_sum, ← inner_smul_left]

@[simp]
theorem PiLp.inner_apply {ι : Type _} [Fintype ι] {f : ι → Type _} [∀ i, InnerProductSpace 𝕜 (f i)] (x y : PiLp 2 f) :
    ⟪x, y⟫ = ∑ i, ⟪x i, y i⟫ :=
  rfl

/-- The standard real/complex Euclidean space, functions on a finite type. For an `n`-dimensional
space use `euclidean_space 𝕜 (fin n)`. -/
@[reducible, nolint unused_arguments]
def EuclideanSpace (𝕜 : Type _) [IsROrC 𝕜] (n : Type _) [Fintype n] : Type _ :=
  PiLp 2 fun i : n => 𝕜

theorem EuclideanSpace.norm_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n] (x : EuclideanSpace 𝕜 n) :
    ∥x∥ = Real.sqrt (∑ i, ∥x i∥ ^ 2) :=
  PiLp.norm_eq_of_L2 x

theorem EuclideanSpace.nnnorm_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n] (x : EuclideanSpace 𝕜 n) :
    ∥x∥₊ = Nnreal.sqrt (∑ i, ∥x i∥₊ ^ 2) :=
  PiLp.nnnorm_eq_of_L2 x

theorem EuclideanSpace.dist_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n] (x y : EuclideanSpace 𝕜 n) :
    dist x y = (∑ i, dist (x i) (y i) ^ 2).sqrt :=
  (PiLp.dist_eq_of_L2 x y : _)

theorem EuclideanSpace.nndist_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n] (x y : EuclideanSpace 𝕜 n) :
    nndist x y = (∑ i, nndist (x i) (y i) ^ 2).sqrt :=
  (PiLp.nndist_eq_of_L2 x y : _)

theorem EuclideanSpace.edist_eq {𝕜 : Type _} [IsROrC 𝕜] {n : Type _} [Fintype n] (x y : EuclideanSpace 𝕜 n) :
    edist x y = (∑ i, edist (x i) (y i) ^ 2) ^ (1 / 2 : ℝ) :=
  (PiLp.edist_eq_of_L2 x y : _)

variable [Fintype ι]

section

attribute [local reducible] PiLp

instance : FiniteDimensional 𝕜 (EuclideanSpace 𝕜 ι) := by
  infer_instance

instance : InnerProductSpace 𝕜 (EuclideanSpace 𝕜 ι) := by
  infer_instance

@[simp]
theorem finrank_euclidean_space : FiniteDimensional.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := by
  simp

theorem finrank_euclidean_space_fin {n : ℕ} : FiniteDimensional.finrank 𝕜 (EuclideanSpace 𝕜 (Finₓ n)) = n := by
  simp

theorem EuclideanSpace.inner_eq_star_dot_product (x y : EuclideanSpace 𝕜 ι) :
    ⟪x, y⟫ = Matrix.dotProduct (star <| PiLp.equiv _ _ x) (PiLp.equiv _ _ y) :=
  rfl

/-- A finite, mutually orthogonal family of subspaces of `E`, which span `E`, induce an isometry
from `E` to `pi_Lp 2` of the subspaces equipped with the `L2` inner product. -/
def DirectSum.IsInternal.isometryL2OfOrthogonalFamily [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : DirectSum.IsInternal V) (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) :
    E ≃ₗᵢ[𝕜] PiLp 2 fun i => V i := by
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV.injective hV.surjective
  refine' (e₂.symm.trans e₁).isometryOfInner _
  suffices ∀ v w, ⟪v, w⟫ = ⟪e₂ (e₁.symm v), e₂ (e₁.symm w)⟫ by
    intro v₀ w₀
    convert this (e₁ (e₂.symm v₀)) (e₁ (e₂.symm w₀)) <;>
      simp only [← LinearEquiv.symm_apply_apply, ← LinearEquiv.apply_symm_apply]
  intro v w
  trans ⟪∑ i, (V i).subtypeₗᵢ (v i), ∑ i, (V i).subtypeₗᵢ (w i)⟫
  · simp only [← sum_inner, ← hV'.inner_right_fintype, ← PiLp.inner_apply]
    
  · congr <;> simp
    

@[simp]
theorem DirectSum.IsInternal.isometry_L2_of_orthogonal_family_symm_apply [DecidableEq ι] {V : ι → Submodule 𝕜 E}
    (hV : DirectSum.IsInternal V) (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ)
    (w : PiLp 2 fun i => V i) : (hV.isometryL2OfOrthogonalFamily hV').symm w = ∑ i, (w i : E) := by
  classical
  let e₁ := DirectSum.linearEquivFunOnFintype 𝕜 ι fun i => V i
  let e₂ := LinearEquiv.ofBijective (DirectSum.coeLinearMap V) hV.injective hV.surjective
  suffices ∀ v : ⨁ i, V i, e₂ v = ∑ i, e₁ v i by
    exact this (e₁.symm w)
  intro v
  simp [← e₂, ← DirectSum.coeLinearMap, ← DirectSum.toModule, ← Dfinsupp.sum_add_hom_apply]

end

/-- The vector given in euclidean space by being `1 : 𝕜` at coordinate `i : ι` and `0 : 𝕜` at
all other coordinates. -/
def EuclideanSpace.single [DecidableEq ι] (i : ι) (a : 𝕜) : EuclideanSpace 𝕜 ι :=
  (PiLp.equiv _ _).symm (Pi.single i a)

@[simp]
theorem PiLp.equiv_single [DecidableEq ι] (i : ι) (a : 𝕜) :
    PiLp.equiv _ _ (EuclideanSpace.single i a) = Pi.single i a :=
  rfl

@[simp]
theorem PiLp.equiv_symm_single [DecidableEq ι] (i : ι) (a : 𝕜) :
    (PiLp.equiv _ _).symm (Pi.single i a) = EuclideanSpace.single i a :=
  rfl

@[simp]
theorem EuclideanSpace.single_apply [DecidableEq ι] (i : ι) (a : 𝕜) (j : ι) :
    (EuclideanSpace.single i a) j = ite (j = i) a 0 := by
  rw [EuclideanSpace.single, PiLp.equiv_symm_apply, ← Pi.single_apply i a j]

theorem EuclideanSpace.inner_single_left [DecidableEq ι] (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪EuclideanSpace.single i (a : 𝕜), v⟫ = conj a * v i := by
  simp [← apply_ite conj]

theorem EuclideanSpace.inner_single_right [DecidableEq ι] (i : ι) (a : 𝕜) (v : EuclideanSpace 𝕜 ι) :
    ⟪v, EuclideanSpace.single i (a : 𝕜)⟫ = a * conj (v i) := by
  simp [← apply_ite conj, ← mul_comm]

theorem EuclideanSpace.pi_Lp_congr_left_single [DecidableEq ι] {ι' : Type _} [Fintype ι'] [DecidableEq ι'] (e : ι' ≃ ι)
    (i' : ι') :
    LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e (EuclideanSpace.single i' (1 : 𝕜)) =
      EuclideanSpace.single (e i') (1 : 𝕜) :=
  by
  ext i
  simpa using if_congr e.symm_apply_eq rfl rfl

variable (ι 𝕜 E)

/-- An orthonormal basis on E is an identification of `E` with its dimensional-matching
`euclidean_space 𝕜 ι`. -/
structure OrthonormalBasis where of_repr ::
  repr : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι

variable {ι 𝕜 E}

namespace OrthonormalBasis

instance : Inhabited (OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι)) :=
  ⟨of_repr (LinearIsometryEquiv.refl 𝕜 (EuclideanSpace 𝕜 ι))⟩

/-- `b i` is the `i`th basis vector. -/
instance :
    CoeFun (OrthonormalBasis ι 𝕜 E) fun _ => ι → E where coe := fun b i => by
    classical <;> exact b.repr.symm (EuclideanSpace.single i (1 : 𝕜))

@[simp]
theorem coe_of_repr [DecidableEq ι] (e : E ≃ₗᵢ[𝕜] EuclideanSpace 𝕜 ι) :
    ⇑(OrthonormalBasis.of_repr e) = fun i => e.symm (EuclideanSpace.single i (1 : 𝕜)) := by
  rw [coeFn]
  unfold CoeFun.coe
  funext
  congr
  simp only [← eq_iff_true_of_subsingleton]

@[simp]
protected theorem repr_symm_single [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr.symm (EuclideanSpace.single i (1 : 𝕜)) = b i := by
  classical
  congr
  simp

@[simp]
protected theorem repr_self [DecidableEq ι] (b : OrthonormalBasis ι 𝕜 E) (i : ι) :
    b.repr (b i) = EuclideanSpace.single i (1 : 𝕜) := by
  rw [← b.repr_symm_single i, LinearIsometryEquiv.apply_symm_apply]

protected theorem repr_apply_apply (b : OrthonormalBasis ι 𝕜 E) (v : E) (i : ι) : b.repr v i = ⟪b i, v⟫ := by
  classical
  rw [← b.repr.inner_map_map (b i) v, b.repr_self i, EuclideanSpace.inner_single_left]
  simp only [← one_mulₓ, ← eq_self_iff_true, ← map_one]

@[simp]
protected theorem orthonormal (b : OrthonormalBasis ι 𝕜 E) : Orthonormal 𝕜 b := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [← b.repr.inner_map_map (b i) (b j), b.repr_self i, b.repr_self j, EuclideanSpace.inner_single_left,
    EuclideanSpace.single_apply, map_one, one_mulₓ]

/-- The `basis ι 𝕜 E` underlying the `orthonormal_basis` --/
protected def toBasis (b : OrthonormalBasis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.ofEquivFun b.repr.toLinearEquiv

@[simp]
protected theorem coe_to_basis (b : OrthonormalBasis ι 𝕜 E) : (⇑b.toBasis : ι → E) = ⇑b := by
  change ⇑(Basis.ofEquivFun b.repr.to_linear_equiv) = b
  ext j
  rw [Basis.coe_of_equiv_fun]
  congr

@[simp]
protected theorem coe_to_basis_repr (b : OrthonormalBasis ι 𝕜 E) : b.toBasis.equivFun = b.repr.toLinearEquiv := by
  change (Basis.ofEquivFun b.repr.to_linear_equiv).equivFun = b.repr.to_linear_equiv
  ext x j
  simp only [← Basis.of_equiv_fun_repr_apply, ← LinearIsometryEquiv.coe_to_linear_equiv, ← Basis.equiv_fun_apply]

@[simp]
protected theorem coe_to_basis_repr_apply (b : OrthonormalBasis ι 𝕜 E) (x : E) (i : ι) :
    b.toBasis.repr x i = b.repr x i := by
  rw [← Basis.equiv_fun_apply, OrthonormalBasis.coe_to_basis_repr, LinearIsometryEquiv.coe_to_linear_equiv]

protected theorem sum_repr_symm (b : OrthonormalBasis ι 𝕜 E) (v : EuclideanSpace 𝕜 ι) :
    (∑ i, v i • b i) = b.repr.symm v := by
  classical
  simpa using (b.to_basis.equiv_fun_symm_apply v).symm

/-- A basis that is orthonormal is an orthonormal basis. -/
def _root_.basis.to_orthonormal_basis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) : OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.of_repr <|
    LinearEquiv.isometryOfInner v.equivFun
      (by
        intro x y
        let p : EuclideanSpace 𝕜 ι := v.equiv_fun x
        let q : EuclideanSpace 𝕜 ι := v.equiv_fun y
        have key : ⟪p, q⟫ = ⟪∑ i, p i • v i, ∑ i, q i • v i⟫ := by
          simp [← sum_inner, ← inner_smul_left, ← hv.inner_right_fintype]
        convert key
        · rw [← v.equiv_fun.symm_apply_apply x, v.equiv_fun_symm_apply]
          
        · rw [← v.equiv_fun.symm_apply_apply y, v.equiv_fun_symm_apply]
          )

@[simp]
theorem _root_.basis.coe_to_orthonormal_basis_repr (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr : E → EuclideanSpace 𝕜 ι) = v.equivFun :=
  rfl

@[simp]
theorem _root_.basis.coe_to_orthonormal_basis_repr_symm (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    ((v.toOrthonormalBasis hv).repr.symm : EuclideanSpace 𝕜 ι → E) = v.equivFun.symm :=
  rfl

@[simp]
theorem _root_.basis.to_basis_to_orthonormal_basis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv).toBasis = v := by
  simp [← Basis.toOrthonormalBasis, ← OrthonormalBasis.toBasis]

@[simp]
theorem _root_.basis.coe_to_orthonormal_basis (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) :
    (v.toOrthonormalBasis hv : ι → E) = (v : ι → E) :=
  calc
    (v.toOrthonormalBasis hv : ι → E) = ((v.toOrthonormalBasis hv).toBasis : ι → E) := by
      classical
      rw [OrthonormalBasis.coe_to_basis]
    _ = (v : ι → E) := by
      simp
    

variable {v : ι → E}

/-- A finite orthonormal set that spans is an orthonormal basis -/
protected def mk (hon : Orthonormal 𝕜 v) (hsp : Submodule.span 𝕜 (Set.Range v) = ⊤) : OrthonormalBasis ι 𝕜 E :=
  (Basis.mk (Orthonormal.linear_independent hon) hsp).toOrthonormalBasis
    (by
      rwa [Basis.coe_mk])

@[simp]
protected theorem coe_mk (hon : Orthonormal 𝕜 v) (hsp : Submodule.span 𝕜 (Set.Range v) = ⊤) :
    ⇑(OrthonormalBasis.mk hon hsp) = v := by
  classical <;> rw [OrthonormalBasis.mk, _root_.basis.coe_to_orthonormal_basis, Basis.coe_mk]

open Submodule

/-- A finite orthonormal family of vectors whose span has trivial orthogonal complement is an
orthonormal basis. -/
protected def mkOfOrthogonalEqBot (hon : Orthonormal 𝕜 v) (hsp : (span 𝕜 (Set.Range v))ᗮ = ⊥) :
    OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk hon
    (by
      have : FiniteDimensional 𝕜 (span 𝕜 (range v)) := FiniteDimensional.span_of_finite 𝕜 (finite_range v)
      have : CompleteSpace (span 𝕜 (range v)) := FiniteDimensional.complete 𝕜 _
      rwa [orthogonal_eq_bot_iff] at hsp)

@[simp]
protected theorem coe_of_orthogonal_eq_bot_mk (hon : Orthonormal 𝕜 v) (hsp : (span 𝕜 (Set.Range v))ᗮ = ⊥) :
    ⇑(OrthonormalBasis.mkOfOrthogonalEqBot hon hsp) = v :=
  OrthonormalBasis.coe_mk hon _

variable [Fintype ι']

/-- `b.reindex (e : ι ≃ ι')` is an `orthonormal_basis` indexed by `ι'` -/
def reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : OrthonormalBasis ι' 𝕜 E :=
  OrthonormalBasis.of_repr (b.repr.trans (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 𝕜 e))

protected theorem reindex_apply (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (i' : ι') :
    (b.reindex e) i' = b (e.symm i') := by
  classical
  dsimp' [← reindex, ← OrthonormalBasis.hasCoeToFun]
  rw [coe_of_repr]
  dsimp'
  rw [← b.repr_symm_single, LinearIsometryEquiv.pi_Lp_congr_left_symm, EuclideanSpace.pi_Lp_congr_left_single]

@[simp]
protected theorem coe_reindex (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') : ⇑(b.reindex e) = ⇑b ∘ ⇑e.symm :=
  funext (b.reindex_apply e)

@[simp]
protected theorem reindex_repr (b : OrthonormalBasis ι 𝕜 E) (e : ι ≃ ι') (x : E) (i' : ι') :
    ((b.reindex e).repr x) i' = (b.repr x) (e.symm i') := by
  classical
  rw [OrthonormalBasis.repr_apply_apply, b.repr_apply_apply, OrthonormalBasis.coe_reindex]

end OrthonormalBasis

/-- If `f : E ≃ₗᵢ[𝕜] E'` is a linear isometry of inner product spaces then an orthonormal basis `v`
of `E` determines a linear isometry `e : E' ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι`. This result states that
`e` may be obtained either by transporting `v` to `E'` or by composing with the linear isometry
`E ≃ₗᵢ[𝕜] euclidean_space 𝕜 ι` provided by `v`. -/
@[simp]
theorem Basis.map_isometry_euclidean_of_orthonormal (v : Basis ι 𝕜 E) (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') :
    ((v.map f.toLinearEquiv).toOrthonormalBasis (hv.map_linear_isometry_equiv f)).repr =
      f.symm.trans (v.toOrthonormalBasis hv).repr :=
  LinearIsometryEquiv.to_linear_equiv_injective <| v.map_equiv_fun _

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:30:4: unsupported: too many args: fin_cases ... #[[]]
/-- `ℂ` is isometric to `ℝ²` with the Euclidean inner product. -/
def Complex.isometryEuclidean : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Finₓ 2) :=
  (Complex.basisOneI.toOrthonormalBasis
      (by
        rw [orthonormal_iff_ite]
        intro i
        fin_cases i <;> intro j <;> fin_cases j <;> simp [← real_inner_eq_re_inner])).repr

@[simp]
theorem Complex.isometry_euclidean_symm_apply (x : EuclideanSpace ℝ (Finₓ 2)) :
    Complex.isometryEuclidean.symm x = x 0 + x 1 * I := by
  convert complex.basis_one_I.equiv_fun_symm_apply x
  · simpa
    
  · simp
    

theorem Complex.isometry_euclidean_proj_eq_self (z : ℂ) :
    ↑(Complex.isometryEuclidean z 0) + ↑(Complex.isometryEuclidean z 1) * (i : ℂ) = z := by
  rw [← Complex.isometry_euclidean_symm_apply (Complex.isometryEuclidean z),
    complex.isometry_euclidean.symm_apply_apply z]

@[simp]
theorem Complex.isometry_euclidean_apply_zero (z : ℂ) : Complex.isometryEuclidean z 0 = z.re := by
  conv_rhs => rw [← Complex.isometry_euclidean_proj_eq_self z]
  simp

@[simp]
theorem Complex.isometry_euclidean_apply_one (z : ℂ) : Complex.isometryEuclidean z 1 = z.im := by
  conv_rhs => rw [← Complex.isometry_euclidean_proj_eq_self z]
  simp

/-- The isometry between `ℂ` and a two-dimensional real inner product space given by a basis. -/
def Complex.isometryOfOrthonormal {v : Basis (Finₓ 2) ℝ F} (hv : Orthonormal ℝ v) : ℂ ≃ₗᵢ[ℝ] F :=
  Complex.isometryEuclidean.trans (v.toOrthonormalBasis hv).repr.symm

@[simp]
theorem Complex.map_isometry_of_orthonormal {v : Basis (Finₓ 2) ℝ F} (hv : Orthonormal ℝ v) (f : F ≃ₗᵢ[ℝ] F') :
    Complex.isometryOfOrthonormal (hv.map_linear_isometry_equiv f) = (Complex.isometryOfOrthonormal hv).trans f := by
  simp [← Complex.isometryOfOrthonormal, ← LinearIsometryEquiv.trans_assoc]

theorem Complex.isometry_of_orthonormal_symm_apply {v : Basis (Finₓ 2) ℝ F} (hv : Orthonormal ℝ v) (f : F) :
    (Complex.isometryOfOrthonormal hv).symm f = (v.Coord 0 f : ℂ) + (v.Coord 1 f : ℂ) * I := by
  simp [← Complex.isometryOfOrthonormal]

theorem Complex.isometry_of_orthonormal_apply {v : Basis (Finₓ 2) ℝ F} (hv : Orthonormal ℝ v) (z : ℂ) :
    Complex.isometryOfOrthonormal hv z = z.re • v 0 + z.im • v 1 := by
  simp [← Complex.isometryOfOrthonormal, ←
    (by
      decide : (Finset.univ : Finset (Finₓ 2)) = {0, 1})]

open FiniteDimensional

/-! ### Existence of orthonormal basis, etc. -/


section FiniteDimensional

variable {v : Set E}

variable {A : ι → Submodule 𝕜 E}

/-- Given an internal direct sum decomposition of a module `M`, and an orthonormal basis for each
of the components of the direct sum, the disjoint union of these orthonormal bases is an
orthonormal basis for `M`. -/
noncomputable def DirectSum.IsInternal.collectedOrthonormalBasis
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => A i) _ fun i => (A i).subtypeₗᵢ) [DecidableEq ι]
    (hV_sum : DirectSum.IsInternal fun i => A i) {α : ι → Type _} [∀ i, Fintype (α i)]
    (v_family : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) : OrthonormalBasis (Σi, α i) 𝕜 E :=
  (hV_sum.collectedBasis fun i => (v_family i).toBasis).toOrthonormalBasis <| by
    simpa using
      hV.orthonormal_sigma_orthonormal
        (show ∀ i, Orthonormal 𝕜 (v_family i).toBasis by
          simp )

theorem DirectSum.IsInternal.collected_orthonormal_basis_mem [DecidableEq ι] (h : DirectSum.IsInternal A)
    {α : ι → Type _} [∀ i, Fintype (α i)] (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => A i) _ fun i => (A i).subtypeₗᵢ)
    (v : ∀ i, OrthonormalBasis (α i) 𝕜 (A i)) (a : Σi, α i) : h.collectedOrthonormalBasis hV v a ∈ A a.1 := by
  simp [← DirectSum.IsInternal.collectedOrthonormalBasis]

variable [FiniteDimensional 𝕜 E]

/-- In a finite-dimensional `inner_product_space`, any orthonormal subset can be extended to an
orthonormal basis. -/
theorem _root_.orthonormal.exists_orthonormal_basis_extension (hv : Orthonormal 𝕜 (coe : v → E)) :
    ∃ (u : Finset E)(b : OrthonormalBasis u 𝕜 E), v ⊆ u ∧ ⇑b = coe := by
  obtain ⟨u₀, hu₀s, hu₀, hu₀_max⟩ := exists_maximal_orthonormal hv
  rw [maximal_orthonormal_iff_orthogonal_complement_eq_bot hu₀] at hu₀_max
  have hu₀_finite : u₀.finite := hu₀.linear_independent.finite
  let u : Finset E := hu₀_finite.to_finset
  let fu : ↥u ≃ ↥u₀ := Equivₓ.cast (congr_arg coeSort hu₀_finite.coe_to_finset)
  have hfu : (coe : u → E) = (coe : u₀ → E) ∘ fu := by
    ext
    simp
  have hu : Orthonormal 𝕜 (coe : u → E) := by
    simpa [← hfu] using hu₀.comp _ fu.injective
  refine' ⟨u, OrthonormalBasis.mkOfOrthogonalEqBot hu _, _, _⟩
  · simpa using hu₀_max
    
  · simpa using hu₀s
    
  · simp
    

variable (𝕜 E)

/-- A finite-dimensional inner product space admits an orthonormal basis. -/
theorem _root_.exists_orthonormal_basis : ∃ (w : Finset E)(b : OrthonormalBasis w 𝕜 E), ⇑b = (coe : w → E) :=
  let ⟨w, hw, hw', hw''⟩ := (orthonormal_empty 𝕜 E).exists_orthonormal_basis_extension
  ⟨w, hw, hw''⟩

/-- Index for an arbitrary orthonormal basis on a finite-dimensional `inner_product_space`. -/
def orthonormalBasisIndex : Finset E :=
  Classical.some (exists_orthonormal_basis 𝕜 E)

/-- A finite-dimensional `inner_product_space` has an orthonormal basis. -/
def stdOrthonormalBasis : OrthonormalBasis (orthonormalBasisIndex 𝕜 E) 𝕜 E :=
  Classical.some (Classical.some_spec (exists_orthonormal_basis 𝕜 E))

@[simp]
theorem coe_std_orthonormal_basis : ⇑(stdOrthonormalBasis 𝕜 E) = coe :=
  Classical.some_spec (Classical.some_spec (exists_orthonormal_basis 𝕜 E))

variable {𝕜 E}

/-- An `n`-dimensional `inner_product_space` has an orthonormal basis indexed by `fin n`. -/
def finStdOrthonormalBasis {n : ℕ} (hn : finrank 𝕜 E = n) : OrthonormalBasis (Finₓ n) 𝕜 E :=
  have h : Fintype.card (orthonormalBasisIndex 𝕜 E) = n := by
    rw [← finrank_eq_card_basis (stdOrthonormalBasis 𝕜 E).toBasis, hn]
  (stdOrthonormalBasis 𝕜 E).reindex (Fintype.equivFinOfCardEq h)

section SubordinateOrthonormalBasis

open DirectSum

variable {n : ℕ} (hn : finrank 𝕜 E = n) [DecidableEq ι] {V : ι → Submodule 𝕜 E} (hV : IsInternal V)

/-- Exhibit a bijection between `fin n` and the index set of a certain basis of an `n`-dimensional
inner product space `E`.  This should not be accessed directly, but only via the subsequent API. -/
irreducible_def DirectSum.IsInternal.sigmaOrthonormalBasisIndexEquiv
  (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) :
  (Σi, orthonormalBasisIndex 𝕜 (V i)) ≃ Finₓ n :=
  let b := hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)
  Fintype.equivFinOfCardEq <| (FiniteDimensional.finrank_eq_card_basis b.toBasis).symm.trans hn

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. -/
irreducible_def DirectSum.IsInternal.subordinateOrthonormalBasis
  (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) : OrthonormalBasis (Finₓ n) 𝕜 E :=
  (hV.collectedOrthonormalBasis hV' fun i => stdOrthonormalBasis 𝕜 (V i)).reindex
    (hV.sigmaOrthonormalBasisIndexEquiv hn hV')

/-- An `n`-dimensional `inner_product_space` equipped with a decomposition as an internal direct
sum has an orthonormal basis indexed by `fin n` and subordinate to that direct sum. This function
provides the mapping by which it is subordinate. -/
def DirectSum.IsInternal.subordinateOrthonormalBasisIndex (a : Finₓ n)
    (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) : ι :=
  ((hV.sigmaOrthonormalBasisIndexEquiv hn hV').symm a).1

/-- The basis constructed in `orthogonal_family.subordinate_orthonormal_basis` is subordinate to
the `orthogonal_family` in question. -/
theorem DirectSum.IsInternal.subordinate_orthonormal_basis_subordinate (a : Finₓ n)
    (hV' : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) :
    hV.subordinateOrthonormalBasis hn hV' a ∈ V (hV.subordinateOrthonormalBasisIndex hn a hV') := by
  simpa only [← DirectSum.IsInternal.subordinateOrthonormalBasis, ← OrthonormalBasis.coe_reindex] using
    hV.collected_orthonormal_basis_mem hV' (fun i => stdOrthonormalBasis 𝕜 (V i))
      ((hV.sigma_orthonormal_basis_index_equiv hn hV').symm a)

end SubordinateOrthonormalBasis

end FiniteDimensional

attribute [local instance] fact_finite_dimensional_of_finrank_eq_succ

/-- Given a natural number `n` one less than the `finrank` of a finite-dimensional inner product
space, there exists an isometry from the orthogonal complement of a nonzero singleton to
`euclidean_space 𝕜 (fin n)`. -/
def OrthonormalBasis.fromOrthogonalSpanSingleton (n : ℕ) [Fact (finrank 𝕜 E = n + 1)] {v : E} (hv : v ≠ 0) :
    OrthonormalBasis (Finₓ n) 𝕜 (𝕜∙v)ᗮ :=
  finStdOrthonormalBasis (finrank_orthogonal_span_singleton hv)

section LinearIsometry

variable {V : Type _} [InnerProductSpace 𝕜 V] [FiniteDimensional 𝕜 V]

variable {S : Submodule 𝕜 V} {L : S →ₗᵢ[𝕜] V}

open FiniteDimensional

/-- Let `S` be a subspace of a finite-dimensional complex inner product space `V`.  A linear
isometry mapping `S` into `V` can be extended to a full isometry of `V`.

TODO:  The case when `S` is a finite-dimensional subspace of an infinite-dimensional `V`.-/
noncomputable def LinearIsometry.extend (L : S →ₗᵢ[𝕜] V) : V →ₗᵢ[𝕜] V := by
  -- Build an isometry from Sᗮ to L(S)ᗮ through euclidean_space
  let d := finrank 𝕜 Sᗮ
  have dim_S_perp : finrank 𝕜 Sᗮ = d := rfl
  let LS := L.to_linear_map.range
  have E : Sᗮ ≃ₗᵢ[𝕜] LSᗮ := by
    have dim_LS_perp : finrank 𝕜 LSᗮ = d
    calc finrank 𝕜 LSᗮ = finrank 𝕜 V - finrank 𝕜 LS := by
        simp only [LS.finrank_add_finrank_orthogonal, ← add_tsub_cancel_left]_ = finrank 𝕜 V - finrank 𝕜 S := by
        simp only [← LinearMap.finrank_range_of_inj L.injective]_ = finrank 𝕜 Sᗮ := by
        simp only [S.finrank_add_finrank_orthogonal, ← add_tsub_cancel_left]_ = d := dim_S_perp
    let BS := finStdOrthonormalBasis dim_S_perp
    let BLS := finStdOrthonormalBasis dim_LS_perp
    exact BS.repr.trans BLS.repr.symm
  let L3 := LSᗮ.subtypeₗᵢ.comp E.to_linear_isometry
  -- Project onto S and Sᗮ
  have : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  have : CompleteSpace V := FiniteDimensional.complete 𝕜 V
  let p1 := (orthogonalProjection S).toLinearMap
  let p2 := (orthogonalProjection Sᗮ).toLinearMap
  -- Build a linear map from the isometries on S and Sᗮ
  let M := L.to_linear_map.comp p1 + L3.to_linear_map.comp p2
  -- Prove that M is an isometry
  have M_norm_map : ∀ x : V, ∥M x∥ = ∥x∥ := by
    intro x
    -- Apply M to the orthogonal decomposition of x
    have Mx_decomp : M x = L (p1 x) + L3 (p2 x) := by
      simp only [← LinearMap.add_apply, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ←
        LinearIsometry.coe_to_linear_map]
    -- Mx_decomp is the orthogonal decomposition of M x
    have Mx_orth : ⟪L (p1 x), L3 (p2 x)⟫ = 0 := by
      have Lp1x : L (p1 x) ∈ L.to_linear_map.range := L.to_linear_map.mem_range_self (p1 x)
      have Lp2x : L3 (p2 x) ∈ L.to_linear_map.rangeᗮ := by
        simp only [← L3, ← LinearIsometry.coe_comp, ← Function.comp_app, ← Submodule.coe_subtypeₗᵢ,
          Submodule.range_subtype LSᗮ]
        apply LinearMap.mem_range_self
      apply Submodule.inner_right_of_mem_orthogonal Lp1x Lp2x
    -- Apply the Pythagorean theorem and simplify
    rw [← sq_eq_sq (norm_nonneg _) (norm_nonneg _), norm_sq_eq_add_norm_sq_projection x S]
    simp only [← sq, ← Mx_decomp]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (L (p1 x)) (L3 (p2 x)) Mx_orth]
    simp only [← LinearIsometry.norm_map, ← p1, ← p2, ← ContinuousLinearMap.to_linear_map_eq_coe, ← add_left_injₓ, ←
      mul_eq_mul_left_iff, ← norm_eq_zero, ← true_orₓ, ← eq_self_iff_true, ← ContinuousLinearMap.coe_coe, ←
      Submodule.coe_norm, ← Submodule.coe_eq_zero]
  exact { toLinearMap := M, norm_map' := M_norm_map }

theorem LinearIsometry.extend_apply (L : S →ₗᵢ[𝕜] V) (s : S) : L.extend s = L s := by
  have : CompleteSpace S := FiniteDimensional.complete 𝕜 S
  simp only [← LinearIsometry.extend, ← ContinuousLinearMap.to_linear_map_eq_coe, LinearIsometry.coe_to_linear_map]
  simp only [← add_right_eq_selfₓ, ← LinearIsometry.coe_to_linear_map, ← LinearIsometryEquiv.coe_to_linear_isometry, ←
    LinearIsometry.coe_comp, ← Function.comp_app, ← orthogonal_projection_mem_subspace_eq_self, ← LinearMap.coe_comp, ←
    ContinuousLinearMap.coe_coe, ← Submodule.coe_subtype, ← LinearMap.add_apply, ← Submodule.coe_eq_zero, ←
    LinearIsometryEquiv.map_eq_zero_iff, ← Submodule.coe_subtypeₗᵢ, ←
    orthogonal_projection_mem_subspace_orthogonal_complement_eq_zero, ← Submodule.orthogonal_orthogonal, ←
    Submodule.coe_mem]

end LinearIsometry

section Matrix

open Matrix

variable {n m : ℕ}

-- mathport name: «expr⟪ , ⟫ₘ»
local notation "⟪" x ", " y "⟫ₘ" => @inner 𝕜 (EuclideanSpace 𝕜 (Finₓ m)) _ x y

-- mathport name: «expr⟪ , ⟫ₙ»
local notation "⟪" x ", " y "⟫ₙ" => @inner 𝕜 (EuclideanSpace 𝕜 (Finₓ n)) _ x y

/-- The inner product of a row of A and a row of B is an entry of B ⬝ Aᴴ. -/
theorem inner_matrix_row_row (A B : Matrix (Finₓ n) (Finₓ m) 𝕜) (i j : Finₓ n) : ⟪A i, B j⟫ₘ = (B ⬝ Aᴴ) j i := by
  simp only [← inner, ← Matrix.mul_apply, ← star_ring_end_apply, ← Matrix.conj_transpose_apply, ← mul_comm]

/-- The inner product of a column of A and a column of B is an entry of Aᴴ ⬝ B -/
theorem inner_matrix_col_col (A B : Matrix (Finₓ n) (Finₓ m) 𝕜) (i j : Finₓ m) : ⟪Aᵀ i, Bᵀ j⟫ₙ = (Aᴴ ⬝ B) i j :=
  rfl

end Matrix

