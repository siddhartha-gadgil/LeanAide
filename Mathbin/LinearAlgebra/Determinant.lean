/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathbin.LinearAlgebra.Multilinear.Basis
import Mathbin.LinearAlgebra.Matrix.Reindex
import Mathbin.RingTheory.AlgebraTower
import Mathbin.Tactic.FieldSimp
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.Basis

/-!
# Determinant of families of vectors

This file defines the determinant of an endomorphism, and of a family of vectors
with respect to some basis. For the determinant of a matrix, see the file
`linear_algebra.matrix.determinant`.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `basis.det`: the determinant of a family of vectors with respect to a basis,
   as a multilinear map
 * `linear_map.det`: the determinant of an endomorphism `f : End R M` as a
   multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
   result is `1` instead)
 * `linear_equiv.det`: the determinant of an isomorphism `f : M ≃ₗ[R] M` as a
   multiplicative homomorphism (if `M` does not have a finite `R`-basis, the
   result is `1` instead)

## Tags

basis, det, determinant
-/


noncomputable section

open BigOperators

open Matrix

open LinearMap

open Submodule

universe u v w

open LinearMap Matrix Set Function

variable {R : Type _} [CommRingₓ R]

variable {M : Type _} [AddCommGroupₓ M] [Module R M]

variable {M' : Type _} [AddCommGroupₓ M'] [Module R M']

variable {ι : Type _} [DecidableEq ι] [Fintype ι]

variable (e : Basis ι R M)

section Conjugate

variable {A : Type _} [CommRingₓ A]

variable {m n : Type _} [Fintype m] [Fintype n]

/-- If `R^m` and `R^n` are linearly equivalent, then `m` and `n` are also equivalent. -/
def equivOfPiLequivPi {R : Type _} [CommRingₓ R] [Nontrivial R] (e : (m → R) ≃ₗ[R] n → R) : m ≃ n :=
  Basis.indexEquiv (Basis.ofEquivFun e.symm) (Pi.basisFun _ _)

namespace Matrix

/-- If `M` and `M'` are each other's inverse matrices, they are square matrices up to
equivalence of types. -/
def indexEquivOfInv [Nontrivial A] [DecidableEq m] [DecidableEq n] {M : Matrix m n A} {M' : Matrix n m A}
    (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) : m ≃ n :=
  equivOfPiLequivPi (toLin'OfInv hMM' hM'M)

theorem det_comm [DecidableEq n] (M N : Matrix n n A) : det (M ⬝ N) = det (N ⬝ M) := by
  rw [det_mul, det_mul, mul_comm]

/-- If there exists a two-sided inverse `M'` for `M` (indexed differently),
then `det (N ⬝ M) = det (M ⬝ N)`. -/
theorem det_comm' [DecidableEq m] [DecidableEq n] {M : Matrix n m A} {N : Matrix m n A} {M' : Matrix m n A}
    (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) : det (M ⬝ N) = det (N ⬝ M) := by
  nontriviality A
  -- Although `m` and `n` are different a priori, we will show they have the same cardinality.
  -- This turns the problem into one for square matrices, which is easy.
  let e := index_equiv_of_inv hMM' hM'M
  rw [← det_minor_equiv_self e, ← minor_mul_equiv _ _ _ (Equivₓ.refl n) _, det_comm, minor_mul_equiv, Equivₓ.coe_refl,
    minor_id_id]

/-- If `M'` is a two-sided inverse for `M` (indexed differently), `det (M ⬝ N ⬝ M') = det N`.

See `matrix.det_conj` and `matrix.det_conj'` for the case when `M' = M⁻¹` or vice versa. -/
theorem det_conj_of_mul_eq_one [DecidableEq m] [DecidableEq n] {M : Matrix m n A} {M' : Matrix n m A} {N : Matrix n n A}
    (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) : det (M ⬝ N ⬝ M') = det N := by
  rw [← det_comm' hM'M hMM', ← Matrix.mul_assoc, hM'M, Matrix.one_mul]

end Matrix

end Conjugate

namespace LinearMap

/-! ### Determinant of a linear map -/


variable {A : Type _} [CommRingₓ A] [Module A M]

variable {κ : Type _} [Fintype κ]

/-- The determinant of `linear_map.to_matrix` does not depend on the choice of basis. -/
theorem det_to_matrix_eq_det_to_matrix [DecidableEq κ] (b : Basis ι A M) (c : Basis κ A M) (f : M →ₗ[A] M) :
    det (LinearMap.toMatrix b b f) = det (LinearMap.toMatrix c c f) := by
  rw [← linear_map_to_matrix_mul_basis_to_matrix c b c, ← basis_to_matrix_mul_linear_map_to_matrix b c b,
      Matrix.det_conj_of_mul_eq_one] <;>
    rw [Basis.to_matrix_mul_to_matrix, Basis.to_matrix_self]

/-- The determinant of an endomorphism given a basis.

See `linear_map.det` for a version that populates the basis non-computably.

Although the `trunc (basis ι A M)` parameter makes it slightly more convenient to switch bases,
there is no good way to generalize over universe parameters, so we can't fully state in `det_aux`'s
type that it does not depend on the choice of basis. Instead you can use the `det_aux_def'` lemma,
or avoid mentioning a basis at all using `linear_map.det`.
-/
def detAux : Trunc (Basis ι A M) → (M →ₗ[A] M) →* A :=
  Trunc.lift (fun b : Basis ι A M => detMonoidHom.comp (toMatrixAlgEquiv b : (M →ₗ[A] M) →* Matrix ι ι A)) fun b c =>
    MonoidHom.ext <| det_to_matrix_eq_det_to_matrix b c

/-- Unfold lemma for `det_aux`.

See also `det_aux_def'` which allows you to vary the basis.
-/
theorem det_aux_def (b : Basis ι A M) (f : M →ₗ[A] M) :
    LinearMap.detAux (Trunc.mk b) f = Matrix.det (LinearMap.toMatrix b b f) :=
  rfl

-- Discourage the elaborator from unfolding `det_aux` and producing a huge term.
theorem det_aux_def' {ι' : Type _} [Fintype ι'] [DecidableEq ι'] (tb : Trunc <| Basis ι A M) (b' : Basis ι' A M)
    (f : M →ₗ[A] M) : LinearMap.detAux tb f = Matrix.det (LinearMap.toMatrix b' b' f) := by
  apply Trunc.induction_on tb
  intro b
  rw [det_aux_def, det_to_matrix_eq_det_to_matrix b b']

@[simp]
theorem det_aux_id (b : Trunc <| Basis ι A M) : LinearMap.detAux b LinearMap.id = 1 :=
  (LinearMap.detAux b).map_one

@[simp]
theorem det_aux_comp (b : Trunc <| Basis ι A M) (f g : M →ₗ[A] M) :
    LinearMap.detAux b (f.comp g) = LinearMap.detAux b f * LinearMap.detAux b g :=
  (LinearMap.detAux b).map_mul f g

section

open Classical

/-- The determinant of an endomorphism independent of basis.

If there is no finite basis on `M`, the result is `1` instead.
-/
-- Discourage the elaborator from unfolding `det` and producing a huge term by marking it
-- as irreducible.
protected irreducible_def det : (M →ₗ[A] M) →* A :=
  if H : ∃ s : Finset M, Nonempty (Basis s A M) then LinearMap.detAux (Trunc.mk H.some_spec.some) else 1

theorem coe_det [DecidableEq M] :
    ⇑(LinearMap.det : (M →ₗ[A] M) →* A) =
      if H : ∃ s : Finset M, Nonempty (Basis s A M) then LinearMap.detAux (Trunc.mk H.some_spec.some) else 1 :=
  by
  ext
  unfold LinearMap.det
  split_ifs
  · congr
    
  -- use the correct `decidable_eq` instance
  rfl

end

-- Auxiliary lemma, the `simp` normal form goes in the other direction
-- (using `linear_map.det_to_matrix`)
theorem det_eq_det_to_matrix_of_finset [DecidableEq M] {s : Finset M} (b : Basis s A M) (f : M →ₗ[A] M) :
    f.det = Matrix.det (LinearMap.toMatrix b b f) := by
  have : ∃ s : Finset M, Nonempty (Basis s A M) := ⟨s, ⟨b⟩⟩
  rw [LinearMap.coe_det, dif_pos, det_aux_def' _ b] <;> assumption

@[simp]
theorem det_to_matrix (b : Basis ι A M) (f : M →ₗ[A] M) : Matrix.det (toMatrix b b f) = f.det := by
  have := Classical.decEq M
  rw [det_eq_det_to_matrix_of_finset b.reindex_finset_range, det_to_matrix_eq_det_to_matrix b]

@[simp]
theorem det_to_matrix' {ι : Type _} [Fintype ι] [DecidableEq ι] (f : (ι → A) →ₗ[A] ι → A) : det f.toMatrix' = f.det :=
  by
  simp [to_matrix_eq_to_matrix']

@[simp]
theorem det_to_lin (b : Basis ι R M) (f : Matrix ι ι R) : LinearMap.det (Matrix.toLin b b f) = f.det := by
  rw [← LinearMap.det_to_matrix b, LinearMap.to_matrix_to_lin]

/-- To show `P f.det` it suffices to consider `P (to_matrix _ _ f).det` and `P 1`. -/
@[elab_as_eliminator]
theorem det_cases [DecidableEq M] {P : A → Prop} (f : M →ₗ[A] M)
    (hb : ∀ (s : Finset M) (b : Basis s A M), P (toMatrix b b f).det) (h1 : P 1) : P f.det := by
  unfold LinearMap.det
  split_ifs with h
  · convert hb _ h.some_spec.some
    apply det_aux_def'
    
  · exact h1
    

@[simp]
theorem det_comp (f g : M →ₗ[A] M) : (f.comp g).det = f.det * g.det :=
  LinearMap.det.map_mul f g

@[simp]
theorem det_id : (LinearMap.id : M →ₗ[A] M).det = 1 :=
  LinearMap.det.map_one

/-- Multiplying a map by a scalar `c` multiplies its determinant by `c ^ dim M`. -/
@[simp]
theorem det_smul {𝕜 : Type _} [Field 𝕜] {M : Type _} [AddCommGroupₓ M] [Module 𝕜 M] (c : 𝕜) (f : M →ₗ[𝕜] M) :
    LinearMap.det (c • f) = c ^ FiniteDimensional.finrank 𝕜 M * LinearMap.det f := by
  by_cases' H : ∃ s : Finset M, Nonempty (Basis s 𝕜 M)
  · have : FiniteDimensional 𝕜 M := by
      rcases H with ⟨s, ⟨hs⟩⟩
      exact FiniteDimensional.of_finset_basis hs
    simp only [det_to_matrix (FiniteDimensional.finBasis 𝕜 M), ← LinearEquiv.map_smul, ← Fintype.card_fin, ← det_smul]
    
  · classical
    have : FiniteDimensional.finrank 𝕜 M = 0 := finrank_eq_zero_of_not_exists_basis H
    simp [← coe_det, ← H, ← this]
    

theorem det_zero' {ι : Type _} [Fintype ι] [Nonempty ι] (b : Basis ι A M) : LinearMap.det (0 : M →ₗ[A] M) = 0 := by
  have := Classical.decEq ι
  rw [← det_to_matrix b, LinearEquiv.map_zero, det_zero]
  assumption

/-- In a finite-dimensional vector space, the zero map has determinant `1` in dimension `0`,
and `0` otherwise. We give a formula that also works in infinite dimension, where we define
the determinant to be `1`. -/
@[simp]
theorem det_zero {𝕜 : Type _} [Field 𝕜] {M : Type _} [AddCommGroupₓ M] [Module 𝕜 M] :
    LinearMap.det (0 : M →ₗ[𝕜] M) = (0 : 𝕜) ^ FiniteDimensional.finrank 𝕜 M := by
  simp only [zero_smul 𝕜 (1 : M →ₗ[𝕜] M), ← det_smul, ← mul_oneₓ, ← MonoidHom.map_one]

/-- Conjugating a linear map by a linear equiv does not change its determinant. -/
@[simp]
theorem det_conj {N : Type _} [AddCommGroupₓ N] [Module A N] (f : M →ₗ[A] M) (e : M ≃ₗ[A] N) :
    LinearMap.det ((e : M →ₗ[A] N) ∘ₗ f ∘ₗ (e.symm : N →ₗ[A] M)) = LinearMap.det f := by
  classical
  by_cases' H : ∃ s : Finset M, Nonempty (Basis s A M)
  · rcases H with ⟨s, ⟨b⟩⟩
    rw [← det_to_matrix b f, ← det_to_matrix (b.map e), to_matrix_comp (b.map e) b (b.map e),
      to_matrix_comp (b.map e) b b, ← Matrix.mul_assoc, Matrix.det_conj_of_mul_eq_one]
    · rw [← to_matrix_comp, LinearEquiv.comp_coe, e.symm_trans_self, LinearEquiv.refl_to_linear_map, to_matrix_id]
      
    · rw [← to_matrix_comp, LinearEquiv.comp_coe, e.self_trans_symm, LinearEquiv.refl_to_linear_map, to_matrix_id]
      
    
  · have H' : ¬∃ t : Finset N, Nonempty (Basis t A N) := by
      contrapose! H
      rcases H with ⟨s, ⟨b⟩⟩
      exact ⟨_, ⟨(b.map e.symm).reindexFinsetRange⟩⟩
    simp only [← coe_det, ← H, ← H', ← Pi.one_apply, ← dif_neg, ← not_false_iff]
    

/-- If a linear map is invertible, so is its determinant. -/
theorem is_unit_det {A : Type _} [CommRingₓ A] [Module A M] (f : M →ₗ[A] M) (hf : IsUnit f) : IsUnit f.det := by
  obtain ⟨g, hg⟩ : ∃ g, f.comp g = 1 := hf.exists_right_inv
  have : LinearMap.det f * LinearMap.det g = 1 := by
    simp only [LinearMap.det_comp, ← hg, ← MonoidHom.map_one]
  exact is_unit_of_mul_eq_one _ _ this

/-- If a linear map has determinant different from `1`, then the space is finite-dimensional. -/
theorem finite_dimensional_of_det_ne_one {𝕜 : Type _} [Field 𝕜] [Module 𝕜 M] (f : M →ₗ[𝕜] M) (hf : f.det ≠ 1) :
    FiniteDimensional 𝕜 M := by
  by_cases' H : ∃ s : Finset M, Nonempty (Basis s 𝕜 M)
  · rcases H with ⟨s, ⟨hs⟩⟩
    exact FiniteDimensional.of_finset_basis hs
    
  · classical
    simp [← LinearMap.coe_det, ← H] at hf
    exact hf.elim
    

/-- If the determinant of a map vanishes, then the map is not onto. -/
theorem range_lt_top_of_det_eq_zero {𝕜 : Type _} [Field 𝕜] [Module 𝕜 M] {f : M →ₗ[𝕜] M} (hf : f.det = 0) :
    f.range < ⊤ := by
  have : FiniteDimensional 𝕜 M := by
    simp [← f.finite_dimensional_of_det_ne_one, ← hf]
  contrapose hf
  simp only [← lt_top_iff_ne_top, ← not_not, is_unit_iff_range_eq_top] at hf
  exact is_unit_iff_ne_zero.1 (f.is_unit_det hf)

/-- If the determinant of a map vanishes, then the map is not injective. -/
theorem bot_lt_ker_of_det_eq_zero {𝕜 : Type _} [Field 𝕜] [Module 𝕜 M] {f : M →ₗ[𝕜] M} (hf : f.det = 0) : ⊥ < f.ker := by
  have : FiniteDimensional 𝕜 M := by
    simp [← f.finite_dimensional_of_det_ne_one, ← hf]
  contrapose hf
  simp only [← bot_lt_iff_ne_bot, ← not_not, is_unit_iff_ker_eq_bot] at hf
  exact is_unit_iff_ne_zero.1 (f.is_unit_det hf)

end LinearMap

namespace LinearEquiv

/-- On a `linear_equiv`, the domain of `linear_map.det` can be promoted to `Rˣ`. -/
protected def det : (M ≃ₗ[R] M) →* Rˣ :=
  (Units.map (LinearMap.det : (M →ₗ[R] M) →* R)).comp
    (LinearMap.GeneralLinearGroup.generalLinearEquiv R M).symm.toMonoidHom

@[simp]
theorem coe_det (f : M ≃ₗ[R] M) : ↑f.det = LinearMap.det (f : M →ₗ[R] M) :=
  rfl

@[simp]
theorem coe_inv_det (f : M ≃ₗ[R] M) : ↑f.det⁻¹ = LinearMap.det (f.symm : M →ₗ[R] M) :=
  rfl

@[simp]
theorem det_refl : (LinearEquiv.refl R M).det = 1 :=
  Units.ext <| LinearMap.det_id

@[simp]
theorem det_trans (f g : M ≃ₗ[R] M) : (f.trans g).det = g.det * f.det :=
  map_mul _ g f

@[simp]
theorem det_symm (f : M ≃ₗ[R] M) : f.symm.det = f.det⁻¹ :=
  map_inv _ f

/-- Conjugating a linear equiv by a linear equiv does not change its determinant. -/
@[simp]
theorem det_conj (f : M ≃ₗ[R] M) (e : M ≃ₗ[R] M') : ((e.symm.trans f).trans e).det = f.det := by
  rw [← Units.eq_iff, coe_det, coe_det, ← comp_coe, ← comp_coe, LinearMap.det_conj]

end LinearEquiv

/-- The determinants of a `linear_equiv` and its inverse multiply to 1. -/
@[simp]
theorem LinearEquiv.det_mul_det_symm {A : Type _} [CommRingₓ A] [Module A M] (f : M ≃ₗ[A] M) :
    (f : M →ₗ[A] M).det * (f.symm : M →ₗ[A] M).det = 1 := by
  simp [LinearMap.det_comp]

/-- The determinants of a `linear_equiv` and its inverse multiply to 1. -/
@[simp]
theorem LinearEquiv.det_symm_mul_det {A : Type _} [CommRingₓ A] [Module A M] (f : M ≃ₗ[A] M) :
    (f.symm : M →ₗ[A] M).det * (f : M →ₗ[A] M).det = 1 := by
  simp [LinearMap.det_comp]

-- Cannot be stated using `linear_map.det` because `f` is not an endomorphism.
theorem LinearEquiv.is_unit_det (f : M ≃ₗ[R] M') (v : Basis ι R M) (v' : Basis ι R M') :
    IsUnit (LinearMap.toMatrix v v' f).det := by
  apply is_unit_det_of_left_inverse
  simpa using (LinearMap.to_matrix_comp v v' v f.symm f).symm

/-- Specialization of `linear_equiv.is_unit_det` -/
theorem LinearEquiv.is_unit_det' {A : Type _} [CommRingₓ A] [Module A M] (f : M ≃ₗ[A] M) :
    IsUnit (LinearMap.det (f : M →ₗ[A] M)) :=
  is_unit_of_mul_eq_one _ _ f.det_mul_det_symm

/-- The determinant of `f.symm` is the inverse of that of `f` when `f` is a linear equiv. -/
theorem LinearEquiv.det_coe_symm {𝕜 : Type _} [Field 𝕜] [Module 𝕜 M] (f : M ≃ₗ[𝕜] M) :
    (f.symm : M →ₗ[𝕜] M).det = (f : M →ₗ[𝕜] M).det⁻¹ := by
  field_simp [← IsUnit.ne_zero f.is_unit_det']

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
@[simps]
def LinearEquiv.ofIsUnitDet {f : M →ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) : M ≃ₗ[R] M' where
  toFun := f
  map_add' := f.map_add
  map_smul' := f.map_smul
  invFun := toLin v' v (toMatrix v v' f)⁻¹
  left_inv := fun x =>
    calc
      toLin v' v (toMatrix v v' f)⁻¹ (f x) = toLin v v ((toMatrix v v' f)⁻¹ ⬝ toMatrix v v' f) x := by
        rw [to_lin_mul v v' v, to_lin_to_matrix, LinearMap.comp_apply]
      _ = x := by
        simp [← h]
      
  right_inv := fun x =>
    calc
      f (toLin v' v (toMatrix v v' f)⁻¹ x) = toLin v' v' (toMatrix v v' f ⬝ (toMatrix v v' f)⁻¹) x := by
        rw [to_lin_mul v' v v', LinearMap.comp_apply, to_lin_to_matrix v v']
      _ = x := by
        simp [← h]
      

@[simp]
theorem LinearEquiv.coe_of_is_unit_det {f : M →ₗ[R] M'} {v : Basis ι R M} {v' : Basis ι R M'}
    (h : IsUnit (LinearMap.toMatrix v v' f).det) : (LinearEquiv.ofIsUnitDet h : M →ₗ[R] M') = f := by
  ext x
  rfl

/-- Builds a linear equivalence from a linear map on a finite-dimensional vector space whose
determinant is nonzero. -/
@[reducible]
def LinearMap.equivOfDetNeZero {𝕜 : Type _} [Field 𝕜] {M : Type _} [AddCommGroupₓ M] [Module 𝕜 M]
    [FiniteDimensional 𝕜 M] (f : M →ₗ[𝕜] M) (hf : LinearMap.det f ≠ 0) : M ≃ₗ[𝕜] M :=
  have : IsUnit (LinearMap.toMatrix (FiniteDimensional.finBasis 𝕜 M) (FiniteDimensional.finBasis 𝕜 M) f).det := by
    simp only [← LinearMap.det_to_matrix, ← is_unit_iff_ne_zero.2 hf]
  LinearEquiv.ofIsUnitDet this

/-- The determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
def Basis.det : AlternatingMap R M R ι where
  toFun := fun v => det (e.toMatrix v)
  map_add' := by
    intro v i x y
    simp only [← e.to_matrix_update, ← LinearEquiv.map_add]
    apply det_update_column_add
  map_smul' := by
    intro u i c x
    simp only [← e.to_matrix_update, ← Algebra.id.smul_eq_mul, ← LinearEquiv.map_smul]
    apply det_update_column_smul
  map_eq_zero_of_eq' := by
    intro v i j h hij
    rw [← Function.update_eq_self i v, h, ← det_transpose, e.to_matrix_update, ← update_row_transpose, ←
      e.to_matrix_transpose_apply]
    apply det_zero_of_row_eq hij
    rw [update_row_ne hij.symm, update_row_self]

theorem Basis.det_apply (v : ι → M) : e.det v = det (e.toMatrix v) :=
  rfl

theorem Basis.det_self : e.det e = 1 := by
  simp [← e.det_apply]

/-- `basis.det` is not the zero map. -/
theorem Basis.det_ne_zero [Nontrivial R] : e.det ≠ 0 := fun h => by
  simpa [← h] using e.det_self

theorem is_basis_iff_det {v : ι → M} : LinearIndependent R v ∧ span R (Set.Range v) = ⊤ ↔ IsUnit (e.det v) := by
  constructor
  · rintro ⟨hli, hspan⟩
    set v' := Basis.mk hli hspan with v'_eq
    rw [e.det_apply]
    convert LinearEquiv.is_unit_det (LinearEquiv.refl _ _) v' e using 2
    ext i j
    simp
    
  · intro h
    rw [Basis.det_apply, Basis.to_matrix_eq_to_matrix_constr] at h
    set v' := Basis.map e (LinearEquiv.ofIsUnitDet h) with v'_def
    have : ⇑v' = v := by
      ext i
      rw [v'_def, Basis.map_apply, LinearEquiv.of_is_unit_det_apply, e.constr_basis]
    rw [← this]
    exact ⟨v'.linear_independent, v'.span_eq⟩
    

theorem Basis.is_unit_det (e' : Basis ι R M) : IsUnit (e.det e') :=
  (is_basis_iff_det e).mp ⟨e'.LinearIndependent, e'.span_eq⟩

/-- Any alternating map to `R` where `ι` has the cardinality of a basis equals the determinant
map with respect to that basis, multiplied by the value of that alternating map on that basis. -/
theorem AlternatingMap.eq_smul_basis_det (f : AlternatingMap R M R ι) : f = f e • e.det := by
  refine' Basis.ext_alternating e fun i h => _
  let σ : Equivₓ.Perm ι := Equivₓ.ofBijective i (Fintype.injective_iff_bijective.1 h)
  change f (e ∘ σ) = (f e • e.det) (e ∘ σ)
  simp [← AlternatingMap.map_perm, ← Basis.det_self]

@[simp]
theorem AlternatingMap.map_basis_eq_zero_iff (f : AlternatingMap R M R ι) : f e = 0 ↔ f = 0 :=
  ⟨fun h => by
    simpa [← h] using f.eq_smul_basis_det e, fun h => h.symm ▸ AlternatingMap.zero_apply _⟩

theorem AlternatingMap.map_basis_ne_zero_iff (f : AlternatingMap R M R ι) : f e ≠ 0 ↔ f ≠ 0 :=
  not_congr <| f.map_basis_eq_zero_iff e

variable {A : Type _} [CommRingₓ A] [Module A M]

@[simp]
theorem Basis.det_comp (e : Basis ι A M) (f : M →ₗ[A] M) (v : ι → M) : e.det (f ∘ v) = f.det * e.det v := by
  rw [Basis.det_apply, Basis.det_apply, ← f.det_to_matrix e, ← Matrix.det_mul, e.to_matrix_eq_to_matrix_constr (f ∘ v),
    e.to_matrix_eq_to_matrix_constr v, ← to_matrix_comp, e.constr_comp]

theorem Basis.det_reindex {ι' : Type _} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) (v : ι' → M) (e : ι ≃ ι') :
    (b.reindex e).det v = b.det (v ∘ e) := by
  rw [Basis.det_apply, Basis.to_matrix_reindex', det_reindex_alg_equiv, Basis.det_apply]

theorem Basis.det_reindex_symm {ι' : Type _} [Fintype ι'] [DecidableEq ι'] (b : Basis ι R M) (v : ι → M) (e : ι' ≃ ι) :
    (b.reindex e.symm).det (v ∘ e) = b.det v := by
  rw [Basis.det_reindex, Function.comp.assoc, e.self_comp_symm, Function.comp.right_id]

@[simp]
theorem Basis.det_map (b : Basis ι R M) (f : M ≃ₗ[R] M') (v : ι → M') : (b.map f).det v = b.det (f.symm ∘ v) := by
  rw [Basis.det_apply, Basis.to_matrix_map, Basis.det_apply]

theorem Basis.det_map' (b : Basis ι R M) (f : M ≃ₗ[R] M') : (b.map f).det = b.det.compLinearMap f.symm :=
  AlternatingMap.ext <| b.det_map f

@[simp]
theorem Pi.basis_fun_det : (Pi.basisFun R ι).det = Matrix.detRowAlternating := by
  ext M
  rw [Basis.det_apply, Basis.CoePiBasisFun.to_matrix_eq_transpose, det_transpose]

/-- If we fix a background basis `e`, then for any other basis `v`, we can characterise the
coordinates provided by `v` in terms of determinants relative to `e`. -/
theorem Basis.det_smul_mk_coord_eq_det_update {v : ι → M} (hli : LinearIndependent R v) (hsp : span R (Range v) = ⊤)
    (i : ι) : e.det v • (Basis.mk hli hsp).Coord i = e.det.toMultilinearMap.toLinearMap v i := by
  apply (Basis.mk hli hsp).ext
  intro k
  rcases eq_or_ne k i with (rfl | hik) <;>
    simp only [← Algebra.id.smul_eq_mul, ← Basis.coe_mk, ← LinearMap.smul_apply, ← LinearMap.coe_mk, ←
      MultilinearMap.to_linear_map_apply]
  · rw [Basis.mk_coord_apply_eq, mul_oneₓ, update_eq_self]
    congr
    
  · rw [Basis.mk_coord_apply_ne hik, mul_zero, eq_comm]
    exact
      e.det.map_eq_zero_of_eq _
        (by
          simp [← hik, ← Function.update_apply])
        hik
    

/-- The determinant of a basis constructed by `units_smul` is the product of the given units. -/
@[simp]
theorem Basis.det_units_smul (w : ι → Rˣ) : e.det (e.units_smul w) = ∏ i, w i := by
  simp [← Basis.det_apply]

/-- The determinant of a basis constructed by `is_unit_smul` is the product of the given units. -/
@[simp]
theorem Basis.det_is_unit_smul {w : ι → R} (hw : ∀ i, IsUnit (w i)) : e.det (e.isUnitSmul hw) = ∏ i, w i :=
  e.det_units_smul _

