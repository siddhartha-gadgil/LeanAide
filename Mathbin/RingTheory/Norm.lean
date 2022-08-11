/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.FieldTheory.PrimitiveElement
import Mathbin.LinearAlgebra.Determinant
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathbin.LinearAlgebra.Matrix.ToLinearEquiv
import Mathbin.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathbin.FieldTheory.Galois

/-!
# Norm for (finite) ring extensions

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the determinant of the linear map given by multiplying by `s` gives information
about the roots of the minimal polynomial of `s` over `R`.

## Implementation notes

Typically, the norm is defined specifically for finite field extensions.
The current definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the norm for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't
matter anyway.

See also `algebra.trace`, which is defined similarly as the trace of
`algebra.left_mul_matrix`.

## References

 * https://en.wikipedia.org/wiki/Field_norm

-/


universe u v w

variable {R S T : Type _} [CommRingₓ R] [CommRingₓ S]

variable [Algebra R S]

variable {K L F : Type _} [Field K] [Field L] [Field F]

variable [Algebra K L] [Algebra K F]

variable {ι : Type w} [Fintype ι]

open FiniteDimensional

open LinearMap

open Matrix Polynomial

open BigOperators

open Matrix

namespace Algebra

variable (R)

/-- The norm of an element `s` of an `R`-algebra is the determinant of `(*) s`. -/
noncomputable def norm : S →* R :=
  LinearMap.det.comp (lmul R S).toRingHom.toMonoidHom

theorem norm_apply (x : S) : norm R x = LinearMap.det (lmul R S x) :=
  rfl

theorem norm_eq_one_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) (x : S) : norm R x = 1 := by
  rw [norm_apply, LinearMap.det]
  split_ifs with h
  rfl

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem norm_eq_matrix_det [DecidableEq ι] (b : Basis ι R S) (s : S) :
    norm R s = Matrix.det (Algebra.leftMulMatrix b s) := by
  rw [norm_apply, ← LinearMap.det_to_matrix b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`. -/
theorem norm_algebra_map_of_basis (b : Basis ι R S) (x : R) : norm R (algebraMap R S x) = x ^ Fintype.card ι := by
  have := Classical.decEq ι
  rw [norm_apply, ← det_to_matrix b, lmul_algebra_map]
  convert @det_diagonal _ _ _ _ _ fun i : ι => x
  · ext i j
    rw [to_matrix_lsmul, Matrix.diagonalₓ]
    
  · rw [Finset.prod_const, Finset.card_univ]
    

/-- If `x` is in the base field `K`, then the norm is `x ^ [L : K]`.

(If `L` is not finite-dimensional over `K`, then `norm = 1 = x ^ 0 = x ^ (finrank L K)`.)
-/
@[simp]
protected theorem norm_algebra_map {K L : Type _} [Field K] [CommRingₓ L] [Algebra K L] (x : K) :
    norm K (algebraMap K L x) = x ^ finrank K L := by
  by_cases' H : ∃ s : Finset L, Nonempty (Basis s K L)
  · rw [norm_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some]
    
  · rw [norm_eq_one_of_not_exists_basis K H, finrank_eq_zero_of_not_exists_basis, pow_zeroₓ]
    rintro ⟨s, ⟨b⟩⟩
    exact H ⟨s, ⟨b⟩⟩
    

section EqProdRoots

/-- Given `pb : power_basis K S`, then the norm of `pb.gen` is
`(-1) ^ pb.dim * coeff (minpoly K pb.gen) 0`. -/
theorem PowerBasis.norm_gen_eq_coeff_zero_minpoly [Algebra K S] (pb : PowerBasis K S) :
    norm K pb.gen = -1 ^ pb.dim * coeff (minpoly K pb.gen) 0 := by
  rw [norm_eq_matrix_det pb.basis, det_eq_sign_charpoly_coeff, charpoly_left_mul_matrix, Fintype.card_fin]

/-- Given `pb : power_basis K S`, then the norm of `pb.gen` is
`((minpoly K pb.gen).map (algebra_map K F)).roots.prod`. -/
theorem PowerBasis.norm_gen_eq_prod_roots [Algebra K S] (pb : PowerBasis K S)
    (hf : (minpoly K pb.gen).Splits (algebraMap K F)) :
    algebraMap K F (norm K pb.gen) = ((minpoly K pb.gen).map (algebraMap K F)).roots.Prod := by
  rw [power_basis.norm_gen_eq_coeff_zero_minpoly, ← pb.nat_degree_minpoly, RingHom.map_mul, ← coeff_map,
    prod_roots_eq_coeff_zero_of_monic_of_split ((minpoly.monic (PowerBasis.is_integral_gen _)).map _)
      ((splits_id_iff_splits _).2 hf),
    nat_degree_map, map_pow, ← mul_assoc, ← mul_powₓ]
  simp

end EqProdRoots

section EqZeroIff

theorem norm_eq_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} : Algebra.norm R x = 0 ↔ x = 0 :=
  by
  have hι : Nonempty ι := b.index_nonempty
  let this := Classical.decEq ι
  rw [Algebra.norm_eq_matrix_det b]
  constructor
  · rw [← Matrix.exists_mul_vec_eq_zero_iff]
    rintro ⟨v, v_ne, hv⟩
    rw [← b.equiv_fun.apply_symm_apply v, b.equiv_fun_symm_apply, b.equiv_fun_apply,
      Algebra.left_mul_matrix_mul_vec_repr] at hv
    refine' (mul_eq_zero.mp (b.ext_elem fun i => _)).resolve_right (show (∑ i, v i • b i) ≠ 0 from _)
    · simpa only [← LinearEquiv.map_zero, ← Pi.zero_apply] using congr_fun hv i
      
    · contrapose! v_ne with sum_eq
      apply b.equiv_fun.symm.injective
      rw [b.equiv_fun_symm_apply, sum_eq, LinearEquiv.map_zero]
      
    
  · rintro rfl
    rw [AlgHom.map_zero, Matrix.det_zero hι]
    

theorem norm_ne_zero_iff_of_basis [IsDomain R] [IsDomain S] (b : Basis ι R S) {x : S} : Algebra.norm R x ≠ 0 ↔ x ≠ 0 :=
  not_iff_not.mpr (Algebra.norm_eq_zero_iff_of_basis b)

/-- See also `algebra.norm_eq_zero_iff'` if you already have rewritten with `algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff {K L : Type _} [Field K] [CommRingₓ L] [Algebra K L] [IsDomain L] [FiniteDimensional K L]
    {x : L} : Algebra.norm K x = 0 ↔ x = 0 :=
  Algebra.norm_eq_zero_iff_of_basis (Basis.ofVectorSpace K L)

/-- This is `algebra.norm_eq_zero_iff` composed with `algebra.norm_apply`. -/
@[simp]
theorem norm_eq_zero_iff' {K L : Type _} [Field K] [CommRingₓ L] [Algebra K L] [IsDomain L] [FiniteDimensional K L]
    {x : L} : LinearMap.det (Algebra.lmul K L x) = 0 ↔ x = 0 :=
  Algebra.norm_eq_zero_iff_of_basis (Basis.ofVectorSpace K L)

end EqZeroIff

open IntermediateField

variable (K)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem norm_eq_norm_adjoin [FiniteDimensional K L] [IsSeparable K L] (x : L) :
    norm K x = norm K (AdjoinSimple.gen K x) ^ finrank K⟮⟯ L := by
  let this := is_separable_tower_top_of_is_separable K K⟮⟯ L
  let pbL := Field.powerBasisOfFiniteOfSeparable K⟮⟯ L
  let pbx := IntermediateField.adjoin.powerBasis (IsSeparable.is_integral K x)
  rw [← adjoin_simple.algebra_map_gen K x, norm_eq_matrix_det (pbx.basis.smul pbL.basis) _,
    smul_left_mul_matrix_algebra_map, det_block_diagonal, norm_eq_matrix_det pbx.basis]
  simp only [← Finset.card_fin, ← Finset.prod_const]
  congr
  rw [← PowerBasis.finrank, adjoin_simple.algebra_map_gen K x]

variable {K}

section IntermediateField

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem _root_.intermediate_field.adjoin_simple.norm_gen_eq_one {x : L} (hx : ¬IsIntegral K x) :
    norm K (AdjoinSimple.gen K x) = 1 := by
  rw [norm_eq_one_of_not_exists_basis]
  contrapose! hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine' is_integral_of_mem_of_fg K⟮⟯.toSubalgebra _ x _
  · exact (Submodule.fg_iff_finite_dimensional _).mpr (of_finset_basis b)
    
  · exact IntermediateField.subset_adjoin K _ (Set.mem_singleton x)
    

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem _root_.intermediate_field.adjoin_simple.norm_gen_eq_prod_roots (x : L)
    (hf : (minpoly K x).Splits (algebraMap K F)) :
    (algebraMap K F) (norm K (AdjoinSimple.gen K x)) = ((minpoly K x).map (algebraMap K F)).roots.Prod := by
  have injKxL := (algebraMap K⟮⟯ L).Injective
  by_cases' hx : _root_.is_integral K x
  swap
  · simp [← minpoly.eq_zero hx, ← IntermediateField.AdjoinSimple.norm_gen_eq_one hx]
    
  have hx' : _root_.is_integral K (adjoin_simple.gen K x) := by
    rwa [← is_integral_algebra_map_iff injKxL, adjoin_simple.algebra_map_gen]
    infer_instance
  rw [← adjoin.power_basis_gen hx, power_basis.norm_gen_eq_prod_roots] <;>
    rw [adjoin.power_basis_gen hx, minpoly.eq_of_algebra_map_eq injKxL hx'] <;>
      try
        simp only [← adjoin_simple.algebra_map_gen _ _]
  exact hf

end IntermediateField

section EqProdEmbeddings

open IntermediateField IntermediateField.AdjoinSimple Polynomial

theorem norm_eq_prod_embeddings_gen {K L : Type _} [Field K] [CommRingₓ L] [Algebra K L] (E : Type _) [Field E]
    [Algebra K E] (pb : PowerBasis K L) (hE : (minpoly K pb.gen).Splits (algebraMap K E))
    (hfx : (minpoly K pb.gen).Separable) :
    algebraMap K E (norm K pb.gen) = (@Finset.univ (PowerBasis.AlgHom.fintype pb)).Prod fun σ => σ pb.gen := by
  let this := Classical.decEq E
  rw [power_basis.norm_gen_eq_prod_roots pb hE, Fintype.prod_equiv pb.lift_equiv', Finset.prod_mem_multiset,
    Finset.prod_eq_multiset_prod, Multiset.to_finset_val, multiset.dedup_eq_self.mpr, Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
    
  · intro x
    rfl
    
  · intro σ
    rw [PowerBasis.lift_equiv'_apply_coe, id.def]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem norm_eq_prod_roots [IsSeparable K L] [FiniteDimensional K L] {x : L}
    (hF : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (norm K x) = ((minpoly K x).map (algebraMap K F)).roots.Prod ^ finrank K⟮⟯ L := by
  rw [norm_eq_norm_adjoin K x, map_pow, IntermediateField.AdjoinSimple.norm_gen_eq_prod_roots _ hF]

variable (F) (E : Type _) [Field E] [Algebra K E]

theorem prod_embeddings_eq_finrank_pow [Algebra L F] [IsScalarTower K L F] [IsAlgClosed E] [IsSeparable K F]
    [FiniteDimensional K F] (pb : PowerBasis K L) :
    (∏ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen)) =
      ((@Finset.univ (PowerBasis.AlgHom.fintype pb)).Prod fun σ : L →ₐ[K] E => σ pb.gen) ^ finrank L F :=
  by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : IsSeparable L F := is_separable_tower_top_of_is_separable K L F
  let this : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  let this : ∀ f : L →ₐ[K] E, Fintype (@AlgHom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _
  rw [Fintype.prod_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen, ← Finset.univ_sigma_univ,
    Finset.prod_sigma, ← Finset.prod_pow]
  refine' Finset.prod_congr rfl fun σ _ => _
  · let this : Algebra L E := σ.to_ring_hom.to_algebra
    simp only [← Finset.prod_const, ← Finset.card_univ]
    congr
    rw [AlgHom.card L F E]
    
  · intro σ
    simp only [← algHomEquivSigma, ← Equivₓ.coe_fn_mk, ← AlgHom.restrictDomain, ← AlgHom.comp_apply, ←
      IsScalarTower.coe_to_alg_hom']
    

variable (K)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
/-- For `L/K` a finite separable extension of fields and `E` an algebraically closed extension
of `K`, the norm (down to `K`) of an element `x` of `L` is equal to the product of the images
of `x` over all the `K`-embeddings `σ`  of `L` into `E`. -/
theorem norm_eq_prod_embeddings [FiniteDimensional K L] [IsSeparable K L] [IsAlgClosed E] {x : L} :
    algebraMap K E (norm K x) = ∏ σ : L →ₐ[K] E, σ x := by
  have hx := IsSeparable.is_integral K x
  rw [norm_eq_norm_adjoin K x, RingHom.map_pow, ← adjoin.power_basis_gen hx,
    norm_eq_prod_embeddings_gen E (adjoin.power_basis hx) (IsAlgClosed.splits_codomain _)]
  · exact (prod_embeddings_eq_finrank_pow L E (adjoin.power_basis hx)).symm
    
  · have := is_separable_tower_bot_of_is_separable K K⟮⟯ L
    exact IsSeparable.separable K _
    

theorem norm_eq_prod_automorphisms [FiniteDimensional K L] [IsGalois K L] {x : L} :
    algebraMap K L (norm K x) = ∏ σ : L ≃ₐ[K] L, σ x := by
  apply NoZeroSmulDivisors.algebra_map_injective L (AlgebraicClosure L)
  rw [map_prod (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.prod_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← norm_eq_prod_embeddings]
    simp only [← algebra_map_eq_smul_one, ← smul_one_smul]
    
  · intro σ
    simp only [← Normal.algHomEquivAut, ← AlgHom.restrictNormal', ← Equivₓ.coe_fn_mk, ← AlgEquiv.coe_of_bijective, ←
      AlgHom.restrict_normal_commutes, ← id.map_eq_id, ← RingHom.id_apply]
    

theorem is_integral_norm [Algebra S L] [Algebra S K] [IsScalarTower S K L] [IsSeparable K L] [FiniteDimensional K L]
    {x : L} (hx : IsIntegral S x) : IsIntegral S (norm K x) := by
  have hx' : _root_.is_integral K x := is_integral_of_is_scalar_tower _ hx
  rw [← is_integral_algebra_map_iff (algebraMap K (AlgebraicClosure L)).Injective, norm_eq_prod_roots]
  · refine' (IsIntegral.multiset_prod fun y hy => _).pow _
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly S x, minpoly.monic hx
    rw [← aeval_def] at hy⊢
    exact minpoly.aeval_of_is_scalar_tower S x y hy
    
  · apply IsAlgClosed.splits_codomain
    
  · infer_instance
    

end EqProdEmbeddings

end Algebra

