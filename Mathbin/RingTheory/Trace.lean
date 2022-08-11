/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.LinearAlgebra.Matrix.BilinearForm
import Mathbin.LinearAlgebra.Matrix.Charpoly.Minpoly
import Mathbin.LinearAlgebra.Determinant
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.Vandermonde
import Mathbin.LinearAlgebra.Trace
import Mathbin.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathbin.FieldTheory.PrimitiveElement
import Mathbin.FieldTheory.Galois
import Mathbin.RingTheory.PowerBasis

/-!
# Trace for (finite) ring extensions.

Suppose we have an `R`-algebra `S` with a finite basis. For each `s : S`,
the trace of the linear map given by multiplying by `s` gives information about
the roots of the minimal polynomial of `s` over `R`.

## Main definitions

 * `algebra.trace R S x`: the trace of an element `s` of an `R`-algebra `S`
 * `algebra.trace_form R S`: bilinear form sending `x`, `y` to the trace of `x * y`
 * `algebra.trace_matrix R b`: the matrix whose `(i j)`-th element is the trace of `b i * b j`.
 * `algebra.embeddings_matrix A C b : matrix κ (B →ₐ[A] C) C` is the matrix whose
   `(i, σ)` coefficient is `σ (b i)`.
 * `algebra.embeddings_matrix_reindex A C b e : matrix κ κ C` is the matrix whose `(i, j)`
   coefficient is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ`
   given by a bijection `e : κ ≃ (B →ₐ[A] C)`.

## Main results

 * `trace_algebra_map_of_basis`, `trace_algebra_map`: if `x : K`, then `Tr_{L/K} x = [L : K] x`
 * `trace_trace_of_basis`, `trace_trace`: `Tr_{L/K} (Tr_{F/L} x) = Tr_{F/K} x`
 * `trace_eq_sum_roots`: the trace of `x : K(x)` is the sum of all conjugate roots of `x`
 * `trace_eq_sum_embeddings`: the trace of `x : K(x)` is the sum of all embeddings of `x` into an
   algebraically closed field
 * `trace_form_nondegenerate`: the trace form over a separable extension is a nondegenerate
   bilinear form

## Implementation notes

Typically, the trace is defined specifically for finite field extensions.
The definition is as general as possible and the assumption that we have
fields or that the extension is finite is added to the lemmas as needed.

We only define the trace for left multiplication (`algebra.left_mul_matrix`,
i.e. `algebra.lmul_left`).
For now, the definitions assume `S` is commutative, so the choice doesn't matter anyway.

## References

 * https://en.wikipedia.org/wiki/Field_trace

-/


universe u v w z

variable {R S T : Type _} [CommRingₓ R] [CommRingₓ S] [CommRingₓ T]

variable [Algebra R S] [Algebra R T]

variable {K L : Type _} [Field K] [Field L] [Algebra K L]

variable {ι κ : Type w} [Fintype ι]

open FiniteDimensional

open LinearMap

open Matrix

open BigOperators

open Matrix

namespace Algebra

variable (b : Basis ι R S)

variable (R S)

/-- The trace of an element `s` of an `R`-algebra is the trace of `(*) s`,
as an `R`-linear map. -/
noncomputable def trace : S →ₗ[R] R :=
  (LinearMap.trace R S).comp (lmul R S).toLinearMap

variable {S}

-- Not a `simp` lemma since there are more interesting ways to rewrite `trace R S x`,
-- for example `trace_trace`
theorem trace_apply (x) : trace R S x = LinearMap.trace R S (lmul R S x) :=
  rfl

theorem trace_eq_zero_of_not_exists_basis (h : ¬∃ s : Finset S, Nonempty (Basis s R S)) : trace R S = 0 := by
  ext s
  simp [← trace_apply, ← LinearMap.trace, ← h]

include b

variable {R}

-- Can't be a `simp` lemma because it depends on a choice of basis
theorem trace_eq_matrix_trace [DecidableEq ι] (b : Basis ι R S) (s : S) :
    trace R S s = Matrix.trace (Algebra.leftMulMatrix b s) := by
  rw [trace_apply, LinearMap.trace_eq_matrix_trace _ b, to_matrix_lmul_eq]

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`. -/
theorem trace_algebra_map_of_basis (x : R) : trace R S (algebraMap R S x) = Fintype.card ι • x := by
  have := Classical.decEq ι
  rw [trace_apply, LinearMap.trace_eq_matrix_trace R b, Matrix.trace]
  convert Finset.sum_const _
  ext i
  simp

omit b

/-- If `x` is in the base field `K`, then the trace is `[L : K] * x`.

(If `L` is not finite-dimensional over `K`, then `trace` and `finrank` return `0`.)
-/
@[simp]
theorem trace_algebra_map (x : K) : trace K L (algebraMap K L x) = finrank K L • x := by
  by_cases' H : ∃ s : Finset L, Nonempty (Basis s K L)
  · rw [trace_algebra_map_of_basis H.some_spec.some, finrank_eq_card_basis H.some_spec.some]
    
  · simp [← trace_eq_zero_of_not_exists_basis K H, ← finrank_eq_zero_of_not_exists_basis_finset H]
    

theorem trace_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type _} [Fintype ι] [Fintype κ]
    (b : Basis ι R S) (c : Basis κ S T) (x : T) : trace R S (trace S T x) = trace R T x := by
  have := Classical.decEq ι
  have := Classical.decEq κ
  rw [trace_eq_matrix_trace (b.smul c), trace_eq_matrix_trace b, trace_eq_matrix_trace c, Matrix.trace, Matrix.trace,
    Matrix.trace, ← Finset.univ_product_univ, Finset.sum_product]
  refine' Finset.sum_congr rfl fun i _ => _
  simp only [← AlgHom.map_sum, ← smul_left_mul_matrix, ← Finset.sum_apply, ← Matrix.diag,
    ←-- The unifier is not smart enough to apply this one by itself:
      Finset.sum_apply
      i _ fun y => left_mul_matrix b (left_mul_matrix c x y y)]

theorem trace_comp_trace_of_basis [Algebra S T] [IsScalarTower R S T] {ι κ : Type _} [Fintype ι] [Fintype κ]
    (b : Basis ι R S) (c : Basis κ S T) : (trace R S).comp ((trace S T).restrictScalars R) = trace R T := by
  ext
  rw [LinearMap.comp_apply, LinearMap.restrict_scalars_apply, trace_trace_of_basis b c]

@[simp]
theorem trace_trace [Algebra K T] [Algebra L T] [IsScalarTower K L T] [FiniteDimensional K L] [FiniteDimensional L T]
    (x : T) : trace K L (trace L T x) = trace K T x :=
  trace_trace_of_basis (Basis.ofVectorSpace K L) (Basis.ofVectorSpace L T) x

@[simp]
theorem trace_comp_trace [Algebra K T] [Algebra L T] [IsScalarTower K L T] [FiniteDimensional K L]
    [FiniteDimensional L T] : (trace K L).comp ((trace L T).restrictScalars K) = trace K T := by
  ext
  rw [LinearMap.comp_apply, LinearMap.restrict_scalars_apply, trace_trace]

section TraceForm

variable (R S)

/-- The `trace_form` maps `x y : S` to the trace of `x * y`.
It is a symmetric bilinear form and is nondegenerate if the extension is separable. -/
noncomputable def traceForm : BilinForm R S :=
  (LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)).toBilin

variable {S}

-- This is a nicer lemma than the one produced by `@[simps] def trace_form`.
@[simp]
theorem trace_form_apply (x y : S) : traceForm R S x y = trace R S (x * y) :=
  rfl

theorem trace_form_is_symm : (traceForm R S).IsSymm := fun x y => congr_arg (trace R S) (mul_comm _ _)

theorem trace_form_to_matrix [DecidableEq ι] (i j) : BilinForm.toMatrix b (traceForm R S) i j = trace R S (b i * b j) :=
  by
  rw [BilinForm.to_matrix_apply, trace_form_apply]

theorem trace_form_to_matrix_power_basis (h : PowerBasis R S) :
    BilinForm.toMatrix h.Basis (traceForm R S) = of fun i j => trace R S (h.gen ^ (↑i + ↑j : ℕ)) := by
  ext
  rw [trace_form_to_matrix, of_apply, pow_addₓ, h.basis_eq_pow, h.basis_eq_pow]

end TraceForm

end Algebra

section EqSumRoots

open Algebra Polynomial

variable {F : Type _} [Field F]

variable [Algebra K S] [Algebra K F]

/-- Given `pb : power_basis K S`, the trace of `pb.gen` is `-(minpoly K pb.gen).next_coeff`. -/
theorem PowerBasis.trace_gen_eq_next_coeff_minpoly [Nontrivial S] (pb : PowerBasis K S) :
    Algebra.trace K S pb.gen = -(minpoly K pb.gen).nextCoeff := by
  have d_pos : 0 < pb.dim := PowerBasis.dim_pos pb
  have d_pos' : 0 < (minpoly K pb.gen).natDegree := by
    simpa
  have : Nonempty (Finₓ pb.dim) := ⟨⟨0, d_pos⟩⟩
  rw [trace_eq_matrix_trace pb.basis, trace_eq_neg_charpoly_coeff, charpoly_left_mul_matrix, ← pb.nat_degree_minpoly,
    Fintype.card_fin, ← next_coeff_of_pos_nat_degree _ d_pos']

/-- Given `pb : power_basis K S`, then the trace of `pb.gen` is
`((minpoly K pb.gen).map (algebra_map K F)).roots.sum`. -/
theorem PowerBasis.trace_gen_eq_sum_roots [Nontrivial S] (pb : PowerBasis K S)
    (hf : (minpoly K pb.gen).Splits (algebraMap K F)) :
    algebraMap K F (trace K S pb.gen) = ((minpoly K pb.gen).map (algebraMap K F)).roots.Sum := by
  rw [PowerBasis.trace_gen_eq_next_coeff_minpoly, RingHom.map_neg, ← next_coeff_map (algebraMap K F).Injective,
    sum_roots_eq_next_coeff_of_monic_of_split ((minpoly.monic (PowerBasis.is_integral_gen _)).map _)
      ((splits_id_iff_splits _).2 hf),
    neg_negₓ]

namespace IntermediateField.AdjoinSimple

open IntermediateField

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem trace_gen_eq_zero {x : L} (hx : ¬IsIntegral K x) : Algebra.trace K K⟮⟯ (AdjoinSimple.gen K x) = 0 := by
  rw [trace_eq_zero_of_not_exists_basis, LinearMap.zero_apply]
  contrapose! hx
  obtain ⟨s, ⟨b⟩⟩ := hx
  refine' is_integral_of_mem_of_fg K⟮⟯.toSubalgebra _ x _
  · exact (Submodule.fg_iff_finite_dimensional _).mpr (FiniteDimensional.of_finset_basis b)
    
  · exact subset_adjoin K _ (Set.mem_singleton x)
    

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem trace_gen_eq_sum_roots (x : L) (hf : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (trace K K⟮⟯ (AdjoinSimple.gen K x)) = ((minpoly K x).map (algebraMap K F)).roots.Sum := by
  have injKxL := (algebraMap K⟮⟯ L).Injective
  by_cases' hx : IsIntegral K x
  swap
  · simp [← minpoly.eq_zero hx, ← trace_gen_eq_zero hx]
    
  have hx' : IsIntegral K (adjoin_simple.gen K x) := by
    rwa [← is_integral_algebra_map_iff injKxL, adjoin_simple.algebra_map_gen]
    infer_instance
  rw [← adjoin.power_basis_gen hx, (adjoin.power_basis hx).trace_gen_eq_sum_roots] <;>
    rw [adjoin.power_basis_gen hx, minpoly.eq_of_algebra_map_eq injKxL hx'] <;>
      try
        simp only [← adjoin_simple.algebra_map_gen _ _]
  exact hf

end IntermediateField.AdjoinSimple

open IntermediateField

variable (K)

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem trace_eq_trace_adjoin [FiniteDimensional K L] (x : L) :
    Algebra.trace K L x = finrank K⟮⟯ L • trace K K⟮⟯ (AdjoinSimple.gen K x) := by
  rw [← @trace_trace _ _ K K⟮⟯ _ _ _ _ _ _ _ _ x]
  conv in x => rw [← IntermediateField.AdjoinSimple.algebra_map_gen K x]
  rw [trace_algebra_map, LinearMap.map_smul_of_tower]

variable {K}

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem trace_eq_sum_roots [FiniteDimensional K L] {x : L} (hF : (minpoly K x).Splits (algebraMap K F)) :
    algebraMap K F (Algebra.trace K L x) = finrank K⟮⟯ L • ((minpoly K x).map (algebraMap K _)).roots.Sum := by
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, RingHom.map_mul, ← Algebra.smul_def,
    IntermediateField.AdjoinSimple.trace_gen_eq_sum_roots _ hF, IsScalarTower.algebra_map_smul]

end EqSumRoots

variable {F : Type _} [Field F]

variable [Algebra R L] [Algebra L F] [Algebra R F] [IsScalarTower R L F]

open Polynomial

theorem Algebra.is_integral_trace [FiniteDimensional L F] {x : F} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace L F x) := by
  have hx' : _root_.is_integral L x := is_integral_of_is_scalar_tower _ hx
  rw [← is_integral_algebra_map_iff (algebraMap L (AlgebraicClosure F)).Injective, trace_eq_sum_roots]
  · refine' (IsIntegral.multiset_sum _).nsmul _
    intro y hy
    rw [mem_roots_map (minpoly.ne_zero hx')] at hy
    use minpoly R x, minpoly.monic hx
    rw [← aeval_def] at hy⊢
    exact minpoly.aeval_of_is_scalar_tower R x y hy
    
  · apply IsAlgClosed.splits_codomain
    
  · infer_instance
    

section EqSumEmbeddings

variable [Algebra K F] [IsScalarTower K L F]

open Algebra IntermediateField

variable (F) (E : Type _) [Field E] [Algebra K E]

theorem trace_eq_sum_embeddings_gen (pb : PowerBasis K L) (hE : (minpoly K pb.gen).Splits (algebraMap K E))
    (hfx : (minpoly K pb.gen).Separable) :
    algebraMap K E (Algebra.trace K L pb.gen) = (@Finset.univ (PowerBasis.AlgHom.fintype pb)).Sum fun σ => σ pb.gen :=
  by
  let this := Classical.decEq E
  rw [pb.trace_gen_eq_sum_roots hE, Fintype.sum_equiv pb.lift_equiv', Finset.sum_mem_multiset,
    Finset.sum_eq_multiset_sum, Multiset.to_finset_val, multiset.dedup_eq_self.mpr _, Multiset.map_id]
  · exact nodup_roots ((separable_map _).mpr hfx)
    
  · intro x
    rfl
    
  · intro σ
    rw [PowerBasis.lift_equiv'_apply_coe, id.def]
    

variable [IsAlgClosed E]

theorem sum_embeddings_eq_finrank_mul [FiniteDimensional K F] [IsSeparable K F] (pb : PowerBasis K L) :
    (∑ σ : F →ₐ[K] E, σ (algebraMap L F pb.gen)) =
      finrank L F • (@Finset.univ (PowerBasis.AlgHom.fintype pb)).Sum fun σ : L →ₐ[K] E => σ pb.gen :=
  by
  have : FiniteDimensional L F := FiniteDimensional.right K L F
  have : IsSeparable L F := is_separable_tower_top_of_is_separable K L F
  let this : Fintype (L →ₐ[K] E) := PowerBasis.AlgHom.fintype pb
  let this : ∀ f : L →ₐ[K] E, Fintype (@AlgHom L F E _ _ _ _ f.to_ring_hom.to_algebra) := _
  -- will be solved by unification
  rw [Fintype.sum_equiv algHomEquivSigma (fun σ : F →ₐ[K] E => _) fun σ => σ.1 pb.gen, ← Finset.univ_sigma_univ,
    Finset.sum_sigma, ← Finset.sum_nsmul]
  refine' Finset.sum_congr rfl fun σ _ => _
  · let this : Algebra L E := σ.to_ring_hom.to_algebra
    simp only [← Finset.sum_const, ← Finset.card_univ]
    rw [AlgHom.card L F E]
    
  · intro σ
    simp only [← algHomEquivSigma, ← Equivₓ.coe_fn_mk, ← AlgHom.restrictDomain, ← AlgHom.comp_apply, ←
      IsScalarTower.coe_to_alg_hom']
    

-- ./././Mathport/Syntax/Translate/Basic.lean:956:11: unsupported (impossible)
theorem trace_eq_sum_embeddings [FiniteDimensional K L] [IsSeparable K L] {x : L} :
    algebraMap K E (Algebra.trace K L x) = ∑ σ : L →ₐ[K] E, σ x := by
  have hx := IsSeparable.is_integral K x
  rw [trace_eq_trace_adjoin K x, Algebra.smul_def, RingHom.map_mul, ← adjoin.power_basis_gen hx,
    trace_eq_sum_embeddings_gen E (adjoin.power_basis hx) (IsAlgClosed.splits_codomain _), ← Algebra.smul_def,
    algebra_map_smul]
  · exact (sum_embeddings_eq_finrank_mul L E (adjoin.power_basis hx)).symm
    
  · have := is_separable_tower_bot_of_is_separable K K⟮⟯ L
    exact IsSeparable.separable K _
    

theorem trace_eq_sum_automorphisms (x : L) [FiniteDimensional K L] [IsGalois K L] :
    algebraMap K L (Algebra.trace K L x) = ∑ σ : L ≃ₐ[K] L, σ x := by
  apply NoZeroSmulDivisors.algebra_map_injective L (AlgebraicClosure L)
  rw [map_sum (algebraMap L (AlgebraicClosure L))]
  rw [← Fintype.sum_equiv (Normal.algHomEquivAut K (AlgebraicClosure L) L)]
  · rw [← trace_eq_sum_embeddings (AlgebraicClosure L)]
    · simp only [← algebra_map_eq_smul_one, ← smul_one_smul]
      
    · exact IsGalois.to_is_separable
      
    
  · intro σ
    simp only [← Normal.algHomEquivAut, ← AlgHom.restrictNormal', ← Equivₓ.coe_fn_mk, ← AlgEquiv.coe_of_bijective, ←
      AlgHom.restrict_normal_commutes, ← id.map_eq_id, ← RingHom.id_apply]
    

end EqSumEmbeddings

section DetNeZero

namespace Algebra

variable (A : Type u) {B : Type v} (C : Type z)

variable [CommRingₓ A] [CommRingₓ B] [Algebra A B] [CommRingₓ C] [Algebra A C]

open Finset

/-- Given an `A`-algebra `B` and `b`, an `κ`-indexed family of elements of `B`, we define
`trace_matrix A b` as the matrix whose `(i j)`-th element is the trace of `b i * b j`. -/
@[simp]
noncomputable def traceMatrix (b : κ → B) : Matrix κ κ A
  | i, j => traceForm A B (b i) (b j)

theorem trace_matrix_def (b : κ → B) : traceMatrix A b = of fun i j => traceForm A B (b i) (b j) :=
  rfl

theorem trace_matrix_reindex {κ' : Type _} (b : Basis κ A B) (f : κ ≃ κ') :
    traceMatrix A (b.reindex f) = reindex f f (traceMatrix A b) := by
  ext x y
  simp

variable {A}

theorem trace_matrix_of_matrix_vec_mul [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A ((P.map (algebraMap A B)).vecMul b) = Pᵀ ⬝ traceMatrix A b ⬝ P := by
  ext α β
  rw [trace_matrix, vec_mul, dot_product, vec_mul, dot_product, Matrix.mul_apply, BilinForm.sum_left,
    Fintype.sum_congr _ _ fun i : κ =>
      @BilinForm.sum_right _ _ _ _ _ _ _ _ (b i * P.map (algebraMap A B) i α) fun y : κ =>
        b y * P.map (algebraMap A B) y β,
    sum_comm]
  congr
  ext x
  rw [Matrix.mul_apply, sum_mul]
  congr
  ext y
  rw [map_apply, trace_form_apply, mul_comm (b y), ← smul_def]
  simp only [← id.smul_eq_mul, ← RingHom.id_apply, ← map_apply, ← transpose_apply, ← LinearMap.map_smulₛₗ, ←
    trace_form_apply, ← Algebra.smul_mul_assoc]
  rw [mul_comm (b x), ← smul_def]
  ring_nf
  simp [← mul_comm]

theorem trace_matrix_of_matrix_mul_vec [Fintype κ] (b : κ → B) (P : Matrix κ κ A) :
    traceMatrix A ((P.map (algebraMap A B)).mulVec b) = P ⬝ traceMatrix A b ⬝ Pᵀ := by
  refine' AddEquiv.injective transpose_add_equiv _
  rw [transpose_add_equiv_apply, transpose_add_equiv_apply, ← vec_mul_transpose, ← transpose_map,
    trace_matrix_of_matrix_vec_mul, transpose_transpose, transpose_mul, transpose_transpose, transpose_mul]

theorem trace_matrix_of_basis [Fintype κ] [DecidableEq κ] (b : Basis κ A B) :
    traceMatrix A b = BilinForm.toMatrix b (traceForm A B) := by
  ext i j
  rw [trace_matrix, trace_form_apply, trace_form_to_matrix]

theorem trace_matrix_of_basis_mul_vec (b : Basis ι A B) (z : B) :
    (traceMatrix A b).mulVec (b.equivFun z) = fun i => trace A B (z * b i) := by
  ext i
  rw [← col_apply ((trace_matrix A b).mulVec (b.equiv_fun z)) i Unit.star, col_mul_vec, Matrix.mul_apply,
    trace_matrix_def]
  simp only [← col_apply, ← trace_form_apply]
  conv_lhs => congr skip ext rw [mul_comm _ (b.equiv_fun z _), ← smul_eq_mul, of_apply, ← LinearMap.map_smul]
  rw [← LinearMap.map_sum]
  congr
  conv_lhs => congr skip ext rw [← mul_smul_comm]
  rw [← Finset.mul_sum, mul_comm z]
  congr
  rw [b.sum_equiv_fun]

variable (A)

/-- `embeddings_matrix A C b : matrix κ (B →ₐ[A] C) C` is the matrix whose `(i, σ)` coefficient is
  `σ (b i)`. It is mostly useful for fields when `fintype.card κ = finrank A B` and `C` is
  algebraically closed. -/
@[simp]
def embeddingsMatrix (b : κ → B) : Matrix κ (B →ₐ[A] C) C
  | i, σ => σ (b i)

/-- `embeddings_matrix_reindex A C b e : matrix κ κ C` is the matrix whose `(i, j)` coefficient
  is `σⱼ (b i)`, where `σⱼ : B →ₐ[A] C` is the embedding corresponding to `j : κ` given by a
  bijection `e : κ ≃ (B →ₐ[A] C)`. It is mostly useful for fields and `C` is algebraically closed.
  In this case, in presence of `h : fintype.card κ = finrank A B`, one can take
  `e := equiv_of_card_eq ((alg_hom.card A B C).trans h.symm)`. -/
def embeddingsMatrixReindex (b : κ → B) (e : κ ≃ (B →ₐ[A] C)) :=
  reindex (Equivₓ.refl κ) e.symm (embeddingsMatrix A C b)

variable {A}

theorem embeddings_matrix_reindex_eq_vandermonde (pb : PowerBasis A B) (e : Finₓ pb.dim ≃ (B →ₐ[A] C)) :
    embeddingsMatrixReindex A C pb.Basis e = (vandermonde fun i => e i pb.gen)ᵀ := by
  ext i j
  simp [← embeddings_matrix_reindex, ← embeddings_matrix]

section Field

variable (K) {L} (E : Type z) [Field E]

variable [Algebra K E]

variable [Module.Finite K L] [IsSeparable K L] [IsAlgClosed E]

variable (b : κ → L) (pb : PowerBasis K L)

theorem trace_matrix_eq_embeddings_matrix_mul_trans :
    (traceMatrix K b).map (algebraMap K E) = embeddingsMatrix K E b ⬝ (embeddingsMatrix K E b)ᵀ := by
  ext i j
  simp [← trace_eq_sum_embeddings, ← embeddings_matrix, ← Matrix.mul_apply]

theorem trace_matrix_eq_embeddings_matrix_reindex_mul_trans [Fintype κ] (e : κ ≃ (L →ₐ[K] E)) :
    (traceMatrix K b).map (algebraMap K E) = embeddingsMatrixReindex K E b e ⬝ (embeddingsMatrixReindex K E b e)ᵀ := by
  rw [trace_matrix_eq_embeddings_matrix_mul_trans, embeddings_matrix_reindex, reindex_apply, transpose_minor, ←
    minor_mul_transpose_minor, ← Equivₓ.coe_refl, Equivₓ.refl_symm]

end Field

end Algebra

open Algebra

variable (pb : PowerBasis K L)

theorem det_trace_matrix_ne_zero' [IsSeparable K L] : det (traceMatrix K pb.Basis) ≠ 0 := by
  suffices algebraMap K (AlgebraicClosure L) (det (trace_matrix K pb.basis)) ≠ 0 by
    refine' mt (fun ht => _) this
    rw [ht, RingHom.map_zero]
  have : FiniteDimensional K L := pb.finite_dimensional
  let e : Finₓ pb.dim ≃ (L →ₐ[K] AlgebraicClosure L) := (Fintype.equivFinOfCardEq _).symm
  rw [RingHom.map_det, RingHom.map_matrix_apply, trace_matrix_eq_embeddings_matrix_reindex_mul_trans K _ _ e,
    embeddings_matrix_reindex_eq_vandermonde, det_mul, det_transpose]
  refine' mt mul_self_eq_zero.mp _
  · simp only [← det_vandermonde, ← Finset.prod_eq_zero_iff, ← not_exists, ← sub_eq_zero]
    intro i _ j hij h
    exact (finset.mem_Ioi.mp hij).ne' (e.injective <| pb.alg_hom_ext h)
    
  · rw [AlgHom.card, pb.finrank]
    

theorem det_trace_form_ne_zero [IsSeparable K L] [DecidableEq ι] (b : Basis ι K L) :
    det (BilinForm.toMatrix b (traceForm K L)) ≠ 0 := by
  have : FiniteDimensional K L := FiniteDimensional.of_fintype_basis b
  let pb : PowerBasis K L := Field.powerBasisOfFiniteOfSeparable _ _
  rw [← BilinForm.to_matrix_mul_basis_to_matrix pb.basis b, ← det_comm' (pb.basis.to_matrix_mul_to_matrix_flip b) _, ←
    Matrix.mul_assoc, det_mul]
  swap
  · apply Basis.to_matrix_mul_to_matrix_flip
    
  refine' mul_ne_zero (is_unit_of_mul_eq_one _ ((b.to_matrix pb.basis)ᵀ ⬝ b.to_matrix pb.basis).det _).ne_zero _
  · calc
      (pb.basis.to_matrix b ⬝ (pb.basis.to_matrix b)ᵀ).det * ((b.to_matrix pb.basis)ᵀ ⬝ b.to_matrix pb.basis).det =
          (pb.basis.to_matrix b ⬝ (b.to_matrix pb.basis ⬝ pb.basis.to_matrix b)ᵀ ⬝ b.to_matrix pb.basis).det :=
        by
        simp only [det_mul, ← Matrix.mul_assoc, ← Matrix.transpose_mul]_ = 1 := by
        simp only [← Basis.to_matrix_mul_to_matrix_flip, ← Matrix.transpose_one, ← Matrix.mul_one, ← Matrix.det_one]
    
  simpa only [← trace_matrix_of_basis] using det_trace_matrix_ne_zero' pb

variable (K L)

theorem trace_form_nondegenerate [FiniteDimensional K L] [IsSeparable K L] : (traceForm K L).Nondegenerate :=
  BilinForm.nondegenerate_of_det_ne_zero (traceForm K L) _ (det_trace_form_ne_zero (FiniteDimensional.finBasis K L))

end DetNeZero

