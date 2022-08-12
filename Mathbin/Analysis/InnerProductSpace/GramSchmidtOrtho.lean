/-
Copyright (c) 2022 Jiale Miao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiale Miao, Kevin Buzzard, Alexander Bentkamp
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Order.WellFoundedSet
import Mathbin.Analysis.InnerProductSpace.PiL2

/-!
# Gram-Schmidt Orthogonalization and Orthonormalization

In this file we introduce Gram-Schmidt Orthogonalization and Orthonormalization.

The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span.

## Main results

- `gram_schmidt` : the Gram-Schmidt process
- `gram_schmidt_orthogonal` :
  `gram_schmidt` produces an orthogonal system of vectors.
- `span_gram_schmidt` :
  `gram_schmidt` preserves span of vectors.
- `gram_schmidt_ne_zero` :
  If the input vectors of `gram_schmidt` are linearly independent,
  then the output vectors are non-zero.
- `gram_schmidt_basis` :
  The basis produced by the Gram-Schmidt process when given a basis as input.
- `gram_schmidt_normed` :
  the normalized `gram_schmidt` (i.e each vector in `gram_schmidt_normed` has unit length.)
- `gram_schmidt_orthornormal` :
  `gram_schmidt_normed` produces an orthornormal system of vectors.

## TODO
  Construct a version with an orthonormal basis from Gram-Schmidt process.
-/


open BigOperators

open Finset

variable (𝕜 : Type _) {E : Type _} [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

variable {ι : Type _} [LinearOrderₓ ι] [LocallyFiniteOrderBot ι] [IsWellOrder ι (· < ·)]

attribute [local instance] IsWellOrder.toHasWellFounded

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The Gram-Schmidt process takes a set of vectors as input
and outputs a set of orthogonal vectors which have the same span. -/
noncomputable def gramSchmidt (f : ι → E) : ι → E
  | n => f n - ∑ i : iio n, orthogonalProjection (𝕜∙gramSchmidt i) (f n)

/-- This lemma uses `∑ i in` instead of `∑ i :`.-/
theorem gram_schmidt_def (f : ι → E) (n : ι) :
    gramSchmidt 𝕜 f n = f n - ∑ i in iio n, orthogonalProjection (𝕜∙gramSchmidt 𝕜 f i) (f n) := by
  rw [← sum_attach, attach_eq_univ, gramSchmidt]
  rfl

theorem gram_schmidt_def' (f : ι → E) (n : ι) :
    f n = gramSchmidt 𝕜 f n + ∑ i in iio n, orthogonalProjection (𝕜∙gramSchmidt 𝕜 f i) (f n) := by
  rw [gram_schmidt_def, sub_add_cancel]

@[simp]
theorem gram_schmidt_zero {ι : Type _} [LinearOrderₓ ι] [LocallyFiniteOrder ι] [OrderBot ι] [IsWellOrder ι (· < ·)]
    (f : ι → E) : gramSchmidt 𝕜 f ⊥ = f ⊥ := by
  rw [gram_schmidt_def, Iio_eq_Ico, Finset.Ico_self, Finset.sum_empty, sub_zero]

/-- **Gram-Schmidt Orthogonalisation**:
`gram_schmidt` produces an orthogonal system of vectors. -/
theorem gram_schmidt_orthogonal (f : ι → E) {a b : ι} (h₀ : a ≠ b) : ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 := by
  suffices ∀ a b : ι, a < b → ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 by
    cases' h₀.lt_or_lt with ha hb
    · exact this _ _ ha
      
    · rw [inner_eq_zero_sym]
      exact this _ _ hb
      
  clear h₀ a b
  intro a b h₀
  revert a
  apply WellFounded.induction (@IsWellOrder.wf ι (· < ·) _) b
  intro b ih a h₀
  simp only [← gram_schmidt_def 𝕜 f b, ← inner_sub_right, ← inner_sum, ← orthogonal_projection_singleton, ←
    inner_smul_right]
  rw [Finset.sum_eq_single_of_mem a (finset.mem_Iio.mpr h₀)]
  · by_cases' h : gramSchmidt 𝕜 f a = 0
    · simp only [← h, ← inner_zero_left, ← zero_div, ← zero_mul, ← sub_zero]
      
    · rw [← inner_self_eq_norm_sq_to_K, div_mul_cancel, sub_self]
      rwa [Ne.def, inner_self_eq_zero]
      
    
  simp_intro i hi hia only [← Finset.mem_range]
  simp only [← mul_eq_zero, ← div_eq_zero_iff, ← inner_self_eq_zero]
  right
  cases' hia.lt_or_lt with hia₁ hia₂
  · rw [inner_eq_zero_sym]
    exact ih a h₀ i hia₁
    
  · exact ih i (mem_Iio.1 hi) a hia₂
    

/-- This is another version of `gram_schmidt_orthogonal` using `pairwise` instead. -/
theorem gram_schmidt_pairwise_orthogonal (f : ι → E) : Pairwise fun a b => ⟪gramSchmidt 𝕜 f a, gramSchmidt 𝕜 f b⟫ = 0 :=
  fun a b => gram_schmidt_orthogonal 𝕜 f

open Submodule Set Order

theorem mem_span_gram_schmidt (f : ι → E) {i j : ι} (hij : i ≤ j) : f i ∈ span 𝕜 (gramSchmidt 𝕜 f '' Iic j) := by
  rw [gram_schmidt_def' 𝕜 f i]
  simp_rw [orthogonal_projection_singleton]
  exact
    Submodule.add_mem _ (subset_span <| mem_image_of_mem _ hij)
      ((Submodule.sum_mem _) fun k hk =>
        smul_mem (span 𝕜 (gramSchmidt 𝕜 f '' Iic j)) _ <|
          subset_span <| mem_image_of_mem (gramSchmidt 𝕜 f) <| (Finset.mem_Iio.1 hk).le.trans hij)

theorem gram_schmidt_mem_span (f : ι → E) : ∀ {j i}, i ≤ j → gramSchmidt 𝕜 f i ∈ span 𝕜 (f '' Iic j)
  | j => fun i hij => by
    rw [gram_schmidt_def 𝕜 f i]
    simp_rw [orthogonal_projection_singleton]
    refine' Submodule.sub_mem _ (subset_span (mem_image_of_mem _ hij)) ((Submodule.sum_mem _) fun k hk => _)
    let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
    exact smul_mem _ _ (span_mono (image_subset f <| Iic_subset_Iic.2 hkj.le) <| gram_schmidt_mem_span le_rfl)

theorem span_gram_schmidt_Iic (f : ι → E) (c : ι) : span 𝕜 (gramSchmidt 𝕜 f '' Iic c) = span 𝕜 (f '' Iic c) :=
  span_eq_span (Set.image_subset_iff.2 fun i => gram_schmidt_mem_span _ _) <|
    Set.image_subset_iff.2 fun i => mem_span_gram_schmidt _ _

theorem span_gram_schmidt_Iio (f : ι → E) (c : ι) : span 𝕜 (gramSchmidt 𝕜 f '' Iio c) = span 𝕜 (f '' Iio c) :=
  span_eq_span
      (Set.image_subset_iff.2 fun i hi =>
        span_mono (image_subset _ <| Iic_subset_Iio.2 hi) <| gram_schmidt_mem_span _ _ le_rfl) <|
    Set.image_subset_iff.2 fun i hi =>
      span_mono (image_subset _ <| Iic_subset_Iio.2 hi) <| mem_span_gram_schmidt _ _ le_rfl

/-- `gram_schmidt` preserves span of vectors. -/
theorem span_gram_schmidt (f : ι → E) : span 𝕜 (Range (gramSchmidt 𝕜 f)) = span 𝕜 (Range f) :=
  span_eq_span (range_subset_iff.2 fun i => span_mono (image_subset_range _ _) <| gram_schmidt_mem_span _ _ le_rfl) <|
    range_subset_iff.2 fun i => span_mono (image_subset_range _ _) <| mem_span_gram_schmidt _ _ le_rfl

theorem gram_schmidt_ne_zero_coe (f : ι → E) (n : ι) (h₀ : LinearIndependent 𝕜 (f ∘ (coe : Set.Iic n → ι))) :
    gramSchmidt 𝕜 f n ≠ 0 := by
  by_contra h
  have h₁ : f n ∈ span 𝕜 (f '' Iio n) := by
    rw [← span_gram_schmidt_Iio 𝕜 f n, gram_schmidt_def' _ f, h, zero_addₓ]
    apply Submodule.sum_mem _ _
    simp_intro a ha only [← Finset.mem_Ico]
    simp only [← Set.mem_image, ← Set.mem_Iio, ← orthogonal_projection_singleton]
    apply Submodule.smul_mem _ _ _
    rw [Finset.mem_Iio] at ha
    refine'
      subset_span
        ⟨a, ha, by
          rfl⟩
  have h₂ : (f ∘ (coe : Set.Iic n → ι)) ⟨n, le_reflₓ n⟩ ∈ span 𝕜 (f ∘ (coe : Set.Iic n → ι) '' Iio ⟨n, le_reflₓ n⟩) :=
    by
    rw [image_comp]
    convert h₁ using 3
    ext i
    simpa using @le_of_ltₓ _ _ i n
  apply LinearIndependent.not_mem_span_image h₀ _ h₂
  simp only [← Set.mem_Iio, ← lt_self_iff_false, ← not_false_iff]

/-- If the input vectors of `gram_schmidt` are linearly independent,
then the output vectors are non-zero. -/
theorem gram_schmidt_ne_zero (f : ι → E) (n : ι) (h₀ : LinearIndependent 𝕜 f) : gramSchmidt 𝕜 f n ≠ 0 :=
  gram_schmidt_ne_zero_coe _ _ _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/-- `gram_schmidt` produces a triangular matrix of vectors when given a basis. -/
theorem gram_schmidt_triangular {i j : ι} (hij : i < j) (b : Basis ι 𝕜 E) : b.repr (gramSchmidt 𝕜 b i) j = 0 := by
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (gramSchmidt 𝕜 b '' Set.Iio j) :=
    subset_span ((Set.mem_image _ _ _).2 ⟨i, hij, rfl⟩)
  have : gramSchmidt 𝕜 b i ∈ span 𝕜 (b '' Set.Iio j) := by
    rwa [← span_gram_schmidt_Iio 𝕜 b j]
  have : ↑(b.repr (gramSchmidt 𝕜 b i)).support ⊆ Set.Iio j := Basis.repr_support_subset_of_mem_span b (Set.Iio j) this
  exact (Finsupp.mem_supported' _ _).1 ((Finsupp.mem_supported 𝕜 _).2 this) j (not_mem_Iio.2 (le_reflₓ j))

/-- `gram_schmidt` produces linearly independent vectors when given linearly independent vectors. -/
theorem gram_schmidt_linear_independent (f : ι → E) (h₀ : LinearIndependent 𝕜 f) :
    LinearIndependent 𝕜 (gramSchmidt 𝕜 f) :=
  linear_independent_of_ne_zero_of_inner_eq_zero (fun i => gram_schmidt_ne_zero _ _ _ h₀) fun i j =>
    gram_schmidt_orthogonal 𝕜 f

/-- When given a basis, `gram_schmidt` produces a basis. -/
noncomputable def gramSchmidtBasis (b : Basis ι 𝕜 E) : Basis ι 𝕜 E :=
  Basis.mk (gram_schmidt_linear_independent 𝕜 b b.LinearIndependent) ((span_gram_schmidt 𝕜 b).trans b.span_eq)

theorem coe_gram_schmidt_basis (b : Basis ι 𝕜 E) : (gramSchmidtBasis 𝕜 b : ι → E) = gramSchmidt 𝕜 b :=
  Basis.coe_mk _ _

/-- the normalized `gram_schmidt`
(i.e each vector in `gram_schmidt_normed` has unit length.) -/
noncomputable def gramSchmidtNormed (f : ι → E) (n : ι) : E :=
  (∥gramSchmidt 𝕜 f n∥ : 𝕜)⁻¹ • gramSchmidt 𝕜 f n

theorem gram_schmidt_normed_unit_length_coe (f : ι → E) (n : ι) (h₀ : LinearIndependent 𝕜 (f ∘ (coe : Set.Iic n → ι))) :
    ∥gramSchmidtNormed 𝕜 f n∥ = 1 := by
  simp only [← gram_schmidt_ne_zero_coe 𝕜 f n h₀, ← gramSchmidtNormed, ← norm_smul_inv_norm, ← Ne.def, ← not_false_iff]

theorem gram_schmidt_normed_unit_length (f : ι → E) (n : ι) (h₀ : LinearIndependent 𝕜 f) :
    ∥gramSchmidtNormed 𝕜 f n∥ = 1 :=
  gram_schmidt_normed_unit_length_coe _ _ _ (LinearIndependent.comp h₀ _ Subtype.coe_injective)

/-- **Gram-Schmidt Orthonormalization**:
`gram_schmidt_normed` produces an orthornormal system of vectors. -/
theorem gram_schmidt_orthonormal (f : ι → E) (h₀ : LinearIndependent 𝕜 f) : Orthonormal 𝕜 (gramSchmidtNormed 𝕜 f) := by
  unfold Orthonormal
  constructor
  · simp only [← gram_schmidt_normed_unit_length, ← h₀, ← eq_self_iff_true, ← implies_true_iff]
    
  · intro i j hij
    simp only [← gramSchmidtNormed, ← inner_smul_left, ← inner_smul_right, ← IsROrC.conj_inv, ← IsROrC.conj_of_real, ←
      mul_eq_zero, ← inv_eq_zero, ← IsROrC.of_real_eq_zero, ← norm_eq_zero]
    repeat'
      right
    exact gram_schmidt_orthogonal 𝕜 f hij
    

theorem span_gram_schmidt_normed (f : ι → E) (s : Set ι) :
    span 𝕜 (gramSchmidtNormed 𝕜 f '' s) = span 𝕜 (gramSchmidt 𝕜 f '' s) := by
  refine'
    span_eq_span (Set.image_subset_iff.2 fun i hi => smul_mem _ _ <| subset_span <| mem_image_of_mem _ hi)
      (Set.image_subset_iff.2 fun i hi => span_mono (image_subset _ <| singleton_subset_set_iff.2 hi) _)
  simp only [← coe_singleton, ← Set.image_singleton]
  by_cases' h : gramSchmidt 𝕜 f i = 0
  · simp [← h]
    
  · refine' mem_span_singleton.2 ⟨∥gramSchmidt 𝕜 f i∥, smul_inv_smul₀ _ _⟩
    exact_mod_cast norm_ne_zero_iff.2 h
    

theorem span_gram_schmidt_normed_range (f : ι → E) :
    span 𝕜 (Range (gramSchmidtNormed 𝕜 f)) = span 𝕜 (Range (gramSchmidt 𝕜 f)) := by
  simpa only [← image_univ.symm] using span_gram_schmidt_normed 𝕜 f univ

/-- When given a basis, `gram_schmidt_normed` produces an orthonormal basis. -/
noncomputable def gramSchmidtOrthonormalBasis [Fintype ι] (b : Basis ι 𝕜 E) : OrthonormalBasis ι 𝕜 E :=
  OrthonormalBasis.mk (gram_schmidt_orthonormal 𝕜 b b.LinearIndependent)
    (((span_gram_schmidt_normed_range 𝕜 b).trans (span_gram_schmidt 𝕜 b)).trans b.span_eq)

