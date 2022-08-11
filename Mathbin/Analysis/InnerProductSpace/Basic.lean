/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
import Mathbin.Algebra.DirectSum.Module
import Mathbin.Analysis.Complex.Basic
import Mathbin.Analysis.Convex.Uniform
import Mathbin.Analysis.NormedSpace.BoundedLinearMaps
import Mathbin.Analysis.NormedSpace.Banach
import Mathbin.LinearAlgebra.BilinearForm
import Mathbin.LinearAlgebra.SesquilinearForm

/-!
# Inner product space

This file defines inner product spaces and proves the basic properties.  We do not formally
define Hilbert spaces, but they can be obtained using the pair of assumptions
`[inner_product_space 𝕜 E] [complete_space E]`.

An inner product space is a vector space endowed with an inner product. It generalizes the notion of
dot product in `ℝ^n` and provides the means of defining the length of a vector and the angle between
two vectors. In particular vectors `x` and `y` are orthogonal if their inner product equals zero.
We define both the real and complex cases at the same time using the `is_R_or_C` typeclass.

This file proves general results on inner product spaces. For the specific construction of an inner
product structure on `n → 𝕜` for `𝕜 = ℝ` or `ℂ`, see `euclidean_space` in
`analysis.inner_product_space.pi_L2`.

## Main results

- We define the class `inner_product_space 𝕜 E` extending `normed_space 𝕜 E` with a number of basic
  properties, most notably the Cauchy-Schwarz inequality. Here `𝕜` is understood to be either `ℝ`
  or `ℂ`, through the `is_R_or_C` typeclass.
- We show that the inner product is continuous, `continuous_inner`, and bundle it as the
  the continuous sesquilinear map `innerSL` (see also `innerₛₗ` for the non-continuous version).
- We define `orthonormal`, a predicate on a function `v : ι → E`, and prove the existence of a
  maximal orthonormal set, `exists_maximal_orthonormal`.  Bessel's inequality,
  `orthonormal.tsum_inner_products_le`, states that given an orthonormal set `v` and a vector `x`,
  the sum of the norm-squares of the inner products `⟪v i, x⟫` is no more than the norm-square of
  `x`. For the existence of orthonormal bases, Hilbert bases, etc., see the file
  `analysis.inner_product_space.projection`.
- The `orthogonal_complement` of a submodule `K` is defined, and basic API established.  Some of
  the more subtle results about the orthogonal complement are delayed to
  `analysis.inner_product_space.projection`.

## Notation

We globally denote the real and complex inner products by `⟪·, ·⟫_ℝ` and `⟪·, ·⟫_ℂ` respectively.
We also provide two notation namespaces: `real_inner_product_space`, `complex_inner_product_space`,
which respectively introduce the plain notation `⟪·, ·⟫` for the real and complex inner product.

The orthogonal complement of a submodule `K` is denoted by `Kᗮ`.

## Implementation notes

We choose the convention that inner products are conjugate linear in the first argument and linear
in the second.

## Tags

inner product space, Hilbert space, norm

## References
*  [Clément & Martin, *The Lax-Milgram Theorem. A detailed proof to be formalized in Coq*]
*  [Clément & Martin, *A Coq formal proof of the Lax–Milgram theorem*]

The Coq code is available at the following address: <http://www.lri.fr/~sboldo/elfic/index.html>
-/


noncomputable section

open IsROrC Real Filter

open BigOperators TopologicalSpace ComplexConjugate

variable {𝕜 E F : Type _} [IsROrC 𝕜]

/-- Syntactic typeclass for types endowed with an inner product -/
class HasInner (𝕜 E : Type _) where
  inner : E → E → 𝕜

export HasInner (inner)

-- mathport name: «expr⟪ , ⟫_ℝ»
notation "⟪" x ", " y "⟫_ℝ" => @inner ℝ _ _ x y

-- mathport name: «expr⟪ , ⟫_ℂ»
notation "⟪" x ", " y "⟫_ℂ" => @inner ℂ _ _ x y

section Notations

-- mathport name: «expr⟪ , ⟫»
localized [RealInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

-- mathport name: «expr⟪ , ⟫»
localized [ComplexInnerProductSpace] notation "⟪" x ", " y "⟫" => @inner ℂ _ _ x y

end Notations

/-- An inner product space is a vector space with an additional operation called inner product.
The norm could be derived from the inner product, instead we require the existence of a norm and
the fact that `∥x∥^2 = re ⟪x, x⟫` to be able to put instances on `𝕂` or product
spaces.

To construct a norm from an inner product, see `inner_product_space.of_core`.
-/
class InnerProductSpace (𝕜 : Type _) (E : Type _) [IsROrC 𝕜] extends NormedGroup E, NormedSpace 𝕜 E, HasInner 𝕜 E where
  norm_sq_eq_inner : ∀ x : E, ∥x∥ ^ 2 = re (inner x x)
  conj_sym : ∀ x y, conj (inner y x) = inner x y
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

attribute [nolint dangerous_instance] InnerProductSpace.toNormedGroup

/-!
### Constructing a normed space structure from an inner product

In the definition of an inner product space, we require the existence of a norm, which is equal
(but maybe not defeq) to the square root of the scalar product. This makes it possible to put
an inner product space structure on spaces with a preexisting norm (for instance `ℝ`), with good
properties. However, sometimes, one would like to define the norm starting only from a well-behaved
scalar product. This is what we implement in this paragraph, starting from a structure
`inner_product_space.core` stating that we have a nice scalar product.

Our goal here is not to develop a whole theory with all the supporting API, as this will be done
below for `inner_product_space`. Instead, we implement the bare minimum to go as directly as
possible to the construction of the norm and the proof of the triangular inequality.

Warning: Do not use this `core` structure if the space you are interested in already has a norm
instance defined on it, otherwise this will create a second non-defeq norm instance!
-/


/-- A structure requiring that a scalar product is positive definite and symmetric, from which one
can construct an `inner_product_space` instance in `inner_product_space.of_core`. -/
-- note [is_R_or_C instance]
@[nolint has_inhabited_instance]
structure InnerProductSpace.Core (𝕜 : Type _) (F : Type _) [IsROrC 𝕜] [AddCommGroupₓ F] [Module 𝕜 F] where
  inner : F → F → 𝕜
  conj_sym : ∀ x y, conj (inner y x) = inner x y
  nonneg_re : ∀ x, 0 ≤ re (inner x x)
  definite : ∀ x, inner x x = 0 → x = 0
  add_left : ∀ x y z, inner (x + y) z = inner x z + inner y z
  smul_left : ∀ x y r, inner (r • x) y = conj r * inner x y

/- We set `inner_product_space.core` to be a class as we will use it as such in the construction
of the normed space structure that it produces. However, all the instances we will use will be
local to this proof. -/
attribute [class] InnerProductSpace.Core

namespace InnerProductSpace.ofCore

variable [AddCommGroupₓ F] [Module 𝕜 F] [c : InnerProductSpace.Core 𝕜 F]

include c

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 F _ x y

-- mathport name: «exprnorm_sqK»
local notation "norm_sqK" => @IsROrC.normSq 𝕜 _

-- mathport name: «exprreK»
local notation "reK" => @IsROrC.re 𝕜 _

-- mathport name: «exprabsK»
local notation "absK" => @IsROrC.abs 𝕜 _

-- mathport name: «exprext_iff»
local notation "ext_iff" => @IsROrC.ext_iff 𝕜 _

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

/-- Inner product defined by the `inner_product_space.core` structure. -/
def toHasInner : HasInner 𝕜 F where inner := c.inner

attribute [local instance] to_has_inner

/-- The norm squared function for `inner_product_space.core` structure. -/
def normSq (x : F) :=
  reK ⟪x, x⟫

-- mathport name: «exprnorm_sqF»
local notation "norm_sqF" => @normSq 𝕜 F _ _ _ _

theorem inner_conj_sym (x y : F) : ⟪y, x⟫† = ⟪x, y⟫ :=
  c.conj_sym x y

theorem inner_self_nonneg {x : F} : 0 ≤ re ⟪x, x⟫ :=
  c.nonneg_re _

theorem inner_self_nonneg_im {x : F} : im ⟪x, x⟫ = 0 := by
  rw [← @of_real_inj 𝕜, im_eq_conj_sub] <;> simp [← inner_conj_sym]

theorem inner_self_im_zero {x : F} : im ⟪x, x⟫ = 0 :=
  inner_self_nonneg_im

theorem inner_add_left {x y z : F} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  c.add_left _ _ _

theorem inner_add_right {x y z : F} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_sym, inner_add_left, RingHom.map_add] <;> simp only [← inner_conj_sym]

theorem inner_norm_sq_eq_inner_self (x : F) : (norm_sqF x : 𝕜) = ⟪x, x⟫ := by
  rw [ext_iff]
  exact
    ⟨by
      simp only [← of_real_re] <;> rfl, by
      simp only [← inner_self_nonneg_im, ← of_real_im]⟩

theorem inner_re_symm {x y : F} : re ⟪x, y⟫ = re ⟪y, x⟫ := by
  rw [← inner_conj_sym, conj_re]

theorem inner_im_symm {x y : F} : im ⟪x, y⟫ = -im ⟪y, x⟫ := by
  rw [← inner_conj_sym, conj_im]

theorem inner_smul_left {x y : F} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  c.smul_left _ _ _

theorem inner_smul_right {x y : F} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_sym, inner_smul_left] <;> simp only [← conj_conj, ← inner_conj_sym, ← RingHom.map_mul]

theorem inner_zero_left {x : F} : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : F), inner_smul_left] <;> simp only [← zero_mul, ← RingHom.map_zero]

theorem inner_zero_right {x : F} : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_sym, inner_zero_left] <;> simp only [← RingHom.map_zero]

theorem inner_self_eq_zero {x : F} : ⟪x, x⟫ = 0 ↔ x = 0 :=
  Iff.intro (c.definite _)
    (by
      rintro rfl
      exact inner_zero_left)

theorem inner_self_re_to_K {x : F} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by
  norm_num [← ext_iff, ← inner_self_nonneg_im]

theorem inner_abs_conj_sym {x y : F} : abs ⟪x, y⟫ = abs ⟪y, x⟫ := by
  rw [← inner_conj_sym, abs_conj]

theorem inner_neg_left {x y : F} : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp

theorem inner_neg_right {x y : F} : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_sym, inner_neg_left] <;> simp only [← RingHom.map_neg, ← inner_conj_sym]

theorem inner_sub_left {x y z : F} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [← sub_eq_add_neg, ← inner_add_left, ← inner_neg_left]

theorem inner_sub_right {x y z : F} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [← sub_eq_add_neg, ← inner_add_right, ← inner_neg_right]

theorem inner_mul_conj_re_abs {x y : F} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) := by
  rw [← inner_conj_sym, mul_comm]
  exact re_eq_abs_of_mul_conj (inner y x)

/-- Expand `inner (x + y) (x + y)` -/
theorem inner_add_add_self {x y : F} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [← inner_add_left, ← inner_add_right] <;> ring

-- Expand `inner (x - y) (x - y)`
theorem inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [← inner_sub_left, ← inner_sub_right] <;> ring

/-- **Cauchy–Schwarz inequality**. This proof follows "Proof 2" on Wikipedia.
We need this for the `core` structure to prove the triangle inequality below when
showing the core is a normed group.
-/
theorem inner_mul_inner_self_le (x y : F) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  by_cases' hy : y = 0
  · rw [hy]
    simp only [← IsROrC.abs_zero, ← inner_zero_left, ← mul_zero, ← AddMonoidHom.map_zero]
    
  · change y ≠ 0 at hy
    have hy' : ⟪y, y⟫ ≠ 0 := fun h => by
      rw [inner_self_eq_zero] at h <;> exact hy h
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫ := by
      rw [mul_div_assoc]
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ := by
        rw [div_mul_eq_div_mul_one_div, div_self hy', one_mulₓ]
      rw [this, div_eq_mul_inv, one_mulₓ, ← div_eq_mul_inv]
    have h₄ : ⟪y, y⟫ = re ⟪y, y⟫ := by
      simp only [← inner_self_re_to_K]
    have h₅ : re ⟪y, y⟫ > 0 := by
      refine' lt_of_le_of_neₓ inner_self_nonneg _
      intro H
      apply hy'
      rw [ext_iff]
      exact
        ⟨by
          simp only [← H, ← zero_re'], by
          simp only [← inner_self_nonneg_im, ← AddMonoidHom.map_zero]⟩
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gtₓ h₅
    have hmain :=
      calc
        0 ≤ re ⟪x - T • y, x - T • y⟫ := inner_self_nonneg
        _ = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫ := by
          simp only [← inner_sub_sub_self, ← inner_smul_left, ← inner_smul_right, ← h₁, ← h₂, ← neg_mul, ←
            AddMonoidHom.map_add, ← mul_re, ← conj_im, ← AddMonoidHom.map_sub, ← mul_neg, ← conj_re, ← neg_negₓ]
        _ = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫) := by
          simp only [← inner_smul_left, ← inner_smul_right, ← mul_assoc]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫) := by
          field_simp [-mul_re, ← inner_conj_sym, ← hT, ← RingHom.map_div, ← h₁, ← h₃]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫) := by
          rw [← mul_div_right_comm]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / re ⟪y, y⟫) := by
          conv_lhs => rw [h₄]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫ := by
          rw [div_re_of_real]
        _ = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫ := by
          rw [inner_mul_conj_re_abs]
        _ = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ := by
          rw [IsROrC.abs_mul]
        
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by
      linarith
    have := (mul_le_mul_right h₅).mpr hmain'
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this
    

/-- Norm constructed from a `inner_product_space.core` structure, defined to be the square root
of the scalar product. -/
def toHasNorm : HasNorm F where norm := fun x => sqrt (re ⟪x, x⟫)

attribute [local instance] to_has_norm

theorem norm_eq_sqrt_inner (x : F) : ∥x∥ = sqrt (re ⟪x, x⟫) :=
  rfl

theorem inner_self_eq_norm_mul_norm (x : F) : re ⟪x, x⟫ = ∥x∥ * ∥x∥ := by
  rw [norm_eq_sqrt_inner, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]

theorem sqrt_norm_sq_eq_norm {x : F} : sqrt (norm_sqF x) = ∥x∥ :=
  rfl

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_inner_le_norm (x y : F) : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))
    (by
      have H : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = re ⟪y, y⟫ * re ⟪x, x⟫ := by
        simp only [← inner_self_eq_norm_mul_norm]
        ring
      rw [H]
      conv => lhs congr rw [inner_abs_conj_sym]
      exact inner_mul_inner_self_le y x)

/-- Normed group structure constructed from an `inner_product_space.core` structure -/
def toNormedGroup : NormedGroup F :=
  NormedGroup.ofCore F
    { norm_eq_zero_iff := fun x => by
        constructor
        · intro H
          change sqrt (re ⟪x, x⟫) = 0 at H
          rw [sqrt_eq_zero inner_self_nonneg] at H
          apply (inner_self_eq_zero : ⟪x, x⟫ = 0 ↔ x = 0).mp
          rw [ext_iff]
          exact
            ⟨by
              simp [← H], by
              simp [← inner_self_im_zero]⟩
          
        · rintro rfl
          change sqrt (re ⟪0, 0⟫) = 0
          simp only [← sqrt_zero, ← inner_zero_right, ← AddMonoidHom.map_zero]
          ,
      triangle := fun x y => by
        have h₁ : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ := abs_inner_le_norm _ _
        have h₂ : re ⟪x, y⟫ ≤ abs ⟪x, y⟫ := re_le_abs _
        have h₃ : re ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ := by
          linarith
        have h₄ : re ⟪y, x⟫ ≤ ∥x∥ * ∥y∥ := by
          rwa [← inner_conj_sym, conj_re]
        have : ∥x + y∥ * ∥x + y∥ ≤ (∥x∥ + ∥y∥) * (∥x∥ + ∥y∥) := by
          simp [inner_self_eq_norm_mul_norm, ← inner_add_add_self, ← add_mulₓ, ← mul_addₓ, ← mul_comm]
          linarith
        exact nonneg_le_nonneg_of_sq_le_sq (add_nonneg (sqrt_nonneg _) (sqrt_nonneg _)) this,
      norm_neg := fun x => by
        simp only [← norm, ← inner_neg_left, ← neg_negₓ, ← inner_neg_right] }

attribute [local instance] to_normed_group

/-- Normed space structure constructed from a `inner_product_space.core` structure -/
def toNormedSpace :
    NormedSpace 𝕜 F where norm_smul_le := fun r x => by
    rw [norm_eq_sqrt_inner, inner_smul_left, inner_smul_right, ← mul_assoc]
    rw [conj_mul_eq_norm_sq_left, of_real_mul_re, sqrt_mul, ← inner_norm_sq_eq_inner_self, of_real_re]
    · simp [← sqrt_norm_sq_eq_norm, ← IsROrC.sqrt_norm_sq_eq_norm]
      
    · exact norm_sq_nonneg r
      

end InnerProductSpace.ofCore

/-- Given a `inner_product_space.core` structure on a space, one can use it to turn
the space into an inner product space, constructing the norm out of the inner product -/
def InnerProductSpace.ofCore [AddCommGroupₓ F] [Module 𝕜 F] (c : InnerProductSpace.Core 𝕜 F) : InnerProductSpace 𝕜 F :=
  by
  let this : NormedGroup F := @InnerProductSpace.OfCore.toNormedGroup 𝕜 F _ _ _ c
  let this : NormedSpace 𝕜 F := @InnerProductSpace.OfCore.toNormedSpace 𝕜 F _ _ _ c
  exact
    { c with
      norm_sq_eq_inner := fun x => by
        have h₁ : ∥x∥ ^ 2 = sqrt (re (c.inner x x)) ^ 2 := rfl
        have h₂ : 0 ≤ re (c.inner x x) := InnerProductSpace.OfCore.inner_self_nonneg
        simp [← h₁, ← sq_sqrt, ← h₂] }

/-! ### Properties of inner product spaces -/


variable [InnerProductSpace 𝕜 E] [InnerProductSpace ℝ F]

variable [dec_E : DecidableEq E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

-- mathport name: «exprIK»
local notation "IK" => @IsROrC.i 𝕜 _

-- mathport name: «exprabsR»
local notation "absR" => HasAbs.abs

-- mathport name: «exprabsK»
local notation "absK" => @IsROrC.abs 𝕜 _

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

export InnerProductSpace (norm_sq_eq_inner)

section BasicProperties

@[simp]
theorem inner_conj_sym (x y : E) : ⟪y, x⟫† = ⟪x, y⟫ :=
  InnerProductSpace.conj_sym _ _

theorem real_inner_comm (x y : F) : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ :=
  @inner_conj_sym ℝ _ _ _ x y

theorem inner_eq_zero_sym {x y : E} : ⟪x, y⟫ = 0 ↔ ⟪y, x⟫ = 0 :=
  ⟨fun h => by
    simp [inner_conj_sym, ← h], fun h => by
    simp [inner_conj_sym, ← h]⟩

@[simp]
theorem inner_self_nonneg_im {x : E} : im ⟪x, x⟫ = 0 := by
  rw [← @of_real_inj 𝕜, im_eq_conj_sub] <;> simp

theorem inner_self_im_zero {x : E} : im ⟪x, x⟫ = 0 :=
  inner_self_nonneg_im

theorem inner_add_left {x y z : E} : ⟪x + y, z⟫ = ⟪x, z⟫ + ⟪y, z⟫ :=
  InnerProductSpace.add_left _ _ _

theorem inner_add_right {x y z : E} : ⟪x, y + z⟫ = ⟪x, y⟫ + ⟪x, z⟫ := by
  rw [← inner_conj_sym, inner_add_left, RingHom.map_add]
  simp only [← inner_conj_sym]

theorem inner_re_symm {x y : E} : re ⟪x, y⟫ = re ⟪y, x⟫ := by
  rw [← inner_conj_sym, conj_re]

theorem inner_im_symm {x y : E} : im ⟪x, y⟫ = -im ⟪y, x⟫ := by
  rw [← inner_conj_sym, conj_im]

theorem inner_smul_left {x y : E} {r : 𝕜} : ⟪r • x, y⟫ = r† * ⟪x, y⟫ :=
  InnerProductSpace.smul_left _ _ _

theorem real_inner_smul_left {x y : F} {r : ℝ} : ⟪r • x, y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_left

theorem inner_smul_real_left {x y : E} {r : ℝ} : ⟪(r : 𝕜) • x, y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_left, conj_of_real, Algebra.smul_def]
  rfl

theorem inner_smul_right {x y : E} {r : 𝕜} : ⟪x, r • y⟫ = r * ⟪x, y⟫ := by
  rw [← inner_conj_sym, inner_smul_left, RingHom.map_mul, conj_conj, inner_conj_sym]

theorem real_inner_smul_right {x y : F} {r : ℝ} : ⟪x, r • y⟫_ℝ = r * ⟪x, y⟫_ℝ :=
  inner_smul_right

theorem inner_smul_real_right {x y : E} {r : ℝ} : ⟪x, (r : 𝕜) • y⟫ = r • ⟪x, y⟫ := by
  rw [inner_smul_right, Algebra.smul_def]
  rfl

/-- The inner product as a sesquilinear form. -/
@[simps]
def sesqFormOfInner : E →ₗ[𝕜] E →ₗ⋆[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ (RingHom.id 𝕜) (starRingEnd _) (fun x y => ⟪y, x⟫) (fun x y z => inner_add_right)
    (fun r x y => inner_smul_right) (fun x y z => inner_add_left) fun r x y => inner_smul_left

/-- The real inner product as a bilinear form. -/
@[simps]
def bilinFormOfRealInner : BilinForm ℝ F where
  bilin := inner
  bilin_add_left := fun x y z => inner_add_left
  bilin_smul_left := fun a x y => inner_smul_left
  bilin_add_right := fun x y z => inner_add_right
  bilin_smul_right := fun a x y => inner_smul_right

/-- An inner product with a sum on the left. -/
theorem sum_inner {ι : Type _} (s : Finset ι) (f : ι → E) (x : E) : ⟪∑ i in s, f i, x⟫ = ∑ i in s, ⟪f i, x⟫ :=
  (sesqFormOfInner x).map_sum

/-- An inner product with a sum on the right. -/
theorem inner_sum {ι : Type _} (s : Finset ι) (f : ι → E) (x : E) : ⟪x, ∑ i in s, f i⟫ = ∑ i in s, ⟪x, f i⟫ :=
  (LinearMap.flip sesqFormOfInner x).map_sum

/-- An inner product with a sum on the left, `finsupp` version. -/
theorem Finsupp.sum_inner {ι : Type _} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
    ⟪l.Sum fun (i : ι) (a : 𝕜) => a • v i, x⟫ = l.Sum fun (i : ι) (a : 𝕜) => conj a • ⟪v i, x⟫ := by
  convert sum_inner l.support (fun a => l a • v a) x
  simp [← inner_smul_left, ← Finsupp.sum]

/-- An inner product with a sum on the right, `finsupp` version. -/
theorem Finsupp.inner_sum {ι : Type _} (l : ι →₀ 𝕜) (v : ι → E) (x : E) :
    ⟪x, l.Sum fun (i : ι) (a : 𝕜) => a • v i⟫ = l.Sum fun (i : ι) (a : 𝕜) => a • ⟪x, v i⟫ := by
  convert inner_sum l.support (fun a => l a • v a) x
  simp [← inner_smul_right, ← Finsupp.sum]

theorem Dfinsupp.sum_inner {ι : Type _} [dec : DecidableEq ι] {α : ι → Type _} [∀ i, AddZeroClassₓ (α i)]
    [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E) (l : Π₀ i, α i) (x : E) :
    ⟪l.Sum f, x⟫ = l.Sum fun i a => ⟪f i a, x⟫ := by
  simp (config := { contextual := true })[← Dfinsupp.sum, ← sum_inner]

theorem Dfinsupp.inner_sum {ι : Type _} [dec : DecidableEq ι] {α : ι → Type _} [∀ i, AddZeroClassₓ (α i)]
    [∀ (i) (x : α i), Decidable (x ≠ 0)] (f : ∀ i, α i → E) (l : Π₀ i, α i) (x : E) :
    ⟪x, l.Sum f⟫ = l.Sum fun i a => ⟪x, f i a⟫ := by
  simp (config := { contextual := true })[← Dfinsupp.sum, ← inner_sum]

@[simp]
theorem inner_zero_left {x : E} : ⟪0, x⟫ = 0 := by
  rw [← zero_smul 𝕜 (0 : E), inner_smul_left, RingHom.map_zero, zero_mul]

theorem inner_re_zero_left {x : E} : re ⟪0, x⟫ = 0 := by
  simp only [← inner_zero_left, ← AddMonoidHom.map_zero]

@[simp]
theorem inner_zero_right {x : E} : ⟪x, 0⟫ = 0 := by
  rw [← inner_conj_sym, inner_zero_left, RingHom.map_zero]

theorem inner_re_zero_right {x : E} : re ⟪x, 0⟫ = 0 := by
  simp only [← inner_zero_right, ← AddMonoidHom.map_zero]

theorem inner_self_nonneg {x : E} : 0 ≤ re ⟪x, x⟫ := by
  rw [← norm_sq_eq_inner] <;> exact pow_nonneg (norm_nonneg x) 2

theorem real_inner_self_nonneg {x : F} : 0 ≤ ⟪x, x⟫_ℝ :=
  @inner_self_nonneg ℝ F _ _ x

@[simp]
theorem inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0 := by
  constructor
  · intro h
    have h₁ : re ⟪x, x⟫ = 0 := by
      rw [IsROrC.ext_iff] at h <;> simp [← h.1]
    rw [← norm_sq_eq_inner x] at h₁
    rw [← norm_eq_zero]
    exact pow_eq_zero h₁
    
  · rintro rfl
    exact inner_zero_left
    

@[simp]
theorem inner_self_nonpos {x : E} : re ⟪x, x⟫ ≤ 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [← inner_self_eq_zero]
    have H₁ : re ⟪x, x⟫ ≥ 0 := inner_self_nonneg
    have H₂ : re ⟪x, x⟫ = 0 := le_antisymmₓ h H₁
    rw [IsROrC.ext_iff]
    exact
      ⟨by
        simp [← H₂], by
        simp [← inner_self_nonneg_im]⟩
    
  · rintro rfl
    simp only [← inner_zero_left, ← AddMonoidHom.map_zero]
    

theorem real_inner_self_nonpos {x : F} : ⟪x, x⟫_ℝ ≤ 0 ↔ x = 0 := by
  have h := @inner_self_nonpos ℝ F _ _ x
  simpa using h

@[simp]
theorem inner_self_re_to_K {x : E} : (re ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by
  rw [IsROrC.ext_iff] <;>
    exact
      ⟨by
        simp , by
        simp [← inner_self_nonneg_im]⟩

theorem inner_self_eq_norm_sq_to_K (x : E) : ⟪x, x⟫ = (∥x∥ ^ 2 : 𝕜) := by
  suffices (IsROrC.re ⟪x, x⟫ : 𝕜) = ∥x∥ ^ 2 by
    simpa [← inner_self_re_to_K] using this
  exact_mod_cast (norm_sq_eq_inner x).symm

theorem inner_self_re_abs {x : E} : re ⟪x, x⟫ = abs ⟪x, x⟫ := by
  conv_rhs => rw [← inner_self_re_to_K]
  symm
  exact IsROrC.abs_of_nonneg inner_self_nonneg

theorem inner_self_abs_to_K {x : E} : (absK ⟪x, x⟫ : 𝕜) = ⟪x, x⟫ := by
  rw [← inner_self_re_abs]
  exact inner_self_re_to_K

theorem real_inner_self_abs {x : F} : absR ⟪x, x⟫_ℝ = ⟪x, x⟫_ℝ := by
  have h := @inner_self_abs_to_K ℝ F _ _ x
  simpa using h

theorem inner_abs_conj_sym {x y : E} : abs ⟪x, y⟫ = abs ⟪y, x⟫ := by
  rw [← inner_conj_sym, abs_conj]

@[simp]
theorem inner_neg_left {x y : E} : ⟪-x, y⟫ = -⟪x, y⟫ := by
  rw [← neg_one_smul 𝕜 x, inner_smul_left]
  simp

@[simp]
theorem inner_neg_right {x y : E} : ⟪x, -y⟫ = -⟪x, y⟫ := by
  rw [← inner_conj_sym, inner_neg_left] <;> simp only [← RingHom.map_neg, ← inner_conj_sym]

theorem inner_neg_neg {x y : E} : ⟪-x, -y⟫ = ⟪x, y⟫ := by
  simp

@[simp]
theorem inner_self_conj {x : E} : ⟪x, x⟫† = ⟪x, x⟫ := by
  rw [IsROrC.ext_iff] <;>
    exact
      ⟨by
        rw [conj_re], by
        rw [conj_im, inner_self_im_zero, neg_zero]⟩

theorem inner_sub_left {x y z : E} : ⟪x - y, z⟫ = ⟪x, z⟫ - ⟪y, z⟫ := by
  simp [← sub_eq_add_neg, ← inner_add_left]

theorem inner_sub_right {x y z : E} : ⟪x, y - z⟫ = ⟪x, y⟫ - ⟪x, z⟫ := by
  simp [← sub_eq_add_neg, ← inner_add_right]

theorem inner_mul_conj_re_abs {x y : E} : re (⟪x, y⟫ * ⟪y, x⟫) = abs (⟪x, y⟫ * ⟪y, x⟫) := by
  rw [← inner_conj_sym, mul_comm]
  exact re_eq_abs_of_mul_conj (inner y x)

/-- Expand `⟪x + y, x + y⟫` -/
theorem inner_add_add_self {x y : E} : ⟪x + y, x + y⟫ = ⟪x, x⟫ + ⟪x, y⟫ + ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [← inner_add_left, ← inner_add_right] <;> ring

/-- Expand `⟪x + y, x + y⟫_ℝ` -/
theorem real_inner_add_add_self {x y : F} : ⟪x + y, x + y⟫_ℝ = ⟪x, x⟫_ℝ + 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by
    rw [← inner_conj_sym] <;> rfl
  simp [← inner_add_add_self, ← this]
  ring

-- Expand `⟪x - y, x - y⟫`
theorem inner_sub_sub_self {x y : E} : ⟪x - y, x - y⟫ = ⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫ := by
  simp only [← inner_sub_left, ← inner_sub_right] <;> ring

/-- Expand `⟪x - y, x - y⟫_ℝ` -/
theorem real_inner_sub_sub_self {x y : F} : ⟪x - y, x - y⟫_ℝ = ⟪x, x⟫_ℝ - 2 * ⟪x, y⟫_ℝ + ⟪y, y⟫_ℝ := by
  have : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by
    rw [← inner_conj_sym] <;> rfl
  simp [← inner_sub_sub_self, ← this]
  ring

/-- Parallelogram law -/
theorem parallelogram_law {x y : E} : ⟪x + y, x + y⟫ + ⟪x - y, x - y⟫ = 2 * (⟪x, x⟫ + ⟪y, y⟫) := by
  simp [← inner_add_add_self, ← inner_sub_sub_self, ← two_mul, ← sub_eq_add_neg, ← add_commₓ, ← add_left_commₓ]

/-- Cauchy–Schwarz inequality. This proof follows "Proof 2" on Wikipedia. -/
theorem inner_mul_inner_self_le (x y : E) : abs ⟪x, y⟫ * abs ⟪y, x⟫ ≤ re ⟪x, x⟫ * re ⟪y, y⟫ := by
  by_cases' hy : y = 0
  · rw [hy]
    simp only [← IsROrC.abs_zero, ← inner_zero_left, ← mul_zero, ← AddMonoidHom.map_zero]
    
  · change y ≠ 0 at hy
    have hy' : ⟪y, y⟫ ≠ 0 := fun h => by
      rw [inner_self_eq_zero] at h <;> exact hy h
    set T := ⟪y, x⟫ / ⟪y, y⟫ with hT
    have h₁ : re ⟪y, x⟫ = re ⟪x, y⟫ := inner_re_symm
    have h₂ : im ⟪y, x⟫ = -im ⟪x, y⟫ := inner_im_symm
    have h₃ : ⟪y, x⟫ * ⟪x, y⟫ * ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = ⟪y, x⟫ * ⟪x, y⟫ / ⟪y, y⟫ := by
      rw [mul_div_assoc]
      have : ⟪y, y⟫ / (⟪y, y⟫ * ⟪y, y⟫) = 1 / ⟪y, y⟫ := by
        rw [div_mul_eq_div_mul_one_div, div_self hy', one_mulₓ]
      rw [this, div_eq_mul_inv, one_mulₓ, ← div_eq_mul_inv]
    have h₄ : ⟪y, y⟫ = re ⟪y, y⟫ := by
      simp
    have h₅ : re ⟪y, y⟫ > 0 := by
      refine' lt_of_le_of_neₓ inner_self_nonneg _
      intro H
      apply hy'
      rw [IsROrC.ext_iff]
      exact
        ⟨by
          simp only [← H, ← zero_re'], by
          simp only [← inner_self_nonneg_im, ← AddMonoidHom.map_zero]⟩
    have h₆ : re ⟪y, y⟫ ≠ 0 := ne_of_gtₓ h₅
    have hmain :=
      calc
        0 ≤ re ⟪x - T • y, x - T • y⟫ := inner_self_nonneg
        _ = re ⟪x, x⟫ - re ⟪T • y, x⟫ - re ⟪x, T • y⟫ + re ⟪T • y, T • y⟫ := by
          simp only [← inner_sub_sub_self, ← inner_smul_left, ← inner_smul_right, ← h₁, ← h₂, ← neg_mul, ←
            AddMonoidHom.map_add, ← conj_im, ← AddMonoidHom.map_sub, ← mul_neg, ← conj_re, ← neg_negₓ, ← mul_re]
        _ = re ⟪x, x⟫ - re (T† * ⟪y, x⟫) - re (T * ⟪x, y⟫) + re (T * T† * ⟪y, y⟫) := by
          simp only [← inner_smul_left, ← inner_smul_right, ← mul_assoc]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ / ⟪y, y⟫ * ⟪y, x⟫) := by
          field_simp [-mul_re, ← hT, ← RingHom.map_div, ← h₁, ← h₃, ← inner_conj_sym]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / ⟪y, y⟫) := by
          rw [← mul_div_right_comm]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫ / re ⟪y, y⟫) := by
          conv_lhs => rw [h₄]
        _ = re ⟪x, x⟫ - re (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫ := by
          rw [div_re_of_real]
        _ = re ⟪x, x⟫ - abs (⟪x, y⟫ * ⟪y, x⟫) / re ⟪y, y⟫ := by
          rw [inner_mul_conj_re_abs]
        _ = re ⟪x, x⟫ - abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ := by
          rw [IsROrC.abs_mul]
        
    have hmain' : abs ⟪x, y⟫ * abs ⟪y, x⟫ / re ⟪y, y⟫ ≤ re ⟪x, x⟫ := by
      linarith
    have := (mul_le_mul_right h₅).mpr hmain'
    rwa [div_mul_cancel (abs ⟪x, y⟫ * abs ⟪y, x⟫) h₆] at this
    

/-- Cauchy–Schwarz inequality for real inner products. -/
theorem real_inner_mul_inner_self_le (x y : F) : ⟪x, y⟫_ℝ * ⟪x, y⟫_ℝ ≤ ⟪x, x⟫_ℝ * ⟪y, y⟫_ℝ := by
  have h₁ : ⟪y, x⟫_ℝ = ⟪x, y⟫_ℝ := by
    rw [← inner_conj_sym] <;> rfl
  have h₂ := @inner_mul_inner_self_le ℝ F _ _ x y
  dsimp'  at h₂
  have h₃ := abs_mul_abs_self ⟪x, y⟫_ℝ
  rw [h₁] at h₂
  simpa [← h₃] using h₂

/-- A family of vectors is linearly independent if they are nonzero
and orthogonal. -/
theorem linear_independent_of_ne_zero_of_inner_eq_zero {ι : Type _} {v : ι → E} (hz : ∀ i, v i ≠ 0)
    (ho : ∀ i j, i ≠ j → ⟪v i, v j⟫ = 0) : LinearIndependent 𝕜 v := by
  rw [linear_independent_iff']
  intro s g hg i hi
  have h' : g i * inner (v i) (v i) = inner (v i) (∑ j in s, g j • v j) := by
    rw [inner_sum]
    symm
    convert Finset.sum_eq_single i _ _
    · rw [inner_smul_right]
      
    · intro j hj hji
      rw [inner_smul_right, ho i j hji.symm, mul_zero]
      
    · exact fun h => False.elim (h hi)
      
  simpa [← hg, ← hz] using h'

end BasicProperties

section OrthonormalSets

variable {ι : Type _} [dec_ι : DecidableEq ι] (𝕜)

include 𝕜

/-- An orthonormal set of vectors in an `inner_product_space` -/
def Orthonormal (v : ι → E) : Prop :=
  (∀ i, ∥v i∥ = 1) ∧ ∀ {i j}, i ≠ j → ⟪v i, v j⟫ = 0

omit 𝕜

variable {𝕜}

include dec_ι

/-- `if ... then ... else` characterization of an indexed set of vectors being orthonormal.  (Inner
product equals Kronecker delta.) -/
theorem orthonormal_iff_ite {v : ι → E} : Orthonormal 𝕜 v ↔ ∀ i j, ⟪v i, v j⟫ = if i = j then (1 : 𝕜) else (0 : 𝕜) := by
  constructor
  · intro hv i j
    split_ifs
    · simp [← h, ← inner_self_eq_norm_sq_to_K, ← hv.1]
      
    · exact hv.2 h
      
    
  · intro h
    constructor
    · intro i
      have h' : ∥v i∥ ^ 2 = 1 ^ 2 := by
        simp [← norm_sq_eq_inner, ← h i i]
      have h₁ : 0 ≤ ∥v i∥ := norm_nonneg _
      have h₂ : (0 : ℝ) ≤ 1 := zero_le_one
      rwa [sq_eq_sq h₁ h₂] at h'
      
    · intro i j hij
      simpa [← hij] using h i j
      
    

omit dec_ι

include dec_E

/-- `if ... then ... else` characterization of a set of vectors being orthonormal.  (Inner product
equals Kronecker delta.) -/
theorem orthonormal_subtype_iff_ite {s : Set E} :
    Orthonormal 𝕜 (coe : s → E) ↔ ∀, ∀ v ∈ s, ∀, ∀, ∀ w ∈ s, ∀, ⟪v, w⟫ = if v = w then 1 else 0 := by
  rw [orthonormal_iff_ite]
  constructor
  · intro h v hv w hw
    convert h ⟨v, hv⟩ ⟨w, hw⟩ using 1
    simp
    
  · rintro h ⟨v, hv⟩ ⟨w, hw⟩
    convert h v hv w hw using 1
    simp
    

omit dec_E

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
    ⟪v i, Finsupp.total ι E 𝕜 v l⟫ = l i := by
  classical <;> simp [← Finsupp.total_apply, ← Finsupp.inner_sum, ← orthonormal_iff_ite.mp hv]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) {s : Finset ι} {i : ι} (hi : i ∈ s) :
    ⟪v i, ∑ i in s, l i • v i⟫ = l i := by
  classical <;> simp [← inner_sum, ← inner_smul_right, ← orthonormal_iff_ite.mp hv, ← hi]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_right_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) (i : ι) :
    ⟪v i, ∑ i : ι, l i • v i⟫ = l i :=
  hv.inner_right_sum l (Finset.mem_univ _)

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_finsupp {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι →₀ 𝕜) (i : ι) :
    ⟪Finsupp.total ι E 𝕜 v l, v i⟫ = conj (l i) := by
  rw [← inner_conj_sym, hv.inner_right_finsupp]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) {s : Finset ι} {i : ι} (hi : i ∈ s) :
    ⟪∑ i in s, l i • v i, v i⟫ = conj (l i) := by
  classical <;> simp [← sum_inner, ← inner_smul_left, ← orthonormal_iff_ite.mp hv, ← hi]

/-- The inner product of a linear combination of a set of orthonormal vectors with one of those
vectors picks out the coefficient of that vector. -/
theorem Orthonormal.inner_left_fintype [Fintype ι] {v : ι → E} (hv : Orthonormal 𝕜 v) (l : ι → 𝕜) (i : ι) :
    ⟪∑ i : ι, l i • v i, v i⟫ = conj (l i) :=
  hv.inner_left_sum l (Finset.mem_univ _)

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the first `finsupp`. -/
theorem Orthonormal.inner_finsupp_eq_sum_left {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪Finsupp.total ι E 𝕜 v l₁, Finsupp.total ι E 𝕜 v l₂⟫ = l₁.Sum fun i y => conj y * l₂ i := by
  simp [← Finsupp.total_apply _ l₁, ← Finsupp.sum_inner, ← hv.inner_right_finsupp]

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum over the second `finsupp`. -/
theorem Orthonormal.inner_finsupp_eq_sum_right {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι →₀ 𝕜) :
    ⟪Finsupp.total ι E 𝕜 v l₁, Finsupp.total ι E 𝕜 v l₂⟫ = l₂.Sum fun i y => conj (l₁ i) * y := by
  simp [← Finsupp.total_apply _ l₂, ← Finsupp.inner_sum, ← hv.inner_left_finsupp, ← mul_comm]

/-- The inner product of two linear combinations of a set of orthonormal vectors, expressed as
a sum. -/
theorem Orthonormal.inner_sum {v : ι → E} (hv : Orthonormal 𝕜 v) (l₁ l₂ : ι → 𝕜) (s : Finset ι) :
    ⟪∑ i in s, l₁ i • v i, ∑ i in s, l₂ i • v i⟫ = ∑ i in s, conj (l₁ i) * l₂ i := by
  simp_rw [sum_inner, inner_smul_left]
  refine' Finset.sum_congr rfl fun i hi => _
  rw [hv.inner_right_sum l₂ hi]

/-- The double sum of weighted inner products of pairs of vectors from an orthonormal sequence is the
sum of the weights.
-/
theorem Orthonormal.inner_left_right_finset {s : Finset ι} {v : ι → E} (hv : Orthonormal 𝕜 v) {a : ι → ι → 𝕜} :
    (∑ i in s, ∑ j in s, a i j • ⟪v j, v i⟫) = ∑ k in s, a k k := by
  classical <;> simp [← orthonormal_iff_ite.mp hv, ← Finset.sum_ite_of_true]

/-- An orthonormal set is linearly independent. -/
theorem Orthonormal.linear_independent {v : ι → E} (hv : Orthonormal 𝕜 v) : LinearIndependent 𝕜 v := by
  rw [linear_independent_iff]
  intro l hl
  ext i
  have key : ⟪v i, Finsupp.total ι E 𝕜 v l⟫ = ⟪v i, 0⟫ := by
    rw [hl]
  simpa [← hv.inner_right_finsupp] using key

/-- A subfamily of an orthonormal family (i.e., a composition with an injective map) is an
orthonormal family. -/
theorem Orthonormal.comp {ι' : Type _} {v : ι → E} (hv : Orthonormal 𝕜 v) (f : ι' → ι) (hf : Function.Injective f) :
    Orthonormal 𝕜 (v ∘ f) := by
  classical
  rw [orthonormal_iff_ite] at hv⊢
  intro i j
  convert hv (f i) (f j) using 1
  simp [← hf.eq_iff]

/-- A linear combination of some subset of an orthonormal set is orthogonal to other members of the
set. -/
theorem Orthonormal.inner_finsupp_eq_zero {v : ι → E} (hv : Orthonormal 𝕜 v) {s : Set ι} {i : ι} (hi : i ∉ s)
    {l : ι →₀ 𝕜} (hl : l ∈ Finsupp.supported 𝕜 𝕜 s) : ⟪Finsupp.total ι E 𝕜 v l, v i⟫ = 0 := by
  rw [Finsupp.mem_supported'] at hl
  simp [← hv.inner_left_finsupp, ← hl i hi]

/-- Given an orthonormal family, a second family of vectors is orthonormal if every vector equals
the corresponding vector in the original family or its negation. -/
theorem Orthonormal.orthonormal_of_forall_eq_or_eq_neg {v w : ι → E} (hv : Orthonormal 𝕜 v)
    (hw : ∀ i, w i = v i ∨ w i = -v i) : Orthonormal 𝕜 w := by
  classical
  rw [orthonormal_iff_ite] at *
  intro i j
  cases' hw i with hi hi <;> cases' hw j with hj hj <;> split_ifs with h <;> simpa [← hi, ← hj, ← h] using hv i j

/- The material that follows, culminating in the existence of a maximal orthonormal subset, is
adapted from the corresponding development of the theory of linearly independents sets.  See
`exists_linear_independent` in particular. -/
variable (𝕜 E)

theorem orthonormal_empty : Orthonormal 𝕜 (fun x => x : (∅ : Set E) → E) := by
  classical <;> simp [← orthonormal_subtype_iff_ite]

variable {𝕜 E}

theorem orthonormal_Union_of_directed {η : Type _} {s : η → Set E} (hs : Directed (· ⊆ ·) s)
    (h : ∀ i, Orthonormal 𝕜 (fun x => x : s i → E)) : Orthonormal 𝕜 (fun x => x : (⋃ i, s i) → E) := by
  classical
  rw [orthonormal_subtype_iff_ite]
  rintro x ⟨_, ⟨i, rfl⟩, hxi⟩ y ⟨_, ⟨j, rfl⟩, hyj⟩
  obtain ⟨k, hik, hjk⟩ := hs i j
  have h_orth : Orthonormal 𝕜 (fun x => x : s k → E) := h k
  rw [orthonormal_subtype_iff_ite] at h_orth
  exact h_orth x (hik hxi) y (hjk hyj)

theorem orthonormal_sUnion_of_directed {s : Set (Set E)} (hs : DirectedOn (· ⊆ ·) s)
    (h : ∀, ∀ a ∈ s, ∀, Orthonormal 𝕜 (fun x => x : (a : Set E) → E)) : Orthonormal 𝕜 (fun x => x : ⋃₀s → E) := by
  rw [Set.sUnion_eq_Union] <;>
    exact
      orthonormal_Union_of_directed hs.directed_coe
        (by
          simpa using h)

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (w «expr ⊇ » s)
-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (u «expr ⊇ » w)
/-- Given an orthonormal set `v` of vectors in `E`, there exists a maximal orthonormal set
containing it. -/
theorem exists_maximal_orthonormal {s : Set E} (hs : Orthonormal 𝕜 (coe : s → E)) :
    ∃ (w : _)(_ : w ⊇ s), Orthonormal 𝕜 (coe : w → E) ∧ ∀ (u) (_ : u ⊇ w), Orthonormal 𝕜 (coe : u → E) → u = w := by
  obtain ⟨b, bi, sb, h⟩ := zorn_subset_nonempty { b | Orthonormal 𝕜 (coe : b → E) } _ _ hs
  · refine' ⟨b, sb, bi, _⟩
    exact fun u hus hu => h u hu hus
    
  · refine' fun c hc cc c0 => ⟨⋃₀c, _, _⟩
    · exact orthonormal_sUnion_of_directed cc.directed_on fun x xc => hc xc
      
    · exact fun _ => Set.subset_sUnion_of_mem
      
    

theorem Orthonormal.ne_zero {v : ι → E} (hv : Orthonormal 𝕜 v) (i : ι) : v i ≠ 0 := by
  have : ∥v i∥ ≠ 0 := by
    rw [hv.1 i]
    norm_num
  simpa using this

open FiniteDimensional

/-- A family of orthonormal vectors with the correct cardinality forms a basis. -/
def basisOfOrthonormalOfCardEqFinrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = finrank 𝕜 E) : Basis ι 𝕜 E :=
  basisOfLinearIndependentOfCardEqFinrank hv.LinearIndependent card_eq

@[simp]
theorem coe_basis_of_orthonormal_of_card_eq_finrank [Fintype ι] [Nonempty ι] {v : ι → E} (hv : Orthonormal 𝕜 v)
    (card_eq : Fintype.card ι = finrank 𝕜 E) : (basisOfOrthonormalOfCardEqFinrank hv card_eq : ι → E) = v :=
  coe_basis_of_linear_independent_of_card_eq_finrank _ _

end OrthonormalSets

section Norm

theorem norm_eq_sqrt_inner (x : E) : ∥x∥ = sqrt (re ⟪x, x⟫) := by
  have h₁ : ∥x∥ ^ 2 = re ⟪x, x⟫ := norm_sq_eq_inner x
  have h₂ := congr_arg sqrt h₁
  simpa using h₂

theorem norm_eq_sqrt_real_inner (x : F) : ∥x∥ = sqrt ⟪x, x⟫_ℝ := by
  have h := @norm_eq_sqrt_inner ℝ F _ _ x
  simpa using h

theorem inner_self_eq_norm_mul_norm (x : E) : re ⟪x, x⟫ = ∥x∥ * ∥x∥ := by
  rw [norm_eq_sqrt_inner, ← sqrt_mul inner_self_nonneg (re ⟪x, x⟫), sqrt_mul_self inner_self_nonneg]

theorem inner_self_eq_norm_sq (x : E) : re ⟪x, x⟫ = ∥x∥ ^ 2 := by
  rw [pow_two, inner_self_eq_norm_mul_norm]

theorem real_inner_self_eq_norm_mul_norm (x : F) : ⟪x, x⟫_ℝ = ∥x∥ * ∥x∥ := by
  have h := @inner_self_eq_norm_mul_norm ℝ F _ _ x
  simpa using h

theorem real_inner_self_eq_norm_sq (x : F) : ⟪x, x⟫_ℝ = ∥x∥ ^ 2 := by
  rw [pow_two, real_inner_self_eq_norm_mul_norm]

/-- Expand the square -/
theorem norm_add_sq {x y : E} : ∥x + y∥ ^ 2 = ∥x∥ ^ 2 + 2 * re ⟪x, y⟫ + ∥y∥ ^ 2 := by
  repeat'
    rw [sq, ← inner_self_eq_norm_mul_norm]
  rw [inner_add_add_self, two_mul]
  simp only [← add_assocₓ, ← add_left_injₓ, ← add_right_injₓ, ← AddMonoidHom.map_add]
  rw [← inner_conj_sym, conj_re]

alias norm_add_sq ← norm_add_pow_two

/-- Expand the square -/
theorem norm_add_sq_real {x y : F} : ∥x + y∥ ^ 2 = ∥x∥ ^ 2 + 2 * ⟪x, y⟫_ℝ + ∥y∥ ^ 2 := by
  have h := @norm_add_sq ℝ F _ _
  simpa using h

alias norm_add_sq_real ← norm_add_pow_two_real

/-- Expand the square -/
theorem norm_add_mul_self {x y : E} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * re ⟪x, y⟫ + ∥y∥ * ∥y∥ := by
  repeat'
    rw [← sq]
  exact norm_add_sq

/-- Expand the square -/
theorem norm_add_mul_self_real {x y : F} : ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + 2 * ⟪x, y⟫_ℝ + ∥y∥ * ∥y∥ := by
  have h := @norm_add_mul_self ℝ F _ _
  simpa using h

/-- Expand the square -/
theorem norm_sub_sq {x y : E} : ∥x - y∥ ^ 2 = ∥x∥ ^ 2 - 2 * re ⟪x, y⟫ + ∥y∥ ^ 2 := by
  repeat'
    rw [sq, ← inner_self_eq_norm_mul_norm]
  rw [inner_sub_sub_self]
  calc re (⟪x, x⟫ - ⟪x, y⟫ - ⟪y, x⟫ + ⟪y, y⟫) = re ⟪x, x⟫ - re ⟪x, y⟫ - re ⟪y, x⟫ + re ⟪y, y⟫ := by
      simp _ = -re ⟪y, x⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ := by
      ring _ = -re (⟪x, y⟫†) - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ := by
      rw [inner_conj_sym]_ = -re ⟪x, y⟫ - re ⟪x, y⟫ + re ⟪x, x⟫ + re ⟪y, y⟫ := by
      rw [conj_re]_ = re ⟪x, x⟫ - 2 * re ⟪x, y⟫ + re ⟪y, y⟫ := by
      ring

alias norm_sub_sq ← norm_sub_pow_two

/-- Expand the square -/
theorem norm_sub_sq_real {x y : F} : ∥x - y∥ ^ 2 = ∥x∥ ^ 2 - 2 * ⟪x, y⟫_ℝ + ∥y∥ ^ 2 :=
  norm_sub_sq

alias norm_sub_sq_real ← norm_sub_pow_two_real

/-- Expand the square -/
theorem norm_sub_mul_self {x y : E} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * re ⟪x, y⟫ + ∥y∥ * ∥y∥ := by
  repeat'
    rw [← sq]
  exact norm_sub_sq

/-- Expand the square -/
theorem norm_sub_mul_self_real {x y : F} : ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ - 2 * ⟪x, y⟫_ℝ + ∥y∥ * ∥y∥ := by
  have h := @norm_sub_mul_self ℝ F _ _
  simpa using h

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_inner_le_norm (x y : E) : abs ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ :=
  nonneg_le_nonneg_of_sq_le_sq (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (by
      have : ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥) = re ⟪x, x⟫ * re ⟪y, y⟫
      simp only [← inner_self_eq_norm_mul_norm]
      ring
      rw [this]
      conv_lhs => congr skip rw [inner_abs_conj_sym]
      exact inner_mul_inner_self_le _ _)

theorem norm_inner_le_norm (x y : E) : ∥⟪x, y⟫∥ ≤ ∥x∥ * ∥y∥ :=
  (IsROrC.norm_eq_abs _).le.trans (abs_inner_le_norm x y)

theorem nnnorm_inner_le_nnnorm (x y : E) : ∥⟪x, y⟫∥₊ ≤ ∥x∥₊ * ∥y∥₊ :=
  norm_inner_le_norm x y

theorem re_inner_le_norm (x y : E) : re ⟪x, y⟫ ≤ ∥x∥ * ∥y∥ :=
  le_transₓ (re_le_abs (inner x y)) (abs_inner_le_norm x y)

/-- Cauchy–Schwarz inequality with norm -/
theorem abs_real_inner_le_norm (x y : F) : absR ⟪x, y⟫_ℝ ≤ ∥x∥ * ∥y∥ := by
  have h := @abs_inner_le_norm ℝ F _ _ x y
  simpa using h

/-- Cauchy–Schwarz inequality with norm -/
theorem real_inner_le_norm (x y : F) : ⟪x, y⟫_ℝ ≤ ∥x∥ * ∥y∥ :=
  le_transₓ (le_abs_self _) (abs_real_inner_le_norm _ _)

include 𝕜

theorem parallelogram_law_with_norm (x y : E) : ∥x + y∥ * ∥x + y∥ + ∥x - y∥ * ∥x - y∥ = 2 * (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥) :=
  by
  simp only [inner_self_eq_norm_mul_norm]
  rw [← re.map_add, parallelogram_law, two_mul, two_mul]
  simp only [← re.map_add]

theorem parallelogram_law_with_nnnorm (x y : E) :
    ∥x + y∥₊ * ∥x + y∥₊ + ∥x - y∥₊ * ∥x - y∥₊ = 2 * (∥x∥₊ * ∥x∥₊ + ∥y∥₊ * ∥y∥₊) :=
  Subtype.ext <| parallelogram_law_with_norm x y

omit 𝕜

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (∥x + y∥ * ∥x + y∥ - ∥x∥ * ∥x∥ - ∥y∥ * ∥y∥) / 2 := by
  rw [norm_add_mul_self]
  ring

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : E) :
    re ⟪x, y⟫ = (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - ∥x - y∥ * ∥x - y∥) / 2 := by
  rw [norm_sub_mul_self]
  ring

/-- Polarization identity: The real part of the  inner product, in terms of the norm. -/
theorem re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four (x y : E) :
    re ⟪x, y⟫ = (∥x + y∥ * ∥x + y∥ - ∥x - y∥ * ∥x - y∥) / 4 := by
  rw [norm_add_mul_self, norm_sub_mul_self]
  ring

/-- Polarization identity: The imaginary part of the inner product, in terms of the norm. -/
theorem im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four (x y : E) :
    im ⟪x, y⟫ = (∥x - IK • y∥ * ∥x - IK • y∥ - ∥x + IK • y∥ * ∥x + IK • y∥) / 4 := by
  simp only [← norm_add_mul_self, ← norm_sub_mul_self, ← inner_smul_right, ← I_mul_re]
  ring

/-- Polarization identity: The inner product, in terms of the norm. -/
theorem inner_eq_sum_norm_sq_div_four (x y : E) :
    ⟪x, y⟫ = (∥x + y∥ ^ 2 - ∥x - y∥ ^ 2 + (∥x - IK • y∥ ^ 2 - ∥x + IK • y∥ ^ 2) * IK) / 4 := by
  rw [← re_add_im ⟪x, y⟫, re_inner_eq_norm_add_mul_self_sub_norm_sub_mul_self_div_four,
    im_inner_eq_norm_sub_I_smul_mul_self_sub_norm_add_I_smul_mul_self_div_four]
  push_cast
  simp only [← sq, mul_div_right_comm, add_div]

/-- Formula for the distance between the images of two nonzero points under an inversion with center
zero. See also `euclidean_geometry.dist_inversion_inversion` for inversions around a general
point. -/
theorem dist_div_norm_sq_smul {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) (R : ℝ) :
    dist ((R / ∥x∥) ^ 2 • x) ((R / ∥y∥) ^ 2 • y) = R ^ 2 / (∥x∥ * ∥y∥) * dist x y :=
  have hx' : ∥x∥ ≠ 0 := norm_ne_zero_iff.2 hx
  have hy' : ∥y∥ ≠ 0 := norm_ne_zero_iff.2 hy
  calc
    dist ((R / ∥x∥) ^ 2 • x) ((R / ∥y∥) ^ 2 • y) = sqrt (∥(R / ∥x∥) ^ 2 • x - (R / ∥y∥) ^ 2 • y∥ ^ 2) := by
      rw [dist_eq_norm, sqrt_sq (norm_nonneg _)]
    _ = sqrt ((R ^ 2 / (∥x∥ * ∥y∥)) ^ 2 * ∥x - y∥ ^ 2) :=
      congr_arg sqrt <| by
        field_simp [← sq, ← norm_sub_mul_self_real, ← norm_smul, ← real_inner_smul_left, ← inner_smul_right, ←
          Real.norm_of_nonneg (mul_self_nonneg _)]
        ring
    _ = R ^ 2 / (∥x∥ * ∥y∥) * dist x y := by
      rw [sqrt_mul (sq_nonneg _), sqrt_sq (norm_nonneg _),
        sqrt_sq (div_nonneg (sq_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))), dist_eq_norm]
    

-- See note [lower instance priority]
instance (priority := 100) InnerProductSpace.to_uniform_convex_space : UniformConvexSpace F :=
  ⟨fun ε hε => by
    refine' ⟨2 - sqrt (4 - ε ^ 2), sub_pos_of_lt <| (sqrt_lt' zero_lt_two).2 _, fun x hx y hy hxy => _⟩
    · norm_num
      exact pow_pos hε _
      
    rw [sub_sub_cancel]
    refine' le_sqrt_of_sq_le _
    rw [sq, eq_sub_iff_add_eq.2 (parallelogram_law_with_norm x y), ← sq ∥x - y∥, hx, hy]
    norm_num
    exact pow_le_pow_of_le_left hε.le hxy _⟩

section Complex

variable {V : Type _} [InnerProductSpace ℂ V]

/-- A complex polarization identity, with a linear map
-/
theorem inner_map_polarization (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T y, x⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ + Complex.i * ⟪T (x + Complex.i • y), x + Complex.i • y⟫_ℂ -
          Complex.i * ⟪T (x - Complex.i • y), x - Complex.i • y⟫_ℂ) /
        4 :=
  by
  simp only [← map_add, ← map_sub, ← inner_add_left, ← inner_add_right, ← LinearMap.map_smul, ← inner_smul_left, ←
    inner_smul_right, ← Complex.conj_I, pow_two, ← Complex.I_sq, ← inner_sub_left, ← inner_sub_right, ← mul_addₓ,
    mul_assoc, ← mul_neg, ← neg_negₓ, ← sub_neg_eq_add, ← one_mulₓ, ← neg_one_mul, ← mul_sub, ← sub_sub]
  ring

theorem inner_map_polarization' (T : V →ₗ[ℂ] V) (x y : V) :
    ⟪T x, y⟫_ℂ =
      (⟪T (x + y), x + y⟫_ℂ - ⟪T (x - y), x - y⟫_ℂ - Complex.i * ⟪T (x + Complex.i • y), x + Complex.i • y⟫_ℂ +
          Complex.i * ⟪T (x - Complex.i • y), x - Complex.i • y⟫_ℂ) /
        4 :=
  by
  simp only [← map_add, ← map_sub, ← inner_add_left, ← inner_add_right, ← LinearMap.map_smul, ← inner_smul_left, ←
    inner_smul_right, ← Complex.conj_I, pow_two, ← Complex.I_sq, ← inner_sub_left, ← inner_sub_right, ← mul_addₓ,
    mul_assoc, ← mul_neg, ← neg_negₓ, ← sub_neg_eq_add, ← one_mulₓ, ← neg_one_mul, ← mul_sub, ← sub_sub]
  ring

/-- If `⟪T x, x⟫_ℂ = 0` for all x, then T = 0.
-/
theorem inner_map_self_eq_zero (T : V →ₗ[ℂ] V) : (∀ x : V, ⟪T x, x⟫_ℂ = 0) ↔ T = 0 := by
  constructor
  · intro hT
    ext x
    simp only [← LinearMap.zero_apply, inner_self_eq_zero, ← inner_map_polarization, ← hT]
    norm_num
    
  · rintro rfl x
    simp only [← LinearMap.zero_apply, ← inner_zero_left]
    

end Complex

section

variable {ι : Type _} {ι' : Type _} {ι'' : Type _}

variable {E' : Type _} [InnerProductSpace 𝕜 E']

variable {E'' : Type _} [InnerProductSpace 𝕜 E'']

/-- A linear isometry preserves the inner product. -/
@[simp]
theorem LinearIsometry.inner_map_map (f : E →ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ := by
  simp [← inner_eq_sum_norm_sq_div_four, f.norm_map]

/-- A linear isometric equivalence preserves the inner product. -/
@[simp]
theorem LinearIsometryEquiv.inner_map_map (f : E ≃ₗᵢ[𝕜] E') (x y : E) : ⟪f x, f y⟫ = ⟪x, y⟫ :=
  f.toLinearIsometry.inner_map_map x y

/-- A linear map that preserves the inner product is a linear isometry. -/
def LinearMap.isometryOfInner (f : E →ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E →ₗᵢ[𝕜] E' :=
  ⟨f, fun x => by
    simp only [← norm_eq_sqrt_inner, ← h]⟩

@[simp]
theorem LinearMap.coe_isometry_of_inner (f : E →ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
theorem LinearMap.isometry_of_inner_to_linear_map (f : E →ₗ[𝕜] E') (h) : (f.isometryOfInner h).toLinearMap = f :=
  rfl

/-- A linear equivalence that preserves the inner product is a linear isometric equivalence. -/
def LinearEquiv.isometryOfInner (f : E ≃ₗ[𝕜] E') (h : ∀ x y, ⟪f x, f y⟫ = ⟪x, y⟫) : E ≃ₗᵢ[𝕜] E' :=
  ⟨f, ((f : E →ₗ[𝕜] E').isometryOfInner h).norm_map⟩

@[simp]
theorem LinearEquiv.coe_isometry_of_inner (f : E ≃ₗ[𝕜] E') (h) : ⇑(f.isometryOfInner h) = f :=
  rfl

@[simp]
theorem LinearEquiv.isometry_of_inner_to_linear_equiv (f : E ≃ₗ[𝕜] E') (h) : (f.isometryOfInner h).toLinearEquiv = f :=
  rfl

/-- A linear isometry preserves the property of being orthonormal. -/
theorem Orthonormal.comp_linear_isometry {v : ι → E} (hv : Orthonormal 𝕜 v) (f : E →ₗᵢ[𝕜] E') : Orthonormal 𝕜 (f ∘ v) :=
  by
  classical
  simp_rw [orthonormal_iff_ite, LinearIsometry.inner_map_map, ← orthonormal_iff_ite]
  exact hv

/-- A linear isometric equivalence preserves the property of being orthonormal. -/
theorem Orthonormal.comp_linear_isometry_equiv {v : ι → E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (f ∘ v) :=
  hv.comp_linear_isometry f.toLinearIsometry

/-- A linear isometric equivalence, applied with `basis.map`, preserves the property of being
orthonormal. --/
theorem Orthonormal.map_linear_isometry_equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) (f : E ≃ₗᵢ[𝕜] E') :
    Orthonormal 𝕜 (v.map f.toLinearEquiv) :=
  hv.comp_linear_isometry_equiv f

/-- A linear map that sends an orthonormal basis to orthonormal vectors is a linear isometry. -/
def LinearMap.isometryOfOrthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E →ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← v.total_repr x, ← v.total_repr y, Finsupp.apply_total, Finsupp.apply_total, hv.inner_finsupp_eq_sum_left,
      hf.inner_finsupp_eq_sum_left]

@[simp]
theorem LinearMap.coe_isometry_of_orthonormal (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl

@[simp]
theorem LinearMap.isometry_of_orthonormal_to_linear_map (f : E →ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : (f.isometryOfOrthonormal hv hf).toLinearMap = f :=
  rfl

/-- A linear equivalence that sends an orthonormal basis to orthonormal vectors is a linear
isometric equivalence. -/
def LinearEquiv.isometryOfOrthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : E ≃ₗᵢ[𝕜] E' :=
  f.isometryOfInner fun x y => by
    rw [← LinearEquiv.coe_coe] at hf
    rw [← v.total_repr x, ← v.total_repr y, ← LinearEquiv.coe_coe, Finsupp.apply_total, Finsupp.apply_total,
      hv.inner_finsupp_eq_sum_left, hf.inner_finsupp_eq_sum_left]

@[simp]
theorem LinearEquiv.coe_isometry_of_orthonormal (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : ⇑(f.isometryOfOrthonormal hv hf) = f :=
  rfl

@[simp]
theorem LinearEquiv.isometry_of_orthonormal_to_linear_equiv (f : E ≃ₗ[𝕜] E') {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v)
    (hf : Orthonormal 𝕜 (f ∘ v)) : (f.isometryOfOrthonormal hv hf).toLinearEquiv = f :=
  rfl

/-- A linear isometric equivalence that sends an orthonormal basis to a given orthonormal basis. -/
def Orthonormal.equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v')
    (e : ι ≃ ι') : E ≃ₗᵢ[𝕜] E' :=
  (v.Equiv v' e).isometryOfOrthonormal hv
    (by
      have h : v.equiv v' e ∘ v = v' ∘ e := by
        ext i
        simp
      rw [h]
      exact hv'.comp _ e.injective)

@[simp]
theorem Orthonormal.equiv_to_linear_equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') : (hv.Equiv hv' e).toLinearEquiv = v.Equiv v' e :=
  rfl

@[simp]
theorem Orthonormal.equiv_apply {ι' : Type _} {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'}
    (hv' : Orthonormal 𝕜 v') (e : ι ≃ ι') (i : ι) : hv.Equiv hv' e (v i) = v' (e i) :=
  Basis.equiv_apply _ _ _ _

@[simp]
theorem Orthonormal.equiv_refl {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) :
    hv.Equiv hv (Equivₓ.refl ι) = LinearIsometryEquiv.refl 𝕜 E :=
  v.ext_linear_isometry_equiv fun i => by
    simp

@[simp]
theorem Orthonormal.equiv_symm {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v')
    (e : ι ≃ ι') : (hv.Equiv hv' e).symm = hv'.Equiv hv e.symm :=
  v'.ext_linear_isometry_equiv fun i =>
    (hv.Equiv hv' e).Injective
      (by
        simp )

@[simp]
theorem Orthonormal.equiv_trans {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v')
    (e : ι ≃ ι') {v'' : Basis ι'' 𝕜 E''} (hv'' : Orthonormal 𝕜 v'') (e' : ι' ≃ ι'') :
    (hv.Equiv hv' e).trans (hv'.Equiv hv'' e') = hv.Equiv hv'' (e.trans e') :=
  v.ext_linear_isometry_equiv fun i => by
    simp

theorem Orthonormal.map_equiv {v : Basis ι 𝕜 E} (hv : Orthonormal 𝕜 v) {v' : Basis ι' 𝕜 E'} (hv' : Orthonormal 𝕜 v')
    (e : ι ≃ ι') : v.map (hv.Equiv hv' e).toLinearEquiv = v'.reindex e.symm :=
  v.mapEquiv _ _

end

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (∥x + y∥ * ∥x + y∥ - ∥x∥ * ∥x∥ - ∥y∥ * ∥y∥) / 2 :=
  re_to_real.symm.trans <| re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two x y

/-- Polarization identity: The real inner product, in terms of the norm. -/
theorem real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two (x y : F) :
    ⟪x, y⟫_ℝ = (∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ - ∥x - y∥ * ∥x - y∥) / 2 :=
  re_to_real.symm.trans <| re_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two x y

/-- Pythagorean theorem, if-and-only-if vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [norm_add_mul_self, add_right_cancel_iffₓ, add_right_eq_selfₓ, mul_eq_zero]
  norm_num

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (x y : E) (h : ⟪x, y⟫ = 0) :
    ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ := by
  rw [norm_add_mul_self, add_right_cancel_iffₓ, add_right_eq_selfₓ, mul_eq_zero]
  apply Or.inr
  simp only [← h, ← zero_re']

/-- Pythagorean theorem, vector inner product form. -/
theorem norm_add_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ∥x + y∥ * ∥x + y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
  (norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- Pythagorean theorem, subtracting vectors, if-and-only-if vector
inner product form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero (x y : F) :
    ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ ↔ ⟪x, y⟫_ℝ = 0 := by
  rw [norm_sub_mul_self, add_right_cancel_iffₓ, sub_eq_add_neg, add_right_eq_selfₓ, neg_eq_zero, mul_eq_zero]
  norm_num

/-- Pythagorean theorem, subtracting vectors, vector inner product
form. -/
theorem norm_sub_sq_eq_norm_sq_add_norm_sq_real {x y : F} (h : ⟪x, y⟫_ℝ = 0) :
    ∥x - y∥ * ∥x - y∥ = ∥x∥ * ∥x∥ + ∥y∥ * ∥y∥ :=
  (norm_sub_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y).2 h

/-- The sum and difference of two vectors are orthogonal if and only
if they have the same norm. -/
theorem real_inner_add_sub_eq_zero_iff (x y : F) : ⟪x + y, x - y⟫_ℝ = 0 ↔ ∥x∥ = ∥y∥ := by
  conv_rhs => rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp only [inner_self_eq_norm_mul_norm, ← inner_add_left, ← inner_sub_right, ← real_inner_comm y x, ← sub_eq_zero, ←
    re_to_real]
  constructor
  · intro h
    rw [add_commₓ] at h
    linarith
    
  · intro h
    linarith
    

/-- Given two orthogonal vectors, their sum and difference have equal norms. -/
theorem norm_sub_eq_norm_add {v w : E} (h : ⟪v, w⟫ = 0) : ∥w - v∥ = ∥w + v∥ := by
  rw [← mul_self_inj_of_nonneg (norm_nonneg _) (norm_nonneg _)]
  simp [← h, inner_self_eq_norm_mul_norm, ← inner_add_left, ← inner_add_right, ← inner_sub_left, ← inner_sub_right, ←
    inner_re_symm]

/-- The real inner product of two vectors, divided by the product of their
norms, has absolute value at most 1. -/
theorem abs_real_inner_div_norm_mul_norm_le_one (x y : F) : absR (⟪x, y⟫_ℝ / (∥x∥ * ∥y∥)) ≤ 1 := by
  rw [_root_.abs_div]
  by_cases' h : 0 = absR (∥x∥ * ∥y∥)
  · rw [← h, div_zero]
    norm_num
    
  · change 0 ≠ absR (∥x∥ * ∥y∥) at h
    rw [div_le_iff' (lt_of_le_of_neₓ (ge_iff_le.mp (_root_.abs_nonneg (∥x∥ * ∥y∥))) h)]
    convert abs_real_inner_le_norm x y using 1
    rw [_root_.abs_mul, _root_.abs_of_nonneg (norm_nonneg x), _root_.abs_of_nonneg (norm_nonneg y), mul_oneₓ]
    

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_left (x : F) (r : ℝ) : ⟪r • x, x⟫_ℝ = r * (∥x∥ * ∥x∥) := by
  rw [real_inner_smul_left, ← real_inner_self_eq_norm_mul_norm]

/-- The inner product of a vector with a multiple of itself. -/
theorem real_inner_smul_self_right (x : F) (r : ℝ) : ⟪x, r • x⟫_ℝ = r * (∥x∥ * ∥x∥) := by
  rw [inner_smul_right, ← real_inner_self_eq_norm_mul_norm]

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : E} {r : 𝕜} (hx : x ≠ 0) (hr : r ≠ 0) :
    abs ⟪x, r • x⟫ / (∥x∥ * ∥r • x∥) = 1 := by
  have hx' : ∥x∥ ≠ 0 := by
    simp [← norm_eq_zero, ← hx]
  have hr' : abs r ≠ 0 := by
    simp [← IsROrC.abs_eq_zero, ← hr]
  rw [inner_smul_right, IsROrC.abs_mul, ← inner_self_re_abs, inner_self_eq_norm_mul_norm, norm_smul]
  rw [IsROrC.norm_eq_abs, ← mul_assoc, ← div_div, mul_div_cancel _ hx', ← div_div, mul_comm, mul_div_cancel _ hr',
    div_self hx']

/-- The inner product of a nonzero vector with a nonzero multiple of
itself, divided by the product of their norms, has absolute value
1. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r ≠ 0) :
    absR ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = 1 := by
  rw [← abs_to_real]
  exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr

/-- The inner product of a nonzero vector with a positive multiple of
itself, divided by the product of their norms, has value 1. -/
theorem real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul {x : F} {r : ℝ} (hx : x ≠ 0) (hr : 0 < r) :
    ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = 1 := by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ∥x∥, mul_comm _ (absR r), mul_assoc,
    _root_.abs_of_nonneg (le_of_ltₓ hr), div_self]
  exact mul_ne_zero (ne_of_gtₓ hr) fun h => hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h))

/-- The inner product of a nonzero vector with a negative multiple of
itself, divided by the product of their norms, has value -1. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul {x : F} {r : ℝ} (hx : x ≠ 0) (hr : r < 0) :
    ⟪x, r • x⟫_ℝ / (∥x∥ * ∥r • x∥) = -1 := by
  rw [real_inner_smul_self_right, norm_smul, Real.norm_eq_abs, ← mul_assoc ∥x∥, mul_comm _ (absR r), mul_assoc,
    abs_of_neg hr, neg_mul, div_neg_eq_neg_div, div_self]
  exact mul_ne_zero (ne_of_ltₓ hr) fun h => hx (norm_eq_zero.1 (eq_zero_of_mul_self_eq_zero h))

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_inner_div_norm_mul_norm_eq_one_iff (x y : E) :
    abs (⟪x, y⟫ / (∥x∥ * ∥y∥)) = 1 ↔ x ≠ 0 ∧ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x := by
  constructor
  · intro h
    have hx0 : x ≠ 0 := by
      intro hx0
      rw [hx0, inner_zero_left, zero_div] at h
      norm_num  at h
    refine' And.intro hx0 _
    set r := ⟪x, y⟫ / (∥x∥ * ∥x∥) with hr
    use r
    set t := y - r • x with ht
    have ht0 : ⟪x, t⟫ = 0 := by
      rw [ht, inner_sub_right, inner_smul_right, hr]
      norm_cast
      rw [← inner_self_eq_norm_mul_norm, inner_self_re_to_K, div_mul_cancel _ fun h => hx0 (inner_self_eq_zero.1 h),
        sub_self]
    replace h : ∥r • x∥ / ∥t + r • x∥ = 1
    · rw [← sub_add_cancel y (r • x), ← ht, inner_add_right, ht0, zero_addₓ, inner_smul_right, IsROrC.abs_div,
        IsROrC.abs_mul, ← inner_self_re_abs, inner_self_eq_norm_mul_norm] at h
      norm_cast  at h
      rwa [_root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm, ← mul_assoc, mul_comm,
        mul_div_mul_left _ _ fun h => hx0 (norm_eq_zero.1 h), ← IsROrC.norm_eq_abs, ← norm_smul] at h
      
    have hr0 : r ≠ 0 := by
      intro hr0
      rw [hr0, zero_smul, norm_zero, zero_div] at h
      norm_num  at h
    refine' And.intro hr0 _
    have h2 : ∥r • x∥ ^ 2 = ∥t + r • x∥ ^ 2 := by
      rw [eq_of_div_eq_one h]
    replace h2 : ⟪r • x, r • x⟫ = ⟪t, t⟫ + ⟪t, r • x⟫ + ⟪r • x, t⟫ + ⟪r • x, r • x⟫
    · rw [sq, sq, ← inner_self_eq_norm_mul_norm, ← inner_self_eq_norm_mul_norm] at h2
      have h2' := congr_arg (fun z : ℝ => (z : 𝕜)) h2
      simp_rw [inner_self_re_to_K, inner_add_add_self] at h2'
      exact h2'
      
    conv at h2 in ⟪r • x, t⟫ => rw [inner_smul_left, ht0, mul_zero]
    symm'  at h2
    have h₁ : ⟪t, r • x⟫ = 0 := by
      rw [inner_smul_right, ← inner_conj_sym, ht0]
      simp
    rw [add_zeroₓ, h₁, add_left_eq_self, add_zeroₓ, inner_self_eq_zero] at h2
    rw [h2] at ht
    exact eq_of_sub_eq_zero ht.symm
    
  · intro h
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    rw [hy, IsROrC.abs_div]
    norm_cast
    rw [_root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm]
    exact abs_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_ne_zero_mul hx hr
    

/-- The inner product of two vectors, divided by the product of their
norms, has absolute value 1 if and only if they are nonzero and one is
a multiple of the other. One form of equality case for Cauchy-Schwarz. -/
theorem abs_real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    absR (⟪x, y⟫_ℝ / (∥x∥ * ∥y∥)) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r ≠ 0 ∧ y = r • x := by
  have := @abs_inner_div_norm_mul_norm_eq_one_iff ℝ F _ _ x y
  simpa [← coe_real_eq_id] using this

/-- If the inner product of two vectors is equal to the product of their norms, then the two vectors
are multiples of each other. One form of the equality case for Cauchy-Schwarz.
Compare `inner_eq_norm_mul_iff`, which takes the stronger hypothesis `⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem abs_inner_eq_norm_iff (x y : E) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    abs ⟪x, y⟫ = ∥x∥ * ∥y∥ ↔ ∃ r : 𝕜, r ≠ 0 ∧ y = r • x := by
  have hx0' : ∥x∥ ≠ 0 := by
    simp [← norm_eq_zero, ← hx0]
  have hy0' : ∥y∥ ≠ 0 := by
    simp [← norm_eq_zero, ← hy0]
  have hxy0 : ∥x∥ * ∥y∥ ≠ 0 := by
    simp [← hx0', ← hy0']
  have h₁ : abs ⟪x, y⟫ = ∥x∥ * ∥y∥ ↔ abs (⟪x, y⟫ / (∥x∥ * ∥y∥)) = 1 := by
    refine' ⟨_, _⟩
    · intro h
      norm_cast
      rw [IsROrC.abs_div, h, abs_of_real, _root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm]
      exact div_self hxy0
      
    · intro h
      norm_cast  at h
      rwa [IsROrC.abs_div, abs_of_real, _root_.abs_mul, abs_norm_eq_norm, abs_norm_eq_norm, div_eq_one_iff_eq hxy0] at h
      
  rw [h₁, abs_inner_div_norm_mul_norm_eq_one_iff x y]
  simp [← hx0]

/-- The inner product of two vectors, divided by the product of their
norms, has value 1 if and only if they are nonzero and one is
a positive multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (∥x∥ * ∥y∥) = 1 ↔ x ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ y = r • x := by
  constructor
  · intro h
    have ha := h
    apply_fun absR  at ha
    norm_num  at ha
    rcases(abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    use hx, r
    refine' And.intro _ hy
    by_contra hrneg
    rw [hy] at h
    rw [real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx (lt_of_le_of_neₓ (le_of_not_ltₓ hrneg) hr)] at
      h
    norm_num  at h
    
  · intro h
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    rw [hy]
    exact real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx hr
    

/-- The inner product of two vectors, divided by the product of their
norms, has value -1 if and only if they are nonzero and one is
a negative multiple of the other. -/
theorem real_inner_div_norm_mul_norm_eq_neg_one_iff (x y : F) :
    ⟪x, y⟫_ℝ / (∥x∥ * ∥y∥) = -1 ↔ x ≠ 0 ∧ ∃ r : ℝ, r < 0 ∧ y = r • x := by
  constructor
  · intro h
    have ha := h
    apply_fun absR  at ha
    norm_num  at ha
    rcases(abs_real_inner_div_norm_mul_norm_eq_one_iff x y).1 ha with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    use hx, r
    refine' And.intro _ hy
    by_contra hrpos
    rw [hy] at h
    rw [real_inner_div_norm_mul_norm_eq_one_of_ne_zero_of_pos_mul hx (lt_of_le_of_neₓ (le_of_not_ltₓ hrpos) hr.symm)] at
      h
    norm_num  at h
    
  · intro h
    rcases h with ⟨hx, ⟨r, ⟨hr, hy⟩⟩⟩
    rw [hy]
    exact real_inner_div_norm_mul_norm_eq_neg_one_of_ne_zero_of_neg_mul hx hr
    

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ∥x∥ * ∥y∥`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem inner_eq_norm_mul_iff {x y : E} : ⟪x, y⟫ = (∥x∥ : 𝕜) * ∥y∥ ↔ (∥y∥ : 𝕜) • x = (∥x∥ : 𝕜) • y := by
  by_cases' h : x = 0 ∨ y = 0
  -- WLOG `x` and `y` are nonzero
  · cases h <;> simp [← h]
    
  calc ⟪x, y⟫ = (∥x∥ : 𝕜) * ∥y∥ ↔ ∥x∥ * ∥y∥ = re ⟪x, y⟫ := by
      norm_cast
      constructor
      · intro h'
        simp [← h']
        
      · have cauchy_schwarz := abs_inner_le_norm x y
        intro h'
        rw [h'] at cauchy_schwarz⊢
        rwa [re_eq_self_of_le]
        _ ↔ 2 * ∥x∥ * ∥y∥ * (∥x∥ * ∥y∥ - re ⟪x, y⟫) = 0 :=
      by
      simp [← h, ←
        show (2 : ℝ) ≠ 0 by
          norm_num,
        ← sub_eq_zero]_ ↔ ∥(∥y∥ : 𝕜) • x - (∥x∥ : 𝕜) • y∥ * ∥(∥y∥ : 𝕜) • x - (∥x∥ : 𝕜) • y∥ = 0 :=
      by
      simp only [← norm_sub_mul_self, ← inner_smul_left, ← inner_smul_right, ← norm_smul, ← conj_of_real, ←
        IsROrC.norm_eq_abs, ← abs_of_real, ← of_real_im, ← of_real_re, ← mul_re, ← abs_norm_eq_norm]
      refine' Eq.congr _ rfl
      ring _ ↔ (∥y∥ : 𝕜) • x = (∥x∥ : 𝕜) • y := by
      simp [← norm_sub_eq_zero_iff]

/-- If the inner product of two vectors is equal to the product of their norms (i.e.,
`⟪x, y⟫ = ∥x∥ * ∥y∥`), then the two vectors are nonnegative real multiples of each other. One form
of the equality case for Cauchy-Schwarz.
Compare `abs_inner_eq_norm_iff`, which takes the weaker hypothesis `abs ⟪x, y⟫ = ∥x∥ * ∥y∥`. -/
theorem inner_eq_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ = ∥x∥ * ∥y∥ ↔ ∥y∥ • x = ∥x∥ • y :=
  inner_eq_norm_mul_iff

/-- If the inner product of two unit vectors is `1`, then the two vectors are equal. One form of
the equality case for Cauchy-Schwarz. -/
theorem inner_eq_norm_mul_iff_of_norm_one {x y : E} (hx : ∥x∥ = 1) (hy : ∥y∥ = 1) : ⟪x, y⟫ = 1 ↔ x = y := by
  convert inner_eq_norm_mul_iff using 2 <;> simp [← hx, ← hy]

theorem inner_lt_norm_mul_iff_real {x y : F} : ⟪x, y⟫_ℝ < ∥x∥ * ∥y∥ ↔ ∥y∥ • x ≠ ∥x∥ • y :=
  calc
    ⟪x, y⟫_ℝ < ∥x∥ * ∥y∥ ↔ ⟪x, y⟫_ℝ ≠ ∥x∥ * ∥y∥ := ⟨ne_of_ltₓ, lt_of_le_of_neₓ (real_inner_le_norm _ _)⟩
    _ ↔ ∥y∥ • x ≠ ∥x∥ • y := not_congr inner_eq_norm_mul_iff_real
    

/-- If the inner product of two unit vectors is strictly less than `1`, then the two vectors are
distinct. One form of the equality case for Cauchy-Schwarz. -/
theorem inner_lt_one_iff_real_of_norm_one {x y : F} (hx : ∥x∥ = 1) (hy : ∥y∥ = 1) : ⟪x, y⟫_ℝ < 1 ↔ x ≠ y := by
  convert inner_lt_norm_mul_iff_real <;> simp [← hx, ← hy]

/-- The inner product of two weighted sums, where the weights in each
sum add to 0, in terms of the norms of pairwise differences. -/
theorem inner_sum_smul_sum_smul_of_sum_eq_zero {ι₁ : Type _} {s₁ : Finset ι₁} {w₁ : ι₁ → ℝ} (v₁ : ι₁ → F)
    (h₁ : (∑ i in s₁, w₁ i) = 0) {ι₂ : Type _} {s₂ : Finset ι₂} {w₂ : ι₂ → ℝ} (v₂ : ι₂ → F)
    (h₂ : (∑ i in s₂, w₂ i) = 0) :
    ⟪∑ i₁ in s₁, w₁ i₁ • v₁ i₁, ∑ i₂ in s₂, w₂ i₂ • v₂ i₂⟫_ℝ =
      (-∑ i₁ in s₁, ∑ i₂ in s₂, w₁ i₁ * w₂ i₂ * (∥v₁ i₁ - v₂ i₂∥ * ∥v₁ i₁ - v₂ i₂∥)) / 2 :=
  by
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    real_inner_eq_norm_mul_self_add_norm_mul_self_sub_norm_sub_mul_self_div_two, ← div_sub_div_same, ← div_add_div_same,
    mul_sub_left_distrib, left_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ←
    Finset.sum_mul, h₁, h₂, zero_mul, mul_zero, Finset.sum_const_zero, zero_addₓ, zero_sub, Finset.mul_sum, neg_div,
    Finset.sum_div, mul_div_assoc, mul_assoc]

/-- The inner product as a sesquilinear map. -/
def innerₛₗ : E →ₗ⋆[𝕜] E →ₗ[𝕜] 𝕜 :=
  LinearMap.mk₂'ₛₗ _ _ (fun v w => ⟪v, w⟫) (fun _ _ _ => inner_add_left) (fun _ _ _ => inner_smul_left)
    (fun _ _ _ => inner_add_right) fun _ _ _ => inner_smul_right

@[simp]
theorem innerₛₗ_apply_coe (v : E) : (innerₛₗ v : E → 𝕜) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerₛₗ_apply (v w : E) : innerₛₗ v w = ⟪v, w⟫ :=
  rfl

/-- The inner product as a continuous sesquilinear map. Note that `to_dual_map` (resp. `to_dual`)
in `inner_product_space.dual` is a version of this given as a linear isometry (resp. linear
isometric equivalence). -/
def innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  LinearMap.mkContinuous₂ innerₛₗ 1 fun x y => by
    simp only [← norm_inner_le_norm, ← one_mulₓ, ← innerₛₗ_apply]

@[simp]
theorem innerSL_apply_coe (v : E) : (innerSL v : E → 𝕜) = fun w => ⟪v, w⟫ :=
  rfl

@[simp]
theorem innerSL_apply (v w : E) : innerSL v w = ⟪v, w⟫ :=
  rfl

/-- `innerSL` is an isometry. Note that the associated `linear_isometry` is defined in
`inner_product_space.dual` as `to_dual_map`.  -/
@[simp]
theorem innerSL_apply_norm {x : E} : ∥(innerSL x : E →L[𝕜] 𝕜)∥ = ∥x∥ := by
  refine' le_antisymmₓ ((innerSL x).op_norm_le_bound (norm_nonneg _) fun y => norm_inner_le_norm _ _) _
  cases' eq_or_lt_of_le (norm_nonneg x) with h h
  · have : x = 0 := norm_eq_zero.mp (Eq.symm h)
    simp [← this]
    
  · refine' (mul_le_mul_right h).mp _
    calc ∥x∥ * ∥x∥ = ∥x∥ ^ 2 := by
        ring _ = re ⟪x, x⟫ := norm_sq_eq_inner _ _ ≤ abs ⟪x, x⟫ := re_le_abs _ _ = ∥innerSL x x∥ := by
        rw [← IsROrC.norm_eq_abs]
        rfl _ ≤ ∥innerSL x∥ * ∥x∥ := (innerSL x).le_op_norm _
    

/-- The inner product as a continuous sesquilinear map, with the two arguments flipped. -/
def innerSLFlip : E →L[𝕜] E →L⋆[𝕜] 𝕜 :=
  @ContinuousLinearMap.flipₗᵢ' 𝕜 𝕜 𝕜 E E 𝕜 _ _ _ _ _ _ _ _ _ (RingHom.id 𝕜) (starRingEnd 𝕜) _ _ innerSL

@[simp]
theorem innerSL_flip_apply {x y : E} : innerSLFlip x y = ⟪y, x⟫ :=
  rfl

namespace ContinuousLinearMap

variable {E' : Type _} [InnerProductSpace 𝕜 E']

/-- Given `f : E →L[𝕜] E'`, construct the continuous sesquilinear form `λ x y, ⟪x, A y⟫`, given
as a continuous linear map. -/
def toSesqForm : (E →L[𝕜] E') →L[𝕜] E' →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  ↑(ContinuousLinearMap.flipₗᵢ' E E' 𝕜 (starRingEnd 𝕜) (RingHom.id 𝕜)).toContinuousLinearEquiv ∘L
    ContinuousLinearMap.compSL E E' (E' →L⋆[𝕜] 𝕜) (RingHom.id 𝕜) (RingHom.id 𝕜) innerSLFlip

@[simp]
theorem to_sesq_form_apply_coe (f : E →L[𝕜] E') (x : E') : toSesqForm f x = (innerSL x).comp f :=
  rfl

theorem to_sesq_form_apply_norm_le {f : E →L[𝕜] E'} {v : E'} : ∥toSesqForm f v∥ ≤ ∥f∥ * ∥v∥ := by
  refine' op_norm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _
  intro x
  have h₁ : ∥f x∥ ≤ ∥f∥ * ∥x∥ := le_op_norm _ _
  have h₂ := @norm_inner_le_norm 𝕜 E' _ _ v (f x)
  calc ∥⟪v, f x⟫∥ ≤ ∥v∥ * ∥f x∥ := h₂ _ ≤ ∥v∥ * (∥f∥ * ∥x∥) :=
      mul_le_mul_of_nonneg_left h₁ (norm_nonneg v)_ = ∥f∥ * ∥v∥ * ∥x∥ := by
      ring

end ContinuousLinearMap

/-- When an inner product space `E` over `𝕜` is considered as a real normed space, its inner
product satisfies `is_bounded_bilinear_map`.

In order to state these results, we need a `normed_space ℝ E` instance. We will later establish
such an instance by restriction-of-scalars, `inner_product_space.is_R_or_C_to_real 𝕜 E`, but this
instance may be not definitionally equal to some other “natural” instance. So, we assume
`[normed_space ℝ E]`.
-/
theorem is_bounded_bilinear_map_inner [NormedSpace ℝ E] : IsBoundedBilinearMap ℝ fun p : E × E => ⟪p.1, p.2⟫ :=
  { add_left := fun _ _ _ => inner_add_left,
    smul_left := fun r x y => by
      simp only [algebra_map_smul 𝕜 r x, ← algebra_map_eq_of_real, ← inner_smul_real_left],
    add_right := fun _ _ _ => inner_add_right,
    smul_right := fun r x y => by
      simp only [algebra_map_smul 𝕜 r y, ← algebra_map_eq_of_real, ← inner_smul_real_right],
    bound :=
      ⟨1, zero_lt_one, fun x y => by
        rw [one_mulₓ]
        exact norm_inner_le_norm x y⟩ }

end Norm

section BesselsInequality

variable {ι : Type _} (x : E) {v : ι → E}

/-- Bessel's inequality for finite sums. -/
theorem Orthonormal.sum_inner_products_le {s : Finset ι} (hv : Orthonormal 𝕜 v) :
    (∑ i in s, ∥⟪v i, x⟫∥ ^ 2) ≤ ∥x∥ ^ 2 := by
  have h₂ : (∑ i in s, ∑ j in s, ⟪v i, x⟫ * ⟪x, v j⟫ * ⟪v j, v i⟫) = (∑ k in s, ⟪v k, x⟫ * ⟪x, v k⟫ : 𝕜) :=
    hv.inner_left_right_finset
  have h₃ : ∀ z : 𝕜, re (z * conj z) = ∥z∥ ^ 2 := by
    intro z
    simp only [← mul_conj, ← norm_sq_eq_def']
    norm_cast
  suffices hbf : ∥x - ∑ i in s, ⟪v i, x⟫ • v i∥ ^ 2 = ∥x∥ ^ 2 - ∑ i in s, ∥⟪v i, x⟫∥ ^ 2
  · rw [← sub_nonneg, ← hbf]
    simp only [← norm_nonneg, ← pow_nonneg]
    
  rw [norm_sub_sq, sub_add]
  simp only [← InnerProductSpace.norm_sq_eq_inner, ← inner_sum]
  simp only [← sum_inner, ← two_mul, ← inner_smul_right, ← inner_conj_sym, mul_assoc, ← h₂, h₃, ← inner_conj_sym, ←
    AddMonoidHom.map_sum, ← Finset.mul_sum, Finset.sum_sub_distrib, ← inner_smul_left, ← add_sub_cancel']

/-- Bessel's inequality. -/
theorem Orthonormal.tsum_inner_products_le (hv : Orthonormal 𝕜 v) : (∑' i, ∥⟪v i, x⟫∥ ^ 2) ≤ ∥x∥ ^ 2 := by
  refine' tsum_le_of_sum_le' _ fun s => hv.sum_inner_products_le x
  simp only [← norm_nonneg, ← pow_nonneg]

/-- The sum defined in Bessel's inequality is summable. -/
theorem Orthonormal.inner_products_summable (hv : Orthonormal 𝕜 v) : Summable fun i => ∥⟪v i, x⟫∥ ^ 2 := by
  use ⨆ s : Finset ι, ∑ i in s, ∥⟪v i, x⟫∥ ^ 2
  apply has_sum_of_is_lub_of_nonneg
  · intro b
    simp only [← norm_nonneg, ← pow_nonneg]
    
  · refine' is_lub_csupr _
    use ∥x∥ ^ 2
    rintro y ⟨s, rfl⟩
    exact hv.sum_inner_products_le x
    

end BesselsInequality

/-- A field `𝕜` satisfying `is_R_or_C` is itself a `𝕜`-inner product space. -/
instance IsROrC.innerProductSpace : InnerProductSpace 𝕜 𝕜 where
  inner := fun x y => conj x * y
  norm_sq_eq_inner := fun x => by
    unfold inner
    rw [mul_comm, mul_conj, of_real_re, norm_sq_eq_def']
  conj_sym := fun x y => by
    simp [← mul_comm]
  add_left := fun x y z => by
    simp [← inner, ← add_mulₓ]
  smul_left := fun x y z => by
    simp [← inner, ← mul_assoc]

@[simp]
theorem IsROrC.inner_apply (x y : 𝕜) : ⟪x, y⟫ = conj x * y :=
  rfl

/-! ### Inner product space structure on subspaces -/


/-- Induced inner product on a submodule. -/
instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  { Submodule.normedSpace W with inner := fun x y => ⟪(x : E), (y : E)⟫, conj_sym := fun _ _ => inner_conj_sym _ _,
    norm_sq_eq_inner := fun _ => norm_sq_eq_inner _, add_left := fun _ _ _ => inner_add_left,
    smul_left := fun _ _ _ => inner_smul_left }

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp]
theorem Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), ↑y⟫ :=
  rfl

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/


section OrthogonalFamily

variable {ι : Type _} [dec_ι : DecidableEq ι] (𝕜)

open DirectSum

/-- An indexed family of mutually-orthogonal subspaces of an inner product space `E`.

The simple way to express this concept would be as a condition on `V : ι → submodule 𝕜 E`.  We
We instead implement it as a condition on a family of inner product spaces each equipped with an
isometric embedding into `E`, thus making it a property of morphisms rather than subobjects.

This definition is less lightweight, but allows for better definitional properties when the inner
product space structure on each of the submodules is important -- for example, when considering
their Hilbert sum (`pi_lp V 2`).  For example, given an orthonormal set of vectors `v : ι → E`,
we have an associated orthogonal family of one-dimensional subspaces of `E`, which it is convenient
to be able to discuss using `ι → 𝕜` rather than `Π i : ι, span 𝕜 (v i)`. -/
def OrthogonalFamily {G : ι → Type _} [∀ i, InnerProductSpace 𝕜 (G i)] (V : ∀ i, G i →ₗᵢ[𝕜] E) : Prop :=
  ∀ ⦃i j⦄, i ≠ j → ∀ v : G i, ∀ w : G j, ⟪V i v, V j w⟫ = 0

variable {𝕜} {G : ι → Type _} [∀ i, InnerProductSpace 𝕜 (G i)] {V : ∀ i, G i →ₗᵢ[𝕜] E} (hV : OrthogonalFamily 𝕜 V)
  [dec_V : ∀ (i) (x : G i), Decidable (x ≠ 0)]

theorem Orthonormal.orthogonal_family {v : ι → E} (hv : Orthonormal 𝕜 v) :
    @OrthogonalFamily 𝕜 _ _ _ _ (fun i : ι => 𝕜) _ fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  fun i j hij a b => by
  simp [← inner_smul_left, ← inner_smul_right, ← hv.2 hij]

include hV dec_ι

theorem OrthogonalFamily.eq_ite {i j : ι} (v : G i) (w : G j) : ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 := by
  split_ifs
  · rfl
    
  · exact hV h v w
    

include dec_V

theorem OrthogonalFamily.inner_right_dfinsupp (l : ⨁ i, G i) (i : ι) (v : G i) :
    ⟪V i v, l.Sum fun j => V j⟫ = ⟪v, l i⟫ :=
  calc
    ⟪V i v, l.Sum fun j => V j⟫ = l.Sum fun j => fun w => ⟪V i v, V j w⟫ := Dfinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.Sum fun j => fun w => ite (i = j) ⟪V i v, V j w⟫ 0 := congr_arg l.Sum <| funext fun j => funext <| hV.eq_ite v
    _ = ⟪v, l i⟫ := by
      simp only [← Dfinsupp.sum, ← Submodule.coe_inner, ← Finset.sum_ite_eq, ← ite_eq_left_iff, ←
        Dfinsupp.mem_support_to_fun]
      split_ifs with h h
      · simp
        
      · simp [← of_not_not h]
        
    

omit dec_ι dec_V

theorem OrthogonalFamily.inner_right_fintype [Fintype ι] (l : ∀ i, G i) (i : ι) (v : G i) :
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ := by
  classical <;>
    calc ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by
        rw [inner_sum]_ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
        congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j)_ = ⟪v, l i⟫ := by
        simp

theorem OrthogonalFamily.inner_sum (l₁ l₂ : ∀ i, G i) (s : Finset ι) :
    ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫ = ∑ i in s, ⟪l₁ i, l₂ i⟫ := by
  classical <;>
    calc ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫ = ∑ j in s, ∑ i in s, ⟪V i (l₁ i), V j (l₂ j)⟫ := by
        simp [← sum_inner, ← inner_sum]_ = ∑ j in s, ∑ i in s, ite (i = j) ⟪V i (l₁ i), V j (l₂ j)⟫ 0 := by
        congr with i
        congr with j
        apply hV.eq_ite _ = ∑ i in s, ⟪l₁ i, l₂ i⟫ := by
        simp [← Finset.sum_ite_of_true]

theorem OrthogonalFamily.norm_sum (l : ∀ i, G i) (s : Finset ι) : ∥∑ i in s, V i (l i)∥ ^ 2 = ∑ i in s, ∥l i∥ ^ 2 := by
  have : (∥∑ i in s, V i (l i)∥ ^ 2 : 𝕜) = ∑ i in s, ∥l i∥ ^ 2 := by
    simp [inner_self_eq_norm_sq_to_K, ← hV.inner_sum]
  exact_mod_cast this

/-- The composition of an orthogonal family of subspaces with an injective function is also an
orthogonal family. -/
theorem OrthogonalFamily.comp {γ : Type _} {f : γ → ι} (hf : Function.Injective f) :
    OrthogonalFamily 𝕜 fun g : γ => (V (f g) : G (f g) →ₗᵢ[𝕜] E) := fun i j hij v w => hV (hf.Ne hij) v w

theorem OrthogonalFamily.orthonormal_sigma_orthonormal {α : ι → Type _} {v_family : ∀ i, α i → G i}
    (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) : Orthonormal 𝕜 fun a : Σi, α i => V a.1 (v_family a.1 a.2) := by
  constructor
  · rintro ⟨i, v⟩
    simpa using (hv_family i).1 v
    
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases' hij : i = j
  · subst hij
    have : v ≠ w := by
      simpa using hvw
    simpa using (hv_family i).2 this
    
  · exact hV hij (v_family i v) (v_family j w)
    

include dec_ι

theorem OrthogonalFamily.norm_sq_diff_sum (f : ∀ i, G i) (s₁ s₂ : Finset ι) :
    ∥(∑ i in s₁, V i (f i)) - ∑ i in s₂, V i (f i)∥ ^ 2 = (∑ i in s₁ \ s₂, ∥f i∥ ^ 2) + ∑ i in s₂ \ s₁, ∥f i∥ ^ 2 := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  let F : ∀ i, G i := fun i => if i ∈ s₁ then f i else -f i
  have hF₁ : ∀, ∀ i ∈ s₁ \ s₂, ∀, F i = f i := fun i hi => if_pos (Finset.sdiff_subset _ _ hi)
  have hF₂ : ∀, ∀ i ∈ s₂ \ s₁, ∀, F i = -f i := fun i hi => if_neg (finset.mem_sdiff.mp hi).2
  have hF : ∀ i, ∥F i∥ = ∥f i∥ := by
    intro i
    dsimp' [← F]
    split_ifs <;> simp
  have :
    ∥(∑ i in s₁ \ s₂, V i (F i)) + ∑ i in s₂ \ s₁, V i (F i)∥ ^ 2 =
      (∑ i in s₁ \ s₂, ∥F i∥ ^ 2) + ∑ i in s₂ \ s₁, ∥F i∥ ^ 2 :=
    by
    have hs : Disjoint (s₁ \ s₂) (s₂ \ s₁) := disjoint_sdiff_sdiff
    simpa only [← Finset.sum_union hs] using hV.norm_sum F (s₁ \ s₂ ∪ s₂ \ s₁)
  convert this using 4
  · refine' Finset.sum_congr rfl fun i hi => _
    simp [← hF₁ i hi]
    
  · refine' Finset.sum_congr rfl fun i hi => _
    simp [← hF₂ i hi]
    
  · simp [← hF]
    
  · simp [← hF]
    

omit dec_ι

/-- A family `f` of mutually-orthogonal elements of `E` is summable, if and only if
`(λ i, ∥f i∥ ^ 2)` is summable. -/
theorem OrthogonalFamily.summable_iff_norm_sq_summable [CompleteSpace E] (f : ∀ i, G i) :
    (Summable fun i => V i (f i)) ↔ Summable fun i => ∥f i∥ ^ 2 := by
  classical
  simp only [← summable_iff_cauchy_seq_finset, ← NormedGroup.cauchy_seq_iff, ← Real.norm_eq_abs]
  constructor
  · intro hf ε hε
    obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
    use a
    intro s₁ hs₁ s₂ hs₂
    rw [← Finset.sum_sdiff_sub_sum_sdiff]
    refine' (_root_.abs_sub _ _).trans_lt _
    have : ∀ i, 0 ≤ ∥f i∥ ^ 2 := fun i : ι => sq_nonneg _
    simp only [← Finset.abs_sum_of_nonneg' this]
    have : ((∑ i in s₁ \ s₂, ∥f i∥ ^ 2) + ∑ i in s₂ \ s₁, ∥f i∥ ^ 2) < sqrt ε ^ 2 := by
      rw [← hV.norm_sq_diff_sum, sq_lt_sq, _root_.abs_of_nonneg (sqrt_nonneg _), _root_.abs_of_nonneg (norm_nonneg _)]
      exact H s₁ hs₁ s₂ hs₂
    have hη := sq_sqrt (le_of_ltₓ hε)
    linarith
    
  · intro hf ε hε
    have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε)
    obtain ⟨a, H⟩ := hf _ hε'
    use a
    intro s₁ hs₁ s₂ hs₂
    refine' (abs_lt_of_sq_lt_sq' _ (le_of_ltₓ hε)).2
    have has : a ≤ s₁⊓s₂ := le_inf hs₁ hs₂
    rw [hV.norm_sq_diff_sum]
    have Hs₁ : (∑ x : ι in s₁ \ s₂, ∥f x∥ ^ 2) < ε ^ 2 / 2 := by
      convert H _ hs₁ _ has
      have : s₁⊓s₂ ⊆ s₁ := Finset.inter_subset_left _ _
      rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
      · simp
        
      · exact fun i => sq_nonneg _
        
    have Hs₂ : (∑ x : ι in s₂ \ s₁, ∥f x∥ ^ 2) < ε ^ 2 / 2 := by
      convert H _ hs₂ _ has
      have : s₁⊓s₂ ⊆ s₂ := Finset.inter_subset_right _ _
      rw [← Finset.sum_sdiff this, add_tsub_cancel_right, Finset.abs_sum_of_nonneg']
      · simp
        
      · exact fun i => sq_nonneg _
        
    linarith
    

omit hV

/-- An orthogonal family forms an independent family of subspaces; that is, any collection of
elements each from a different subspace in the family is linearly independent. In particular, the
pairwise intersections of elements of the family are 0. -/
theorem OrthogonalFamily.independent {V : ι → Submodule 𝕜 E}
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ) : CompleteLattice.Independent V := by
  classical
  apply CompleteLattice.independent_of_dfinsupp_lsum_injective
  rw [← @LinearMap.ker_eq_bot _ _ _ _ _ _ (DirectSum.addCommGroup fun i => V i), Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  ext i
  suffices ⟪(v i : E), v i⟫ = 0 by
    simpa using this
  calc ⟪(v i : E), v i⟫ = ⟪(v i : E), Dfinsupp.lsum ℕ (fun i => (V i).Subtype) v⟫ := by
      simpa [← Dfinsupp.sum_add_hom_apply, ← Submodule.coe_subtype] using
        (hV.inner_right_dfinsupp v i (v i)).symm _ = 0 :=
      by
      simp [← hv]

include dec_ι

theorem DirectSum.IsInternal.collected_basis_orthonormal {V : ι → Submodule 𝕜 E}
    (hV : @OrthogonalFamily 𝕜 _ _ _ _ (fun i => V i) _ fun i => (V i).subtypeₗᵢ)
    (hV_sum : DirectSum.IsInternal fun i => V i) {α : ι → Type _} {v_family : ∀ i, Basis (α i) 𝕜 (V i)}
    (hv_family : ∀ i, Orthonormal 𝕜 (v_family i)) : Orthonormal 𝕜 (hV_sum.collectedBasis v_family) := by
  simpa using hV.orthonormal_sigma_orthonormal hv_family

end OrthogonalFamily

section IsROrCToReal

variable {G : Type _}

variable (𝕜 E)

include 𝕜

/-- A general inner product implies a real inner product. This is not registered as an instance
since it creates problems with the case `𝕜 = ℝ`. -/
def HasInner.isROrCToReal : HasInner ℝ E where inner := fun x y => re ⟪x, y⟫

/-- A general inner product space structure implies a real inner product structure. This is not
registered as an instance since it creates problems with the case `𝕜 = ℝ`, but in can be used in a
proof to obtain a real inner product space structure from a given `𝕜`-inner product space
structure. -/
def InnerProductSpace.isROrCToReal : InnerProductSpace ℝ E :=
  { HasInner.isROrCToReal 𝕜 E, NormedSpace.restrictScalars ℝ 𝕜 E with norm_sq_eq_inner := norm_sq_eq_inner,
    conj_sym := fun x y => inner_re_symm,
    add_left := fun x y z => by
      change re ⟪x + y, z⟫ = re ⟪x, z⟫ + re ⟪y, z⟫
      simp [← inner_add_left],
    smul_left := fun x y r => by
      change re ⟪(r : 𝕜) • x, y⟫ = r * re ⟪x, y⟫
      simp [← inner_smul_left] }

variable {E}

theorem real_inner_eq_re_inner (x y : E) : @HasInner.inner ℝ E (HasInner.isROrCToReal 𝕜 E) x y = re ⟪x, y⟫ :=
  rfl

theorem real_inner_I_smul_self (x : E) : @HasInner.inner ℝ E (HasInner.isROrCToReal 𝕜 E) x ((i : 𝕜) • x) = 0 := by
  simp [← real_inner_eq_re_inner, ← inner_smul_right]

omit 𝕜

/-- A complex inner product implies a real inner product -/
instance InnerProductSpace.complexToReal [InnerProductSpace ℂ G] : InnerProductSpace ℝ G :=
  InnerProductSpace.isROrCToReal ℂ G

end IsROrCToReal

section Continuous

/-!
### Continuity of the inner product
-/


theorem continuous_inner : Continuous fun p : E × E => ⟪p.1, p.2⟫ := by
  let this : InnerProductSpace ℝ E := InnerProductSpace.isROrCToReal 𝕜 E
  exact is_bounded_bilinear_map_inner.continuous

variable {α : Type _}

theorem Filter.Tendsto.inner {f g : α → E} {l : Filter α} {x y : E} (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun t => ⟪f t, g t⟫) l (𝓝 ⟪x, y⟫) :=
  (continuous_inner.Tendsto _).comp (hf.prod_mk_nhds hg)

variable [TopologicalSpace α] {f g : α → E} {x : α} {s : Set α}

include 𝕜

theorem ContinuousWithinAt.inner (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun t => ⟪f t, g t⟫) s x :=
  hf.inner hg

theorem ContinuousAt.inner (hf : ContinuousAt f x) (hg : ContinuousAt g x) : ContinuousAt (fun t => ⟪f t, g t⟫) x :=
  hf.inner hg

theorem ContinuousOn.inner (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun t => ⟪f t, g t⟫) s :=
  fun x hx => (hf x hx).inner (hg x hx)

theorem Continuous.inner (hf : Continuous f) (hg : Continuous g) : Continuous fun t => ⟪f t, g t⟫ :=
  continuous_iff_continuous_at.2 fun x => hf.ContinuousAt.inner hg.ContinuousAt

end Continuous

section ReApplyInnerSelf

/-- Extract a real bilinear form from an operator `T`, by taking the pairing `λ x, re ⟪T x, x⟫`. -/
def ContinuousLinearMap.reApplyInnerSelf (T : E →L[𝕜] E) (x : E) : ℝ :=
  re ⟪T x, x⟫

theorem ContinuousLinearMap.re_apply_inner_self_apply (T : E →L[𝕜] E) (x : E) : T.reApplyInnerSelf x = re ⟪T x, x⟫ :=
  rfl

theorem ContinuousLinearMap.re_apply_inner_self_continuous (T : E →L[𝕜] E) : Continuous T.reApplyInnerSelf :=
  reClm.Continuous.comp <| T.Continuous.inner continuous_id

theorem ContinuousLinearMap.re_apply_inner_self_smul (T : E →L[𝕜] E) (x : E) {c : 𝕜} :
    T.reApplyInnerSelf (c • x) = ∥c∥ ^ 2 * T.reApplyInnerSelf x := by
  simp only [← ContinuousLinearMap.map_smul, ← ContinuousLinearMap.re_apply_inner_self_apply, ← inner_smul_left, ←
    inner_smul_right, mul_assoc, ← mul_conj, ← norm_sq_eq_def', smul_re, ← Algebra.smul_def (∥c∥ ^ 2) ⟪T x, x⟫, ←
    algebra_map_eq_of_real]

end ReApplyInnerSelf

/-! ### The orthogonal complement -/


section Orthogonal

variable (K : Submodule 𝕜 E)

/-- The subspace of vectors orthogonal to a given subspace. -/
def Submodule.orthogonal : Submodule 𝕜 E where
  Carrier := { v | ∀, ∀ u ∈ K, ∀, ⟪u, v⟫ = 0 }
  zero_mem' := fun _ _ => inner_zero_right
  add_mem' := fun x y hx hy u hu => by
    rw [inner_add_right, hx u hu, hy u hu, add_zeroₓ]
  smul_mem' := fun c x hx u hu => by
    rw [inner_smul_right, hx u hu, mul_zero]

-- mathport name: «expr ᗮ»
notation:1200 K "ᗮ" => Submodule.orthogonal K

/-- When a vector is in `Kᗮ`. -/
theorem Submodule.mem_orthogonal (v : E) : v ∈ Kᗮ ↔ ∀, ∀ u ∈ K, ∀, ⟪u, v⟫ = 0 :=
  Iff.rfl

/-- When a vector is in `Kᗮ`, with the inner product the
other way round. -/
theorem Submodule.mem_orthogonal' (v : E) : v ∈ Kᗮ ↔ ∀, ∀ u ∈ K, ∀, ⟪v, u⟫ = 0 := by
  simp_rw [Submodule.mem_orthogonal, inner_eq_zero_sym]

variable {K}

/-- A vector in `K` is orthogonal to one in `Kᗮ`. -/
theorem Submodule.inner_right_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪u, v⟫ = 0 :=
  (K.mem_orthogonal v).1 hv u hu

/-- A vector in `Kᗮ` is orthogonal to one in `K`. -/
theorem Submodule.inner_left_of_mem_orthogonal {u v : E} (hu : u ∈ K) (hv : v ∈ Kᗮ) : ⟪v, u⟫ = 0 := by
  rw [inner_eq_zero_sym] <;> exact Submodule.inner_right_of_mem_orthogonal hu hv

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem inner_right_of_mem_orthogonal_singleton (u : E) {v : E} (hv : v ∈ (𝕜∙u)ᗮ) : ⟪u, v⟫ = 0 :=
  Submodule.inner_right_of_mem_orthogonal (Submodule.mem_span_singleton_self u) hv

/-- A vector in `(𝕜 ∙ u)ᗮ` is orthogonal to `u`. -/
theorem inner_left_of_mem_orthogonal_singleton (u : E) {v : E} (hv : v ∈ (𝕜∙u)ᗮ) : ⟪v, u⟫ = 0 :=
  Submodule.inner_left_of_mem_orthogonal (Submodule.mem_span_singleton_self u) hv

/-- A vector orthogonal to `u` lies in `(𝕜 ∙ u)ᗮ`. -/
theorem mem_orthogonal_singleton_of_inner_right (u : E) {v : E} (hv : ⟪u, v⟫ = 0) : v ∈ (𝕜∙u)ᗮ := by
  intro w hw
  rw [Submodule.mem_span_singleton] at hw
  obtain ⟨c, rfl⟩ := hw
  simp [← inner_smul_left, ← hv]

/-- A vector orthogonal to `u` lies in `(𝕜 ∙ u)ᗮ`. -/
theorem mem_orthogonal_singleton_of_inner_left (u : E) {v : E} (hv : ⟪v, u⟫ = 0) : v ∈ (𝕜∙u)ᗮ :=
  mem_orthogonal_singleton_of_inner_right u <| inner_eq_zero_sym.2 hv

variable (K)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem Submodule.inf_orthogonal_eq_bot : K⊓Kᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x
  rw [Submodule.mem_inf]
  exact fun ⟨hx, ho⟩ => inner_self_eq_zero.1 (ho x hx)

/-- `K` and `Kᗮ` have trivial intersection. -/
theorem Submodule.orthogonal_disjoint : Disjoint K Kᗮ := by
  simp [← disjoint_iff, ← K.inf_orthogonal_eq_bot]

/-- `Kᗮ` can be characterized as the intersection of the kernels of the operations of
inner product with each of the elements of `K`. -/
theorem orthogonal_eq_inter : Kᗮ = ⨅ v : K, (innerSL (v : E)).ker := by
  apply le_antisymmₓ
  · rw [le_infi_iff]
    rintro ⟨v, hv⟩ w hw
    simpa using hw _ hv
    
  · intro v hv w hw
    simp only [← Submodule.mem_infi] at hv
    exact hv ⟨w, hw⟩
    

/-- The orthogonal complement of any submodule `K` is closed. -/
theorem Submodule.is_closed_orthogonal : IsClosed (Kᗮ : Set E) := by
  rw [orthogonal_eq_inter K]
  convert is_closed_Inter fun v : K => (innerSL (v : E)).is_closed_ker
  simp

/-- In a complete space, the orthogonal complement of any submodule `K` is complete. -/
instance [CompleteSpace E] : CompleteSpace Kᗮ :=
  K.is_closed_orthogonal.complete_space_coe

variable (𝕜 E)

/-- `submodule.orthogonal` gives a `galois_connection` between
`submodule 𝕜 E` and its `order_dual`. -/
theorem Submodule.orthogonal_gc :
    @GaloisConnection (Submodule 𝕜 E) (Submodule 𝕜 E)ᵒᵈ _ _ Submodule.orthogonal Submodule.orthogonal := fun K₁ K₂ =>
  ⟨fun h v hv u hu => Submodule.inner_left_of_mem_orthogonal hv (h hu), fun h v hv u hu =>
    Submodule.inner_left_of_mem_orthogonal hv (h hu)⟩

variable {𝕜 E}

/-- `submodule.orthogonal` reverses the `≤` ordering of two
subspaces. -/
theorem Submodule.orthogonal_le {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₂ᗮ ≤ K₁ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).monotone_l h

/-- `submodule.orthogonal.orthogonal` preserves the `≤` ordering of two
subspaces. -/
theorem Submodule.orthogonal_orthogonal_monotone {K₁ K₂ : Submodule 𝕜 E} (h : K₁ ≤ K₂) : K₁ᗮᗮ ≤ K₂ᗮᗮ :=
  Submodule.orthogonal_le (Submodule.orthogonal_le h)

/-- `K` is contained in `Kᗮᗮ`. -/
theorem Submodule.le_orthogonal_orthogonal : K ≤ Kᗮᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).le_u_l _

/-- The inf of two orthogonal subspaces equals the subspace orthogonal
to the sup. -/
theorem Submodule.inf_orthogonal (K₁ K₂ : Submodule 𝕜 E) : K₁ᗮ⊓K₂ᗮ = (K₁⊔K₂)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_sup.symm

/-- The inf of an indexed family of orthogonal subspaces equals the
subspace orthogonal to the sup. -/
theorem Submodule.infi_orthogonal {ι : Type _} (K : ι → Submodule 𝕜 E) : (⨅ i, (K i)ᗮ) = (supr K)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_supr.symm

/-- The inf of a set of orthogonal subspaces equals the subspace orthogonal to the sup. -/
theorem Submodule.Inf_orthogonal (s : Set <| Submodule 𝕜 E) : (⨅ K ∈ s, Kᗮ) = (sup s)ᗮ :=
  (Submodule.orthogonal_gc 𝕜 E).l_Sup.symm

@[simp]
theorem Submodule.top_orthogonal_eq_bot : (⊤ : Submodule 𝕜 E)ᗮ = ⊥ := by
  ext
  rw [Submodule.mem_bot, Submodule.mem_orthogonal]
  exact
    ⟨fun h => inner_self_eq_zero.mp (h x Submodule.mem_top), by
      rintro rfl
      simp ⟩

@[simp]
theorem Submodule.bot_orthogonal_eq_top : (⊥ : Submodule 𝕜 E)ᗮ = ⊤ := by
  rw [← Submodule.top_orthogonal_eq_bot, eq_top_iff]
  exact Submodule.le_orthogonal_orthogonal ⊤

@[simp]
theorem Submodule.orthogonal_eq_top_iff : Kᗮ = ⊤ ↔ K = ⊥ := by
  refine'
    ⟨_, by
      rintro rfl
      exact Submodule.bot_orthogonal_eq_top⟩
  intro h
  have : K⊓Kᗮ = ⊥ := K.orthogonal_disjoint.eq_bot
  rwa [h, inf_comm, top_inf_eq] at this

end Orthogonal

