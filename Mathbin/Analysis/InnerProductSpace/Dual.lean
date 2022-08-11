/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathbin.Analysis.InnerProductSpace.Projection
import Mathbin.Analysis.NormedSpace.Dual
import Mathbin.Analysis.NormedSpace.Star.Basic

/-!
# The Fréchet-Riesz representation theorem

We consider an inner product space `E` over `𝕜`, which is either `ℝ` or `ℂ`. We define
`to_dual_map`, a conjugate-linear isometric embedding of `E` into its dual, which maps an element
`x` of the space to `λ y, ⟪x, y⟫`.

Under the hypothesis of completeness (i.e., for Hilbert spaces), we upgrade this to `to_dual`, a
conjugate-linear isometric *equivalence* of `E` onto its dual; that is, we establish the
surjectivity of `to_dual_map`.  This is the Fréchet-Riesz representation theorem: every element of
the dual of a Hilbert space `E` has the form `λ u, ⟪x, u⟫` for some `x : E`.

For a bounded sesquilinear form `B : E →L⋆[𝕜] E →L[𝕜] 𝕜`,
we define a map `inner_product_space.continuous_linear_map_of_bilin B : E →L[𝕜] E`,
given by substituting `E →L[𝕜] 𝕜` with `E` using `to_dual`.


## References

* [M. Einsiedler and T. Ward, *Functional Analysis, Spectral Theory, and Applications*]
  [EinsiedlerWard2017]

## Tags

dual, Fréchet-Riesz
-/


noncomputable section

open Classical ComplexConjugate

universe u v

namespace InnerProductSpace

open IsROrC ContinuousLinearMap

variable (𝕜 : Type _)

variable (E : Type _) [IsROrC 𝕜] [InnerProductSpace 𝕜 E]

-- mathport name: «expr⟪ , ⟫»
local notation "⟪" x ", " y "⟫" => @inner 𝕜 E _ x y

-- mathport name: «expr †»
local postfix:90 "†" => starRingEnd _

/-- An element `x` of an inner product space `E` induces an element of the dual space `dual 𝕜 E`,
the map `λ y, ⟪x, y⟫`; moreover this operation is a conjugate-linear isometric embedding of `E`
into `dual 𝕜 E`.
If `E` is complete, this operation is surjective, hence a conjugate-linear isometric equivalence;
see `to_dual`.
-/
def toDualMap : E →ₗᵢ⋆[𝕜] NormedSpace.Dual 𝕜 E :=
  { innerSL with norm_map' := fun _ => innerSL_apply_norm }

variable {E}

@[simp]
theorem to_dual_map_apply {x y : E} : toDualMap 𝕜 E x y = ⟪x, y⟫ :=
  rfl

theorem innerSL_norm [Nontrivial E] : ∥(innerSL : E →L⋆[𝕜] E →L[𝕜] 𝕜)∥ = 1 :=
  show ∥(toDualMap 𝕜 E).toContinuousLinearMap∥ = 1 from LinearIsometry.norm_to_continuous_linear_map _

variable (𝕜)

include 𝕜

theorem ext_inner_left {x y : E} (h : ∀ v, ⟪v, x⟫ = ⟪v, y⟫) : x = y := by
  apply (to_dual_map 𝕜 E).map_eq_iff.mp
  ext v
  rw [to_dual_map_apply, to_dual_map_apply, ← inner_conj_sym]
  nth_rw_rhs 0[← inner_conj_sym]
  exact congr_arg conj (h v)

theorem ext_inner_right {x y : E} (h : ∀ v, ⟪x, v⟫ = ⟪y, v⟫) : x = y := by
  refine' ext_inner_left 𝕜 fun v => _
  rw [← inner_conj_sym]
  nth_rw_rhs 0[← inner_conj_sym]
  exact congr_arg conj (h v)

omit 𝕜

variable {𝕜}

theorem ext_inner_left_basis {ι : Type _} {x y : E} (b : Basis ι 𝕜 E) (h : ∀ i : ι, ⟪b i, x⟫ = ⟪b i, y⟫) : x = y := by
  apply (to_dual_map 𝕜 E).map_eq_iff.mp
  refine' (Function.Injective.eq_iff ContinuousLinearMap.coe_injective).mp (Basis.ext b _)
  intro i
  simp only [← to_dual_map_apply, ← ContinuousLinearMap.coe_coe]
  rw [← inner_conj_sym]
  nth_rw_rhs 0[← inner_conj_sym]
  exact congr_arg conj (h i)

theorem ext_inner_right_basis {ι : Type _} {x y : E} (b : Basis ι 𝕜 E) (h : ∀ i : ι, ⟪x, b i⟫ = ⟪y, b i⟫) : x = y := by
  refine' ext_inner_left_basis b fun i => _
  rw [← inner_conj_sym]
  nth_rw_rhs 0[← inner_conj_sym]
  exact congr_arg conj (h i)

variable (𝕜) (E) [CompleteSpace E]

/-- Fréchet-Riesz representation: any `ℓ` in the dual of a Hilbert space `E` is of the form
`λ u, ⟪y, u⟫` for some `y : E`, i.e. `to_dual_map` is surjective.
-/
def toDual : E ≃ₗᵢ⋆[𝕜] NormedSpace.Dual 𝕜 E :=
  LinearIsometryEquiv.ofSurjective (toDualMap 𝕜 E)
    (by
      intro ℓ
      set Y := ker ℓ with hY
      by_cases' htriv : Y = ⊤
      · have hℓ : ℓ = 0 := by
          have h' := linear_map.ker_eq_top.mp htriv
          rw [← coe_zero] at h'
          apply coe_injective
          exact h'
        exact
          ⟨0, by
            simp [← hℓ]⟩
        
      · rw [← Submodule.orthogonal_eq_bot_iff] at htriv
        change Yᗮ ≠ ⊥ at htriv
        rw [Submodule.ne_bot_iff] at htriv
        obtain ⟨z : E, hz : z ∈ Yᗮ, z_ne_0 : z ≠ 0⟩ := htriv
        refine' ⟨(ℓ z† / ⟪z, z⟫) • z, _⟩
        ext x
        have h₁ : ℓ z • x - ℓ x • z ∈ Y := by
          rw [mem_ker, map_sub, ContinuousLinearMap.map_smul, ContinuousLinearMap.map_smul, Algebra.id.smul_eq_mul,
            Algebra.id.smul_eq_mul, mul_comm]
          exact sub_self (ℓ x * ℓ z)
        have h₂ : ℓ z * ⟪z, x⟫ = ℓ x * ⟪z, z⟫ := by
          have h₃ :=
            calc
              0 = ⟪z, ℓ z • x - ℓ x • z⟫ := by
                rw [(Y.mem_orthogonal' z).mp hz]
                exact h₁
              _ = ⟪z, ℓ z • x⟫ - ⟪z, ℓ x • z⟫ := by
                rw [inner_sub_right]
              _ = ℓ z * ⟪z, x⟫ - ℓ x * ⟪z, z⟫ := by
                simp [← inner_smul_right]
              
          exact sub_eq_zero.mp (Eq.symm h₃)
        have h₄ :=
          calc
            ⟪(ℓ z† / ⟪z, z⟫) • z, x⟫ = ℓ z / ⟪z, z⟫ * ⟪z, x⟫ := by
              simp [← inner_smul_left, ← RingHom.map_div, ← conj_conj]
            _ = ℓ z * ⟪z, x⟫ / ⟪z, z⟫ := by
              rw [← div_mul_eq_mul_div]
            _ = ℓ x * ⟪z, z⟫ / ⟪z, z⟫ := by
              rw [h₂]
            _ = ℓ x := by
              have : ⟪z, z⟫ ≠ 0 := by
                change z = 0 → False at z_ne_0
                rwa [← inner_self_eq_zero] at z_ne_0
              field_simp [← this]
            
        exact h₄
        )

variable {𝕜} {E}

@[simp]
theorem to_dual_apply {x y : E} : toDual 𝕜 E x y = ⟪x, y⟫ :=
  rfl

@[simp]
theorem to_dual_symm_apply {x : E} {y : NormedSpace.Dual 𝕜 E} : ⟪(toDual 𝕜 E).symm y, x⟫ = y x := by
  rw [← to_dual_apply]
  simp only [← LinearIsometryEquiv.apply_symm_apply]

variable {E 𝕜}

/-- Maps a bounded sesquilinear form to its continuous linear map,
given by interpreting the form as a map `B : E →L⋆[𝕜] normed_space.dual 𝕜 E`
and dualizing the result using `to_dual`.
-/
def continuousLinearMapOfBilin (B : E →L⋆[𝕜] E →L[𝕜] 𝕜) : E →L[𝕜] E :=
  comp (toDual 𝕜 E).symm.toContinuousLinearEquiv.toContinuousLinearMap B

-- mathport name: «expr ♯»
local postfix:1024 "♯" => continuousLinearMapOfBilin

variable (B : E →L⋆[𝕜] E →L[𝕜] 𝕜)

@[simp]
theorem continuous_linear_map_of_bilin_apply (v w : E) : ⟪B♯ v, w⟫ = B v w := by
  simp [← continuous_linear_map_of_bilin]

theorem unique_continuous_linear_map_of_bilin {v f : E} (is_lax_milgram : ∀ w, ⟪f, w⟫ = B v w) : f = B♯ v := by
  refine' ext_inner_right 𝕜 _
  intro w
  rw [continuous_linear_map_of_bilin_apply]
  exact is_lax_milgram w

end InnerProductSpace

