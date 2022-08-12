/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Analysis.NormedSpace.Multilinear

/-!
# Formal multilinear series

In this file we define `formal_multilinear_series 𝕜 E F` to be a family of `n`-multilinear maps for
all `n`, designed to model the sequence of derivatives of a function. In other files we use this
notion to define `C^n` functions (called `cont_diff` in `mathlib`) and analytic functions.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

## Tags

multilinear, formal series
-/


noncomputable section

open Set Finₓ

open TopologicalSpace

variable {𝕜 𝕜' E F G : Type _}

section

variable [CommRingₓ 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [HasContinuousConstSmul 𝕜 E] [AddCommGroupₓ F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
  [HasContinuousConstSmul 𝕜 F] [AddCommGroupₓ G] [Module 𝕜 G] [TopologicalSpace G] [TopologicalAddGroup G]
  [HasContinuousConstSmul 𝕜 G]

/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[nolint unused_arguments]
def FormalMultilinearSeries (𝕜 : Type _) (E : Type _) (F : Type _) [Ringₓ 𝕜] [AddCommGroupₓ E] [Module 𝕜 E]
    [TopologicalSpace E] [TopologicalAddGroup E] [HasContinuousConstSmul 𝕜 E] [AddCommGroupₓ F] [Module 𝕜 F]
    [TopologicalSpace F] [TopologicalAddGroup F] [HasContinuousConstSmul 𝕜 F] :=
  ∀ n : ℕ, E[×n]→L[𝕜] F deriving AddCommGroupₓ

instance : Inhabited (FormalMultilinearSeries 𝕜 E F) :=
  ⟨0⟩

section Module

/- `derive` is not able to find the module structure, probably because Lean is confused by the
dependent types. We register it explicitly. -/
instance : Module 𝕜 (FormalMultilinearSeries 𝕜 E F) := by
  let this : ∀ n, Module 𝕜 (ContinuousMultilinearMap 𝕜 (fun i : Finₓ n => E) F) := fun n => by
    infer_instance
  refine' Pi.module _ _ _

end Module

namespace FormalMultilinearSeries

/-- Killing the zeroth coefficient in a formal multilinear series -/
def removeZero (p : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E F
  | 0 => 0
  | n + 1 => p (n + 1)

@[simp]
theorem remove_zero_coeff_zero (p : FormalMultilinearSeries 𝕜 E F) : p.removeZero 0 = 0 :=
  rfl

@[simp]
theorem remove_zero_coeff_succ (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) : p.removeZero (n + 1) = p (n + 1) :=
  rfl

theorem remove_zero_of_pos (p : FormalMultilinearSeries 𝕜 E F) {n : ℕ} (h : 0 < n) : p.removeZero n = p n := by
  rw [← Nat.succ_pred_eq_of_posₓ h]
  rfl

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
theorem congr (p : FormalMultilinearSeries 𝕜 E F) {m n : ℕ} {v : Finₓ m → E} {w : Finₓ n → E} (h1 : m = n)
    (h2 : ∀ (i : ℕ) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) : p m v = p n w := by
  cases h1
  congr with ⟨i, hi⟩
  exact h2 i hi hi

/-- Composing each term `pₙ` in a formal multilinear series with `(u, ..., u)` where `u` is a fixed
continuous linear map, gives a new formal multilinear series `p.comp_continuous_linear_map u`. -/
def compContinuousLinearMap (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) : FormalMultilinearSeries 𝕜 E G :=
  fun n => (p n).compContinuousLinearMap fun i : Finₓ n => u

@[simp]
theorem comp_continuous_linear_map_apply (p : FormalMultilinearSeries 𝕜 F G) (u : E →L[𝕜] F) (n : ℕ) (v : Finₓ n → E) :
    (p.compContinuousLinearMap u) n v = p n (u ∘ v) :=
  rfl

variable (𝕜) [CommRingₓ 𝕜'] [HasSmul 𝕜 𝕜']

variable [Module 𝕜' E] [HasContinuousConstSmul 𝕜' E] [IsScalarTower 𝕜 𝕜' E]

variable [Module 𝕜' F] [HasContinuousConstSmul 𝕜' F] [IsScalarTower 𝕜 𝕜' F]

/-- Reinterpret a formal `𝕜'`-multilinear series as a formal `𝕜`-multilinear series. -/
@[simp]
protected def restrictScalars (p : FormalMultilinearSeries 𝕜' E F) : FormalMultilinearSeries 𝕜 E F := fun n =>
  (p n).restrictScalars 𝕜

end FormalMultilinearSeries

end

namespace FormalMultilinearSeries

variable [NondiscreteNormedField 𝕜] [NormedGroup E] [NormedSpace 𝕜 E] [NormedGroup F] [NormedSpace 𝕜 F] [NormedGroup G]
  [NormedSpace 𝕜 G]

variable (p : FormalMultilinearSeries 𝕜 E F)

/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E →L[𝕜] F`. If `p` corresponds to the Taylor series of a function, then
`p.shift` is the Taylor series of the derivative of the function. -/
def shift : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F) := fun n => (p n.succ).curryRight

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series for the derivative of a function, and building a Taylor
series for the function itself. -/
def unshift (q : FormalMultilinearSeries 𝕜 E (E →L[𝕜] F)) (z : F) : FormalMultilinearSeries 𝕜 E F
  | 0 => (continuousMultilinearCurryFin0 𝕜 E F).symm z
  | n + 1 => continuousMultilinearCurryRightEquiv' 𝕜 n E F (q n)

end FormalMultilinearSeries

namespace ContinuousLinearMap

variable [CommRingₓ 𝕜] [AddCommGroupₓ E] [Module 𝕜 E] [TopologicalSpace E] [TopologicalAddGroup E]
  [HasContinuousConstSmul 𝕜 E] [AddCommGroupₓ F] [Module 𝕜 F] [TopologicalSpace F] [TopologicalAddGroup F]
  [HasContinuousConstSmul 𝕜 F] [AddCommGroupₓ G] [Module 𝕜 G] [TopologicalSpace G] [TopologicalAddGroup G]
  [HasContinuousConstSmul 𝕜 G]

/-- Composing each term `pₙ` in a formal multilinear series with a continuous linear map `f` on the
left gives a new formal multilinear series `f.comp_formal_multilinear_series p` whose general term
is `f ∘ pₙ`. -/
def compFormalMultilinearSeries (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) : FormalMultilinearSeries 𝕜 E G :=
  fun n => f.compContinuousMultilinearMap (p n)

@[simp]
theorem comp_formal_multilinear_series_apply (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ) :
    (f.compFormalMultilinearSeries p) n = f.compContinuousMultilinearMap (p n) :=
  rfl

theorem comp_formal_multilinear_series_apply' (f : F →L[𝕜] G) (p : FormalMultilinearSeries 𝕜 E F) (n : ℕ)
    (v : Finₓ n → E) : (f.compFormalMultilinearSeries p) n v = f (p n v) :=
  rfl

end ContinuousLinearMap

