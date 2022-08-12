/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Topology.ContinuousFunction.Compact
import Mathbin.Analysis.NormedSpace.Units
import Mathbin.Algebra.Algebra.Spectrum

/-!
# Units of continuous functions

This file concerns itself with `C(X, M)ˣ` and `C(X, Mˣ)` when `X` is a topological space
and `M` has some monoid structure compatible with its topology.
-/


variable {X M R 𝕜 : Type _} [TopologicalSpace X]

namespace ContinuousMap

section Monoidₓ

variable [Monoidₓ M] [TopologicalSpace M] [HasContinuousMul M]

/-- Equivalence between continuous maps into the units of a monoid with continuous multiplication
and the units of the monoid of continuous maps. -/
@[to_additive
      "Equivalence between continuous maps into the additive units of an additive monoid\nwith continuous addition and the additive units of the additive monoid of continuous maps.",
  simps]
def unitsLift : C(X, Mˣ) ≃ C(X, M)ˣ where
  toFun := fun f =>
    { val := ⟨fun x => f x, Units.continuous_coe.comp f.Continuous⟩,
      inv := ⟨fun x => ↑(f x)⁻¹, Units.continuous_coe.comp (continuous_inv.comp f.Continuous)⟩,
      val_inv := ext fun x => Units.mul_inv _, inv_val := ext fun x => Units.inv_mul _ }
  invFun := fun f =>
    { toFun := fun x => ⟨f x, f⁻¹ x, ContinuousMap.congr_fun f.mul_inv x, ContinuousMap.congr_fun f.inv_mul x⟩,
      continuous_to_fun :=
        continuous_induced_rng <|
          Continuous.prod_mk (f : C(X, M)).Continuous <| MulOpposite.continuous_op.comp (↑f⁻¹ : C(X, M)).Continuous }
  left_inv := fun f => by
    ext
    rfl
  right_inv := fun f => by
    ext
    rfl

end Monoidₓ

section NormedRing

variable [NormedRing R] [CompleteSpace R]

theorem _root_.normed_ring.is_unit_unit_continuous {f : C(X, R)} (h : ∀ x, IsUnit (f x)) :
    Continuous fun x => (h x).Unit := by
  refine'
    continuous_induced_rng
      (Continuous.prod_mk f.continuous (mul_opposite.continuous_op.comp (continuous_iff_continuous_at.mpr fun x => _)))
  have := NormedRing.inverse_continuous_at (h x).Unit
  simp only [Ring.inverse_unit, ← IsUnit.unit_spec, Function.comp_applyₓ] at this⊢
  exact this.comp (f.continuous_at x)

/-- Construct a continuous map into the group of units of a normed ring from a function into the
normed ring and a proof that every element of the range is a unit. -/
@[simps]
noncomputable def unitsOfForallIsUnit {f : C(X, R)} (h : ∀ x, IsUnit (f x)) : C(X, Rˣ) where
  toFun := fun x => (h x).Unit
  continuous_to_fun := NormedRing.is_unit_unit_continuous h

instance : CanLift C(X, R) C(X, Rˣ) where
  coe := fun f => ⟨fun x => f x, Units.continuous_coe.comp f.Continuous⟩
  cond := fun f => ∀ x, IsUnit (f x)
  prf := fun f h =>
    ⟨unitsOfForallIsUnit h, by
      ext
      rfl⟩

theorem is_unit_iff_forall_is_unit (f : C(X, R)) : IsUnit f ↔ ∀ x, IsUnit (f x) :=
  Iff.intro (fun h => fun x => ⟨unitsLift.symm h.Unit x, rfl⟩) fun h =>
    ⟨(unitsOfForallIsUnit h).unitsLift, by
      ext
      rfl⟩

end NormedRing

section NormedField

variable [NormedField 𝕜] [CompleteSpace 𝕜]

theorem is_unit_iff_forall_ne_zero (f : C(X, 𝕜)) : IsUnit f ↔ ∀ x, f x ≠ 0 := by
  simp_rw [f.is_unit_iff_forall_is_unit, is_unit_iff_ne_zero]

theorem spectrum_eq_range (f : C(X, 𝕜)) : Spectrum 𝕜 f = Set.Range f := by
  ext
  simp only [← Spectrum.mem_iff, ← is_unit_iff_forall_ne_zero, ← not_forall, ← coe_sub, ← Pi.sub_apply, ←
    algebra_map_apply, ← Algebra.id.smul_eq_mul, ← mul_oneₓ, ← not_not, ← Set.mem_range, ← sub_eq_zero, ←
    @eq_comm _ x _]

end NormedField

end ContinuousMap

