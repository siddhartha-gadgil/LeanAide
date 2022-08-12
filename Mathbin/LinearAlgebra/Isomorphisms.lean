/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Kevin Buzzard, Yury Kudryashov
-/
import Mathbin.LinearAlgebra.Quotient

/-!
# Isomorphism theorems for modules.

* The Noether's first, second, and third isomorphism theorems for modules are proved as
  `linear_map.quot_ker_equiv_range`, `linear_map.quotient_inf_equiv_sup_quotient` and
  `submodule.quotient_quotient_equiv_quotient`.

-/


universe u v

variable {R M M₂ M₃ : Type _}

variable [Ringₓ R] [AddCommGroupₓ M] [AddCommGroupₓ M₂] [AddCommGroupₓ M₃]

variable [Module R M] [Module R M₂] [Module R M₃]

variable (f : M →ₗ[R] M₂)

/-! The first and second isomorphism theorems for modules. -/


namespace LinearMap

open Submodule

section IsomorphismLaws

/-- The first isomorphism law for modules. The quotient of `M` by the kernel of `f` is linearly
equivalent to the range of `f`. -/
noncomputable def quotKerEquivRange : (M ⧸ f.ker) ≃ₗ[R] f.range :=
  (LinearEquiv.ofInjective (f.ker.liftq f <| le_rfl) <|
        ker_eq_bot.mp <| Submodule.ker_liftq_eq_bot _ _ _ (le_reflₓ f.ker)).trans
    (LinearEquiv.ofEq _ _ <| Submodule.range_liftq _ _ _)

/-- The first isomorphism theorem for surjective linear maps. -/
noncomputable def quotKerEquivOfSurjective (f : M →ₗ[R] M₂) (hf : Function.Surjective f) : (M ⧸ f.ker) ≃ₗ[R] M₂ :=
  f.quotKerEquivRange.trans (LinearEquiv.ofTop f.range (LinearMap.range_eq_top.2 hf))

@[simp]
theorem quot_ker_equiv_range_apply_mk (x : M) : (f.quotKerEquivRange (Submodule.Quotient.mk x) : M₂) = f x :=
  rfl

@[simp]
theorem quot_ker_equiv_range_symm_apply_image (x : M) (h : f x ∈ f.range) :
    f.quotKerEquivRange.symm ⟨f x, h⟩ = f.ker.mkq x :=
  f.quotKerEquivRange.symm_apply_apply (f.ker.mkq x)

/-- Canonical linear map from the quotient `p/(p ∩ p')` to `(p+p')/p'`, mapping `x + (p ∩ p')`
to `x + p'`, where `p` and `p'` are submodules of an ambient module.
-/
def quotientInfToSupQuotient (p p' : Submodule R M) : p ⧸ comap p.Subtype (p⊓p') →ₗ[R] _ ⧸ comap (p⊔p').Subtype p' :=
  (comap p.Subtype (p⊓p')).liftq ((comap (p⊔p').Subtype p').mkq.comp (ofLe le_sup_left))
    (by
      rw [ker_comp, of_le, comap_cod_restrict, ker_mkq, map_comap_subtype]
      exact comap_mono (inf_le_inf_right _ le_sup_left))

/-- Second Isomorphism Law : the canonical map from `p/(p ∩ p')` to `(p+p')/p'` as a linear isomorphism.
-/
noncomputable def quotientInfEquivSupQuotient (p p' : Submodule R M) :
    (p ⧸ comap p.Subtype (p⊓p')) ≃ₗ[R] _ ⧸ comap (p⊔p').Subtype p' :=
  LinearEquiv.ofBijective (quotientInfToSupQuotient p p')
    (by
      rw [← ker_eq_bot, quotient_inf_to_sup_quotient, ker_liftq_eq_bot]
      rw [ker_comp, ker_mkq]
      exact fun ⟨x, hx1⟩ hx2 => ⟨hx1, hx2⟩)
    (by
      rw [← range_eq_top, quotient_inf_to_sup_quotient, range_liftq, eq_top_iff']
      rintro ⟨x, hx⟩
      rcases mem_sup.1 hx with ⟨y, hy, z, hz, rfl⟩
      use ⟨y, hy⟩
      apply (Submodule.Quotient.eq _).2
      change y - (y + z) ∈ p'
      rwa [sub_add_eq_sub_sub, sub_self, zero_sub, neg_mem_iff])

@[simp]
theorem coe_quotient_inf_to_sup_quotient (p p' : Submodule R M) :
    ⇑(quotientInfToSupQuotient p p') = quotientInfEquivSupQuotient p p' :=
  rfl

@[simp]
theorem quotient_inf_equiv_sup_quotient_apply_mk (p p' : Submodule R M) (x : p) :
    quotientInfEquivSupQuotient p p' (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (ofLe (le_sup_left : p ≤ p⊔p') x) :=
  rfl

theorem quotient_inf_equiv_sup_quotient_symm_apply_left (p p' : Submodule R M) (x : p⊔p') (hx : (x : M) ∈ p) :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) = Submodule.Quotient.mk ⟨x, hx⟩ :=
  (LinearEquiv.symm_apply_eq _).2 <| by
    simp [← of_le_apply]

@[simp]
theorem quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff {p p' : Submodule R M} {x : p⊔p'} :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) = 0 ↔ (x : M) ∈ p' :=
  (LinearEquiv.symm_apply_eq _).trans <| by
    simp [← of_le_apply]

theorem quotient_inf_equiv_sup_quotient_symm_apply_right (p p' : Submodule R M) {x : p⊔p'} (hx : (x : M) ∈ p') :
    (quotientInfEquivSupQuotient p p').symm (Submodule.Quotient.mk x) = 0 :=
  quotient_inf_equiv_sup_quotient_symm_apply_eq_zero_iff.2 hx

end IsomorphismLaws

end LinearMap

/-! The third isomorphism theorem for modules. -/


namespace Submodule

variable (S T : Submodule R M) (h : S ≤ T)

/-- The map from the third isomorphism theorem for modules: `(M / S) / (T / S) → M / T`. -/
def quotientQuotientEquivQuotientAux : (M ⧸ S) ⧸ T.map S.mkq →ₗ[R] M ⧸ T :=
  liftq _ (mapq S T LinearMap.id h)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [LinearMap.mem_ker, mkq_apply, mapq_apply]
      exact (quotient.mk_eq_zero _).mpr hx)

@[simp]
theorem quotient_quotient_equiv_quotient_aux_mk (x : M ⧸ S) :
    quotientQuotientEquivQuotientAux S T h (Quotient.mk x) = mapq S T LinearMap.id h x :=
  liftq_apply _ _ _

@[simp]
theorem quotient_quotient_equiv_quotient_aux_mk_mk (x : M) :
    quotientQuotientEquivQuotientAux S T h (Quotient.mk (Quotient.mk x)) = Quotient.mk x := by
  rw [quotient_quotient_equiv_quotient_aux_mk, mapq_apply, LinearMap.id_apply]

/-- **Noether's third isomorphism theorem** for modules: `(M / S) / (T / S) ≃ M / T`. -/
def quotientQuotientEquivQuotient : ((M ⧸ S) ⧸ T.map S.mkq) ≃ₗ[R] M ⧸ T :=
  { quotientQuotientEquivQuotientAux S T h with toFun := quotientQuotientEquivQuotientAux S T h,
    invFun := mapq _ _ (mkq S) (le_comap_map _ _),
    left_inv := fun x =>
      (Quotientₓ.induction_on' x) fun x =>
        (Quotientₓ.induction_on' x) fun x => by
          simp ,
    right_inv := fun x =>
      (Quotientₓ.induction_on' x) fun x => by
        simp }

end Submodule

