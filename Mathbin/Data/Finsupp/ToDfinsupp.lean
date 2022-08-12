/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathbin.Algebra.Module.Equiv
import Mathbin.Data.Dfinsupp.Basic
import Mathbin.Data.Finsupp.Basic

/-!
# Conversion between `finsupp` and homogenous `dfinsupp`

This module provides conversions between `finsupp` and `dfinsupp`.
It is in its own file since neither `finsupp` or `dfinsupp` depend on each other.

## Main definitions

* "identity" maps between `finsupp` and `dfinsupp`:
  * `finsupp.to_dfinsupp : (ι →₀ M) → (Π₀ i : ι, M)`
  * `dfinsupp.to_finsupp : (Π₀ i : ι, M) → (ι →₀ M)`
  * Bundled equiv versions of the above:
    * `finsupp_equiv_dfinsupp : (ι →₀ M) ≃ (Π₀ i : ι, M)`
    * `finsupp_add_equiv_dfinsupp : (ι →₀ M) ≃+ (Π₀ i : ι, M)`
    * `finsupp_lequiv_dfinsupp R : (ι →₀ M) ≃ₗ[R] (Π₀ i : ι, M)`
* stronger versions of `finsupp.split`:
  * `sigma_finsupp_equiv_dfinsupp : ((Σ i, η i) →₀ N) ≃ (Π₀ i, (η i →₀ N))`
  * `sigma_finsupp_add_equiv_dfinsupp : ((Σ i, η i) →₀ N) ≃+ (Π₀ i, (η i →₀ N))`
  * `sigma_finsupp_lequiv_dfinsupp : ((Σ i, η i) →₀ N) ≃ₗ[R] (Π₀ i, (η i →₀ N))`

## Theorems

The defining features of these operations is that they preserve the function and support:

* `finsupp.to_dfinsupp_coe`
* `finsupp.to_dfinsupp_support`
* `dfinsupp.to_finsupp_coe`
* `dfinsupp.to_finsupp_support`

and therefore map `finsupp.single` to `dfinsupp.single` and vice versa:

* `finsupp.to_dfinsupp_single`
* `dfinsupp.to_finsupp_single`

as well as preserving arithmetic operations.

For the bundled equivalences, we provide lemmas that they reduce to `finsupp.to_dfinsupp`:

* `finsupp_add_equiv_dfinsupp_apply`
* `finsupp_lequiv_dfinsupp_apply`
* `finsupp_add_equiv_dfinsupp_symm_apply`
* `finsupp_lequiv_dfinsupp_symm_apply`

## Implementation notes

We provide `dfinsupp.to_finsupp` and `finsupp_equiv_dfinsupp` computably by adding
`[decidable_eq ι]` and `[Π m : M, decidable (m ≠ 0)]` arguments. To aid with definitional unfolding,
these arguments are also present on the `noncomputable` equivs.
-/


variable {ι : Type _} {R : Type _} {M : Type _}

/-! ### Basic definitions and lemmas -/


section Defs

/-- Interpret a `finsupp` as a homogenous `dfinsupp`. -/
def Finsupp.toDfinsupp [Zero M] (f : ι →₀ M) : Π₀ i : ι, M :=
  ⟦⟨f, f.support.1, fun i => (Classical.em (f i = 0)).symm.imp_left Finsupp.mem_support_iff.mpr⟩⟧

@[simp]
theorem Finsupp.to_dfinsupp_coe [Zero M] (f : ι →₀ M) : ⇑f.toDfinsupp = f :=
  rfl

section

variable [DecidableEq ι] [Zero M]

@[simp]
theorem Finsupp.to_dfinsupp_single (i : ι) (m : M) : (Finsupp.single i m).toDfinsupp = Dfinsupp.single i m := by
  ext
  simp [← Finsupp.single_apply, ← Dfinsupp.single_apply]

variable [∀ m : M, Decidable (m ≠ 0)]

@[simp]
theorem to_dfinsupp_support (f : ι →₀ M) : f.toDfinsupp.support = f.support := by
  ext
  simp

/-- Interpret a homogenous `dfinsupp` as a `finsupp`.

Note that the elaborator has a lot of trouble with this definition - it is often necessary to
write `(dfinsupp.to_finsupp f : ι →₀ M)` instead of `f.to_finsupp`, as for some unknown reason
using dot notation or omitting the type ascription prevents the type being resolved correctly. -/
def Dfinsupp.toFinsupp (f : Π₀ i : ι, M) : ι →₀ M :=
  ⟨f.support, f, fun i => by
    simp only [← Dfinsupp.mem_support_iff]⟩

@[simp]
theorem Dfinsupp.to_finsupp_coe (f : Π₀ i : ι, M) : ⇑f.toFinsupp = f :=
  rfl

@[simp]
theorem Dfinsupp.to_finsupp_support (f : Π₀ i : ι, M) : f.toFinsupp.support = f.support := by
  ext
  simp

@[simp]
theorem Dfinsupp.to_finsupp_single (i : ι) (m : M) :
    (Dfinsupp.single i m : Π₀ i : ι, M).toFinsupp = Finsupp.single i m := by
  ext
  simp [← Finsupp.single_apply, ← Dfinsupp.single_apply]

@[simp]
theorem Finsupp.to_dfinsupp_to_finsupp (f : ι →₀ M) : f.toDfinsupp.toFinsupp = f :=
  Finsupp.coe_fn_injective rfl

@[simp]
theorem Dfinsupp.to_finsupp_to_dfinsupp (f : Π₀ i : ι, M) : f.toFinsupp.toDfinsupp = f :=
  Dfinsupp.coe_fn_injective rfl

end

end Defs

/-! ### Lemmas about arithmetic operations -/


section Lemmas

namespace Finsupp

@[simp]
theorem to_dfinsupp_zero [Zero M] : (0 : ι →₀ M).toDfinsupp = 0 :=
  Dfinsupp.coe_fn_injective rfl

@[simp]
theorem to_dfinsupp_add [AddZeroClassₓ M] (f g : ι →₀ M) : (f + g).toDfinsupp = f.toDfinsupp + g.toDfinsupp :=
  Dfinsupp.coe_fn_injective rfl

@[simp]
theorem to_dfinsupp_neg [AddGroupₓ M] (f : ι →₀ M) : (-f).toDfinsupp = -f.toDfinsupp :=
  Dfinsupp.coe_fn_injective rfl

@[simp]
theorem to_dfinsupp_sub [AddGroupₓ M] (f g : ι →₀ M) : (f - g).toDfinsupp = f.toDfinsupp - g.toDfinsupp :=
  Dfinsupp.coe_fn_injective rfl

@[simp]
theorem to_dfinsupp_smul [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] (r : R) (f : ι →₀ M) :
    (r • f).toDfinsupp = r • f.toDfinsupp :=
  Dfinsupp.coe_fn_injective rfl

end Finsupp

namespace Dfinsupp

variable [DecidableEq ι]

@[simp]
theorem to_finsupp_zero [Zero M] [∀ m : M, Decidable (m ≠ 0)] : toFinsupp 0 = (0 : ι →₀ M) :=
  Finsupp.coe_fn_injective rfl

@[simp]
theorem to_finsupp_add [AddZeroClassₓ M] [∀ m : M, Decidable (m ≠ 0)] (f g : Π₀ i : ι, M) :
    (toFinsupp (f + g) : ι →₀ M) = toFinsupp f + toFinsupp g :=
  Finsupp.coe_fn_injective <| Dfinsupp.coe_add _ _

@[simp]
theorem to_finsupp_neg [AddGroupₓ M] [∀ m : M, Decidable (m ≠ 0)] (f : Π₀ i : ι, M) :
    (toFinsupp (-f) : ι →₀ M) = -toFinsupp f :=
  Finsupp.coe_fn_injective <| Dfinsupp.coe_neg _

@[simp]
theorem to_finsupp_sub [AddGroupₓ M] [∀ m : M, Decidable (m ≠ 0)] (f g : Π₀ i : ι, M) :
    (toFinsupp (f - g) : ι →₀ M) = toFinsupp f - toFinsupp g :=
  Finsupp.coe_fn_injective <| Dfinsupp.coe_sub _ _

@[simp]
theorem to_finsupp_smul [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] [∀ m : M, Decidable (m ≠ 0)] (r : R)
    (f : Π₀ i : ι, M) : (toFinsupp (r • f) : ι →₀ M) = r • toFinsupp f :=
  Finsupp.coe_fn_injective <| Dfinsupp.coe_smul _ _

end Dfinsupp

end Lemmas

/-! ### Bundled `equiv`s -/


section Equivs

/-- `finsupp.to_dfinsupp` and `dfinsupp.to_finsupp` together form an equiv. -/
@[simps (config := { fullyApplied := false })]
def finsuppEquivDfinsupp [DecidableEq ι] [Zero M] [∀ m : M, Decidable (m ≠ 0)] : (ι →₀ M) ≃ Π₀ i : ι, M where
  toFun := Finsupp.toDfinsupp
  invFun := Dfinsupp.toFinsupp
  left_inv := Finsupp.to_dfinsupp_to_finsupp
  right_inv := Dfinsupp.to_finsupp_to_dfinsupp

/-- The additive version of `finsupp.to_finsupp`. Note that this is `noncomputable` because
`finsupp.has_add` is noncomputable. -/
@[simps (config := { fullyApplied := false })]
def finsuppAddEquivDfinsupp [DecidableEq ι] [AddZeroClassₓ M] [∀ m : M, Decidable (m ≠ 0)] : (ι →₀ M) ≃+ Π₀ i : ι, M :=
  { finsuppEquivDfinsupp with toFun := Finsupp.toDfinsupp, invFun := Dfinsupp.toFinsupp,
    map_add' := Finsupp.to_dfinsupp_add }

variable (R)

/-- The additive version of `finsupp.to_finsupp`. Note that this is `noncomputable` because
`finsupp.has_add` is noncomputable. -/
@[simps (config := { fullyApplied := false })]
def finsuppLequivDfinsupp [DecidableEq ι] [Semiringₓ R] [AddCommMonoidₓ M] [∀ m : M, Decidable (m ≠ 0)] [Module R M] :
    (ι →₀ M) ≃ₗ[R] Π₀ i : ι, M :=
  { finsuppEquivDfinsupp with toFun := Finsupp.toDfinsupp, invFun := Dfinsupp.toFinsupp,
    map_smul' := Finsupp.to_dfinsupp_smul, map_add' := Finsupp.to_dfinsupp_add }

section Sigma

/-! ### Stronger versions of `finsupp.split` -/
noncomputable section

open Classical

variable {η : ι → Type _} {N : Type _} [Semiringₓ R]

open Finsupp

/-- `finsupp.split` is an equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
def sigmaFinsuppEquivDfinsupp [Zero N] : ((Σi, η i) →₀ N) ≃ Π₀ i, η i →₀ N where
  toFun := fun f =>
    ⟦⟨split f, (splitSupport f : Finset ι).val, fun i => by
        rw [← Finset.mem_def, mem_split_support_iff_nonzero]
        exact (Decidable.em _).symm⟩⟧
  invFun := fun f => by
    refine'
      on_finset (Finset.sigma f.support fun j => (f j).support) (fun ji => f ji.1 ji.2) fun g hg =>
        finset.mem_sigma.mpr ⟨_, mem_support_iff.mpr hg⟩
    simp only [← Ne.def, ← Dfinsupp.mem_support_to_fun]
    intro h
    rw [h] at hg
    simpa using hg
  left_inv := fun f => by
    ext
    simp [← split]
  right_inv := fun f => by
    ext
    simp [← split]

@[simp]
theorem sigma_finsupp_equiv_dfinsupp_apply [Zero N] (f : (Σi, η i) →₀ N) :
    (sigmaFinsuppEquivDfinsupp f : ∀ i, η i →₀ N) = Finsupp.split f :=
  rfl

@[simp]
theorem sigma_finsupp_equiv_dfinsupp_symm_apply [Zero N] (f : Π₀ i, η i →₀ N) (s : Σi, η i) :
    (sigmaFinsuppEquivDfinsupp.symm f : (Σi, η i) →₀ N) s = f s.1 s.2 :=
  rfl

@[simp]
theorem sigma_finsupp_equiv_dfinsupp_support [Zero N] (f : (Σi, η i) →₀ N) :
    (sigmaFinsuppEquivDfinsupp f).support = Finsupp.splitSupport f := by
  ext
  rw [Dfinsupp.mem_support_to_fun]
  exact (Finsupp.mem_split_support_iff_nonzero _ _).symm

@[simp]
theorem sigma_finsupp_equiv_dfinsupp_single [Zero N] (a : Σi, η i) (n : N) :
    sigmaFinsuppEquivDfinsupp (Finsupp.single a n) =
      @Dfinsupp.single _ (fun i => η i →₀ N) _ _ a.1 (Finsupp.single a.2 n) :=
  by
  obtain ⟨i, a⟩ := a
  ext j b
  by_cases' h : i = j
  · subst h
    simp [← split_apply, ← Finsupp.single_apply]
    
  suffices Finsupp.single (⟨i, a⟩ : Σi, η i) n ⟨j, b⟩ = 0 by
    simp [← split_apply, ← dif_neg h, ← this]
  have H : (⟨i, a⟩ : Σi, η i) ≠ ⟨j, b⟩ := by
    simp [← h]
  rw [Finsupp.single_apply, if_neg H]

-- Without this Lean fails to find the `add_zero_class` instance on `Π₀ i, (η i →₀ N)`.
attribute [-instance] Finsupp.hasZero

@[simp]
theorem sigma_finsupp_equiv_dfinsupp_add [AddZeroClassₓ N] (f g : (Σi, η i) →₀ N) :
    sigmaFinsuppEquivDfinsupp (f + g) =
      (sigmaFinsuppEquivDfinsupp f + sigmaFinsuppEquivDfinsupp g : Π₀ i : ι, η i →₀ N) :=
  by
  ext
  rfl

/-- `finsupp.split` is an additive equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
def sigmaFinsuppAddEquivDfinsupp [AddZeroClassₓ N] : ((Σi, η i) →₀ N) ≃+ Π₀ i, η i →₀ N :=
  { sigmaFinsuppEquivDfinsupp with toFun := sigmaFinsuppEquivDfinsupp, invFun := sigmaFinsuppEquivDfinsupp.symm,
    map_add' := sigma_finsupp_equiv_dfinsupp_add }

attribute [-instance] Finsupp.addZeroClass

--tofix: r • (sigma_finsupp_equiv_dfinsupp f) doesn't work.
@[simp]
theorem sigma_finsupp_equiv_dfinsupp_smul {R} [Monoidₓ R] [AddMonoidₓ N] [DistribMulAction R N] (r : R)
    (f : (Σi, η i) →₀ N) :
    sigmaFinsuppEquivDfinsupp (r • f) =
      @HasSmul.smul R (Π₀ i, η i →₀ N) MulAction.toHasSmul r (sigmaFinsuppEquivDfinsupp f) :=
  by
  ext
  rfl

attribute [-instance] Finsupp.addMonoid

/-- `finsupp.split` is a linear equivalence between `(Σ i, η i) →₀ N` and `Π₀ i, (η i →₀ N)`. -/
@[simps]
def sigmaFinsuppLequivDfinsupp [AddCommMonoidₓ N] [Module R N] : ((Σi, η i) →₀ N) ≃ₗ[R] Π₀ i, η i →₀ N :=
  { sigmaFinsuppAddEquivDfinsupp with map_smul' := sigma_finsupp_equiv_dfinsupp_smul }

end Sigma

end Equivs

