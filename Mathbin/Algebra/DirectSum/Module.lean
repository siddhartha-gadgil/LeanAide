/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.Algebra.DirectSum.Basic
import Mathbin.LinearAlgebra.Dfinsupp

/-!
# Direct sum of modules

The first part of the file provides constructors for direct sums of modules. It provides a
construction of the direct sum using the universal property and proves its uniqueness
(`direct_sum.to_module.unique`).

The second part of the file covers the special case of direct sums of submodules of a fixed module
`M`.  There is a canonical linear map from this direct sum to `M` (`direct_sum.coe_linear_map`), and
the construction is of particular importance when this linear map is an equivalence; that is, when
the submodules provide an internal decomposition of `M`.  The property is defined more generally
elsewhere as `direct_sum.is_internal`, but its basic consequences on `submodule`s are established
in this file.

-/


universe u v w u₁

namespace DirectSum

open DirectSum

section General

variable {R : Type u} [Semiringₓ R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

include R

variable {M : ι → Type w} [∀ i, AddCommMonoidₓ (M i)] [∀ i, Module R (M i)]

instance : Module R (⨁ i, M i) :=
  Dfinsupp.module

instance {S : Type _} [Semiringₓ S] [∀ i, Module S (M i)] [∀ i, SmulCommClass R S (M i)] :
    SmulCommClass R S (⨁ i, M i) :=
  Dfinsupp.smul_comm_class

instance {S : Type _} [Semiringₓ S] [HasSmul R S] [∀ i, Module S (M i)] [∀ i, IsScalarTower R S (M i)] :
    IsScalarTower R S (⨁ i, M i) :=
  Dfinsupp.is_scalar_tower

instance [∀ i, Module Rᵐᵒᵖ (M i)] [∀ i, IsCentralScalar R (M i)] : IsCentralScalar R (⨁ i, M i) :=
  Dfinsupp.is_central_scalar

theorem smul_apply (b : R) (v : ⨁ i, M i) (i : ι) : (b • v) i = b • v i :=
  Dfinsupp.smul_apply _ _ _

include dec_ι

variable (R ι M)

/-- Create the direct sum given a family `M` of `R` modules indexed over `ι`. -/
def lmk : ∀ s : Finset ι, (∀ i : (↑s : Set ι), M i.val) →ₗ[R] ⨁ i, M i :=
  Dfinsupp.lmk

/-- Inclusion of each component into the direct sum. -/
def lof : ∀ i : ι, M i →ₗ[R] ⨁ i, M i :=
  Dfinsupp.lsingle

theorem lof_eq_of (i : ι) (b : M i) : lof R ι M i b = of M i b :=
  rfl

variable {ι M}

theorem single_eq_lof (i : ι) (b : M i) : Dfinsupp.single i b = lof R ι M i b :=
  rfl

/-- Scalar multiplication commutes with direct sums. -/
theorem mk_smul (s : Finset ι) (c : R) (x) : mk M s (c • x) = c • mk M s x :=
  (lmk R ι M s).map_smul c x

/-- Scalar multiplication commutes with the inclusion of each component into the direct sum. -/
theorem of_smul (i : ι) (c : R) (x) : of M i (c • x) = c • of M i x :=
  (lof R ι M i).map_smul c x

variable {R}

theorem support_smul [∀ (i : ι) (x : M i), Decidable (x ≠ 0)] (c : R) (v : ⨁ i, M i) : (c • v).support ⊆ v.support :=
  Dfinsupp.support_smul _ _

variable {N : Type u₁} [AddCommMonoidₓ N] [Module R N]

variable (φ : ∀ i, M i →ₗ[R] N)

variable (R ι N φ)

/-- The linear map constructed using the universal property of the coproduct. -/
def toModule : (⨁ i, M i) →ₗ[R] N :=
  Dfinsupp.lsum ℕ φ

/-- Coproducts in the categories of modules and additive monoids commute with the forgetful functor
from modules to additive monoids. -/
theorem coe_to_module_eq_coe_to_add_monoid :
    (toModule R ι N φ : (⨁ i, M i) → N) = toAddMonoid fun i => (φ i).toAddMonoidHom :=
  rfl

variable {ι N φ}

/-- The map constructed using the universal property gives back the original maps when
restricted to each component. -/
@[simp]
theorem to_module_lof (i) (x : M i) : toModule R ι N φ (lof R ι M i x) = φ i x :=
  to_add_monoid_of (fun i => (φ i).toAddMonoidHom) i x

variable (ψ : (⨁ i, M i) →ₗ[R] N)

/-- Every linear map from a direct sum agrees with the one obtained by applying
the universal property to each of its components. -/
theorem toModule.unique (f : ⨁ i, M i) : ψ f = toModule R ι N (fun i => ψ.comp <| lof R ι M i) f :=
  toAddMonoid.unique ψ.toAddMonoidHom f

variable {ψ} {ψ' : (⨁ i, M i) →ₗ[R] N}

/-- Two `linear_map`s out of a direct sum are equal if they agree on the generators.

See note [partially-applied ext lemmas]. -/
@[ext]
theorem linear_map_ext ⦃ψ ψ' : (⨁ i, M i) →ₗ[R] N⦄ (H : ∀ i, ψ.comp (lof R ι M i) = ψ'.comp (lof R ι M i)) : ψ = ψ' :=
  Dfinsupp.lhom_ext' H

/-- The inclusion of a subset of the direct summands
into a larger subset of the direct summands, as a linear map.
-/
def lsetToSet (S T : Set ι) (H : S ⊆ T) : (⨁ i : S, M i) →ₗ[R] ⨁ i : T, M i :=
  (toModule R _ _) fun i => lof R T (fun i : Subtype T => M i) ⟨i, H i.Prop⟩

omit dec_ι

variable (ι M)

/-- Given `fintype α`, `linear_equiv_fun_on_fintype R` is the natural `R`-linear equivalence
between `⨁ i, M i` and `Π i, M i`. -/
@[simps apply]
def linearEquivFunOnFintype [Fintype ι] : (⨁ i, M i) ≃ₗ[R] ∀ i, M i :=
  { Dfinsupp.equivFunOnFintype with toFun := coeFn,
    map_add' := fun f g => by
      ext
      simp only [← add_apply, ← Pi.add_apply],
    map_smul' := fun c f => by
      ext
      simp only [← Dfinsupp.coe_smul, ← RingHom.id_apply] }

variable {ι M}

@[simp]
theorem linear_equiv_fun_on_fintype_lof [Fintype ι] [DecidableEq ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M) (lof R ι M i m) = Pi.single i m := by
  ext a
  change (Dfinsupp.equivFunOnFintype (lof R ι M i m)) a = _
  convert _root_.congr_fun (Dfinsupp.equiv_fun_on_fintype_single i m) a

@[simp]
theorem linear_equiv_fun_on_fintype_symm_single [Fintype ι] [DecidableEq ι] (i : ι) (m : M i) :
    (linearEquivFunOnFintype R ι M).symm (Pi.single i m) = lof R ι M i m := by
  ext a
  change (dfinsupp.equiv_fun_on_fintype.symm (Pi.single i m)) a = _
  rw [Dfinsupp.equiv_fun_on_fintype_symm_single i m]
  rfl

@[simp]
theorem linear_equiv_fun_on_fintype_symm_coe [Fintype ι] (f : ⨁ i, M i) : (linearEquivFunOnFintype R ι M).symm f = f :=
  by
  ext
  simp [← linear_equiv_fun_on_fintype]

/-- The natural linear equivalence between `⨁ _ : ι, M` and `M` when `unique ι`. -/
protected def lid (M : Type v) (ι : Type _ := PUnit) [AddCommMonoidₓ M] [Module R M] [Unique ι] :
    (⨁ _ : ι, M) ≃ₗ[R] M :=
  { DirectSum.id M ι, toModule R ι M fun i => LinearMap.id with }

variable (ι M)

/-- The projection map onto one component, as a linear map. -/
def component (i : ι) : (⨁ i, M i) →ₗ[R] M i :=
  Dfinsupp.lapply i

variable {ι M}

theorem apply_eq_component (f : ⨁ i, M i) (i : ι) : f i = component R ι M i f :=
  rfl

@[ext]
theorem ext {f g : ⨁ i, M i} (h : ∀ i, component R ι M i f = component R ι M i g) : f = g :=
  Dfinsupp.ext h

theorem ext_iff {f g : ⨁ i, M i} : f = g ↔ ∀ i, component R ι M i f = component R ι M i g :=
  ⟨fun h _ => by
    rw [h], ext R⟩

include dec_ι

@[simp]
theorem lof_apply (i : ι) (b : M i) : ((lof R ι M i) b) i = b :=
  Dfinsupp.single_eq_same

@[simp]
theorem component.lof_self (i : ι) (b : M i) : component R ι M i ((lof R ι M i) b) = b :=
  lof_apply R i b

theorem component.of (i j : ι) (b : M j) :
    component R ι M i ((lof R ι M j) b) = if h : j = i then Eq.recOnₓ h b else 0 :=
  Dfinsupp.single_apply

omit dec_ι

section CongrLeft

variable {κ : Type _}

/-- Reindexing terms of a direct sum is linear.-/
def lequivCongrLeft (h : ι ≃ κ) : (⨁ i, M i) ≃ₗ[R] ⨁ k, M (h.symm k) :=
  { equivCongrLeft h with map_smul' := Dfinsupp.comap_domain'_smul _ _ }

@[simp]
theorem lequiv_congr_left_apply (h : ι ≃ κ) (f : ⨁ i, M i) (k : κ) : lequivCongrLeft R h f k = f (h.symm k) :=
  equiv_congr_left_apply _ _ _

end CongrLeft

section Sigma

variable {α : ι → Type _} {δ : ∀ i, α i → Type w}

variable [∀ i j, AddCommMonoidₓ (δ i j)] [∀ i j, Module R (δ i j)]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
/-- `curry` as a linear map.-/
noncomputable def sigmaLcurry : (⨁ i : Σi, _, δ i.1 i.2) →ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurry with
    map_smul' := fun r => by
      convert @Dfinsupp.sigma_curry_smul _ _ _ δ _ _ _ r }

@[simp]
theorem sigma_lcurry_apply (f : ⨁ i : Σi, _, δ i.1 i.2) (i : ι) (j : α i) : sigmaLcurry R f i j = f ⟨i, j⟩ :=
  sigma_curry_apply f i j

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
/-- `uncurry` as a linear map.-/
noncomputable def sigmaLuncurry : (⨁ (i) (j), δ i j) →ₗ[R] ⨁ i : Σi, _, δ i.1 i.2 :=
  { sigmaUncurry with map_smul' := Dfinsupp.sigma_uncurry_smul }

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem sigma_luncurry_apply (f : ⨁ (i) (j), δ i j) (i : ι) (j : α i) : sigmaLuncurry R f ⟨i, j⟩ = f i j :=
  sigma_uncurry_apply f i j

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
/-- `curry_equiv` as a linear equiv.-/
noncomputable def sigmaLcurryEquiv : (⨁ i : Σi, _, δ i.1 i.2) ≃ₗ[R] ⨁ (i) (j), δ i j :=
  { sigmaCurryEquiv, sigmaLcurry R with }

end Sigma

section Option

variable {α : Option ι → Type w} [∀ i, AddCommMonoidₓ (α i)] [∀ i, Module R (α i)]

include dec_ι

/-- Linear isomorphism obtained by separating the term of index `none` of a direct sum over
`option ι`.-/
@[simps]
noncomputable def lequivProdDirectSum : (⨁ i, α i) ≃ₗ[R] α none × ⨁ i, α (some i) :=
  { addEquivProdDirectSum with map_smul' := Dfinsupp.equiv_prod_dfinsupp_smul }

end Option

end General

section Submodule

section Semiringₓ

variable {R : Type u} [Semiringₓ R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

include dec_ι

variable {M : Type _} [AddCommMonoidₓ M] [Module R M]

variable (A : ι → Submodule R M)

/-- The canonical embedding from `⨁ i, A i` to `M`  where `A` is a collection of `submodule R M`
indexed by `ι`. This is `direct_sum.coe_add_monoid_hom` as a `linear_map`. -/
def coeLinearMap : (⨁ i, A i) →ₗ[R] M :=
  toModule R ι M fun i => (A i).Subtype

@[simp]
theorem coe_linear_map_of (i : ι) (x : A i) : DirectSum.coeLinearMap A (of (fun i => A i) i x) = x :=
  to_add_monoid_of _ _ _

variable {A}

/-- If a direct sum of submodules is internal then the submodules span the module. -/
theorem IsInternal.submodule_supr_eq_top (h : IsInternal A) : supr A = ⊤ := by
  rw [Submodule.supr_eq_range_dfinsupp_lsum, LinearMap.range_eq_top]
  exact Function.Bijective.surjective h

/-- If a direct sum of submodules is internal then the submodules are independent. -/
theorem IsInternal.submodule_independent (h : IsInternal A) : CompleteLattice.Independent A :=
  CompleteLattice.independent_of_dfinsupp_lsum_injective _ h.Injective

/-- Given an internal direct sum decomposition of a module `M`, and a basis for each of the
components of the direct sum, the disjoint union of these bases is a basis for `M`. -/
noncomputable def IsInternal.collectedBasis (h : IsInternal A) {α : ι → Type _} (v : ∀ i, Basis (α i) R (A i)) :
    Basis (Σi, α i) R
      M where repr :=
    ((LinearEquiv.ofBijective (DirectSum.coeLinearMap A) h.Injective h.Surjective).symm ≪≫ₗ
        Dfinsupp.mapRange.linearEquiv fun i => (v i).repr) ≪≫ₗ
      (sigmaFinsuppLequivDfinsupp R).symm

@[simp]
theorem IsInternal.collected_basis_coe (h : IsInternal A) {α : ι → Type _} (v : ∀ i, Basis (α i) R (A i)) :
    ⇑(h.collectedBasis v) = fun a : Σi, α i => ↑(v a.1 a.2) := by
  funext a
  simp only [← is_internal.collected_basis, ← to_module, ← coe_linear_map, ← AddEquiv.to_fun_eq_coe, ←
    Basis.coe_of_repr, ← Basis.repr_symm_apply, ← Dfinsupp.lsum_apply_apply, ← Dfinsupp.mapRange.linear_equiv_apply, ←
    Dfinsupp.mapRange.linear_equiv_symm, ← Dfinsupp.map_range_single, ← Finsupp.total_single, ←
    LinearEquiv.of_bijective_apply, ← LinearEquiv.symm_symm, ← LinearEquiv.symm_trans_apply, ← one_smul, ←
    sigma_finsupp_add_equiv_dfinsupp_apply, ← sigma_finsupp_equiv_dfinsupp_single, ←
    sigma_finsupp_lequiv_dfinsupp_apply]
  convert Dfinsupp.sum_add_hom_single (fun i => (A i).Subtype.toAddMonoidHom) a.1 (v a.1 a.2)

theorem IsInternal.collected_basis_mem (h : IsInternal A) {α : ι → Type _} (v : ∀ i, Basis (α i) R (A i))
    (a : Σi, α i) : h.collectedBasis v a ∈ A a.1 := by
  simp

/-- When indexed by only two distinct elements, `direct_sum.is_internal` implies
the two submodules are complementary. Over a `ring R`, this is true as an iff, as
`direct_sum.is_internal_iff_is_compl`. --/
theorem IsInternal.is_compl {A : ι → Submodule R M} {i j : ι} (hij : i ≠ j) (h : (Set.Univ : Set ι) = {i, j})
    (hi : IsInternal A) : IsCompl (A i) (A j) :=
  ⟨hi.submodule_independent.PairwiseDisjoint _ _ hij,
    Eq.le <|
      hi.submodule_supr_eq_top.symm.trans <| by
        rw [← Sup_pair, supr, ← Set.image_univ, h, Set.image_insert_eq, Set.image_singleton]⟩

end Semiringₓ

section Ringₓ

variable {R : Type u} [Ringₓ R]

variable {ι : Type v} [dec_ι : DecidableEq ι]

include dec_ι

variable {M : Type _} [AddCommGroupₓ M] [Module R M]

/-- Note that this is not generally true for `[semiring R]`; see
`complete_lattice.independent.dfinsupp_lsum_injective` for details. -/
theorem is_internal_submodule_of_independent_of_supr_eq_top {A : ι → Submodule R M} (hi : CompleteLattice.Independent A)
    (hs : supr A = ⊤) : IsInternal A :=
  ⟨hi.dfinsupp_lsum_injective, LinearMap.range_eq_top.1 <| (Submodule.supr_eq_range_dfinsupp_lsum _).symm.trans hs⟩

/-- `iff` version of `direct_sum.is_internal_submodule_of_independent_of_supr_eq_top`,
`direct_sum.is_internal.independent`, and `direct_sum.is_internal.supr_eq_top`.
-/
theorem is_internal_submodule_iff_independent_and_supr_eq_top (A : ι → Submodule R M) :
    IsInternal A ↔ CompleteLattice.Independent A ∧ supr A = ⊤ :=
  ⟨fun i => ⟨i.submodule_independent, i.submodule_supr_eq_top⟩,
    And.ndrec is_internal_submodule_of_independent_of_supr_eq_top⟩

/-- If a collection of submodules has just two indices, `i` and `j`, then
`direct_sum.is_internal` is equivalent to `is_compl`. -/
theorem is_internal_submodule_iff_is_compl (A : ι → Submodule R M) {i j : ι} (hij : i ≠ j)
    (h : (Set.Univ : Set ι) = {i, j}) : IsInternal A ↔ IsCompl (A i) (A j) := by
  have : ∀ k, k = i ∨ k = j := fun k => by
    simpa using set.ext_iff.mp h k
  rw [is_internal_submodule_iff_independent_and_supr_eq_top, supr, ← Set.image_univ, h, Set.image_insert_eq,
    Set.image_singleton, Sup_pair, CompleteLattice.independent_pair hij this]
  exact ⟨fun ⟨hd, ht⟩ => ⟨hd, ht.Ge⟩, fun ⟨hd, ht⟩ => ⟨hd, eq_top_iff.mpr ht⟩⟩

/-! Now copy the lemmas for subgroup and submonoids. -/


theorem IsInternal.add_submonoid_independent {M : Type _} [AddCommMonoidₓ M] {A : ι → AddSubmonoid M}
    (h : IsInternal A) : CompleteLattice.Independent A :=
  CompleteLattice.independent_of_dfinsupp_sum_add_hom_injective _ h.Injective

theorem IsInternal.add_subgroup_independent {M : Type _} [AddCommGroupₓ M] {A : ι → AddSubgroup M} (h : IsInternal A) :
    CompleteLattice.Independent A :=
  CompleteLattice.independent_of_dfinsupp_sum_add_hom_injective' _ h.Injective

end Ringₓ

end Submodule

end DirectSum

