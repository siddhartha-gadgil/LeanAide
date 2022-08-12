/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.LinearAlgebra.Dimension
import Mathbin.LinearAlgebra.FiniteDimensional
import Mathbin.LinearAlgebra.StdBasis

/-!
# Linear structures on function with finite support `ι →₀ M`

This file contains results on the `R`-module structure on functions of finite support from a type
`ι` to an `R`-module `M`, in particular in the case that `R` is a field.

Furthermore, it contains some facts about isomorphisms of vector spaces from equality of dimension
as well as the cardinality of finite dimensional vector spaces.

## TODO

Move the second half of this file to more appropriate other files.
-/


noncomputable section

attribute [local instance] Classical.propDecidable

open Set LinearMap Submodule

open Cardinal

universe u v w

namespace Finsupp

section Ringₓ

variable {R : Type _} {M : Type _} {ι : Type _}

variable [Ringₓ R] [AddCommGroupₓ M] [Module R M]

theorem linear_independent_single {φ : ι → Type _} {f : ∀ ι, φ ι → M} (hf : ∀ i, LinearIndependent R (f i)) :
    LinearIndependent R fun ix : Σi, φ i => single ix.1 (f ix.1 ix.2) := by
  apply @linear_independent_Union_finite R _ _ _ _ ι φ fun i x => single i (f i x)
  · intro i
    have h_disjoint : Disjoint (span R (range (f i))) (ker (lsingle i)) := by
      rw [ker_lsingle]
      exact disjoint_bot_right
    apply (hf i).map h_disjoint
    
  · intro i t ht hit
    refine' (disjoint_lsingle_lsingle {i} t (disjoint_singleton_left.2 hit)).mono _ _
    · rw [span_le]
      simp only [← supr_singleton]
      rw [range_coe]
      apply range_comp_subset_range
      
    · refine' supr₂_mono fun i hi => _
      rw [span_le, range_coe]
      apply range_comp_subset_range
      
    

open LinearMap Submodule

/-- The basis on `ι →₀ M` with basis vectors `λ ⟨i, x⟩, single i (b i x)`. -/
protected def basis {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) : Basis (Σi, φ i) R (ι →₀ M) :=
  Basis.of_repr
    { toFun := fun g =>
        { toFun := fun ix => (b ix.1).repr (g ix.1) ix.2,
          support := g.support.Sigma fun i => ((b i).repr (g i)).support,
          mem_support_to_fun := fun ix => by
            simp only [← Finset.mem_sigma, ← mem_support_iff, ← and_iff_right_iff_imp, ← Ne.def]
            intro b hg
            simpa [← hg] using b },
      invFun := fun g =>
        { toFun := fun i => (b i).repr.symm (g.comapDomain _ (Set.inj_on_of_injective sigma_mk_injective _)),
          support := g.support.Image Sigma.fst,
          mem_support_to_fun := fun i => by
            rw [Ne.def, ← (b i).repr.Injective.eq_iff, (b i).repr.apply_symm_apply, ext_iff]
            simp only [← exists_prop, ← LinearEquiv.map_zero, ← comap_domain_apply, ← zero_apply, ←
              exists_and_distrib_right, ← mem_support_iff, ← exists_eq_right, ← Sigma.exists, ← Finset.mem_image, ←
              not_forall] },
      left_inv := fun g => by
        ext i
        rw [← (b i).repr.Injective.eq_iff]
        ext x
        simp only [← coe_mk, ← LinearEquiv.apply_symm_apply, ← comap_domain_apply],
      right_inv := fun g => by
        ext ⟨i, x⟩
        simp only [← coe_mk, ← LinearEquiv.apply_symm_apply, ← comap_domain_apply],
      map_add' := fun g h => by
        ext ⟨i, x⟩
        simp only [← coe_mk, ← add_apply, ← LinearEquiv.map_add],
      map_smul' := fun c h => by
        ext ⟨i, x⟩
        simp only [← coe_mk, ← smul_apply, ← LinearEquiv.map_smul, ← RingHom.id_apply] }

@[simp]
theorem basis_repr {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) (g : ι →₀ M) (ix) :
    (Finsupp.basis b).repr g ix = (b ix.1).repr (g ix.1) ix.2 :=
  rfl

@[simp]
theorem coe_basis {φ : ι → Type _} (b : ∀ i, Basis (φ i) R M) :
    ⇑(Finsupp.basis b) = fun ix : Σi, φ i => single ix.1 (b ix.1 ix.2) :=
  funext fun ⟨i, x⟩ =>
    Basis.apply_eq_iff.mpr <| by
      ext ⟨j, y⟩
      by_cases' h : i = j
      · cases h
        simp only [← basis_repr, ← single_eq_same, ← Basis.repr_self, ←
          Basis.Finsupp.single_apply_left sigma_mk_injective]
        
      simp only [← basis_repr, ← single_apply, ← h, ← false_andₓ, ← if_false, ← LinearEquiv.map_zero, ← zero_apply]

/-- The basis on `ι →₀ M` with basis vectors `λ i, single i 1`. -/
@[simps]
protected def basisSingleOne : Basis ι R (ι →₀ R) :=
  Basis.of_repr (LinearEquiv.refl _ _)

@[simp]
theorem coe_basis_single_one : (Finsupp.basisSingleOne : ι → ι →₀ R) = fun i => Finsupp.single i 1 :=
  funext fun i => Basis.apply_eq_iff.mpr rfl

end Ringₓ

section Dim

variable {K : Type u} {V : Type v} {ι : Type v}

variable [Field K] [AddCommGroupₓ V] [Module K V]

theorem dim_eq : Module.rank K (ι →₀ V) = # ι * Module.rank K V := by
  let bs := Basis.ofVectorSpace K V
  rw [← bs.mk_eq_dim'', ← (Finsupp.basis fun a : ι => bs).mk_eq_dim'', Cardinal.mk_sigma, Cardinal.sum_const']

end Dim

end Finsupp

section Module

variable {K : Type u} {V V₁ V₂ : Type v} {V' : Type w}

variable [Field K]

variable [AddCommGroupₓ V] [Module K V]

variable [AddCommGroupₓ V₁] [Module K V₁]

variable [AddCommGroupₓ V₂] [Module K V₂]

variable [AddCommGroupₓ V'] [Module K V']

open Module

theorem equiv_of_dim_eq_lift_dim (h : Cardinal.lift.{w} (Module.rank K V) = Cardinal.lift.{v} (Module.rank K V')) :
    Nonempty (V ≃ₗ[K] V') := by
  have := Classical.decEq V
  have := Classical.decEq V'
  let m := Basis.ofVectorSpace K V
  let m' := Basis.ofVectorSpace K V'
  rw [← Cardinal.lift_inj.1 m.mk_eq_dim, ← Cardinal.lift_inj.1 m'.mk_eq_dim] at h
  rcases Quotientₓ.exact h with ⟨e⟩
  let e := (equiv.ulift.symm.trans e).trans Equivₓ.ulift
  exact ⟨m.repr ≪≫ₗ Finsupp.domLcongr e ≪≫ₗ m'.repr.symm⟩

/-- Two `K`-vector spaces are equivalent if their dimension is the same. -/
def equivOfDimEqDim (h : Module.rank K V₁ = Module.rank K V₂) : V₁ ≃ₗ[K] V₂ := by
  classical
  exact Classical.choice (equiv_of_dim_eq_lift_dim (Cardinal.lift_inj.2 h))

/-- An `n`-dimensional `K`-vector space is equivalent to `fin n → K`. -/
def finDimVectorspaceEquiv (n : ℕ) (hn : Module.rank K V = n) : V ≃ₗ[K] Finₓ n → K := by
  have : Cardinal.lift.{u} (n : Cardinal.{v}) = Cardinal.lift.{v} (n : Cardinal.{u}) := by
    simp
  have hn := Cardinal.lift_inj.{v, u}.2 hn
  rw [this] at hn
  rw [← @dim_fin_fun K _ n] at hn
  exact Classical.choice (equiv_of_dim_eq_lift_dim hn)

end Module

section Module

open Module

variable (K V : Type u) [Field K] [AddCommGroupₓ V] [Module K V]

theorem cardinal_mk_eq_cardinal_mk_field_pow_dim [FiniteDimensional K V] : # V = # K ^ Module.rank K V := by
  let s := Basis.OfVectorSpaceIndex K V
  let hs := Basis.ofVectorSpace K V
  calc # V = # (s →₀ K) := Quotientₓ.sound ⟨hs.repr.to_equiv⟩_ = # (s → K) :=
      Quotientₓ.sound ⟨Finsupp.equivFunOnFintype⟩_ = _ := by
      rw [← Cardinal.lift_inj.1 hs.mk_eq_dim, Cardinal.power_def]

theorem cardinal_lt_aleph_0_of_finite_dimensional [Fintype K] [FiniteDimensional K V] : # V < ℵ₀ := by
  let this : IsNoetherian K V := IsNoetherian.iff_fg.2 inferInstance
  rw [cardinal_mk_eq_cardinal_mk_field_pow_dim K V]
  exact Cardinal.power_lt_aleph_0 (Cardinal.lt_aleph_0_of_finite K) (IsNoetherian.dim_lt_aleph_0 K V)

end Module

