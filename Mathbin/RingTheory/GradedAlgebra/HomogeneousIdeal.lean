/-
Copyright (c) 2021 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang, Eric Wieser
-/
import Mathbin.RingTheory.Ideal.Basic
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.LinearAlgebra.Finsupp
import Mathbin.RingTheory.GradedAlgebra.Basic

/-!
# Homogeneous ideals of a graded algebra

This file defines homogeneous ideals of `graded_ring 𝒜` where `𝒜 : ι → submodule R A` and
operations on them.

## Main definitions

For any `I : ideal A`:
* `ideal.is_homogeneous 𝒜 I`: The property that an ideal is closed under `graded_ring.proj`.
* `homogeneous_ideal 𝒜`: The structure extending ideals which satisfy `ideal.is_homogeneous`
* `ideal.homogeneous_core I 𝒜`: The largest homogeneous ideal smaller than `I`.
* `ideal.homogeneous_hull I 𝒜`: The smallest homogeneous ideal larger than `I`.

## Main statements

* `homogeneous_ideal.complete_lattice`: `ideal.is_homogeneous` is preserved by `⊥`, `⊤`, `⊔`, `⊓`,
  `⨆`, `⨅`, and so the subtype of homogeneous ideals inherits a complete lattice structure.
* `ideal.homogeneous_core.gi`: `ideal.homogeneous_core` forms a galois insertion with coercion.
* `ideal.homogeneous_hull.gi`: `ideal.homogeneous_hull` forms a galois insertion with coercion.

## Implementation notes

We introduce `ideal.homogeneous_core'` earlier than might be expected so that we can get access
to `ideal.is_homogeneous.iff_exists` as quickly as possible.

## Tags

graded algebra, homogeneous
-/


open SetLike DirectSum Set

open BigOperators Pointwise DirectSum

variable {ι σ R A : Type _}

section HomogeneousDef

variable [Semiringₓ A]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

variable [DecidableEq ι] [AddMonoidₓ ι] [GradedRing 𝒜]

variable (I : Ideal A)

include A

/-- An `I : ideal A` is homogeneous if for every `r ∈ I`, all homogeneous components
  of `r` are in `I`.-/
def Ideal.IsHomogeneous : Prop :=
  ∀ (i : ι) ⦃r : A⦄, r ∈ I → (DirectSum.decompose 𝒜 r i : A) ∈ I

/-- For any `semiring A`, we collect the homogeneous ideals of `A` into a type. -/
structure HomogeneousIdeal extends Submodule A A where
  is_homogeneous' : Ideal.IsHomogeneous 𝒜 to_submodule

variable {𝒜}

/-- Converting a homogeneous ideal to an ideal-/
def HomogeneousIdeal.toIdeal (I : HomogeneousIdeal 𝒜) : Ideal A :=
  I.toSubmodule

theorem HomogeneousIdeal.is_homogeneous (I : HomogeneousIdeal 𝒜) : I.toIdeal.IsHomogeneous 𝒜 :=
  I.is_homogeneous'

theorem HomogeneousIdeal.to_ideal_injective :
    Function.Injective (HomogeneousIdeal.toIdeal : HomogeneousIdeal 𝒜 → Ideal A) := fun ⟨x, hx⟩ ⟨y, hy⟩ (h : x = y) =>
  by
  simp [← h]

instance HomogeneousIdeal.setLike : SetLike (HomogeneousIdeal 𝒜) A where
  coe := fun I => I.toIdeal
  coe_injective' := fun I J h => HomogeneousIdeal.to_ideal_injective <| SetLike.coe_injective h

@[ext]
theorem HomogeneousIdeal.ext {I J : HomogeneousIdeal 𝒜} (h : I.toIdeal = J.toIdeal) : I = J :=
  HomogeneousIdeal.to_ideal_injective h

@[simp]
theorem HomogeneousIdeal.mem_iff {I : HomogeneousIdeal 𝒜} {x : A} : x ∈ I.toIdeal ↔ x ∈ I :=
  Iff.rfl

end HomogeneousDef

section HomogeneousCore

variable [Semiringₓ A]

variable [SetLike σ A] (𝒜 : ι → σ)

variable (I : Ideal A)

include A

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`, as an ideal. -/
def Ideal.homogeneousCore' (I : Ideal A) : Ideal A :=
  Ideal.span (coe '' ((coe : Subtype (IsHomogeneous 𝒜) → A) ⁻¹' I))

theorem Ideal.homogeneous_core'_mono : Monotone (Ideal.homogeneousCore' 𝒜) := fun I J I_le_J =>
  Ideal.span_mono <| (Set.image_subset _) fun x => @I_le_J _

theorem Ideal.homogeneous_core'_le : I.homogeneousCore' 𝒜 ≤ I :=
  Ideal.span_le.2 <| image_preimage_subset _ _

end HomogeneousCore

section IsHomogeneousIdealDefs

variable [Semiringₓ A]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

variable [DecidableEq ι] [AddMonoidₓ ι] [GradedRing 𝒜]

variable (I : Ideal A)

include A

theorem Ideal.is_homogeneous_iff_forall_subset : I.IsHomogeneous 𝒜 ↔ ∀ i, (I : Set A) ⊆ GradedRing.proj 𝒜 i ⁻¹' I :=
  Iff.rfl

theorem Ideal.is_homogeneous_iff_subset_Inter : I.IsHomogeneous 𝒜 ↔ (I : Set A) ⊆ ⋂ i, GradedRing.proj 𝒜 i ⁻¹' ↑I :=
  subset_Inter_iff.symm

theorem Ideal.mul_homogeneous_element_mem_of_mem {I : Ideal A} (r x : A) (hx₁ : IsHomogeneous 𝒜 x) (hx₂ : x ∈ I)
    (j : ι) : GradedRing.proj 𝒜 j (r * x) ∈ I := by
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r, Finset.sum_mul, map_sum]
  apply Ideal.sum_mem
  intro k hk
  obtain ⟨i, hi⟩ := hx₁
  have mem₁ : (DirectSum.decompose 𝒜 r k : A) * x ∈ 𝒜 (k + i) := graded_monoid.mul_mem (SetLike.coe_mem _) hi
  erw [GradedRing.proj_apply, DirectSum.decompose_of_mem 𝒜 mem₁, coe_of_apply, SetLike.coe_mk]
  split_ifs
  · exact I.mul_mem_left _ hx₂
    
  · exact I.zero_mem
    

theorem Ideal.is_homogeneous_span (s : Set A) (h : ∀, ∀ x ∈ s, ∀, IsHomogeneous 𝒜 x) : (Ideal.span s).IsHomogeneous 𝒜 :=
  by
  rintro i r hr
  rw [Ideal.span, Finsupp.span_eq_range_total] at hr
  rw [LinearMap.mem_range] at hr
  obtain ⟨s, rfl⟩ := hr
  rw [Finsupp.total_apply, Finsupp.sum, decompose_sum, Dfinsupp.finset_sum_apply, AddSubmonoidClass.coe_finset_sum]
  refine' Ideal.sum_mem _ _
  rintro z hz1
  rw [smul_eq_mul]
  refine' Ideal.mul_homogeneous_element_mem_of_mem 𝒜 (s z) z _ _ i
  · rcases z with ⟨z, hz2⟩
    apply h _ hz2
    
  · exact Ideal.subset_span z.2
    

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_core' 𝒜`
is the largest homogeneous ideal of `A` contained in `I`.-/
def Ideal.homogeneousCore : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.homogeneousCore' 𝒜 I,
    Ideal.is_homogeneous_span _ _ fun x h => by
      rw [Subtype.image_preimage_coe] at h
      exact h.2⟩

theorem Ideal.homogeneous_core_mono : Monotone (Ideal.homogeneousCore 𝒜) :=
  Ideal.homogeneous_core'_mono 𝒜

theorem Ideal.to_ideal_homogeneous_core_le : (I.homogeneousCore 𝒜).toIdeal ≤ I :=
  Ideal.homogeneous_core'_le 𝒜 I

variable {𝒜 I}

theorem Ideal.mem_homogeneous_core_of_is_homogeneous_of_mem {x : A} (h : SetLike.IsHomogeneous 𝒜 x) (hmem : x ∈ I) :
    x ∈ I.homogeneousCore 𝒜 :=
  Ideal.subset_span ⟨⟨x, h⟩, hmem, rfl⟩

theorem Ideal.IsHomogeneous.to_ideal_homogeneous_core_eq_self (h : I.IsHomogeneous 𝒜) :
    (I.homogeneousCore 𝒜).toIdeal = I := by
  apply le_antisymmₓ (I.homogeneous_core'_le 𝒜) _
  intro x hx
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun j hj => Ideal.subset_span ⟨⟨_, is_homogeneous_coe _⟩, h _ hx, rfl⟩

@[simp]
theorem HomogeneousIdeal.to_ideal_homogeneous_core_eq_self (I : HomogeneousIdeal 𝒜) : I.toIdeal.homogeneousCore 𝒜 = I :=
  by
  ext1 <;> convert Ideal.IsHomogeneous.to_ideal_homogeneous_core_eq_self I.is_homogeneous

variable (𝒜 I)

theorem Ideal.IsHomogeneous.iff_eq : I.IsHomogeneous 𝒜 ↔ (I.homogeneousCore 𝒜).toIdeal = I :=
  ⟨fun hI => hI.to_ideal_homogeneous_core_eq_self, fun hI => hI ▸ (Ideal.homogeneousCore 𝒜 I).2⟩

theorem Ideal.IsHomogeneous.iff_exists :
    I.IsHomogeneous 𝒜 ↔ ∃ S : Set (homogeneousSubmonoid 𝒜), I = Ideal.span (coe '' S) := by
  rw [Ideal.IsHomogeneous.iff_eq, eq_comm]
  exact ((set.image_preimage.compose (Submodule.gi _ _).gc).exists_eq_l _).symm

end IsHomogeneousIdealDefs

/-! ### Operations

In this section, we show that `ideal.is_homogeneous` is preserved by various notations, then use
these results to provide these notation typeclasses for `homogeneous_ideal`. -/


section Operations

section Semiringₓ

variable [Semiringₓ A] [DecidableEq ι] [AddMonoidₓ ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

include A

namespace Ideal.IsHomogeneous

theorem bot : Ideal.IsHomogeneous 𝒜 ⊥ := fun i r hr => by
  simp only [← Ideal.mem_bot] at hr
  rw [hr, decompose_zero, zero_apply]
  apply Ideal.zero_mem

theorem top : Ideal.IsHomogeneous 𝒜 ⊤ := fun i r hr => by
  simp only [← Submodule.mem_top]

variable {𝒜}

theorem inf {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) : (I⊓J).IsHomogeneous 𝒜 := fun i r hr =>
  ⟨HI _ hr.1, HJ _ hr.2⟩

theorem sup {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) : (I⊔J).IsHomogeneous 𝒜 := by
  rw [iff_exists] at HI HJ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  refine' ⟨s₁ ∪ s₂, _⟩
  rw [Set.image_union]
  exact (Submodule.span_union _ _).symm

protected theorem supr {κ : Sort _} {f : κ → Ideal A} (h : ∀ i, (f i).IsHomogeneous 𝒜) : (⨆ i, f i).IsHomogeneous 𝒜 :=
  by
  simp_rw [iff_exists] at h⊢
  choose s hs using h
  refine' ⟨⋃ i, s i, _⟩
  simp_rw [Set.image_Union, Ideal.span_Union]
  congr
  exact funext hs

protected theorem infi {κ : Sort _} {f : κ → Ideal A} (h : ∀ i, (f i).IsHomogeneous 𝒜) : (⨅ i, f i).IsHomogeneous 𝒜 :=
  by
  intro i x hx
  simp only [← Ideal.mem_infi] at hx⊢
  exact fun j => h _ _ (hx j)

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem supr₂ {κ : Sort _} {κ' : κ → Sort _} {f : ∀ i, κ' i → Ideal A} (h : ∀ i j, (f i j).IsHomogeneous 𝒜) :
    (⨆ (i) (j), f i j).IsHomogeneous 𝒜 :=
  is_homogeneous.supr fun i => is_homogeneous.supr <| h i

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem infi₂ {κ : Sort _} {κ' : κ → Sort _} {f : ∀ i, κ' i → Ideal A} (h : ∀ i j, (f i j).IsHomogeneous 𝒜) :
    (⨅ (i) (j), f i j).IsHomogeneous 𝒜 :=
  is_homogeneous.infi fun i => is_homogeneous.infi <| h i

theorem Sup {ℐ : Set (Ideal A)} (h : ∀, ∀ I ∈ ℐ, ∀, Ideal.IsHomogeneous 𝒜 I) : (sup ℐ).IsHomogeneous 𝒜 := by
  rw [Sup_eq_supr]
  exact supr₂ h

theorem Inf {ℐ : Set (Ideal A)} (h : ∀, ∀ I ∈ ℐ, ∀, Ideal.IsHomogeneous 𝒜 I) : (inf ℐ).IsHomogeneous 𝒜 := by
  rw [Inf_eq_infi]
  exact infi₂ h

end Ideal.IsHomogeneous

variable {𝒜}

namespace HomogeneousIdeal

instance : PartialOrderₓ (HomogeneousIdeal 𝒜) :=
  SetLike.partialOrder

instance : HasTop (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊤, Ideal.IsHomogeneous.top 𝒜⟩⟩

instance : HasBot (HomogeneousIdeal 𝒜) :=
  ⟨⟨⊥, Ideal.IsHomogeneous.bot 𝒜⟩⟩

instance : HasSup (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.IsHomogeneous.sup J.IsHomogeneous⟩⟩

instance : HasInf (HomogeneousIdeal 𝒜) :=
  ⟨fun I J => ⟨_, I.IsHomogeneous.inf J.IsHomogeneous⟩⟩

instance : HasSupₓ (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨆ s ∈ S, toIdeal s, Ideal.IsHomogeneous.supr₂ fun s _ => s.IsHomogeneous⟩⟩

instance : HasInfₓ (HomogeneousIdeal 𝒜) :=
  ⟨fun S => ⟨⨅ s ∈ S, toIdeal s, Ideal.IsHomogeneous.infi₂ fun s _ => s.IsHomogeneous⟩⟩

@[simp]
theorem coe_top : ((⊤ : HomogeneousIdeal 𝒜) : Set A) = univ :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : HomogeneousIdeal 𝒜) : Set A) = 0 :=
  rfl

@[simp]
theorem coe_sup (I J : HomogeneousIdeal 𝒜) : ↑(I⊔J) = (I + J : Set A) :=
  Submodule.coe_sup _ _

@[simp]
theorem coe_inf (I J : HomogeneousIdeal 𝒜) : (↑(I⊓J) : Set A) = I ∩ J :=
  rfl

@[simp]
theorem to_ideal_top : (⊤ : HomogeneousIdeal 𝒜).toIdeal = (⊤ : Ideal A) :=
  rfl

@[simp]
theorem to_ideal_bot : (⊥ : HomogeneousIdeal 𝒜).toIdeal = (⊥ : Ideal A) :=
  rfl

@[simp]
theorem to_ideal_sup (I J : HomogeneousIdeal 𝒜) : (I⊔J).toIdeal = I.toIdeal⊔J.toIdeal :=
  rfl

@[simp]
theorem to_ideal_inf (I J : HomogeneousIdeal 𝒜) : (I⊓J).toIdeal = I.toIdeal⊓J.toIdeal :=
  rfl

@[simp]
theorem to_ideal_Sup (ℐ : Set (HomogeneousIdeal 𝒜)) : (sup ℐ).toIdeal = ⨆ s ∈ ℐ, toIdeal s :=
  rfl

@[simp]
theorem to_ideal_Inf (ℐ : Set (HomogeneousIdeal 𝒜)) : (inf ℐ).toIdeal = ⨅ s ∈ ℐ, toIdeal s :=
  rfl

@[simp]
theorem to_ideal_supr {κ : Sort _} (s : κ → HomogeneousIdeal 𝒜) : (⨆ i, s i).toIdeal = ⨆ i, (s i).toIdeal := by
  rw [supr, to_ideal_Sup, supr_range]

@[simp]
theorem to_ideal_infi {κ : Sort _} (s : κ → HomogeneousIdeal 𝒜) : (⨅ i, s i).toIdeal = ⨅ i, (s i).toIdeal := by
  rw [infi, to_ideal_Inf, infi_range]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem to_ideal_supr₂ {κ : Sort _} {κ' : κ → Sort _} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨆ (i) (j), s i j).toIdeal = ⨆ (i) (j), (s i j).toIdeal := by
  simp_rw [to_ideal_supr]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem to_ideal_infi₂ {κ : Sort _} {κ' : κ → Sort _} (s : ∀ i, κ' i → HomogeneousIdeal 𝒜) :
    (⨅ (i) (j), s i j).toIdeal = ⨅ (i) (j), (s i j).toIdeal := by
  simp_rw [to_ideal_infi]

@[simp]
theorem eq_top_iff (I : HomogeneousIdeal 𝒜) : I = ⊤ ↔ I.toIdeal = ⊤ :=
  to_ideal_injective.eq_iff.symm

@[simp]
theorem eq_bot_iff (I : HomogeneousIdeal 𝒜) : I = ⊥ ↔ I.toIdeal = ⊥ :=
  to_ideal_injective.eq_iff.symm

instance : CompleteLattice (HomogeneousIdeal 𝒜) :=
  to_ideal_injective.CompleteLattice _ to_ideal_sup to_ideal_inf to_ideal_Sup to_ideal_Inf to_ideal_top to_ideal_bot

instance : Add (HomogeneousIdeal 𝒜) :=
  ⟨(·⊔·)⟩

@[simp]
theorem to_ideal_add (I J : HomogeneousIdeal 𝒜) : (I + J).toIdeal = I.toIdeal + J.toIdeal :=
  rfl

instance : Inhabited (HomogeneousIdeal 𝒜) where default := ⊥

end HomogeneousIdeal

end Semiringₓ

section CommSemiringₓ

variable [CommSemiringₓ A]

variable [DecidableEq ι] [AddMonoidₓ ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] {𝒜 : ι → σ} [GradedRing 𝒜]

variable (I : Ideal A)

include A

theorem Ideal.IsHomogeneous.mul {I J : Ideal A} (HI : I.IsHomogeneous 𝒜) (HJ : J.IsHomogeneous 𝒜) :
    (I * J).IsHomogeneous 𝒜 := by
  rw [Ideal.IsHomogeneous.iff_exists] at HI HJ⊢
  obtain ⟨⟨s₁, rfl⟩, ⟨s₂, rfl⟩⟩ := HI, HJ
  rw [Ideal.span_mul_span']
  exact ⟨s₁ * s₂, congr_arg _ <| (Set.image_mul (homogeneous_submonoid 𝒜).Subtype).symm⟩

variable {𝒜}

instance : Mul (HomogeneousIdeal 𝒜) where mul := fun I J => ⟨I.toIdeal * J.toIdeal, I.IsHomogeneous.mul J.IsHomogeneous⟩

@[simp]
theorem HomogeneousIdeal.to_ideal_mul (I J : HomogeneousIdeal 𝒜) : (I * J).toIdeal = I.toIdeal * J.toIdeal :=
  rfl

end CommSemiringₓ

end Operations

/-! ### Homogeneous core

Note that many results about the homogeneous core came earlier in this file, as they are helpful
for building the lattice structure. -/


section HomogeneousCore

open HomogeneousIdeal

variable [Semiringₓ A] [DecidableEq ι] [AddMonoidₓ ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

variable (I : Ideal A)

include A

theorem Ideal.homogeneousCore.gc : GaloisConnection toIdeal (Ideal.homogeneousCore 𝒜) := fun I J =>
  ⟨fun H => I.to_ideal_homogeneous_core_eq_self ▸ Ideal.homogeneous_core_mono 𝒜 H, fun H =>
    le_transₓ H (Ideal.homogeneous_core'_le _ _)⟩

/-- `to_ideal : homogeneous_ideal 𝒜 → ideal A` and `ideal.homogeneous_core 𝒜` forms a galois
coinsertion-/
def Ideal.homogeneousCore.gi : GaloisCoinsertion toIdeal (Ideal.homogeneousCore 𝒜) where
  choice := fun I HI => ⟨I, le_antisymmₓ (I.to_ideal_homogeneous_core_le 𝒜) HI ▸ HomogeneousIdeal.is_homogeneous _⟩
  gc := Ideal.homogeneousCore.gc 𝒜
  u_l_le := fun I => Ideal.homogeneous_core'_le _ _
  choice_eq := fun I H => le_antisymmₓ H (I.to_ideal_homogeneous_core_le _)

theorem Ideal.homogeneous_core_eq_Sup : I.homogeneousCore 𝒜 = sup { J : HomogeneousIdeal 𝒜 | J.toIdeal ≤ I } :=
  Eq.symm <| IsLub.Sup_eq <| (Ideal.homogeneousCore.gc 𝒜).is_greatest_u.IsLub

theorem Ideal.homogeneous_core'_eq_Sup : I.homogeneousCore' 𝒜 = sup { J : Ideal A | J.IsHomogeneous 𝒜 ∧ J ≤ I } := by
  refine' (IsLub.Sup_eq _).symm
  apply IsGreatest.is_lub
  have coe_mono : Monotone (to_ideal : HomogeneousIdeal 𝒜 → Ideal A) := fun x y => id
  convert coe_mono.map_is_greatest (Ideal.homogeneousCore.gc 𝒜).is_greatest_u using 1
  ext
  rw [mem_image, mem_set_of_eq]
  refine'
    ⟨fun hI => ⟨⟨x, hI.1⟩, ⟨hI.2, rfl⟩⟩, by
      rintro ⟨x, ⟨hx, rfl⟩⟩ <;> exact ⟨x.is_homogeneous, hx⟩⟩

end HomogeneousCore

/-! ### Homogeneous hulls -/


section HomogeneousHull

open HomogeneousIdeal

variable [Semiringₓ A] [DecidableEq ι] [AddMonoidₓ ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

variable (I : Ideal A)

include A

/-- For any `I : ideal A`, not necessarily homogeneous, `I.homogeneous_hull 𝒜` is
the smallest homogeneous ideal containing `I`. -/
def Ideal.homogeneousHull : HomogeneousIdeal 𝒜 :=
  ⟨Ideal.span { r : A | ∃ (i : ι)(x : I), (DirectSum.decompose 𝒜 (x : A) i : A) = r }, by
    refine' Ideal.is_homogeneous_span _ _ fun x hx => _
    obtain ⟨i, x, rfl⟩ := hx
    apply SetLike.is_homogeneous_coe⟩

theorem Ideal.le_to_ideal_homogeneous_hull : I ≤ (Ideal.homogeneousHull 𝒜 I).toIdeal := by
  intro r hr
  classical
  rw [← DirectSum.sum_support_decompose 𝒜 r]
  refine' Ideal.sum_mem _ _
  intro j hj
  apply Ideal.subset_span
  use j
  use ⟨r, hr⟩
  rfl

theorem Ideal.homogeneous_hull_mono : Monotone (Ideal.homogeneousHull 𝒜) := fun I J I_le_J => by
  apply Ideal.span_mono
  rintro r ⟨hr1, ⟨x, hx⟩, rfl⟩
  refine' ⟨hr1, ⟨⟨x, I_le_J hx⟩, rfl⟩⟩

variable {I 𝒜}

theorem Ideal.IsHomogeneous.to_ideal_homogeneous_hull_eq_self (h : I.IsHomogeneous 𝒜) :
    (Ideal.homogeneousHull 𝒜 I).toIdeal = I := by
  apply le_antisymmₓ _ (Ideal.le_to_ideal_homogeneous_hull _ _)
  apply Ideal.span_le.2
  rintro _ ⟨i, x, rfl⟩
  exact h _ x.prop

@[simp]
theorem HomogeneousIdeal.homogeneous_hull_to_ideal_eq_self (I : HomogeneousIdeal 𝒜) : I.toIdeal.homogeneousHull 𝒜 = I :=
  HomogeneousIdeal.to_ideal_injective <| I.IsHomogeneous.to_ideal_homogeneous_hull_eq_self

variable (I 𝒜)

theorem Ideal.to_ideal_homogeneous_hull_eq_supr :
    (I.homogeneousHull 𝒜).toIdeal = ⨆ i, Ideal.span (GradedRing.proj 𝒜 i '' I) := by
  rw [← Ideal.span_Union]
  apply congr_arg Ideal.span _
  ext1
  simp only [← Set.mem_Union, ← Set.mem_image, ← mem_set_of_eq, ← GradedRing.proj_apply, ← SetLike.exists, ←
    exists_prop, ← Subtype.coe_mk, ← SetLike.mem_coe]

theorem Ideal.homogeneous_hull_eq_supr :
    I.homogeneousHull 𝒜 =
      ⨆ i,
        ⟨Ideal.span (GradedRing.proj 𝒜 i '' I),
          Ideal.is_homogeneous_span 𝒜 _
            (by
              rintro _ ⟨x, -, rfl⟩
              apply SetLike.is_homogeneous_coe)⟩ :=
  by
  ext1
  rw [Ideal.to_ideal_homogeneous_hull_eq_supr, to_ideal_supr]
  rfl

end HomogeneousHull

section GaloisConnection

open HomogeneousIdeal

variable [Semiringₓ A] [DecidableEq ι] [AddMonoidₓ ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

include A

theorem Ideal.homogeneousHull.gc : GaloisConnection (Ideal.homogeneousHull 𝒜) toIdeal := fun I J =>
  ⟨le_transₓ (Ideal.le_to_ideal_homogeneous_hull _ _), fun H =>
    J.homogeneous_hull_to_ideal_eq_self ▸ Ideal.homogeneous_hull_mono 𝒜 H⟩

/-- `ideal.homogeneous_hull 𝒜` and `to_ideal : homogeneous_ideal 𝒜 → ideal A` form a galois
insertion-/
def Ideal.homogeneousHull.gi : GaloisInsertion (Ideal.homogeneousHull 𝒜) toIdeal where
  choice := fun I H => ⟨I, le_antisymmₓ H (I.le_to_ideal_homogeneous_hull 𝒜) ▸ is_homogeneous _⟩
  gc := Ideal.homogeneousHull.gc 𝒜
  le_l_u := fun I => Ideal.le_to_ideal_homogeneous_hull _ _
  choice_eq := fun I H => le_antisymmₓ (I.le_to_ideal_homogeneous_hull 𝒜) H

theorem Ideal.homogeneous_hull_eq_Inf (I : Ideal A) :
    Ideal.homogeneousHull 𝒜 I = inf { J : HomogeneousIdeal 𝒜 | I ≤ J.toIdeal } :=
  Eq.symm <| IsGlb.Inf_eq <| (Ideal.homogeneousHull.gc 𝒜).is_least_l.IsGlb

end GaloisConnection

section IrrelevantIdeal

variable [Semiringₓ A]

variable [DecidableEq ι]

variable [CanonicallyOrderedAddMonoid ι]

variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

include A

open GradedRing SetLike.GradedMonoid DirectSum

/-- For a graded ring `⨁ᵢ 𝒜ᵢ` graded by a `canonically_ordered_add_monoid ι`, the irrelevant ideal
refers to `⨁_{i>0} 𝒜ᵢ`, or equivalently `{a | a₀ = 0}`. This definition is used in `Proj`
construction where `ι` is always `ℕ` so the irrelevant ideal is simply elements with `0` as
0-th coordinate.

# Future work
Here in the definition, `ι` is assumed to be `canonically_ordered_add_monoid`. However, the notion
of irrelevant ideal makes sense in a more general setting by defining it as the ideal of elements
with `0` as i-th coordinate for all `i ≤ 0`, i.e. `{a | ∀ (i : ι), i ≤ 0 → aᵢ = 0}`.
-/
def HomogeneousIdeal.irrelevant : HomogeneousIdeal 𝒜 :=
  ⟨(GradedRing.projZeroRingHom 𝒜).ker, fun i r (hr : (decompose 𝒜 r 0 : A) = 0) => by
    change (decompose 𝒜 (decompose 𝒜 r _ : A) 0 : A) = 0
    by_cases' h : i = 0
    · rw [h, hr, decompose_zero, zero_apply, AddSubmonoidClass.coe_zero]
      
    · rw [decompose_of_mem_ne 𝒜 (SetLike.coe_mem _) h]
      ⟩

@[simp]
theorem HomogeneousIdeal.mem_irrelevant_iff (a : A) : a ∈ HomogeneousIdeal.irrelevant 𝒜 ↔ proj 𝒜 0 a = 0 :=
  Iff.rfl

@[simp]
theorem HomogeneousIdeal.to_ideal_irrelevant :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal = (GradedRing.projZeroRingHom 𝒜).ker :=
  rfl

end IrrelevantIdeal

