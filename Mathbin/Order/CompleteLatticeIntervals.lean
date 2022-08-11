/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Data.Set.Intervals.OrdConnected

/-! # Subtypes of conditionally complete linear orders

In this file we give conditions on a subset of a conditionally complete linear order, to ensure that
the subtype is itself conditionally complete.

We check that an `ord_connected` set satisfies these conditions.

## TODO

Add appropriate instances for all `set.Ixx`. This requires a refactor that will allow different
default values for `Sup` and `Inf`.
-/


open Classical

open Set

variable {α : Type _} (s : Set α)

section HasSupₓ

variable [HasSupₓ α]

/-- `has_Sup` structure on a nonempty subset `s` of an object with `has_Sup`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetHasSup [Inhabited s] :
    HasSupₓ s where sup := fun t => if ht : sup (coe '' t : Set α) ∈ s then ⟨sup (coe '' t : Set α), ht⟩ else default

attribute [local instance] subsetHasSup

@[simp]
theorem subset_Sup_def [Inhabited s] :
    @sup s _ = fun t => if ht : sup (coe '' t : Set α) ∈ s then ⟨sup (coe '' t : Set α), ht⟩ else default :=
  rfl

theorem subset_Sup_of_within [Inhabited s] {t : Set s} (h : sup (coe '' t : Set α) ∈ s) :
    sup (coe '' t : Set α) = (@sup s _ t : α) := by
  simp [← dif_pos h]

end HasSupₓ

section HasInfₓ

variable [HasInfₓ α]

/-- `has_Inf` structure on a nonempty subset `s` of an object with `has_Inf`. This definition is
non-canonical (it uses `default s`); it should be used only as here, as an auxiliary instance in the
construction of the `conditionally_complete_linear_order` structure. -/
noncomputable def subsetHasInf [Inhabited s] :
    HasInfₓ s where inf := fun t => if ht : inf (coe '' t : Set α) ∈ s then ⟨inf (coe '' t : Set α), ht⟩ else default

attribute [local instance] subsetHasInf

@[simp]
theorem subset_Inf_def [Inhabited s] :
    @inf s _ = fun t => if ht : inf (coe '' t : Set α) ∈ s then ⟨inf (coe '' t : Set α), ht⟩ else default :=
  rfl

theorem subset_Inf_of_within [Inhabited s] {t : Set s} (h : inf (coe '' t : Set α) ∈ s) :
    inf (coe '' t : Set α) = (@inf s _ t : α) := by
  simp [← dif_pos h]

end HasInfₓ

variable [ConditionallyCompleteLinearOrder α]

attribute [local instance] subsetHasSup

attribute [local instance] subsetHasInf

/-- For a nonempty subset of a conditionally complete linear order to be a conditionally complete
linear order, it suffices that it contain the `Sup` of all its nonempty bounded-above subsets, and
the `Inf` of all its nonempty bounded-below subsets.
See note [reducible non-instances]. -/
@[reducible]
noncomputable def subsetConditionallyCompleteLinearOrder [Inhabited s]
    (h_Sup : ∀ {t : Set s} (ht : t.Nonempty) (h_bdd : BddAbove t), sup (coe '' t : Set α) ∈ s)
    (h_Inf : ∀ {t : Set s} (ht : t.Nonempty) (h_bdd : BddBelow t), inf (coe '' t : Set α) ∈ s) :
    ConditionallyCompleteLinearOrder s :=
  { -- The following would be a more natural way to finish, but gives a "deep recursion" error:
      -- simpa [subset_Sup_of_within (h_Sup t)] using
      --   (strict_mono_coe s).monotone.le_cSup_image hct h_bdd,
      subsetHasSup
      s,
    subsetHasInf s, DistribLattice.toLattice s, (inferInstance : LinearOrderₓ s) with
    le_cSup := by
      rintro t c h_bdd hct
      have := (Subtype.mono_coe s).le_cSup_image hct h_bdd
      rwa [subset_Sup_of_within s (h_Sup ⟨c, hct⟩ h_bdd)] at this,
    cSup_le := by
      rintro t B ht hB
      have := (Subtype.mono_coe s).cSup_image_le ht hB
      rwa [subset_Sup_of_within s (h_Sup ht ⟨B, hB⟩)] at this,
    le_cInf := by
      intro t B ht hB
      have := (Subtype.mono_coe s).le_cInf_image ht hB
      rwa [subset_Inf_of_within s (h_Inf ht ⟨B, hB⟩)] at this,
    cInf_le := by
      rintro t c h_bdd hct
      have := (Subtype.mono_coe s).cInf_image_le hct h_bdd
      rwa [subset_Inf_of_within s (h_Inf ⟨c, hct⟩ h_bdd)] at this }

section OrdConnected

/-- The `Sup` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-above subsets of `s`. -/
theorem Sup_within_of_ord_connected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddAbove t) : sup (coe '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ UpperBounds t := h_bdd
  refine' hs.out c.2 B.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_cSup_image hct ⟨B, hB⟩
    
  · exact (Subtype.mono_coe s).cSup_image_le ⟨c, hct⟩ hB
    

/-- The `Inf` function on a nonempty `ord_connected` set `s` in a conditionally complete linear
order takes values within `s`, for all nonempty bounded-below subsets of `s`. -/
theorem Inf_within_of_ord_connected {s : Set α} [hs : OrdConnected s] ⦃t : Set s⦄ (ht : t.Nonempty)
    (h_bdd : BddBelow t) : inf (coe '' t : Set α) ∈ s := by
  obtain ⟨c, hct⟩ : ∃ c, c ∈ t := ht
  obtain ⟨B, hB⟩ : ∃ B, B ∈ LowerBounds t := h_bdd
  refine' hs.out B.2 c.2 ⟨_, _⟩
  · exact (Subtype.mono_coe s).le_cInf_image ⟨c, hct⟩ hB
    
  · exact (Subtype.mono_coe s).cInf_image_le hct ⟨B, hB⟩
    

/-- A nonempty `ord_connected` set in a conditionally complete linear order is naturally a
conditionally complete linear order. -/
noncomputable instance ordConnectedSubsetConditionallyCompleteLinearOrder [Inhabited s] [OrdConnected s] :
    ConditionallyCompleteLinearOrder s :=
  subsetConditionallyCompleteLinearOrder s Sup_within_of_ord_connected Inf_within_of_ord_connected

end OrdConnected

