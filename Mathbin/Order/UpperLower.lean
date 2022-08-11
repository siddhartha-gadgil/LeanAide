/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
import Mathbin.Data.SetLike.Basic
import Mathbin.Order.Hom.CompleteLattice

/-!
# Up-sets and down-sets

This file defines upper and lower sets in an order.

## Main declarations

* `is_upper_set`: Predicate for a set to be an upper set. This means every element greater than a
  member of the set is in the set itself.
* `is_lower_set`: Predicate for a set to be a lower set. This means every element less than a member
  of the set is in the set itself.
* `upper_set`: The type of upper sets.
* `lower_set`: The type of lower sets.
* `upper_set.Ici`: Principal upper set. `set.Ici` as an upper set.
* `upper_set.Ioi`: Strict principal upper set. `set.Ioi` as an upper set.
* `lower_set.Iic`: Principal lower set. `set.Iic` as an lower set.
* `lower_set.Iio`: Strict principal lower set. `set.Iio` as an lower set.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `filter`.

## TODO

Lattice structure on antichains. Order equivalence between upper/lower sets and antichains.
-/


open OrderDual Set

variable {α : Type _} {ι : Sort _} {κ : ι → Sort _}

/-! ### Unbundled upper/lower sets -/


section LE

variable [LE α] {s t : Set α}

/-- An upper set in an order `α` is a set such that any element greater than one of its members is
also a member. Also called up-set, upward-closed set. -/
def IsUpperSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ≤ b → a ∈ s → b ∈ s

/-- A lower set in an order `α` is a set such that any element less than one of its members is also
a member. Also called down-set, downward-closed set. -/
def IsLowerSet (s : Set α) : Prop :=
  ∀ ⦃a b : α⦄, b ≤ a → a ∈ s → b ∈ s

theorem is_upper_set_empty : IsUpperSet (∅ : Set α) := fun _ _ _ => id

theorem is_lower_set_empty : IsLowerSet (∅ : Set α) := fun _ _ _ => id

theorem is_upper_set_univ : IsUpperSet (Univ : Set α) := fun _ _ _ => id

theorem is_lower_set_univ : IsLowerSet (Univ : Set α) := fun _ _ _ => id

theorem IsUpperSet.compl (hs : IsUpperSet s) : IsLowerSet (sᶜ) := fun a b h hb ha => hb <| hs h ha

theorem IsLowerSet.compl (hs : IsLowerSet s) : IsUpperSet (sᶜ) := fun a b h hb ha => hb <| hs h ha

@[simp]
theorem is_upper_set_compl : IsUpperSet (sᶜ) ↔ IsLowerSet s :=
  ⟨fun h => by
    convert h.compl
    rw [compl_compl], IsLowerSet.compl⟩

@[simp]
theorem is_lower_set_compl : IsLowerSet (sᶜ) ↔ IsUpperSet s :=
  ⟨fun h => by
    convert h.compl
    rw [compl_compl], IsUpperSet.compl⟩

theorem IsUpperSet.union (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∪ t) := fun a b h =>
  Or.imp (hs h) (ht h)

theorem IsLowerSet.union (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∪ t) := fun a b h =>
  Or.imp (hs h) (ht h)

theorem IsUpperSet.inter (hs : IsUpperSet s) (ht : IsUpperSet t) : IsUpperSet (s ∩ t) := fun a b h =>
  And.imp (hs h) (ht h)

theorem IsLowerSet.inter (hs : IsLowerSet s) (ht : IsLowerSet t) : IsLowerSet (s ∩ t) := fun a b h =>
  And.imp (hs h) (ht h)

theorem is_upper_set_Union {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋃ i, f i) := fun a b h =>
  Exists₂.imp <| forall_range_iff.2 fun i => hf i h

theorem is_lower_set_Union {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋃ i, f i) := fun a b h =>
  Exists₂.imp <| forall_range_iff.2 fun i => hf i h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem is_upper_set_Union₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) : IsUpperSet (⋃ (i) (j), f i j) :=
  is_upper_set_Union fun i => is_upper_set_Union <| hf i

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem is_lower_set_Union₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) : IsLowerSet (⋃ (i) (j), f i j) :=
  is_lower_set_Union fun i => is_lower_set_Union <| hf i

theorem is_upper_set_sUnion {S : Set (Set α)} (hf : ∀, ∀ s ∈ S, ∀, IsUpperSet s) : IsUpperSet (⋃₀S) := fun a b h =>
  Exists₂.imp fun s hs => hf s hs h

theorem is_lower_set_sUnion {S : Set (Set α)} (hf : ∀, ∀ s ∈ S, ∀, IsLowerSet s) : IsLowerSet (⋃₀S) := fun a b h =>
  Exists₂.imp fun s hs => hf s hs h

theorem is_upper_set_Inter {f : ι → Set α} (hf : ∀ i, IsUpperSet (f i)) : IsUpperSet (⋂ i, f i) := fun a b h =>
  forall₂_imp <| forall_range_iff.2 fun i => hf i h

theorem is_lower_set_Inter {f : ι → Set α} (hf : ∀ i, IsLowerSet (f i)) : IsLowerSet (⋂ i, f i) := fun a b h =>
  forall₂_imp <| forall_range_iff.2 fun i => hf i h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem is_upper_set_Inter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsUpperSet (f i j)) : IsUpperSet (⋂ (i) (j), f i j) :=
  is_upper_set_Inter fun i => is_upper_set_Inter <| hf i

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
theorem is_lower_set_Inter₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsLowerSet (f i j)) : IsLowerSet (⋂ (i) (j), f i j) :=
  is_lower_set_Inter fun i => is_lower_set_Inter <| hf i

theorem is_upper_set_sInter {S : Set (Set α)} (hf : ∀, ∀ s ∈ S, ∀, IsUpperSet s) : IsUpperSet (⋂₀ S) := fun a b h =>
  forall₂_imp fun s hs => hf s hs h

theorem is_lower_set_sInter {S : Set (Set α)} (hf : ∀, ∀ s ∈ S, ∀, IsLowerSet s) : IsLowerSet (⋂₀ S) := fun a b h =>
  forall₂_imp fun s hs => hf s hs h

@[simp]
theorem is_lower_set_preimage_of_dual_iff : IsLowerSet (of_dual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
theorem is_upper_set_preimage_of_dual_iff : IsUpperSet (of_dual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

@[simp]
theorem is_lower_set_preimage_to_dual_iff {s : Set αᵒᵈ} : IsLowerSet (to_dual ⁻¹' s) ↔ IsUpperSet s :=
  Iff.rfl

@[simp]
theorem is_upper_set_preimage_to_dual_iff {s : Set αᵒᵈ} : IsUpperSet (to_dual ⁻¹' s) ↔ IsLowerSet s :=
  Iff.rfl

alias is_lower_set_preimage_of_dual_iff ↔ _ IsUpperSet.of_dual

alias is_upper_set_preimage_of_dual_iff ↔ _ IsLowerSet.of_dual

alias is_lower_set_preimage_to_dual_iff ↔ _ IsUpperSet.to_dual

alias is_upper_set_preimage_to_dual_iff ↔ _ IsLowerSet.to_dual

end LE

section Preorderₓ

variable [Preorderₓ α] (a : α)

theorem is_upper_set_Ici : IsUpperSet (Ici a) := fun _ _ => ge_transₓ

theorem is_lower_set_Iic : IsLowerSet (Iic a) := fun _ _ => le_transₓ

theorem is_upper_set_Ioi : IsUpperSet (Ioi a) := fun _ _ => flip lt_of_lt_of_leₓ

theorem is_lower_set_Iio : IsLowerSet (Iio a) := fun _ _ => lt_of_le_of_ltₓ

section OrderTop

variable [OrderTop α] {s : Set α}

theorem IsLowerSet.top_mem (hs : IsLowerSet s) : ⊤ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun a => hs le_top h, fun h => h.symm ▸ mem_univ _⟩

theorem IsUpperSet.top_mem (hs : IsUpperSet s) : ⊤ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨a, ha⟩ => hs le_top ha⟩

theorem IsUpperSet.not_top_mem (hs : IsUpperSet s) : ⊤ ∉ s ↔ s = ∅ :=
  hs.top_mem.Not.trans not_nonempty_iff_eq_empty

end OrderTop

section OrderBot

variable [OrderBot α] {s : Set α}

theorem IsUpperSet.bot_mem (hs : IsUpperSet s) : ⊥ ∈ s ↔ s = univ :=
  ⟨fun h => eq_univ_of_forall fun a => hs bot_le h, fun h => h.symm ▸ mem_univ _⟩

theorem IsLowerSet.bot_mem (hs : IsLowerSet s) : ⊥ ∈ s ↔ s.Nonempty :=
  ⟨fun h => ⟨_, h⟩, fun ⟨a, ha⟩ => hs bot_le ha⟩

theorem IsLowerSet.not_bot_mem (hs : IsLowerSet s) : ⊥ ∉ s ↔ s = ∅ :=
  hs.bot_mem.Not.trans not_nonempty_iff_eq_empty

end OrderBot

end Preorderₓ

/-! ### Bundled upper/lower sets -/


section LE

variable [LE α]

/-- The type of upper sets of an order. -/
structure UpperSet (α : Type _) [LE α] where
  Carrier : Set α
  upper' : IsUpperSet carrier

/-- The type of lower sets of an order. -/
structure LowerSet (α : Type _) [LE α] where
  Carrier : Set α
  lower' : IsLowerSet carrier

namespace UpperSet

instance : SetLike (UpperSet α) α where
  coe := UpperSet.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

@[ext]
theorem ext {s t : UpperSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

@[simp]
theorem carrier_eq_coe (s : UpperSet α) : s.Carrier = s :=
  rfl

protected theorem upper (s : UpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'

end UpperSet

namespace LowerSet

instance : SetLike (LowerSet α) α where
  coe := LowerSet.Carrier
  coe_injective' := fun s t h => by
    cases s
    cases t
    congr

@[ext]
theorem ext {s t : LowerSet α} : (s : Set α) = t → s = t :=
  SetLike.ext'

@[simp]
theorem carrier_eq_coe (s : LowerSet α) : s.Carrier = s :=
  rfl

protected theorem lower (s : LowerSet α) : IsLowerSet (s : Set α) :=
  s.lower'

end LowerSet

/-! #### Order -/


namespace UpperSet

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

instance : HasSup (UpperSet α) :=
  ⟨fun s t => ⟨s ∩ t, s.upper.inter t.upper⟩⟩

instance : HasInf (UpperSet α) :=
  ⟨fun s t => ⟨s ∪ t, s.upper.union t.upper⟩⟩

instance : HasTop (UpperSet α) :=
  ⟨⟨∅, is_upper_set_empty⟩⟩

instance : HasBot (UpperSet α) :=
  ⟨⟨Univ, is_upper_set_univ⟩⟩

instance : HasSupₓ (UpperSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, is_upper_set_Inter₂ fun s _ => s.upper⟩⟩

instance : HasInfₓ (UpperSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, is_upper_set_Union₂ fun s _ => s.upper⟩⟩

instance : CompleteDistribLattice (UpperSet α) :=
  (toDual.Injective.comp <| SetLike.coe_injective).CompleteDistribLattice _ (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[simp]
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_sup (s t : UpperSet α) : (↑(s⊔t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_inf (s t : UpperSet α) : (↑(s⊓t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_Sup (S : Set (UpperSet α)) : (↑(sup S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp]
theorem coe_Inf (S : Set (UpperSet α)) : (↑(inf S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl

@[simp]
theorem coe_supr (f : ι → UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by
  simp [← supr]

@[simp]
theorem coe_infi (f : ι → UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by
  simp [← infi]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem coe_supr₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by
  simp_rw [coe_supr]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem coe_infi₂ (f : ∀ i, κ i → UpperSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by
  simp_rw [coe_infi]

@[simp]
theorem not_mem_top : a ∉ (⊤ : UpperSet α) :=
  id

@[simp]
theorem mem_bot : a ∈ (⊥ : UpperSet α) :=
  trivialₓ

@[simp]
theorem mem_sup_iff : a ∈ s⊔t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_inf_iff : a ∈ s⊓t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_Sup_iff : a ∈ sup S ↔ ∀, ∀ s ∈ S, ∀, a ∈ s :=
  mem_Inter₂

@[simp]
theorem mem_Inf_iff : a ∈ inf S ↔ ∃ s ∈ S, a ∈ s :=
  mem_Union₂

@[simp]
theorem mem_supr_iff {f : ι → UpperSet α} : (a ∈ ⨆ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_supr]
  exact mem_Inter

@[simp]
theorem mem_infi_iff {f : ι → UpperSet α} : (a ∈ ⨅ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_infi]
  exact mem_Union

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem mem_supr₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_supr_iff]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem mem_infi₂_iff {f : ∀ i, κ i → UpperSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_infi_iff]

end UpperSet

namespace LowerSet

variable {S : Set (LowerSet α)} {s t : LowerSet α} {a : α}

instance : HasSup (LowerSet α) :=
  ⟨fun s t => ⟨s ∪ t, fun a b h => Or.imp (s.lower h) (t.lower h)⟩⟩

instance : HasInf (LowerSet α) :=
  ⟨fun s t => ⟨s ∩ t, fun a b h => And.imp (s.lower h) (t.lower h)⟩⟩

instance : HasTop (LowerSet α) :=
  ⟨⟨Univ, fun a b h => id⟩⟩

instance : HasBot (LowerSet α) :=
  ⟨⟨∅, fun a b h => id⟩⟩

instance : HasSupₓ (LowerSet α) :=
  ⟨fun S => ⟨⋃ s ∈ S, ↑s, is_lower_set_Union₂ fun s _ => s.lower⟩⟩

instance : HasInfₓ (LowerSet α) :=
  ⟨fun S => ⟨⋂ s ∈ S, ↑s, is_lower_set_Inter₂ fun s _ => s.lower⟩⟩

instance : CompleteDistribLattice (LowerSet α) :=
  SetLike.coe_injective.CompleteDistribLattice _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

instance : Inhabited (LowerSet α) :=
  ⟨⊥⟩

@[simp]
theorem coe_top : ((⊤ : LowerSet α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : ((⊥ : LowerSet α) : Set α) = ∅ :=
  rfl

@[simp]
theorem coe_sup (s t : LowerSet α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf (s t : LowerSet α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_Sup (S : Set (LowerSet α)) : (↑(sup S) : Set α) = ⋃ s ∈ S, ↑s :=
  rfl

@[simp]
theorem coe_Inf (S : Set (LowerSet α)) : (↑(inf S) : Set α) = ⋂ s ∈ S, ↑s :=
  rfl

@[simp]
theorem coe_supr (f : ι → LowerSet α) : (↑(⨆ i, f i) : Set α) = ⋃ i, f i := by
  simp_rw [supr, coe_Sup, mem_range, Union_exists, Union_Union_eq']

@[simp]
theorem coe_infi (f : ι → LowerSet α) : (↑(⨅ i, f i) : Set α) = ⋂ i, f i := by
  simp_rw [infi, coe_Inf, mem_range, Inter_exists, Inter_Inter_eq']

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem coe_supr₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨆ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by
  simp_rw [coe_supr]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem coe_infi₂ (f : ∀ i, κ i → LowerSet α) : (↑(⨅ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by
  simp_rw [coe_infi]

@[simp]
theorem mem_top : a ∈ (⊤ : LowerSet α) :=
  trivialₓ

@[simp]
theorem not_mem_bot : a ∉ (⊥ : LowerSet α) :=
  id

@[simp]
theorem mem_sup_iff : a ∈ s⊔t ↔ a ∈ s ∨ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_inf_iff : a ∈ s⊓t ↔ a ∈ s ∧ a ∈ t :=
  Iff.rfl

@[simp]
theorem mem_Sup_iff : a ∈ sup S ↔ ∃ s ∈ S, a ∈ s :=
  mem_Union₂

@[simp]
theorem mem_Inf_iff : a ∈ inf S ↔ ∀, ∀ s ∈ S, ∀, a ∈ s :=
  mem_Inter₂

@[simp]
theorem mem_supr_iff {f : ι → LowerSet α} : (a ∈ ⨆ i, f i) ↔ ∃ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_supr]
  exact mem_Union

@[simp]
theorem mem_infi_iff {f : ι → LowerSet α} : (a ∈ ⨅ i, f i) ↔ ∀ i, a ∈ f i := by
  rw [← SetLike.mem_coe, coe_infi]
  exact mem_Inter

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem mem_supr₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨆ (i) (j), f i j) ↔ ∃ i j, a ∈ f i j := by
  simp_rw [mem_supr_iff]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem mem_infi₂_iff {f : ∀ i, κ i → LowerSet α} : (a ∈ ⨅ (i) (j), f i j) ↔ ∀ i j, a ∈ f i j := by
  simp_rw [mem_infi_iff]

end LowerSet

/-! #### Complement -/


/-- The complement of a lower set as an upper set. -/
def UpperSet.compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩

/-- The complement of a lower set as an upper set. -/
def LowerSet.compl (s : LowerSet α) : UpperSet α :=
  ⟨sᶜ, s.lower.compl⟩

namespace UpperSet

variable {s t : UpperSet α} {a : α}

@[simp]
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = sᶜ :=
  rfl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl

@[simp]
theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
  UpperSet.ext <| compl_compl _

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl

@[simp]
protected theorem compl_sup (s t : UpperSet α) : (s⊔t).compl = s.compl⊔t.compl :=
  LowerSet.ext compl_inf

@[simp]
protected theorem compl_inf (s t : UpperSet α) : (s⊓t).compl = s.compl⊓t.compl :=
  LowerSet.ext compl_sup

@[simp]
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty

@[simp]
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ

@[simp]
protected theorem compl_Sup (S : Set (UpperSet α)) : (sup S).compl = ⨆ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by
    simp only [← coe_compl, ← coe_Sup, ← compl_Inter₂, ← LowerSet.coe_supr₂]

@[simp]
protected theorem compl_Inf (S : Set (UpperSet α)) : (inf S).compl = ⨅ s ∈ S, UpperSet.compl s :=
  LowerSet.ext <| by
    simp only [← coe_compl, ← coe_Inf, ← compl_Union₂, ← LowerSet.coe_infi₂]

@[simp]
protected theorem compl_supr (f : ι → UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  LowerSet.ext <| by
    simp only [← coe_compl, ← coe_supr, ← compl_Inter, ← LowerSet.coe_supr]

@[simp]
protected theorem compl_infi (f : ι → UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  LowerSet.ext <| by
    simp only [← coe_compl, ← coe_infi, ← compl_Union, ← LowerSet.coe_infi]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem compl_supr₂ (f : ∀ i, κ i → UpperSet α) : (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by
  simp_rw [UpperSet.compl_supr]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem compl_infi₂ (f : ∀ i, κ i → UpperSet α) : (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by
  simp_rw [UpperSet.compl_infi]

end UpperSet

namespace LowerSet

variable {s t : LowerSet α} {a : α}

@[simp]
theorem coe_compl (s : LowerSet α) : (s.compl : Set α) = sᶜ :=
  rfl

@[simp]
theorem mem_compl_iff : a ∈ s.compl ↔ a ∉ s :=
  Iff.rfl

@[simp]
theorem compl_compl (s : LowerSet α) : s.compl.compl = s :=
  LowerSet.ext <| compl_compl _

@[simp]
theorem compl_le_compl : s.compl ≤ t.compl ↔ s ≤ t :=
  compl_subset_compl

protected theorem compl_sup (s t : LowerSet α) : (s⊔t).compl = s.compl⊔t.compl :=
  UpperSet.ext compl_sup

protected theorem compl_inf (s t : LowerSet α) : (s⊓t).compl = s.compl⊓t.compl :=
  UpperSet.ext compl_inf

protected theorem compl_top : (⊤ : LowerSet α).compl = ⊤ :=
  UpperSet.ext compl_univ

protected theorem compl_bot : (⊥ : LowerSet α).compl = ⊥ :=
  UpperSet.ext compl_empty

protected theorem compl_Sup (S : Set (LowerSet α)) : (sup S).compl = ⨆ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by
    simp only [← coe_compl, ← coe_Sup, ← compl_Union₂, ← UpperSet.coe_supr₂]

protected theorem compl_Inf (S : Set (LowerSet α)) : (inf S).compl = ⨅ s ∈ S, LowerSet.compl s :=
  UpperSet.ext <| by
    simp only [← coe_compl, ← coe_Inf, ← compl_Inter₂, ← UpperSet.coe_infi₂]

protected theorem compl_supr (f : ι → LowerSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
  UpperSet.ext <| by
    simp only [← coe_compl, ← coe_supr, ← compl_Union, ← UpperSet.coe_supr]

protected theorem compl_infi (f : ι → LowerSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
  UpperSet.ext <| by
    simp only [← coe_compl, ← coe_infi, ← compl_Inter, ← UpperSet.coe_infi]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem compl_supr₂ (f : ∀ i, κ i → LowerSet α) : (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by
  simp_rw [LowerSet.compl_supr]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem compl_infi₂ (f : ∀ i, κ i → LowerSet α) : (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by
  simp_rw [LowerSet.compl_infi]

end LowerSet

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
def upperSetIsoLowerSet : UpperSet α ≃o LowerSet α where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := fun _ _ => UpperSet.compl_le_compl

end LE

/-! #### Principal sets -/


namespace UpperSet

section Preorderₓ

variable [Preorderₓ α] {a b : α}

/-- The smallest upper set containing a given element. -/
def ici (a : α) : UpperSet α :=
  ⟨Ici a, is_upper_set_Ici a⟩

/-- The smallest upper set containing a given element. -/
def ioi (a : α) : UpperSet α :=
  ⟨Ioi a, is_upper_set_Ioi a⟩

@[simp]
theorem coe_Ici (a : α) : ↑(ici a) = Set.Ici a :=
  rfl

@[simp]
theorem coe_Ioi (a : α) : ↑(ioi a) = Set.Ioi a :=
  rfl

@[simp]
theorem mem_Ici_iff : b ∈ ici a ↔ a ≤ b :=
  Iff.rfl

@[simp]
theorem mem_Ioi_iff : b ∈ ioi a ↔ a < b :=
  Iff.rfl

theorem Icoi_le_Ioi (a : α) : ici a ≤ ioi a :=
  Ioi_subset_Ici_self

@[simp]
theorem Ioi_top [OrderTop α] : ioi (⊤ : α) = ⊤ :=
  SetLike.coe_injective Ioi_top

@[simp]
theorem Ici_bot [OrderBot α] : ici (⊥ : α) = ⊥ :=
  SetLike.coe_injective Ici_bot

end Preorderₓ

section SemilatticeSup

variable [SemilatticeSup α]

@[simp]
theorem Ici_sup (a b : α) : ici (a⊔b) = ici a⊔ici b :=
  ext Ici_inter_Ici.symm

/-- `upper_set.Ici` as a `sup_hom`. -/
def iciSupHom : SupHom α (UpperSet α) :=
  ⟨ici, Ici_sup⟩

@[simp]
theorem Ici_sup_hom_apply (a : α) : iciSupHom a = ici a :=
  rfl

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Ici_Sup (S : Set α) : ici (sup S) = ⨆ a ∈ S, ici a :=
  SetLike.ext fun c => by
    simp only [← mem_Ici_iff, ← mem_supr_iff, ← Sup_le_iff]

@[simp]
theorem Ici_supr (f : ι → α) : ici (⨆ i, f i) = ⨆ i, ici (f i) :=
  SetLike.ext fun c => by
    simp only [← mem_Ici_iff, ← mem_supr_iff, ← supr_le_iff]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem Ici_supr₂ (f : ∀ i, κ i → α) : ici (⨆ (i) (j), f i j) = ⨆ (i) (j), ici (f i j) := by
  simp_rw [Ici_supr]

/-- `upper_set.Ici` as a `Sup_hom`. -/
def iciSupHomₓ : SupHomₓ α (UpperSet α) :=
  ⟨ici, fun s => (Ici_Sup s).trans Sup_image.symm⟩

@[simp]
theorem Ici_Sup_hom_apply (a : α) : iciSupHomₓ a = toDual (ici a) :=
  rfl

end CompleteLattice

end UpperSet

namespace LowerSet

section Preorderₓ

variable [Preorderₓ α] {a b : α}

/-- Principal lower set. `set.Iic` as a lower set. The smallest lower set containing a given
element. -/
def iic (a : α) : LowerSet α :=
  ⟨Iic a, is_lower_set_Iic a⟩

/-- Strict principal lower set. `set.Iio` as a lower set. -/
def iio (a : α) : LowerSet α :=
  ⟨Iio a, is_lower_set_Iio a⟩

@[simp]
theorem coe_Iic (a : α) : ↑(iic a) = Set.Iic a :=
  rfl

@[simp]
theorem coe_Iio (a : α) : ↑(iio a) = Set.Iio a :=
  rfl

@[simp]
theorem mem_Iic_iff : b ∈ iic a ↔ b ≤ a :=
  Iff.rfl

@[simp]
theorem mem_Iio_iff : b ∈ iio a ↔ b < a :=
  Iff.rfl

theorem Ioi_le_Ici (a : α) : Ioi a ≤ Ici a :=
  Ioi_subset_Ici_self

@[simp]
theorem Iic_top [OrderTop α] : iic (⊤ : α) = ⊤ :=
  SetLike.coe_injective Iic_top

@[simp]
theorem Iio_bot [OrderBot α] : iio (⊥ : α) = ⊥ :=
  SetLike.coe_injective Iio_bot

end Preorderₓ

section SemilatticeInf

variable [SemilatticeInf α]

@[simp]
theorem Iic_inf (a b : α) : iic (a⊓b) = iic a⊓iic b :=
  SetLike.coe_injective Iic_inter_Iic.symm

/-- `lower_set.Iic` as an `inf_hom`. -/
def iicInfHom : InfHom α (LowerSet α) :=
  ⟨iic, Iic_inf⟩

@[simp]
theorem coe_Iic_inf_hom : (iicInfHom : α → LowerSet α) = Iic :=
  rfl

@[simp]
theorem Iic_inf_hom_apply (a : α) : iicInfHom a = iic a :=
  rfl

end SemilatticeInf

section CompleteLattice

variable [CompleteLattice α]

@[simp]
theorem Iic_Inf (S : Set α) : iic (inf S) = ⨅ a ∈ S, iic a :=
  SetLike.ext fun c => by
    simp only [← mem_Iic_iff, ← mem_infi₂_iff, ← le_Inf_iff]

@[simp]
theorem Iic_infi (f : ι → α) : iic (⨅ i, f i) = ⨅ i, iic (f i) :=
  SetLike.ext fun c => by
    simp only [← mem_Iic_iff, ← mem_infi_iff, ← le_infi_iff]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (i j)
@[simp]
theorem Iic_infi₂ (f : ∀ i, κ i → α) : iic (⨅ (i) (j), f i j) = ⨅ (i) (j), iic (f i j) := by
  simp_rw [Iic_infi]

/-- `lower_set.Iic` as an `Inf_hom`. -/
def iicInfHomₓ : InfHomₓ α (LowerSet α) :=
  ⟨iic, fun s => (Iic_Inf s).trans Inf_image.symm⟩

@[simp]
theorem coe_Iic_Inf_hom : (iicInfHomₓ : α → LowerSet α) = Iic :=
  rfl

@[simp]
theorem Iic_Inf_hom_apply (a : α) : iicInfHomₓ a = iic a :=
  rfl

end CompleteLattice

end LowerSet

