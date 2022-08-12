/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Order.UpperLower
import Mathbin.Topology.Sets.Closeds

/-!
# Clopen upper sets

In this file we define the type of clopen upper sets.
-/


open Set TopologicalSpace

variable {α β : Type _} [TopologicalSpace α] [LE α] [TopologicalSpace β] [LE β]

/-! ### Compact open sets -/


/-- The type of clopen upper sets of a topological space. -/
structure ClopenUpperSet (α : Type _) [TopologicalSpace α] [LE α] extends Clopens α where
  upper' : IsUpperSet carrier

namespace ClopenUpperSet

instance : SetLike (ClopenUpperSet α) α where
  coe := fun s => s.Carrier
  coe_injective' := fun s t h => by
    obtain ⟨⟨_, _⟩, _⟩ := s
    obtain ⟨⟨_, _⟩, _⟩ := t
    congr

theorem upper (s : ClopenUpperSet α) : IsUpperSet (s : Set α) :=
  s.upper'

theorem clopen (s : ClopenUpperSet α) : IsClopen (s : Set α) :=
  s.clopen'

/-- Reinterpret a upper clopen as an upper set. -/
@[simps]
def toUpperSet (s : ClopenUpperSet α) : UpperSet α :=
  ⟨s, s.upper⟩

@[ext]
protected theorem ext {s t : ClopenUpperSet α} (h : (s : Set α) = t) : s = t :=
  SetLike.ext' h

@[simp]
theorem coe_mk (s : Clopens α) (h) : (mk s h : Set α) = s :=
  rfl

instance : HasSup (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens⊔t.toClopens, s.upper.union t.upper⟩⟩

instance : HasInf (ClopenUpperSet α) :=
  ⟨fun s t => ⟨s.toClopens⊓t.toClopens, s.upper.inter t.upper⟩⟩

instance : HasTop (ClopenUpperSet α) :=
  ⟨⟨⊤, is_upper_set_univ⟩⟩

instance : HasBot (ClopenUpperSet α) :=
  ⟨⟨⊥, is_upper_set_empty⟩⟩

instance : Lattice (ClopenUpperSet α) :=
  SetLike.coe_injective.Lattice _ (fun _ _ => rfl) fun _ _ => rfl

instance : BoundedOrder (ClopenUpperSet α) :=
  BoundedOrder.lift (coe : _ → Set α) (fun _ _ => id) rfl rfl

@[simp]
theorem coe_sup (s t : ClopenUpperSet α) : (↑(s⊔t) : Set α) = s ∪ t :=
  rfl

@[simp]
theorem coe_inf (s t : ClopenUpperSet α) : (↑(s⊓t) : Set α) = s ∩ t :=
  rfl

@[simp]
theorem coe_top : (↑(⊤ : ClopenUpperSet α) : Set α) = univ :=
  rfl

@[simp]
theorem coe_bot : (↑(⊥ : ClopenUpperSet α) : Set α) = ∅ :=
  rfl

instance : Inhabited (ClopenUpperSet α) :=
  ⟨⊥⟩

end ClopenUpperSet

