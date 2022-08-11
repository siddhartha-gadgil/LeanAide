/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Topology.Bornology.Basic

/-!
# Locally bounded maps

This file defines locally bounded maps between bornologies.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `locally_bounded_map`: Locally bounded maps. Maps which preserve boundedness.

## Typeclasses

* `locally_bounded_map_class`
-/


open Bornology Filter Function Set

variable {F α β γ δ : Type _}

/-- The type of bounded maps from `α` to `β`, the maps which send a bounded set to a bounded set. -/
structure LocallyBoundedMap (α β : Type _) [Bornology α] [Bornology β] where
  toFun : α → β
  comap_cobounded_le' : (cobounded β).comap to_fun ≤ cobounded α

/-- `locally_bounded_map_class F α β` states that `F` is a type of bounded maps.

You should extend this class when you extend `locally_bounded_map`. -/
class LocallyBoundedMapClass (F : Type _) (α β : outParam <| Type _) [Bornology α] [Bornology β] extends
  FunLike F α fun _ => β where
  comap_cobounded_le (f : F) : (cobounded β).comap f ≤ cobounded α

export LocallyBoundedMapClass (comap_cobounded_le)

theorem IsBounded.image [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] {f : F} {s : Set α}
    (hs : IsBounded s) : IsBounded (f '' s) :=
  comap_cobounded_le_iff.1 (comap_cobounded_le f) hs

instance [Bornology α] [Bornology β] [LocallyBoundedMapClass F α β] : CoeTₓ F (LocallyBoundedMap α β) :=
  ⟨fun f => ⟨f, comap_cobounded_le f⟩⟩

namespace LocallyBoundedMap

variable [Bornology α] [Bornology β] [Bornology γ] [Bornology δ]

instance : LocallyBoundedMapClass (LocallyBoundedMap α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    cases f
    cases g
    congr
  comap_cobounded_le := fun f => f.comap_cobounded_le'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (LocallyBoundedMap α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : LocallyBoundedMap α β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : LocallyBoundedMap α β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `locally_bounded_map` with a new `to_fun` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : LocallyBoundedMap α β) (f' : α → β) (h : f' = f) : LocallyBoundedMap α β :=
  ⟨f', h.symm ▸ f.comap_cobounded_le'⟩

/-- Construct a `locally_bounded_map` from the fact that the function maps bounded sets to bounded
sets. -/
def ofMapBounded (f : α → β) (h) : LocallyBoundedMap α β :=
  ⟨f, comap_cobounded_le_iff.2 h⟩

@[simp]
theorem coe_of_map_bounded (f : α → β) {h} : ⇑(ofMapBounded f h) = f :=
  rfl

@[simp]
theorem of_map_bounded_apply (f : α → β) {h} (a : α) : ofMapBounded f h a = f a :=
  rfl

variable (α)

/-- `id` as a `locally_bounded_map`. -/
protected def id : LocallyBoundedMap α α :=
  ⟨id, comap_id.le⟩

instance : Inhabited (LocallyBoundedMap α α) :=
  ⟨LocallyBoundedMap.id α⟩

@[simp]
theorem coe_id : ⇑(LocallyBoundedMap.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : LocallyBoundedMap.id α a = a :=
  rfl

/-- Composition of `locally_bounded_map`s as a `locally_bounded_map`. -/
def comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : LocallyBoundedMap α γ where
  toFun := f ∘ g
  comap_cobounded_le' := comap_comap.Ge.trans <| (comap_mono f.comap_cobounded_le').trans g.comap_cobounded_le'

@[simp]
theorem coe_comp (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : LocallyBoundedMap β γ) (g : LocallyBoundedMap α β) (a : α) : f.comp g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : LocallyBoundedMap γ δ) (g : LocallyBoundedMap β γ) (h : LocallyBoundedMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : LocallyBoundedMap α β) : f.comp (LocallyBoundedMap.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : LocallyBoundedMap α β) : (LocallyBoundedMap.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : LocallyBoundedMap β γ} {f : LocallyBoundedMap α β} (hf : Surjective f) :
    g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : LocallyBoundedMap β γ} {f₁ f₂ : LocallyBoundedMap α β} (hg : Injective g) :
    g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end LocallyBoundedMap

