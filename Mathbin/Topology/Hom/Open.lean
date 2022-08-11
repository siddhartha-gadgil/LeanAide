/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Continuous open maps

This file defines bundled continuous open maps.

We use the `fun_like` design, so each type of morphisms has a companion typeclass which is meant to
be satisfied by itself and all stricter types.

## Types of morphisms

* `continuous_open_map`: Continuous open maps.

## Typeclasses

* `continuous_open_map_class`
-/


open Function

variable {F α β γ δ : Type _}

/-- The type of continuous open maps from `α` to `β`, aka Priestley homomorphisms. -/
structure ContinuousOpenMap (α β : Type _) [TopologicalSpace α] [TopologicalSpace β] extends ContinuousMap α β where
  map_open' : IsOpenMap to_fun

-- mathport name: «expr →CO »
infixr:25 " →CO " => ContinuousOpenMap

/-- `continuous_open_map_class F α β` states that `F` is a type of continuous open maps.

You should extend this class when you extend `continuous_open_map`. -/
class ContinuousOpenMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMapClass F α β where
  map_open (f : F) : IsOpenMap f

export ContinuousOpenMapClass (map_open)

instance [TopologicalSpace α] [TopologicalSpace β] [ContinuousOpenMapClass F α β] : CoeTₓ F (α →CO β) :=
  ⟨fun f => ⟨f, map_open f⟩⟩

/-! ### Continuous open maps -/


namespace ContinuousOpenMap

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

instance : ContinuousOpenMapClass (α →CO β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_continuous := fun f => f.continuous_to_fun
  map_open := fun f => f.map_open'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →CO β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe {f : α →CO β} : f.toFun = (f : α → β) :=
  rfl

@[ext]
theorem ext {f g : α →CO β} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext f g h

/-- Copy of a `continuous_open_map` with a new `continuous_map` equal to the old one. Useful to fix
definitional equalities. -/
protected def copy (f : α →CO β) (f' : α → β) (h : f' = f) : α →CO β :=
  ⟨f.toContinuousMap.copy f' <| h, h.symm.subst f.map_open'⟩

variable (α)

/-- `id` as a `continuous_open_map`. -/
protected def id : α →CO α :=
  ⟨ContinuousMap.id _, IsOpenMap.id⟩

instance : Inhabited (α →CO α) :=
  ⟨ContinuousOpenMap.id _⟩

@[simp]
theorem coe_id : ⇑(ContinuousOpenMap.id α) = id :=
  rfl

variable {α}

@[simp]
theorem id_apply (a : α) : ContinuousOpenMap.id α a = a :=
  rfl

/-- Composition of `continuous_open_map`s as a `continuous_open_map`. -/
def comp (f : β →CO γ) (g : α →CO β) : ContinuousOpenMap α γ :=
  ⟨f.toContinuousMap.comp g.toContinuousMap, f.map_open'.comp g.map_open'⟩

@[simp]
theorem coe_comp (f : β →CO γ) (g : α →CO β) : (f.comp g : α → γ) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : β →CO γ) (g : α →CO β) (a : α) : (f.comp g) a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : γ →CO δ) (g : β →CO γ) (h : α →CO β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem comp_id (f : α →CO β) : f.comp (ContinuousOpenMap.id α) = f :=
  ext fun a => rfl

@[simp]
theorem id_comp (f : α →CO β) : (ContinuousOpenMap.id β).comp f = f :=
  ext fun a => rfl

theorem cancel_right {g₁ g₂ : β →CO γ} {f : α →CO β} (hf : Surjective f) : g₁.comp f = g₂.comp f ↔ g₁ = g₂ :=
  ⟨fun h => ext <| hf.forall.2 <| FunLike.ext_iff.1 h, congr_arg _⟩

theorem cancel_left {g : β →CO γ} {f₁ f₂ : α →CO β} (hg : Injective g) : g.comp f₁ = g.comp f₂ ↔ f₁ = f₂ :=
  ⟨fun h =>
    ext fun a =>
      hg <| by
        rw [← comp_apply, h, comp_apply],
    congr_arg _⟩

end ContinuousOpenMap

