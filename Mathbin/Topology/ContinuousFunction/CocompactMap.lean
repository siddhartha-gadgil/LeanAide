/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
import Mathbin.Topology.ContinuousFunction.Basic

/-!
# Cocompact continuous maps

The type of *cocompact continuous maps* are those which tend to the cocompact filter on the
codomain along the cocompact filter on the domain. When the domain and codomain are Hausdorff, this
is equivalent to many other conditions, including that preimages of compact sets are compact. -/


universe u v w

open Filter Set

/-! ### Cocompact continuous maps -/


/-- A *cocompact continuous map* is a continuous function between topological spaces which
tends to the cocompact filter along the cocompact filter. Functions for which preimages of compact
sets are compact always satisfy this property, and the converse holds for cocompact continuous maps
when the codomain is Hausdorff (see `cocompact_map.tendsto_of_forall_preimage` and
`cocompact_map.compact_preimage`) -/
structure CocompactMap (α : Type u) (β : Type v) [TopologicalSpace α] [TopologicalSpace β] extends ContinuousMap α β :
  Type max u v where
  cocompact_tendsto' : Tendsto to_fun (cocompact α) (cocompact β)

/-- `cocompact_map_class F α β` states that `F` is a type of cocompact continuous maps.

You should also extend this typeclass when you extend `cocompact_map`. -/
class CocompactMapClass (F : Type _) (α β : outParam <| Type _) [TopologicalSpace α] [TopologicalSpace β] extends
  ContinuousMapClass F α β where
  cocompact_tendsto (f : F) : Tendsto f (cocompact α) (cocompact β)

namespace CocompactMapClass

variable {F α β : Type _} [TopologicalSpace α] [TopologicalSpace β] [CocompactMapClass F α β]

instance : CoeTₓ F (CocompactMap α β) :=
  ⟨fun f => ⟨f, cocompact_tendsto f⟩⟩

end CocompactMapClass

export CocompactMapClass (cocompact_tendsto)

namespace CocompactMap

section Basics

variable {α β γ δ : Type _} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

instance : CocompactMapClass (CocompactMap α β) α β where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_continuous := fun f => f.continuous_to_fun
  cocompact_tendsto := fun f => f.cocompact_tendsto'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (CocompactMap α β) fun _ => α → β :=
  FunLike.hasCoeToFun

@[simp]
theorem coe_to_continuous_fun {f : CocompactMap α β} : (f.toContinuousMap : α → β) = f :=
  rfl

@[ext]
theorem ext {f g : CocompactMap α β} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext _ _ h

/-- Copy of a `cocompact_map` with a new `to_fun` equal to the old one. Useful
to fix definitional equalities. -/
protected def copy (f : CocompactMap α β) (f' : α → β) (h : f' = f) : CocompactMap α β where
  toFun := f'
  continuous_to_fun := by
    rw [h]
    exact f.continuous_to_fun
  cocompact_tendsto' := by
    simp_rw [h]
    exact f.cocompact_tendsto'

@[simp]
theorem coe_mk (f : C(α, β)) (h : Tendsto f (cocompact α) (cocompact β)) : ⇑(⟨f, h⟩ : CocompactMap α β) = f :=
  rfl

section

variable (α)

/-- The identity as a cocompact continuous map. -/
protected def id : CocompactMap α α :=
  ⟨ContinuousMap.id _, tendsto_id⟩

@[simp]
theorem coe_id : ⇑(CocompactMap.id α) = id :=
  rfl

end

instance : Inhabited (CocompactMap α α) :=
  ⟨CocompactMap.id α⟩

/-- The composition of cocompact continuous maps, as a cocompact continuous map. -/
def comp (f : CocompactMap β γ) (g : CocompactMap α β) : CocompactMap α γ :=
  ⟨f.toContinuousMap.comp g, (cocompact_tendsto f).comp (cocompact_tendsto g)⟩

@[simp]
theorem coe_comp (f : CocompactMap β γ) (g : CocompactMap α β) : ⇑(comp f g) = f ∘ g :=
  rfl

@[simp]
theorem comp_apply (f : CocompactMap β γ) (g : CocompactMap α β) (a : α) : comp f g a = f (g a) :=
  rfl

@[simp]
theorem comp_assoc (f : CocompactMap γ δ) (g : CocompactMap β γ) (h : CocompactMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

@[simp]
theorem id_comp (f : CocompactMap α β) : (CocompactMap.id _).comp f = f :=
  ext fun _ => rfl

@[simp]
theorem comp_id (f : CocompactMap α β) : f.comp (CocompactMap.id _) = f :=
  ext fun _ => rfl

theorem tendsto_of_forall_preimage {f : α → β} (h : ∀ s, IsCompact s → IsCompact (f ⁻¹' s)) :
    Tendsto f (cocompact α) (cocompact β) := fun s hs =>
  match mem_cocompact.mp hs with
  | ⟨t, ht, hts⟩ =>
    mem_map.mpr
      (mem_cocompact.mpr
        ⟨f ⁻¹' t, h t ht, by
          simpa using preimage_mono hts⟩)

/-- If the codomain is Hausdorff, preimages of compact sets are compact under a cocompact
continuous map. -/
theorem compact_preimage [T2Space β] (f : CocompactMap α β) ⦃s : Set β⦄ (hs : IsCompact s) : IsCompact (f ⁻¹' s) := by
  obtain ⟨t, ht, hts⟩ :=
    mem_cocompact'.mp
      (by
        simpa only [← preimage_image_preimage, ← preimage_compl] using
          mem_map.mp
            (cocompact_tendsto f <| mem_cocompact.mpr ⟨s, hs, compl_subset_compl.mpr (image_preimage_subset f _)⟩))
  exact
    compact_of_is_closed_subset ht (hs.is_closed.preimage <| map_continuous f)
      (by
        simpa using hts)

end Basics

end CocompactMap

