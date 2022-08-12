/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathbin.Data.Vector.Basic

/-!
# Small types

A type is `w`-small if there exists an equivalence to some `S : Type w`.

We provide a noncomputable model `shrink α : Type w`, and `equiv_shrink α : α ≃ shrink α`.

A subsingleton type is `w`-small for any `w`.

If `α ≃ β`, then `small.{w} α ↔ small.{w} β`.
-/


universe u w v

/-- A type is `small.{w}` if there exists an equivalence to some `S : Type w`.
-/
class Small (α : Type v) : Prop where
  equiv_small : ∃ S : Type w, Nonempty (α ≃ S)

/-- Constructor for `small α` from an explicit witness type and equivalence.
-/
theorem Small.mk' {α : Type v} {S : Type w} (e : α ≃ S) : Small.{w} α :=
  ⟨⟨S, ⟨e⟩⟩⟩

/-- An arbitrarily chosen model in `Type w` for a `w`-small type.
-/
@[nolint has_inhabited_instance]
def Shrink (α : Type v) [Small.{w} α] : Type w :=
  Classical.some (@Small.equiv_small α _)

/-- The noncomputable equivalence between a `w`-small type and a model.
-/
noncomputable def equivShrink (α : Type v) [Small.{w} α] : α ≃ Shrink α :=
  Nonempty.some (Classical.some_spec (@Small.equiv_small α _))

instance (priority := 100) small_self (α : Type v) : Small.{v} α :=
  Small.mk' <| Equivₓ.refl α

theorem small_map {α : Type _} {β : Type _} [hβ : Small.{w} β] (e : α ≃ β) : Small.{w} α :=
  let ⟨γ, ⟨f⟩⟩ := hβ.equiv_small
  Small.mk' (e.trans f)

theorem small_lift (α : Type u) [hα : Small.{v} α] : Small.{max v w} α :=
  let ⟨⟨γ, ⟨f⟩⟩⟩ := hα
  Small.mk' <| f.trans Equivₓ.ulift.symm

instance (priority := 100) small_max (α : Type v) : Small.{max w v} α :=
  small_lift.{v, w} α

instance small_ulift (α : Type u) [Small.{v} α] : Small.{v} (ULift.{w} α) :=
  small_map Equivₓ.ulift

theorem small_type : Small.{max (u + 1) v} (Type u) :=
  small_max.{max (u + 1) v} _

section

open Classical

theorem small_congr {α : Type _} {β : Type _} (e : α ≃ β) : Small.{w} α ↔ Small.{w} β :=
  ⟨fun h => @small_map _ _ h e.symm, fun h => @small_map _ _ h e⟩

instance small_subtype (α : Type v) [Small.{w} α] (P : α → Prop) : Small.{w} { x // P x } :=
  small_map (equivShrink α).subtypeEquivOfSubtype'

theorem small_of_injective {α : Type v} {β : Type w} [Small.{u} β] {f : α → β} (hf : Function.Injective f) :
    Small.{u} α :=
  small_map (Equivₓ.ofInjective f hf)

theorem small_of_surjective {α : Type v} {β : Type w} [Small.{u} α] {f : α → β} (hf : Function.Surjective f) :
    Small.{u} β :=
  small_of_injective (Function.injective_surj_inv hf)

theorem small_subset {α : Type v} {s t : Set α} (hts : t ⊆ s) [Small.{u} s] : Small.{u} t :=
  let f : t → s := fun x => ⟨x, hts x.Prop⟩
  @small_of_injective _ _ _ f fun x y hxy => Subtype.ext (Subtype.mk.injₓ hxy)

instance (priority := 100) small_subsingleton (α : Type v) [Subsingleton α] : Small.{w} α := by
  rcases is_empty_or_nonempty α with ⟨⟩ <;> skip
  · apply small_map (Equivₓ.equivPempty α)
    
  · apply small_map Equivₓ.punitOfNonemptyOfSubsingleton
    assumption'
    

/-!
We don't define `small_of_fintype` or `small_of_encodable` in this file,
to keep imports to `logic` to a minimum.
-/


instance small_Pi {α} (β : α → Type _) [Small.{w} α] [∀ a, Small.{w} (β a)] : Small.{w} (∀ a, β a) :=
  ⟨⟨∀ a' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equivₓ.piCongr (equivShrink α) fun a => by
          simpa using equivShrink (β a)⟩⟩⟩

instance small_sigma {α} (β : α → Type _) [Small.{w} α] [∀ a, Small.{w} (β a)] : Small.{w} (Σa, β a) :=
  ⟨⟨Σa' : Shrink α, Shrink (β ((equivShrink α).symm a')),
      ⟨Equivₓ.sigmaCongr (equivShrink α) fun a => by
          simpa using equivShrink (β a)⟩⟩⟩

instance small_prod {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (α × β) :=
  ⟨⟨Shrink α × Shrink β, ⟨Equivₓ.prodCongr (equivShrink α) (equivShrink β)⟩⟩⟩

instance small_sum {α β} [Small.{w} α] [Small.{w} β] : Small.{w} (Sum α β) :=
  ⟨⟨Sum (Shrink α) (Shrink β), ⟨Equivₓ.sumCongr (equivShrink α) (equivShrink β)⟩⟩⟩

instance small_set {α} [Small.{w} α] : Small.{w} (Set α) :=
  ⟨⟨Set (Shrink α), ⟨Equivₓ.Set.congr (equivShrink α)⟩⟩⟩

instance small_range {α : Type v} {β : Type w} (f : α → β) [Small.{u} α] : Small.{u} (Set.Range f) :=
  small_of_surjective Set.surjective_onto_range

instance small_image {α : Type v} {β : Type w} (f : α → β) (S : Set α) [Small.{u} S] : Small.{u} (f '' S) :=
  small_of_surjective Set.surjective_onto_image

theorem not_small_type : ¬Small.{u} (Type max u v)
  | ⟨⟨S, ⟨e⟩⟩⟩ =>
    @Function.cantor_injective (Σα, e.symm α) (fun a => ⟨_, cast (e.3 _).symm a⟩) fun a b e =>
      (cast_inj _).1 <| eq_of_heq (Sigma.mk.inj e).2

instance small_vector {α : Type v} {n : ℕ} [Small.{u} α] : Small.{u} (Vector α n) :=
  small_of_injective (Equivₓ.vectorEquivFin α n).Injective

instance small_list {α : Type v} [Small.{u} α] : Small.{u} (List α) := by
  let e : (Σn, Vector α n) ≃ List α := Equivₓ.sigmaFiberEquiv List.length
  exact small_of_surjective e.surjective

end

