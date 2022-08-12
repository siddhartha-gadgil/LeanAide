/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.Topology.LocalHomeomorph

/-!
# Local homeomorphisms

This file defines local homeomorphisms.

## Main definitions

* `is_locally_homeomorph`: A function `f : X → Y` satisfies `is_locally_homeomorph` if for each
  point `x : X`, the restriction of `f` to some open neighborhood `U` of `x` gives a homeomorphism
  between `U` and an open subset of `Y`.

  Note that `is_locally_homeomorph` is a global condition. This is in contrast to
  `local_homeomorph`, which is a homeomorphism between specific open subsets.
-/


open TopologicalSpace

variable {X Y Z : Type _} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] (g : Y → Z) (f : X → Y)

/-- A function `f : X → Y` satisfies `is_locally_homeomorph` if each `x : x` is contained in
  the source of some `e : local_homeomorph X Y` with `f = e`. -/
def IsLocallyHomeomorph :=
  ∀ x : X, ∃ e : LocalHomeomorph X Y, x ∈ e.Source ∧ f = e

namespace IsLocallyHomeomorph

/-- Proves that `f` satisfies `is_locally_homeomorph`. The condition `h` is weaker than definition
of `is_locally_homeomorph`, since it only requires `e : local_homeomorph X Y` to agree with `f` on
its source `e.source`, as opposed to on the whole space `X`. -/
theorem mk (h : ∀ x : X, ∃ e : LocalHomeomorph X Y, x ∈ e.Source ∧ ∀ x, x ∈ e.Source → f x = e x) :
    IsLocallyHomeomorph f := by
  intro x
  obtain ⟨e, hx, he⟩ := h x
  exact
    ⟨{ e with toFun := f,
        map_source' := fun x hx => by
          rw [he x hx] <;> exact e.map_source' hx,
        left_inv' := fun x hx => by
          rw [he x hx] <;> exact e.left_inv' hx,
        right_inv' := fun y hy => by
          rw [he _ (e.map_target' hy)] <;> exact e.right_inv' hy,
        continuous_to_fun := (continuous_on_congr he).mpr e.continuous_to_fun },
      hx, rfl⟩

variable {g f}

theorem map_nhds_eq (hf : IsLocallyHomeomorph f) (x : X) : (𝓝 x).map f = 𝓝 (f x) := by
  obtain ⟨e, hx, rfl⟩ := hf x
  exact e.map_nhds_eq hx

protected theorem continuous (hf : IsLocallyHomeomorph f) : Continuous f :=
  continuous_iff_continuous_at.mpr fun x => le_of_eqₓ (hf.map_nhds_eq x)

theorem is_open_map (hf : IsLocallyHomeomorph f) : IsOpenMap f :=
  IsOpenMap.of_nhds_le fun x => ge_of_eq (hf.map_nhds_eq x)

protected theorem comp (hg : IsLocallyHomeomorph g) (hf : IsLocallyHomeomorph f) : IsLocallyHomeomorph (g ∘ f) := by
  intro x
  obtain ⟨eg, hxg, rfl⟩ := hg (f x)
  obtain ⟨ef, hxf, rfl⟩ := hf x
  exact ⟨ef.trans eg, ⟨hxf, hxg⟩, rfl⟩

end IsLocallyHomeomorph

