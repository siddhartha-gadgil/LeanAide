/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.ModelTheory.Substructures

/-!
# Finitely Generated First-Order Structures
This file defines what it means for a first-order (sub)structure to be finitely or countably
generated, similarly to other finitely-generated objects in the algebra library.

## Main Definitions
* `first_order.language.substructure.fg` indicates that a substructure is finitely generated.
* `first_order.language.Structure.fg` indicates that a structure is finitely generated.
* `first_order.language.substructure.cg` indicates that a substructure is countably generated.
* `first_order.language.Structure.cg` indicates that a structure is countably generated.


## TODO
Develop a more unified definition of finite generation using the theory of closure operators, or use
this definition of finite generation to define the others.

-/


open FirstOrder

open Set

namespace FirstOrder

namespace Language

open Structure

variable {L : Language} {M : Type _} [L.Structure M]

namespace Substructure

/-- A substructure of `M` is finitely generated if it is the closure of a finite subset of `M`. -/
def Fg (N : L.Substructure M) : Prop :=
  ∃ S : Finset M, closure L ↑S = N

theorem fg_def {N : L.Substructure M} : N.Fg ↔ ∃ S : Set M, S.Finite ∧ closure L S = N :=
  ⟨fun ⟨t, h⟩ => ⟨_, Finset.finite_to_set t, h⟩, by
    rintro ⟨t', h, rfl⟩
    rcases finite.exists_finset_coe h with ⟨t, rfl⟩
    exact ⟨t, rfl⟩⟩

theorem fg_iff_exists_fin_generating_family {N : L.Substructure M} :
    N.Fg ↔ ∃ (n : ℕ)(s : Finₓ n → M), closure L (Range s) = N := by
  rw [fg_def]
  constructor
  · rintro ⟨S, Sfin, hS⟩
    obtain ⟨n, f, rfl⟩ := Sfin.fin_embedding
    exact ⟨n, f, hS⟩
    
  · rintro ⟨n, s, hs⟩
    refine' ⟨range s, finite_range s, hs⟩
    

theorem fg_bot : (⊥ : L.Substructure M).Fg :=
  ⟨∅, by
    rw [Finset.coe_empty, closure_empty]⟩

theorem fg_closure {s : Set M} (hs : s.Finite) : Fg (closure L s) :=
  ⟨hs.toFinset, by
    rw [hs.coe_to_finset]⟩

theorem fg_closure_singleton (x : M) : Fg (closure L ({x} : Set M)) :=
  fg_closure (finite_singleton x)

theorem Fg.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.Fg) (hN₂ : N₂.Fg) : (N₁⊔N₂).Fg :=
  let ⟨t₁, ht₁⟩ := fg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := fg_def.1 hN₂
  fg_def.2
    ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by
      rw [closure_union, ht₁.2, ht₂.2]⟩

theorem Fg.map {N : Type _} [L.Structure N] (f : M →[L] N) {s : L.Substructure M} (hs : s.Fg) : (s.map f).Fg :=
  let ⟨t, ht⟩ := fg_def.1 hs
  fg_def.2
    ⟨f '' t, ht.1.Image _, by
      rw [closure_image, ht.2]⟩

theorem Fg.of_map_embedding {N : Type _} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).Fg) : s.Fg := by
  rcases hs with ⟨t, h⟩
  rw [fg_def]
  refine' ⟨f ⁻¹' t, t.finite_to_set.preimage (f.injective.inj_on _), _⟩
  have hf : Function.Injective f.to_hom := f.injective
  refine' map_injective_of_injective hf _
  rw [← h, map_closure, embedding.coe_to_hom, image_preimage_eq_of_subset]
  intro x hx
  have h' := subset_closure hx
  rw [h] at h'
  exact hom.map_le_range h'

/-- A substructure of `M` is countably generated if it is the closure of a countable subset of `M`.
-/
def Cg (N : L.Substructure M) : Prop :=
  ∃ S : Set M, S.Countable ∧ closure L S = N

theorem cg_def {N : L.Substructure M} : N.Cg ↔ ∃ S : Set M, S.Countable ∧ closure L S = N :=
  Iff.refl _

theorem Fg.cg {N : L.Substructure M} (h : N.Fg) : N.Cg := by
  obtain ⟨s, hf, rfl⟩ := fg_def.1 h
  refine' ⟨s, hf.countable, rfl⟩

theorem cg_iff_empty_or_exists_nat_generating_family {N : L.Substructure M} :
    N.Cg ↔ ↑N = (∅ : Set M) ∨ ∃ s : ℕ → M, closure L (Range s) = N := by
  rw [cg_def]
  constructor
  · rintro ⟨S, Scount, hS⟩
    cases' eq_empty_or_nonempty ↑N with h h
    · exact Or.intro_left _ h
      
    obtain ⟨f, h'⟩ := (Scount.union (Set.countable_singleton h.some)).exists_surjective (singleton_nonempty h.some).inr
    refine' Or.intro_rightₓ _ ⟨f, _⟩
    rw [← h', closure_union, hS, sup_eq_left, closure_le]
    exact singleton_subset_iff.2 h.some_mem
    
  · intro h
    cases' h with h h
    · refine' ⟨∅, countable_empty, closure_eq_of_le (empty_subset _) _⟩
      rw [← SetLike.coe_subset_coe, h]
      exact empty_subset _
      
    · obtain ⟨f, rfl⟩ := h
      exact ⟨range f, countable_range _, rfl⟩
      
    

theorem cg_bot : (⊥ : L.Substructure M).Cg :=
  fg_bot.Cg

theorem cg_closure {s : Set M} (hs : s.Countable) : Cg (closure L s) :=
  ⟨s, hs, rfl⟩

theorem cg_closure_singleton (x : M) : Cg (closure L ({x} : Set M)) :=
  (fg_closure_singleton x).Cg

theorem Cg.sup {N₁ N₂ : L.Substructure M} (hN₁ : N₁.Cg) (hN₂ : N₂.Cg) : (N₁⊔N₂).Cg :=
  let ⟨t₁, ht₁⟩ := cg_def.1 hN₁
  let ⟨t₂, ht₂⟩ := cg_def.1 hN₂
  cg_def.2
    ⟨t₁ ∪ t₂, ht₁.1.union ht₂.1, by
      rw [closure_union, ht₁.2, ht₂.2]⟩

theorem Cg.map {N : Type _} [L.Structure N] (f : M →[L] N) {s : L.Substructure M} (hs : s.Cg) : (s.map f).Cg :=
  let ⟨t, ht⟩ := cg_def.1 hs
  cg_def.2
    ⟨f '' t, ht.1.Image _, by
      rw [closure_image, ht.2]⟩

theorem Cg.of_map_embedding {N : Type _} [L.Structure N] (f : M ↪[L] N) {s : L.Substructure M}
    (hs : (s.map f.toHom).Cg) : s.Cg := by
  rcases hs with ⟨t, h1, h2⟩
  rw [cg_def]
  refine' ⟨f ⁻¹' t, h1.preimage f.injective, _⟩
  have hf : Function.Injective f.to_hom := f.injective
  refine' map_injective_of_injective hf _
  rw [← h2, map_closure, embedding.coe_to_hom, image_preimage_eq_of_subset]
  intro x hx
  have h' := subset_closure hx
  rw [h2] at h'
  exact hom.map_le_range h'

theorem cg_iff_countable [L.CountableFunctions] {s : L.Substructure M} : s.Cg ↔ Nonempty (Encodable s) := by
  refine' ⟨_, fun h => ⟨s, h, s.closure_eq⟩⟩
  rintro ⟨s, h, rfl⟩
  exact h.substructure_closure L

end Substructure

open Substructure

namespace Structure

variable (L) (M)

/-- A structure is finitely generated if it is the closure of a finite subset. -/
class Fg : Prop where
  out : (⊤ : L.Substructure M).Fg

/-- A structure is countably generated if it is the closure of a countable subset. -/
class Cg : Prop where
  out : (⊤ : L.Substructure M).Cg

variable {L M}

theorem fg_def : Fg L M ↔ (⊤ : L.Substructure M).Fg :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Structure.fg` in terms of `set.finite` instead of `finset`. -/
theorem fg_iff : Fg L M ↔ ∃ S : Set M, S.Finite ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [fg_def, substructure.fg_def]

theorem Fg.range {N : Type _} [L.Structure N] (h : Fg L M) (f : M →[L] N) : f.range.Fg := by
  rw [hom.range_eq_map]
  exact (fg_def.1 h).map f

theorem Fg.map_of_surjective {N : Type _} [L.Structure N] (h : Fg L M) (f : M →[L] N) (hs : Function.Surjective f) :
    Fg L N := by
  rw [← hom.range_eq_top] at hs
  rw [fg_def, ← hs]
  exact h.range f

theorem cg_def : Cg L M ↔ (⊤ : L.Substructure M).Cg :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩

/-- An equivalent expression of `Structure.cg`. -/
theorem cg_iff : Cg L M ↔ ∃ S : Set M, S.Countable ∧ closure L S = (⊤ : L.Substructure M) := by
  rw [cg_def, substructure.cg_def]

theorem Cg.range {N : Type _} [L.Structure N] (h : Cg L M) (f : M →[L] N) : f.range.Cg := by
  rw [hom.range_eq_map]
  exact (cg_def.1 h).map f

theorem Cg.map_of_surjective {N : Type _} [L.Structure N] (h : Cg L M) (f : M →[L] N) (hs : Function.Surjective f) :
    Cg L N := by
  rw [← hom.range_eq_top] at hs
  rw [cg_def, ← hs]
  exact h.range f

theorem cg_iff_countable [L.CountableFunctions] : Cg L M ↔ Nonempty (Encodable M) := by
  rw [cg_def, cg_iff_countable, Cardinal.encodable_iff, Cardinal.encodable_iff, top_equiv.to_equiv.cardinal_eq]

theorem Fg.cg (h : Fg L M) : Cg L M :=
  cg_def.2 (fg_def.1 h).Cg

instance (priority := 100) cg_of_fg [h : Fg L M] : Cg L M :=
  h.Cg

end Structure

theorem Equiv.fg_iff {N : Type _} [L.Structure N] (f : M ≃[L] N) : Structure.Fg L M ↔ Structure.Fg L N :=
  ⟨fun h => h.mapOfSurjective f.toHom f.toEquiv.Surjective, fun h =>
    h.mapOfSurjective f.symm.toHom f.toEquiv.symm.Surjective⟩

theorem Substructure.fg_iff_Structure_fg (S : L.Substructure M) : S.Fg ↔ Structure.Fg L S := by
  rw [Structure.fg_def]
  refine' ⟨fun h => fg.of_map_embedding S.subtype _, fun h => _⟩
  · rw [← hom.range_eq_map, range_subtype]
    exact h
    
  · have h := h.map S.subtype.to_hom
    rw [← hom.range_eq_map, range_subtype] at h
    exact h
    

theorem Equiv.cg_iff {N : Type _} [L.Structure N] (f : M ≃[L] N) : Structure.Cg L M ↔ Structure.Cg L N :=
  ⟨fun h => h.mapOfSurjective f.toHom f.toEquiv.Surjective, fun h =>
    h.mapOfSurjective f.symm.toHom f.toEquiv.symm.Surjective⟩

theorem Substructure.cg_iff_Structure_cg (S : L.Substructure M) : S.Cg ↔ Structure.Cg L S := by
  rw [Structure.cg_def]
  refine' ⟨fun h => cg.of_map_embedding S.subtype _, fun h => _⟩
  · rw [← hom.range_eq_map, range_subtype]
    exact h
    
  · have h := h.map S.subtype.to_hom
    rw [← hom.range_eq_map, range_subtype] at h
    exact h
    

end Language

end FirstOrder

