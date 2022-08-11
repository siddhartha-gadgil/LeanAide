/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.Data.Fintype.Basic
import Mathbin.ModelTheory.Semantics

/-!
# Quotients of First-Order Structures
This file defines prestructures and quotients of first-order structures.

## Main Definitions
* If `s` is a setoid (equivalence relation) on `M`, a `first_order.language.prestructure s` is the
data for a first-order structure on `M` that will still be a structure when modded out by `s`.
* The structure `first_order.language.quotient_structure s` is the resulting structure on
`quotient s`.

-/


namespace FirstOrder

namespace Language

variable (L : Language) {M : Type _}

open FirstOrder

open Structure

/-- A prestructure is a first-order structure with a `setoid` equivalence relation on it,
  such that quotienting by that equivalence relation is still a structure. -/
class Prestructure (s : Setoidₓ M) where
  toStructure : L.Structure M
  fun_equiv : ∀ {n} {f : L.Functions n} (x y : Finₓ n → M), x ≈ y → funMap f x ≈ funMap f y
  rel_equiv : ∀ {n} {r : L.Relations n} (x y : Finₓ n → M) (h : x ≈ y), RelMap r x = RelMap r y

variable {L} {s : Setoidₓ M} [ps : L.Prestructure s]

instance quotientStructure : L.Structure (Quotientₓ s) where
  funMap := fun n f x => Quotientₓ.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotientₓ.finChoice x)
  rel_map := fun n r x => Quotientₓ.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotientₓ.finChoice x)

variable (s)

include s

theorem fun_map_quotient_mk {n : ℕ} (f : L.Functions n) (x : Finₓ n → M) :
    (funMap f fun i => ⟦x i⟧) = ⟦@funMap _ _ ps.toStructure _ f x⟧ := by
  change Quotientₓ.map (@fun_map L M ps.to_structure n f) prestructure.fun_equiv (Quotientₓ.finChoice _) = _
  rw [Quotientₓ.fin_choice_eq, Quotientₓ.map_mk]

theorem rel_map_quotient_mk {n : ℕ} (r : L.Relations n) (x : Finₓ n → M) :
    (RelMap r fun i => ⟦x i⟧) ↔ @RelMap _ _ ps.toStructure _ r x := by
  change Quotientₓ.lift (@rel_map L M ps.to_structure n r) prestructure.rel_equiv (Quotientₓ.finChoice _) ↔ _
  rw [Quotientₓ.fin_choice_eq, Quotientₓ.lift_mk]

theorem Term.realize_quotient_mk {β : Type _} (t : L.Term β) (x : β → M) :
    (t.realize fun i => ⟦x i⟧) = ⟦@Term.realizeₓ _ _ ps.toStructure _ x t⟧ := by
  induction' t with _ _ _ _ ih
  · rfl
    
  · simp only [← ih, ← fun_map_quotient_mk, ← term.realize]
    

end Language

end FirstOrder

