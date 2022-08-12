/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathbin.LinearAlgebra.Span
import Mathbin.Order.Atoms

/-!
# Simple Modules

## Main Definitions
  * `is_simple_module` indicates that a module has no proper submodules
  (the only submodules are `⊥` and `⊤`).
  * `is_semisimple_module` indicates that every submodule has a complement, or equivalently,
    the module is a direct sum of simple modules.
  * A `division_ring` structure on the endomorphism ring of a simple module.

## Main Results
  * Schur's Lemma: `bijective_or_eq_zero` shows that a linear map between simple modules
  is either bijective or 0, leading to a `division_ring` structure on the endomorphism ring.

## TODO
  * Artin-Wedderburn Theory
  * Unify with the work on Schur's Lemma in a category theory context

-/


variable (R : Type _) [Ringₓ R] (M : Type _) [AddCommGroupₓ M] [Module R M]

/-- A module is simple when it has only two submodules, `⊥` and `⊤`. -/
abbrev IsSimpleModule :=
  IsSimpleOrder (Submodule R M)

/-- A module is semisimple when every submodule has a complement, or equivalently, the module
  is a direct sum of simple modules. -/
abbrev IsSemisimpleModule :=
  IsComplemented (Submodule R M)

-- Making this an instance causes the linter to complain of "dangerous instances"
theorem IsSimpleModule.nontrivial [IsSimpleModule R M] : Nontrivial M :=
  ⟨⟨0, by
      have h : (⊥ : Submodule R M) ≠ ⊤ := bot_ne_top
      contrapose! h
      ext
      simp [← Submodule.mem_bot, ← Submodule.mem_top, ← h x]⟩⟩

variable {R} {M} {m : Submodule R M} {N : Type _} [AddCommGroupₓ N] [Module R N]

theorem is_simple_module_iff_is_atom : IsSimpleModule R m ↔ IsAtom m := by
  rw [← Set.is_simple_order_Iic_iff_is_atom]
  apply OrderIso.is_simple_order_iff
  exact Submodule.MapSubtype.relIso m

namespace IsSimpleModule

variable [hm : IsSimpleModule R m]

@[simp]
theorem is_atom : IsAtom m :=
  is_simple_module_iff_is_atom.1 hm

end IsSimpleModule

theorem is_semisimple_of_Sup_simples_eq_top (h : sup { m : Submodule R M | IsSimpleModule R m } = ⊤) :
    IsSemisimpleModule R M :=
  is_complemented_of_Sup_atoms_eq_top
    (by
      simp_rw [← h, is_simple_module_iff_is_atom])

namespace IsSemisimpleModule

variable [IsSemisimpleModule R M]

theorem Sup_simples_eq_top : sup { m : Submodule R M | IsSimpleModule R m } = ⊤ := by
  simp_rw [is_simple_module_iff_is_atom]
  exact Sup_atoms_eq_top

instance is_semisimple_submodule {m : Submodule R M} : IsSemisimpleModule R m := by
  have f : Submodule R m ≃o Set.Iic m := Submodule.MapSubtype.relIso m
  exact f.is_complemented_iff.2 IsModularLattice.is_complemented_Iic

end IsSemisimpleModule

theorem is_semisimple_iff_top_eq_Sup_simples :
    sup { m : Submodule R M | IsSimpleModule R m } = ⊤ ↔ IsSemisimpleModule R M :=
  ⟨is_semisimple_of_Sup_simples_eq_top, by
    intro
    exact IsSemisimpleModule.Sup_simples_eq_top⟩

namespace LinearMap

theorem injective_or_eq_zero [IsSimpleModule R M] (f : M →ₗ[R] N) : Function.Injective f ∨ f = 0 := by
  rw [← ker_eq_bot, ← ker_eq_top]
  apply eq_bot_or_eq_top

theorem injective_of_ne_zero [IsSimpleModule R M] {f : M →ₗ[R] N} (h : f ≠ 0) : Function.Injective f :=
  f.injective_or_eq_zero.resolve_right h

theorem surjective_or_eq_zero [IsSimpleModule R N] (f : M →ₗ[R] N) : Function.Surjective f ∨ f = 0 := by
  rw [← range_eq_top, ← range_eq_bot, or_comm]
  apply eq_bot_or_eq_top

theorem surjective_of_ne_zero [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) : Function.Surjective f :=
  f.surjective_or_eq_zero.resolve_right h

/-- **Schur's Lemma** for linear maps between (possibly distinct) simple modules -/
theorem bijective_or_eq_zero [IsSimpleModule R M] [IsSimpleModule R N] (f : M →ₗ[R] N) : Function.Bijective f ∨ f = 0 :=
  by
  by_cases' h : f = 0
  · right
    exact h
    
  exact Or.intro_left _ ⟨injective_of_ne_zero h, surjective_of_ne_zero h⟩

theorem bijective_of_ne_zero [IsSimpleModule R M] [IsSimpleModule R N] {f : M →ₗ[R] N} (h : f ≠ 0) :
    Function.Bijective f :=
  f.bijective_or_eq_zero.resolve_right h

/-- Schur's Lemma makes the endomorphism ring of a simple module a division ring. -/
noncomputable instance _root_.module.End.division_ring [DecidableEq (Module.End R M)] [IsSimpleModule R M] :
    DivisionRing (Module.End R M) :=
  { (Module.End.ring : Ringₓ (Module.End R M)) with
    inv := fun f =>
      if h : f = 0 then 0
      else
        LinearMap.inverse f (Equivₓ.ofBijective _ (bijective_of_ne_zero h)).invFun
          (Equivₓ.ofBijective _ (bijective_of_ne_zero h)).left_inv
          (Equivₓ.ofBijective _ (bijective_of_ne_zero h)).right_inv,
    exists_pair_ne :=
      ⟨0, 1, by
        have := IsSimpleModule.nontrivial R M
        have h := exists_pair_ne M
        contrapose! h
        intro x y
        simp_rw [ext_iff, one_apply, zero_apply] at h
        rw [← h x, h y]⟩,
    mul_inv_cancel := by
      intro a a0
      change a * dite _ _ _ = 1
      ext
      rw [dif_neg a0, mul_eq_comp, one_apply, comp_apply]
      exact (Equivₓ.ofBijective _ (bijective_of_ne_zero a0)).right_inv x,
    inv_zero := dif_pos rfl }

end LinearMap

