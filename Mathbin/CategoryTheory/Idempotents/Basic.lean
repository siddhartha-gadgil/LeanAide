/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathbin.CategoryTheory.Abelian.Basic

/-!
# Idempotent complete categories

In this file, we define the notion of idempotent complete categories
(also known as Karoubian categories, or pseudoabelian in the case of
preadditive categories).

## Main definitions

- `is_idempotent_complete C` expresses that `C` is idempotent complete, i.e.
all idempotents in `C` split. Other characterisations of idempotent completeness are given
by `is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent` and
`is_idempotent_complete_iff_idempotents_have_kernels`.
- `is_idempotent_complete_of_abelian` expresses that abelian categories are
idempotent complete.
- `is_idempotent_complete_iff_of_equivalence` expresses that if two categories `C` and `D`
are equivalent, then `C` is idempotent complete iff `D` is.
- `is_idempotent_complete_iff_opposite` expresses that `Cᵒᵖ` is idempotent complete
iff `C` is.

## References
* [Stacks: Karoubian categories] https://stacks.math.columbia.edu/tag/09SF

-/


open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Limits

open CategoryTheory.Preadditive

open Opposite

namespace CategoryTheory

variable (C : Type _) [Category C]

/-- A category is idempotent complete iff all idempotent endomorphisms `p`
split as a composition `p = e ≫ i` with `i ≫ e = 𝟙 _` -/
class IsIdempotentComplete : Prop where
  idempotents_split : ∀ (X : C) (p : X ⟶ X), p ≫ p = p → ∃ (Y : C)(i : Y ⟶ X)(e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p

namespace Idempotents

/-- A category is idempotent complete iff for all idempotent endomorphisms,
the equalizer of the identity and this idempotent exists. -/
theorem is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent :
    IsIdempotentComplete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasEqualizer (𝟙 X) p := by
  constructor
  · intro
    intro X p hp
    rcases is_idempotent_complete.idempotents_split X p hp with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
    exact
      ⟨Nonempty.intro
          { Cone :=
              fork.of_ι i
                (show i ≫ 𝟙 X = i ≫ p by
                  rw [comp_id, ← h₂, ← assoc, h₁, id_comp]),
            IsLimit := by
              apply fork.is_limit.mk'
              intro s
              refine' ⟨s.ι ≫ e, _⟩
              constructor
              · erw [assoc, h₂, ← limits.fork.condition s, comp_id]
                
              · intro m hm
                rw [fork.ι_of_ι] at hm
                rw [← hm]
                simp only [hm, ← assoc, ← h₁]
                exact (comp_id m).symm
                 }⟩
    
  · intro h
    refine' ⟨_⟩
    intro X p hp
    have := h X p hp
    use equalizer (𝟙 X) p
    use equalizer.ι (𝟙 X) p
    use
      equalizer.lift p
        (show p ≫ 𝟙 X = p ≫ p by
          rw [hp, comp_id])
    constructor
    · ext
      rw [assoc, equalizer.lift_ι, id_comp]
      conv => rhs erw [← comp_id (equalizer.ι (𝟙 X) p)]
      exact (limits.fork.condition (equalizer.fork (𝟙 X) p)).symm
      
    · rw [equalizer.lift_ι]
      
    

variable {C}

/-- In a preadditive category, when `p : X ⟶ X` is idempotent,
then `𝟙 X - p` is also idempotent. -/
theorem idem_of_id_sub_idem [Preadditive C] {X : C} (p : X ⟶ X) (hp : p ≫ p = p) : (𝟙 _ - p) ≫ (𝟙 _ - p) = 𝟙 _ - p := by
  simp only [← comp_sub, ← sub_comp, ← id_comp, ← comp_id, ← hp, ← sub_self, ← sub_zero]

variable (C)

/-- A preadditive category is pseudoabelian iff all idempotent endomorphisms have a kernel. -/
theorem is_idempotent_complete_iff_idempotents_have_kernels [Preadditive C] :
    IsIdempotentComplete C ↔ ∀ (X : C) (p : X ⟶ X), p ≫ p = p → HasKernel p := by
  rw [is_idempotent_complete_iff_has_equalizer_of_id_and_idempotent]
  constructor
  · intro h X p hp
    have := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    convert has_kernel_of_has_equalizer (𝟙 X) (𝟙 X - p)
    rw [sub_sub_cancel]
    
  · intro h X p hp
    have : has_kernel (𝟙 _ - p) := h X (𝟙 _ - p) (idem_of_id_sub_idem p hp)
    apply preadditive.has_equalizer_of_has_kernel
    

/-- An abelian category is idempotent complete. -/
instance (priority := 100) is_idempotent_complete_of_abelian (D : Type _) [Category D] [Abelian D] :
    IsIdempotentComplete D := by
  rw [is_idempotent_complete_iff_idempotents_have_kernels]
  intros
  infer_instance

variable {C}

theorem split_imp_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X') (hpp' : p ≫ φ.Hom = φ.Hom ≫ p')
    (h : ∃ (Y : C)(i : Y ⟶ X)(e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) :
    ∃ (Y' : C)(i' : Y' ⟶ X')(e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' := by
  rcases h with ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y, i ≫ φ.hom, φ.inv ≫ e
  constructor
  · slice_lhs 2 3 => rw [φ.hom_inv_id]
    rw [id_comp, h₁]
    
  · slice_lhs 2 3 => rw [h₂]
    rw [hpp', ← assoc, φ.inv_hom_id, id_comp]
    

theorem split_iff_of_iso {X X' : C} (φ : X ≅ X') (p : X ⟶ X) (p' : X' ⟶ X') (hpp' : p ≫ φ.Hom = φ.Hom ≫ p') :
    (∃ (Y : C)(i : Y ⟶ X)(e : X ⟶ Y), i ≫ e = 𝟙 Y ∧ e ≫ i = p) ↔
      ∃ (Y' : C)(i' : Y' ⟶ X')(e' : X' ⟶ Y'), i' ≫ e' = 𝟙 Y' ∧ e' ≫ i' = p' :=
  by
  constructor
  · exact split_imp_of_iso φ p p' hpp'
    
  · apply split_imp_of_iso φ.symm p' p
    rw [← comp_id p, ← φ.hom_inv_id]
    slice_rhs 2 3 => rw [hpp']
    slice_rhs 1 2 => erw [φ.inv_hom_id]
    simpa only [← id_comp]
    

theorem Equivalence.is_idempotent_complete {D : Type _} [Category D] (ε : C ≌ D) (h : IsIdempotentComplete C) :
    IsIdempotentComplete D := by
  refine' ⟨_⟩
  intro X' p hp
  let φ := ε.counit_iso.symm.app X'
  erw
    [split_iff_of_iso φ p (φ.inv ≫ p ≫ φ.hom)
      (by
        slice_rhs 1 2 => rw [φ.hom_inv_id]
        rw [id_comp])]
  rcases is_idempotent_complete.idempotents_split (ε.inverse.obj X') (ε.inverse.map p)
      (by
        rw [← ε.inverse.map_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use ε.functor.obj Y, ε.functor.map i, ε.functor.map e
  constructor
  · rw [← ε.functor.map_comp, h₁, ε.functor.map_id]
    
  · simpa only [ε.functor.map_comp, ← h₂, ← equivalence.fun_inv_map]
    

/-- If `C` and `D` are equivalent categories, that `C` is idempotent complete iff `D` is. -/
theorem is_idempotent_complete_iff_of_equivalence {D : Type _} [Category D] (ε : C ≌ D) :
    IsIdempotentComplete C ↔ IsIdempotentComplete D := by
  constructor
  · exact equivalence.is_idempotent_complete ε
    
  · exact equivalence.is_idempotent_complete ε.symm
    

theorem is_idempotent_complete_of_is_idempotent_complete_opposite (h : IsIdempotentComplete Cᵒᵖ) :
    IsIdempotentComplete C := by
  refine' ⟨_⟩
  intro X p hp
  rcases is_idempotent_complete.idempotents_split (op X) p.op
      (by
        rw [← op_comp, hp]) with
    ⟨Y, i, e, ⟨h₁, h₂⟩⟩
  use Y.unop, e.unop, i.unop
  constructor
  · simpa only [unop_comp, ← h₁]
    
  · simpa only [unop_comp, ← h₂]
    

theorem is_idempotent_complete_iff_opposite : IsIdempotentComplete Cᵒᵖ ↔ IsIdempotentComplete C := by
  constructor
  · exact is_idempotent_complete_of_is_idempotent_complete_opposite
    
  · intro h
    apply is_idempotent_complete_of_is_idempotent_complete_opposite
    rw [is_idempotent_complete_iff_of_equivalence (op_op_equivalence C)]
    exact h
    

instance [IsIdempotentComplete C] : IsIdempotentComplete Cᵒᵖ := by
  rwa [is_idempotent_complete_iff_opposite]

end Idempotents

end CategoryTheory

