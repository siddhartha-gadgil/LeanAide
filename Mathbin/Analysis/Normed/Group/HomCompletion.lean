/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
import Mathbin.Analysis.Normed.Group.Hom
import Mathbin.Analysis.Normed.Group.Completion

/-!
# Completion of normed group homs

Given two (semi) normed groups `G` and `H` and a normed group hom `f : normed_group_hom G H`,
we build and study a normed group hom
`f.completion  : normed_group_hom (completion G) (completion H)` such that the diagram

```
                   f
     G       ----------->     H

     |                        |
     |                        |
     |                        |
     V                        V

completion G -----------> completion H
            f.completion
```

commutes. The map itself comes from the general theory of completion of uniform spaces, but here
we want a normed group hom, study its operator norm and kernel.

The vertical maps in the above diagrams are also normed group homs constructed in this file.

## Main definitions and results:

* `normed_group_hom.completion`: see the discussion above.
* `normed_group.to_compl : normed_group_hom G (completion G)`: the canonical map from `G` to its
  completion, as a normed group hom
* `normed_group_hom.completion_to_compl`: the above diagram indeed commutes.
* `normed_group_hom.norm_completion`: `∥f.completion∥ = ∥f∥`
* `normed_group_hom.ker_le_ker_completion`: the kernel of `f.completion` contains the image of the
  kernel of `f`.
* `normed_group_hom.ker_completion`: the kernel of `f.completion` is the closure of the image of the
  kernel of `f` under an assumption that `f` is quantitatively surjective onto its image.
* `normed_group_hom.extension` : if `H` is complete, the extension of `f : normed_group_hom G H`
  to a `normed_group_hom (completion G) H`.
-/


noncomputable section

open Set NormedGroupHom UniformSpace

section Completion

variable {G : Type _} [SemiNormedGroup G]

variable {H : Type _} [SemiNormedGroup H]

variable {K : Type _} [SemiNormedGroup K]

/-- The normed group hom induced between completions. -/
def NormedGroupHom.completion (f : NormedGroupHom G H) : NormedGroupHom (Completion G) (Completion H) :=
  { f.toAddMonoidHom.Completion f.Continuous with
    bound' := by
      use ∥f∥
      intro y
      apply completion.induction_on y
      · exact
          is_closed_le (continuous_norm.comp <| f.to_add_monoid_hom.continuous_completion f.continuous)
            (continuous_const.mul continuous_norm)
        
      · intro x
        change ∥f.to_add_monoid_hom.completion _ ↑x∥ ≤ ∥f∥ * ∥↑x∥
        rw [f.to_add_monoid_hom.completion_coe f.continuous]
        simp only [← completion.norm_coe]
        exact f.le_op_norm x
         }

theorem NormedGroupHom.completion_def (f : NormedGroupHom G H) (x : Completion G) :
    f.Completion x = Completion.map f x :=
  rfl

@[simp]
theorem NormedGroupHom.completion_coe_to_fun (f : NormedGroupHom G H) :
    (f.Completion : Completion G → Completion H) = Completion.map f := by
  ext x
  exact NormedGroupHom.completion_def f x

@[simp]
theorem NormedGroupHom.completion_coe (f : NormedGroupHom G H) (g : G) : f.Completion g = f g :=
  Completion.map_coe f.UniformContinuous _

/-- Completion of normed group homs as a normed group hom. -/
@[simps]
def normedGroupHomCompletionHom : NormedGroupHom G H →+ NormedGroupHom (Completion G) (Completion H) where
  toFun := NormedGroupHom.completion
  map_zero' := by
    apply to_add_monoid_hom_injective
    exact AddMonoidHom.completion_zero
  map_add' := fun f g => by
    apply to_add_monoid_hom_injective
    exact f.to_add_monoid_hom.completion_add g.to_add_monoid_hom f.continuous g.continuous

@[simp]
theorem NormedGroupHom.completion_id : (NormedGroupHom.id G).Completion = NormedGroupHom.id (Completion G) := by
  ext x
  rw [NormedGroupHom.completion_def, NormedGroupHom.coe_id, completion.map_id]
  rfl

theorem NormedGroupHom.completion_comp (f : NormedGroupHom G H) (g : NormedGroupHom H K) :
    g.Completion.comp f.Completion = (g.comp f).Completion := by
  ext x
  rw [NormedGroupHom.coe_comp, NormedGroupHom.completion_def, NormedGroupHom.completion_coe_to_fun,
    NormedGroupHom.completion_coe_to_fun,
    completion.map_comp (NormedGroupHom.uniform_continuous _) (NormedGroupHom.uniform_continuous _)]
  rfl

theorem NormedGroupHom.completion_neg (f : NormedGroupHom G H) : (-f).Completion = -f.Completion :=
  map_neg (normedGroupHomCompletionHom : NormedGroupHom G H →+ _) f

theorem NormedGroupHom.completion_add (f g : NormedGroupHom G H) : (f + g).Completion = f.Completion + g.Completion :=
  normedGroupHomCompletionHom.map_add f g

theorem NormedGroupHom.completion_sub (f g : NormedGroupHom G H) : (f - g).Completion = f.Completion - g.Completion :=
  map_sub (normedGroupHomCompletionHom : NormedGroupHom G H →+ _) f g

@[simp]
theorem NormedGroupHom.zero_completion : (0 : NormedGroupHom G H).Completion = 0 :=
  normedGroupHomCompletionHom.map_zero

/-- The map from a normed group to its completion, as a normed group hom. -/
def NormedGroup.toCompl : NormedGroupHom G (Completion G) where
  toFun := coe
  map_add' := Completion.toCompl.map_add
  bound' :=
    ⟨1, by
      simp [← le_reflₓ]⟩

open NormedGroup

theorem NormedGroup.norm_to_compl (x : G) : ∥toCompl x∥ = ∥x∥ :=
  Completion.norm_coe x

theorem NormedGroup.dense_range_to_compl : DenseRange (toCompl : G → Completion G) :=
  Completion.dense_inducing_coe.dense

@[simp]
theorem NormedGroupHom.completion_to_compl (f : NormedGroupHom G H) : f.Completion.comp toCompl = toCompl.comp f := by
  ext x
  change f.completion x = _
  simpa

@[simp]
theorem NormedGroupHom.norm_completion (f : NormedGroupHom G H) : ∥f.Completion∥ = ∥f∥ := by
  apply f.completion.op_norm_eq_of_bounds (norm_nonneg _)
  · intro x
    apply completion.induction_on x
    · apply is_closed_le
      continuity
      
    · intro g
      simp [← f.le_op_norm g]
      
    
  · intro N N_nonneg hN
    apply f.op_norm_le_bound N_nonneg
    intro x
    simpa using hN x
    

theorem NormedGroupHom.ker_le_ker_completion (f : NormedGroupHom G H) :
    (toCompl.comp <| incl f.ker).range ≤ f.Completion.ker := by
  intro a h
  replace h : ∃ y : f.ker, to_compl (y : G) = a
  · simpa using h
    
  rcases h with ⟨⟨g, g_in : g ∈ f.ker⟩, rfl⟩
  rw [f.mem_ker] at g_in
  change f.completion (g : completion G) = 0
  simp [← NormedGroupHom.mem_ker, ← f.completion_coe g, ← g_in, ← completion.coe_zero]

theorem NormedGroupHom.ker_completion {f : NormedGroupHom G H} {C : ℝ} (h : f.SurjectiveOnWith f.range C) :
    (f.Completion.ker : Set <| Completion G) = Closure (toCompl.comp <| incl f.ker).range := by
  rcases h.exists_pos with ⟨C', C'_pos, hC'⟩
  apply le_antisymmₓ
  · intro hatg hatg_in
    rw [SemiNormedGroup.mem_closure_iff]
    intro ε ε_pos
    have hCf : 0 ≤ C' * ∥f∥ := (zero_le_mul_left C'_pos).mpr (norm_nonneg f)
    have ineq : 0 < 1 + C' * ∥f∥ := by
      linarith
    set δ := ε / (1 + C' * ∥f∥)
    have δ_pos : δ > 0 := div_pos ε_pos ineq
    obtain ⟨_, ⟨g : G, rfl⟩, hg : ∥hatg - g∥ < δ⟩ :=
      semi_normed_group.mem_closure_iff.mp (completion.dense_inducing_coe.dense hatg) δ δ_pos
    obtain ⟨g' : G, hgg' : f g' = f g, hfg : ∥g'∥ ≤ C' * ∥f g∥⟩ := hC' (f g) (mem_range_self g)
    have mem_ker : g - g' ∈ f.ker := by
      rw [f.mem_ker, map_sub, sub_eq_zero.mpr hgg'.symm]
    have : ∥f g∥ ≤ ∥f∥ * ∥hatg - g∥
    calc ∥f g∥ = ∥f.completion g∥ := by
        rw [f.completion_coe, completion.norm_coe]_ = ∥f.completion g - 0∥ := by
        rw [sub_zero _]_ = ∥f.completion g - f.completion hatg∥ := by
        rw [(f.completion.mem_ker _).mp hatg_in]_ = ∥f.completion (g - hatg)∥ := by
        rw [map_sub]_ ≤ ∥f.completion∥ * ∥(g : completion G) - hatg∥ :=
        f.completion.le_op_norm _ _ = ∥f∥ * ∥hatg - g∥ := by
        rw [norm_sub_rev, f.norm_completion]
    have : ∥(g' : completion G)∥ ≤ C' * ∥f∥ * ∥hatg - g∥
    calc ∥(g' : completion G)∥ = ∥g'∥ := completion.norm_coe _ _ ≤ C' * ∥f g∥ := hfg _ ≤ C' * ∥f∥ * ∥hatg - g∥ := by
        rw [mul_assoc]
        exact (mul_le_mul_left C'_pos).mpr this
    refine' ⟨g - g', _, _⟩
    · norm_cast
      rw [NormedGroupHom.comp_range]
      apply AddSubgroup.mem_map_of_mem
      simp only [← incl_range, ← mem_ker]
      
    · calc ∥hatg - (g - g')∥ = ∥hatg - g + g'∥ := by
          abel _ ≤ ∥hatg - g∥ + ∥(g' : completion G)∥ := norm_add_le _ _ _ < δ + C' * ∥f∥ * ∥hatg - g∥ := by
          linarith _ ≤ δ + C' * ∥f∥ * δ :=
          add_le_add_left (mul_le_mul_of_nonneg_left hg.le hCf) δ _ = (1 + C' * ∥f∥) * δ := by
          ring _ = ε := mul_div_cancel' _ ineq.ne.symm
      
    
  · rw [← f.completion.is_closed_ker.closure_eq]
    exact closure_mono f.ker_le_ker_completion
    

end Completion

section Extension

variable {G : Type _} [SemiNormedGroup G]

variable {H : Type _} [SemiNormedGroup H] [SeparatedSpace H] [CompleteSpace H]

/-- If `H` is complete, the extension of `f : normed_group_hom G H` to a
`normed_group_hom (completion G) H`. -/
def NormedGroupHom.extension (f : NormedGroupHom G H) : NormedGroupHom (Completion G) H :=
  { f.toAddMonoidHom.extension f.Continuous with
    bound' := by
      refine' ⟨∥f∥, fun v => completion.induction_on v (is_closed_le _ _) fun a => _⟩
      · exact Continuous.comp continuous_norm completion.continuous_extension
        
      · exact Continuous.mul continuous_const continuous_norm
        
      · rw [completion.norm_coe, AddMonoidHom.to_fun_eq_coe, AddMonoidHom.extension_coe]
        exact le_op_norm f a
         }

theorem NormedGroupHom.extension_def (f : NormedGroupHom G H) (v : G) : f.extension v = Completion.extension f v :=
  rfl

@[simp]
theorem NormedGroupHom.extension_coe (f : NormedGroupHom G H) (v : G) : f.extension v = f v :=
  AddMonoidHom.extension_coe _ f.Continuous _

theorem NormedGroupHom.extension_coe_to_fun (f : NormedGroupHom G H) :
    (f.extension : Completion G → H) = Completion.extension f :=
  rfl

theorem NormedGroupHom.extension_unique (f : NormedGroupHom G H) {g : NormedGroupHom (Completion G) H}
    (hg : ∀ v, f v = g v) : f.extension = g := by
  ext v
  rw [NormedGroupHom.extension_coe_to_fun,
    completion.extension_unique f.uniform_continuous g.uniform_continuous fun a => hg a]

end Extension

