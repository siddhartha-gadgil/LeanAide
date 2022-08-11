/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Analysis.NormedSpace.Basic

/-!
# Extended norm

In this file we define a structure `enorm 𝕜 V` representing an extended norm (i.e., a norm that can
take the value `∞`) on a vector space `V` over a normed field `𝕜`. We do not use `class` for
an `enorm` because the same space can have more than one extended norm. For example, the space of
measurable functions `f : α → ℝ` has a family of `L_p` extended norms.

We prove some basic inequalities, then define

* `emetric_space` structure on `V` corresponding to `e : enorm 𝕜 V`;
* the subspace of vectors with finite norm, called `e.finite_subspace`;
* a `normed_space` structure on this space.

The last definition is an instance because the type involves `e`.

## Implementation notes

We do not define extended normed groups. They can be added to the chain once someone will need them.

## Tags

normed space, extended norm
-/


noncomputable section

attribute [local instance] Classical.propDecidable

open Ennreal

/-- Extended norm on a vector space. As in the case of normed spaces, we require only
`∥c • x∥ ≤ ∥c∥ * ∥x∥` in the definition, then prove an equality in `map_smul`. -/
structure Enorm (𝕜 : Type _) (V : Type _) [NormedField 𝕜] [AddCommGroupₓ V] [Module 𝕜 V] where
  toFun : V → ℝ≥0∞
  eq_zero' : ∀ x, to_fun x = 0 → x = 0
  map_add_le' : ∀ x y : V, to_fun (x + y) ≤ to_fun x + to_fun y
  map_smul_le' : ∀ (c : 𝕜) (x : V), to_fun (c • x) ≤ ∥c∥₊ * to_fun x

namespace Enorm

variable {𝕜 : Type _} {V : Type _} [NormedField 𝕜] [AddCommGroupₓ V] [Module 𝕜 V] (e : Enorm 𝕜 V)

instance : CoeFun (Enorm 𝕜 V) fun _ => V → ℝ≥0∞ :=
  ⟨Enorm.toFun⟩

theorem coe_fn_injective : Function.Injective (coeFn : Enorm 𝕜 V → V → ℝ≥0∞) := fun e₁ e₂ h => by
  cases e₁ <;> cases e₂ <;> congr <;> exact h

@[ext]
theorem ext {e₁ e₂ : Enorm 𝕜 V} (h : ∀ x, e₁ x = e₂ x) : e₁ = e₂ :=
  coe_fn_injective <| funext h

theorem ext_iff {e₁ e₂ : Enorm 𝕜 V} : e₁ = e₂ ↔ ∀ x, e₁ x = e₂ x :=
  ⟨fun h x => h ▸ rfl, ext⟩

@[simp, norm_cast]
theorem coe_inj {e₁ e₂ : Enorm 𝕜 V} : (e₁ : V → ℝ≥0∞) = e₂ ↔ e₁ = e₂ :=
  coe_fn_injective.eq_iff

@[simp]
theorem map_smul (c : 𝕜) (x : V) : e (c • x) = ∥c∥₊ * e x :=
  le_antisymmₓ (e.map_smul_le' c x) <| by
    by_cases' hc : c = 0
    · simp [← hc]
      
    calc (∥c∥₊ : ℝ≥0∞) * e x = ∥c∥₊ * e (c⁻¹ • c • x) := by
        rw [inv_smul_smul₀ hc]_ ≤ ∥c∥₊ * (∥c⁻¹∥₊ * e (c • x)) := _ _ = e (c • x) := _
    · exact Ennreal.mul_le_mul le_rfl (e.map_smul_le' _ _)
      
    · rw [← mul_assoc, nnnorm_inv, Ennreal.coe_inv, Ennreal.mul_inv_cancel _ Ennreal.coe_ne_top, one_mulₓ] <;>
        simp [← hc]
      

@[simp]
theorem map_zero : e 0 = 0 := by
  rw [← zero_smul 𝕜 (0 : V), e.map_smul]
  norm_num

@[simp]
theorem eq_zero_iff {x : V} : e x = 0 ↔ x = 0 :=
  ⟨e.eq_zero' x, fun h => h.symm ▸ e.map_zero⟩

@[simp]
theorem map_neg (x : V) : e (-x) = e x :=
  calc
    e (-x) = ∥(-1 : 𝕜)∥₊ * e x := by
      rw [← map_smul, neg_one_smul]
    _ = e x := by
      simp
    

theorem map_sub_rev (x y : V) : e (x - y) = e (y - x) := by
  rw [← neg_sub, e.map_neg]

theorem map_add_le (x y : V) : e (x + y) ≤ e x + e y :=
  e.map_add_le' x y

theorem map_sub_le (x y : V) : e (x - y) ≤ e x + e y :=
  calc
    e (x - y) = e (x + -y) := by
      rw [sub_eq_add_neg]
    _ ≤ e x + e (-y) := e.map_add_le x (-y)
    _ = e x + e y := by
      rw [e.map_neg]
    

instance : PartialOrderₓ (Enorm 𝕜 V) where
  le := fun e₁ e₂ => ∀ x, e₁ x ≤ e₂ x
  le_refl := fun e x => le_rfl
  le_trans := fun e₁ e₂ e₃ h₁₂ h₂₃ x => le_transₓ (h₁₂ x) (h₂₃ x)
  le_antisymm := fun e₁ e₂ h₁₂ h₂₁ => ext fun x => le_antisymmₓ (h₁₂ x) (h₂₁ x)

/-- The `enorm` sending each non-zero vector to infinity. -/
noncomputable instance : HasTop (Enorm 𝕜 V) :=
  ⟨{ toFun := fun x => if x = 0 then 0 else ⊤,
      eq_zero' := fun x => by
        split_ifs <;> simp [*],
      map_add_le' := fun x y => by
        split_ifs with hxy hx hy hy hx hy hy <;>
          try
            simp [*]
        simpa [← hx, ← hy] using hxy,
      map_smul_le' := fun c x => by
        split_ifs with hcx hx hx <;> simp only [← smul_eq_zero, ← not_or_distrib] at hcx
        · simp only [← mul_zero, ← le_reflₓ]
          
        · have : c = 0 := by
            tauto
          simp [← this]
          
        · tauto
          
        · simp [← hcx.1]
           }⟩

noncomputable instance : Inhabited (Enorm 𝕜 V) :=
  ⟨⊤⟩

theorem top_map {x : V} (hx : x ≠ 0) : (⊤ : Enorm 𝕜 V) x = ⊤ :=
  if_neg hx

noncomputable instance : OrderTop (Enorm 𝕜 V) where
  top := ⊤
  le_top := fun e x =>
    if h : x = 0 then by
      simp [← h]
    else by
      simp [← top_map h]

noncomputable instance : SemilatticeSup (Enorm 𝕜 V) :=
  { Enorm.partialOrder with le := (· ≤ ·), lt := (· < ·),
    sup := fun e₁ e₂ =>
      { toFun := fun x => max (e₁ x) (e₂ x), eq_zero' := fun x h => e₁.eq_zero_iff.1 (Ennreal.max_eq_zero_iff.1 h).1,
        map_add_le' := fun x y =>
          max_leₓ (le_transₓ (e₁.map_add_le _ _) <| add_le_add (le_max_leftₓ _ _) (le_max_leftₓ _ _))
            (le_transₓ (e₂.map_add_le _ _) <| add_le_add (le_max_rightₓ _ _) (le_max_rightₓ _ _)),
        map_smul_le' := fun c x =>
          le_of_eqₓ <| by
            simp only [← map_smul, ← Ennreal.mul_max] },
    le_sup_left := fun e₁ e₂ x => le_max_leftₓ _ _, le_sup_right := fun e₁ e₂ x => le_max_rightₓ _ _,
    sup_le := fun e₁ e₂ e₃ h₁ h₂ x => max_leₓ (h₁ x) (h₂ x) }

@[simp, norm_cast]
theorem coe_max (e₁ e₂ : Enorm 𝕜 V) : ⇑(e₁⊔e₂) = fun x => max (e₁ x) (e₂ x) :=
  rfl

@[norm_cast]
theorem max_map (e₁ e₂ : Enorm 𝕜 V) (x : V) : (e₁⊔e₂) x = max (e₁ x) (e₂ x) :=
  rfl

/-- Structure of an `emetric_space` defined by an extended norm. -/
@[reducible]
def emetricSpace : EmetricSpace V where
  edist := fun x y => e (x - y)
  edist_self := fun x => by
    simp
  eq_of_edist_eq_zero := fun x y => by
    simp [← sub_eq_zero]
  edist_comm := e.map_sub_rev
  edist_triangle := fun x y z =>
    calc
      e (x - z) = e (x - y + (y - z)) := by
        rw [sub_add_sub_cancel]
      _ ≤ e (x - y) + e (y - z) := e.map_add_le (x - y) (y - z)
      

/-- The subspace of vectors with finite enorm. -/
def finiteSubspace : Subspace 𝕜 V where
  Carrier := { x | e x < ⊤ }
  zero_mem' := by
    simp
  add_mem' := fun x y hx hy => lt_of_le_of_ltₓ (e.map_add_le x y) (Ennreal.add_lt_top.2 ⟨hx, hy⟩)
  smul_mem' := fun c x (hx : _ < _) =>
    calc
      e (c • x) = ∥c∥₊ * e x := e.map_smul c x
      _ < ⊤ := Ennreal.mul_lt_top Ennreal.coe_ne_top hx.Ne
      

/-- Metric space structure on `e.finite_subspace`. We use `emetric_space.to_metric_space`
to ensure that this definition agrees with `e.emetric_space`. -/
instance : MetricSpace e.finiteSubspace := by
  let this := e.emetric_space
  refine' EmetricSpace.toMetricSpace fun x y => _
  change e (x - y) ≠ ⊤
  exact ne_top_of_le_ne_top (Ennreal.add_lt_top.2 ⟨x.2, y.2⟩).Ne (e.map_sub_le x y)

theorem finite_dist_eq (x y : e.finiteSubspace) : dist x y = (e (x - y)).toReal :=
  rfl

theorem finite_edist_eq (x y : e.finiteSubspace) : edist x y = e (x - y) :=
  rfl

/-- Normed group instance on `e.finite_subspace`. -/
instance : NormedGroup e.finiteSubspace :=
  { finiteSubspace.metricSpace e, Submodule.addCommGroup _ with norm := fun x => (e x).toReal,
    dist_eq := fun x y => rfl }

theorem finite_norm_eq (x : e.finiteSubspace) : ∥x∥ = (e x).toReal :=
  rfl

/-- Normed space instance on `e.finite_subspace`. -/
instance :
    NormedSpace 𝕜 e.finiteSubspace where norm_smul_le := fun c x =>
    le_of_eqₓ <| by
      simp [← finite_norm_eq, ← Ennreal.to_real_mul]

end Enorm

