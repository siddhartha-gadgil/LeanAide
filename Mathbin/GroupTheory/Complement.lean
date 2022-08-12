/-
Copyright (c) 2021 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
import Mathbin.GroupTheory.GroupAction.Quotient
import Mathbin.GroupTheory.OrderOfElement

/-!
# Complements

In this file we define the complement of a subgroup.

## Main definitions

- `is_complement S T` where `S` and `T` are subsets of `G` states that every `g : G` can be
  written uniquely as a product `s * t` for `s ∈ S`, `t ∈ T`.
- `left_transversals T` where `T` is a subset of `G` is the set of all left-complements of `T`,
  i.e. the set of all `S : set G` that contain exactly one element of each left coset of `T`.
- `right_transversals S` where `S` is a subset of `G` is the set of all right-complements of `S`,
  i.e. the set of all `T : set G` that contain exactly one element of each right coset of `S`.

## Main results

- `is_complement_of_coprime` : Subgroups of coprime order are complements.
-/


open BigOperators

namespace Subgroup

variable {G : Type _} [Groupₓ G] (H K : Subgroup G) (S T : Set G)

/-- `S` and `T` are complements if `(*) : S × T → G` is a bijection.
  This notion generalizes left transversals, right transversals, and complementary subgroups. -/
@[to_additive "`S` and `T` are complements if `(*) : S × T → G` is a bijection"]
def IsComplement : Prop :=
  Function.Bijective fun x : S × T => x.1.1 * x.2.1

/-- `H` and `K` are complements if `(*) : H × K → G` is a bijection -/
@[to_additive "`H` and `K` are complements if `(*) : H × K → G` is a bijection"]
abbrev IsComplement' :=
  IsComplement (H : Set G) (K : Set G)

/-- The set of left-complements of `T : set G` -/
@[to_additive "The set of left-complements of `T : set G`"]
def LeftTransversals : Set (Set G) :=
  { S : Set G | IsComplement S T }

/-- The set of right-complements of `S : set G` -/
@[to_additive "The set of right-complements of `S : set G`"]
def RightTransversals : Set (Set G) :=
  { T : Set G | IsComplement S T }

variable {H K S T}

@[to_additive]
theorem is_complement'_def : IsComplement' H K ↔ IsComplement (H : Set G) (K : Set G) :=
  Iff.rfl

@[to_additive]
theorem is_complement_iff_exists_unique : IsComplement S T ↔ ∀ g : G, ∃! x : S × T, x.1.1 * x.2.1 = g :=
  Function.bijective_iff_exists_unique _

@[to_additive]
theorem IsComplement.exists_unique (h : IsComplement S T) (g : G) : ∃! x : S × T, x.1.1 * x.2.1 = g :=
  is_complement_iff_exists_unique.mp h g

@[to_additive]
theorem IsComplement'.symm (h : IsComplement' H K) : IsComplement' K H := by
  let ϕ : H × K ≃ K × H :=
    Equivₓ.mk (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => ⟨x.2⁻¹, x.1⁻¹⟩) (fun x => Prod.extₓ (inv_invₓ _) (inv_invₓ _))
      fun x => Prod.extₓ (inv_invₓ _) (inv_invₓ _)
  let ψ : G ≃ G := Equivₓ.mk (fun g : G => g⁻¹) (fun g : G => g⁻¹) inv_invₓ inv_invₓ
  suffices (ψ ∘ fun x : H × K => x.1.1 * x.2.1) = (fun x : K × H => x.1.1 * x.2.1) ∘ ϕ by
    rwa [is_complement'_def, is_complement, ← Equivₓ.bijective_comp, ← this, Equivₓ.comp_bijective]
  exact funext fun x => mul_inv_rev _ _

@[to_additive]
theorem is_complement'_comm : IsComplement' H K ↔ IsComplement' K H :=
  ⟨IsComplement'.symm, IsComplement'.symm⟩

@[to_additive]
theorem is_complement_top_singleton {g : G} : IsComplement (⊤ : Set G) {g} :=
  ⟨fun ⟨x, _, rfl⟩ ⟨y, _, rfl⟩ h => Prod.extₓ (Subtype.ext (mul_right_cancelₓ h)) rfl, fun x =>
    ⟨⟨⟨x * g⁻¹, ⟨⟩⟩, g, rfl⟩, inv_mul_cancel_right x g⟩⟩

@[to_additive]
theorem is_complement_singleton_top {g : G} : IsComplement ({g} : Set G) ⊤ :=
  ⟨fun ⟨⟨_, rfl⟩, x⟩ ⟨⟨_, rfl⟩, y⟩ h => Prod.extₓ rfl (Subtype.ext (mul_left_cancelₓ h)), fun x =>
    ⟨⟨⟨g, rfl⟩, g⁻¹ * x, ⟨⟩⟩, mul_inv_cancel_left g x⟩⟩

@[to_additive]
theorem is_complement_singleton_left {g : G} : IsComplement {g} S ↔ S = ⊤ := by
  refine' ⟨fun h => top_le_iff.mp fun x hx => _, fun h => (congr_arg _ h).mpr is_complement_singleton_top⟩
  obtain ⟨⟨⟨z, rfl : z = g⟩, y, _⟩, hy⟩ := h.2 (g * x)
  rwa [← mul_left_cancelₓ hy]

@[to_additive]
theorem is_complement_singleton_right {g : G} : IsComplement S {g} ↔ S = ⊤ := by
  refine' ⟨fun h => top_le_iff.mp fun x hx => _, fun h => (congr_arg _ h).mpr is_complement_top_singleton⟩
  obtain ⟨y, hy⟩ := h.2 (x * g)
  conv_rhs at hy => rw [← show y.2.1 = g from y.2.2]
  rw [← mul_right_cancelₓ hy]
  exact y.1.2

@[to_additive]
theorem is_complement_top_left : IsComplement ⊤ S ↔ ∃ g : G, S = {g} := by
  refine' ⟨fun h => set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, fun a ha b hb => _⟩, _⟩
  · obtain ⟨a, ha⟩ := h.2 1
    exact ⟨a.2.1, a.2.2⟩
    
  · have : (⟨⟨_, mem_top a⁻¹⟩, ⟨a, ha⟩⟩ : (⊤ : Set G) × S) = ⟨⟨_, mem_top b⁻¹⟩, ⟨b, hb⟩⟩ :=
      h.1 ((inv_mul_selfₓ a).trans (inv_mul_selfₓ b).symm)
    exact subtype.ext_iff.mp (prod.ext_iff.mp this).2
    
  · rintro ⟨g, rfl⟩
    exact is_complement_top_singleton
    

@[to_additive]
theorem is_complement_top_right : IsComplement S ⊤ ↔ ∃ g : G, S = {g} := by
  refine' ⟨fun h => set.exists_eq_singleton_iff_nonempty_subsingleton.mpr ⟨_, fun a ha b hb => _⟩, _⟩
  · obtain ⟨a, ha⟩ := h.2 1
    exact ⟨a.1.1, a.1.2⟩
    
  · have : (⟨⟨a, ha⟩, ⟨_, mem_top a⁻¹⟩⟩ : S × (⊤ : Set G)) = ⟨⟨b, hb⟩, ⟨_, mem_top b⁻¹⟩⟩ :=
      h.1 ((mul_inv_selfₓ a).trans (mul_inv_selfₓ b).symm)
    exact subtype.ext_iff.mp (prod.ext_iff.mp this).1
    
  · rintro ⟨g, rfl⟩
    exact is_complement_singleton_top
    

@[to_additive]
theorem is_complement'_top_bot : IsComplement' (⊤ : Subgroup G) ⊥ :=
  is_complement_top_singleton

@[to_additive]
theorem is_complement'_bot_top : IsComplement' (⊥ : Subgroup G) ⊤ :=
  is_complement_singleton_top

@[simp, to_additive]
theorem is_complement'_bot_left : IsComplement' ⊥ H ↔ H = ⊤ :=
  is_complement_singleton_left.trans coe_eq_univ

@[simp, to_additive]
theorem is_complement'_bot_right : IsComplement' H ⊥ ↔ H = ⊤ :=
  is_complement_singleton_right.trans coe_eq_univ

@[simp, to_additive]
theorem is_complement'_top_left : IsComplement' ⊤ H ↔ H = ⊥ :=
  is_complement_top_left.trans coe_eq_singleton

@[simp, to_additive]
theorem is_complement'_top_right : IsComplement' H ⊤ ↔ H = ⊥ :=
  is_complement_top_right.trans coe_eq_singleton

@[to_additive]
theorem mem_left_transversals_iff_exists_unique_inv_mul_mem :
    S ∈ LeftTransversals T ↔ ∀ g : G, ∃! s : S, (s : G)⁻¹ * g ∈ T := by
  rw [left_transversals, Set.mem_set_of_eq, is_complement_iff_exists_unique]
  refine' ⟨fun h g => _, fun h g => _⟩
  · obtain ⟨x, h1, h2⟩ := h g
    exact
      ⟨x.1, (congr_arg (· ∈ T) (eq_inv_mul_of_mul_eq h1)).mp x.2.2, fun y hy =>
        (prod.ext_iff.mp (h2 ⟨y, y⁻¹ * g, hy⟩ (mul_inv_cancel_left y g))).1⟩
    
  · obtain ⟨x, h1, h2⟩ := h g
    refine' ⟨⟨x, x⁻¹ * g, h1⟩, mul_inv_cancel_left x g, fun y hy => _⟩
    have := h2 y.1 ((congr_arg (· ∈ T) (eq_inv_mul_of_mul_eq hy)).mp y.2.2)
    exact Prod.extₓ this (Subtype.ext (eq_inv_mul_of_mul_eq ((congr_arg _ this).mp hy)))
    

@[to_additive]
theorem mem_right_transversals_iff_exists_unique_mul_inv_mem :
    S ∈ RightTransversals T ↔ ∀ g : G, ∃! s : S, g * (s : G)⁻¹ ∈ T := by
  rw [right_transversals, Set.mem_set_of_eq, is_complement_iff_exists_unique]
  refine' ⟨fun h g => _, fun h g => _⟩
  · obtain ⟨x, h1, h2⟩ := h g
    exact
      ⟨x.2, (congr_arg (· ∈ T) (eq_mul_inv_of_mul_eq h1)).mp x.1.2, fun y hy =>
        (prod.ext_iff.mp (h2 ⟨⟨g * y⁻¹, hy⟩, y⟩ (inv_mul_cancel_right g y))).2⟩
    
  · obtain ⟨x, h1, h2⟩ := h g
    refine' ⟨⟨⟨g * x⁻¹, h1⟩, x⟩, inv_mul_cancel_right g x, fun y hy => _⟩
    have := h2 y.2 ((congr_arg (· ∈ T) (eq_mul_inv_of_mul_eq hy)).mp y.1.2)
    exact Prod.extₓ (Subtype.ext (eq_mul_inv_of_mul_eq ((congr_arg _ this).mp hy))) this
    

@[to_additive]
theorem mem_left_transversals_iff_exists_unique_quotient_mk'_eq :
    S ∈ LeftTransversals (H : Set G) ↔ ∀ q : Quotientₓ (QuotientGroup.leftRel H), ∃! s : S, Quotientₓ.mk' s.1 = q := by
  simp_rw [mem_left_transversals_iff_exists_unique_inv_mul_mem, SetLike.mem_coe, ← QuotientGroup.eq']
  exact ⟨fun h q => Quotientₓ.induction_on' q h, fun h g => h (Quotientₓ.mk' g)⟩

@[to_additive]
theorem mem_right_transversals_iff_exists_unique_quotient_mk'_eq :
    S ∈ RightTransversals (H : Set G) ↔ ∀ q : Quotientₓ (QuotientGroup.rightRel H), ∃! s : S, Quotientₓ.mk' s.1 = q :=
  by
  simp_rw [mem_right_transversals_iff_exists_unique_mul_inv_mem, SetLike.mem_coe, ← QuotientGroup.right_rel_apply, ←
    Quotientₓ.eq']
  exact ⟨fun h q => Quotientₓ.induction_on' q h, fun h g => h (Quotientₓ.mk' g)⟩

@[to_additive]
theorem mem_left_transversals_iff_bijective :
    S ∈ LeftTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotientₓ.mk' : G → Quotientₓ (QuotientGroup.leftRel H))) :=
  mem_left_transversals_iff_exists_unique_quotient_mk'_eq.trans
    (Function.bijective_iff_exists_unique (S.restrict Quotientₓ.mk')).symm

@[to_additive]
theorem mem_right_transversals_iff_bijective :
    S ∈ RightTransversals (H : Set G) ↔
      Function.Bijective (S.restrict (Quotientₓ.mk' : G → Quotientₓ (QuotientGroup.rightRel H))) :=
  mem_right_transversals_iff_exists_unique_quotient_mk'_eq.trans
    (Function.bijective_iff_exists_unique (S.restrict Quotientₓ.mk')).symm

@[to_additive]
theorem range_mem_left_transversals {f : G ⧸ H → G} (hf : ∀ q, ↑(f q) = q) :
    Set.Range f ∈ LeftTransversals (H : Set G) :=
  mem_left_transversals_iff_bijective.mpr
    ⟨by
      rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h <;> exact congr_arg _ (((hf q₁).symm.trans h).trans (hf q₂)), fun q =>
      ⟨⟨f q, q, rfl⟩, hf q⟩⟩

@[to_additive]
theorem range_mem_right_transversals {f : Quotientₓ (QuotientGroup.rightRel H) → G}
    (hf : ∀ q, Quotientₓ.mk' (f q) = q) : Set.Range f ∈ RightTransversals (H : Set G) :=
  mem_right_transversals_iff_bijective.mpr
    ⟨by
      rintro ⟨-, q₁, rfl⟩ ⟨-, q₂, rfl⟩ h <;> exact congr_arg _ (((hf q₁).symm.trans h).trans (hf q₂)), fun q =>
      ⟨⟨f q, q, rfl⟩, hf q⟩⟩

@[to_additive]
theorem exists_left_transversal (g : G) : ∃ S ∈ LeftTransversals (H : Set G), g ∈ S := by
  classical
  refine'
    ⟨Set.Range (Function.update Quotientₓ.out' (↑g) g), range_mem_left_transversals fun q => _, g,
      Function.update_same g g Quotientₓ.out'⟩
  by_cases' hq : q = g
  · exact hq.symm ▸ congr_arg _ (Function.update_same g g Quotientₓ.out')
    
  · exact Eq.trans (congr_arg _ (Function.update_noteq hq g Quotientₓ.out')) q.out_eq'
    

@[to_additive]
theorem exists_right_transversal (g : G) : ∃ S ∈ RightTransversals (H : Set G), g ∈ S := by
  classical
  refine'
    ⟨Set.Range (Function.update Quotientₓ.out' _ g), range_mem_right_transversals fun q => _, Quotientₓ.mk' g,
      Function.update_same (Quotientₓ.mk' g) g Quotientₓ.out'⟩
  by_cases' hq : q = Quotientₓ.mk' g
  · exact hq.symm ▸ congr_arg _ (Function.update_same (Quotientₓ.mk' g) g Quotientₓ.out')
    
  · exact Eq.trans (congr_arg _ (Function.update_noteq hq g Quotientₓ.out')) q.out_eq'
    

namespace MemLeftTransversals

/-- A left transversal is in bijection with left cosets. -/
@[to_additive "A left transversal is in bijection with left cosets."]
noncomputable def toEquiv (hS : S ∈ Subgroup.LeftTransversals (H : Set G)) : G ⧸ H ≃ S :=
  (Equivₓ.ofBijective _ (Subgroup.mem_left_transversals_iff_bijective.mp hS)).symm

@[to_additive]
theorem mk'_to_equiv (hS : S ∈ Subgroup.LeftTransversals (H : Set G)) (q : G ⧸ H) :
    Quotientₓ.mk' (toEquiv hS q : G) = q :=
  (toEquiv hS).symm_apply_apply q

@[to_additive]
theorem to_equiv_apply {f : G ⧸ H → G} (hf : ∀ q, (f q : G ⧸ H) = q) (q : G ⧸ H) :
    (toEquiv (range_mem_left_transversals hf) q : G) = f q := by
  refine' (subtype.ext_iff.mp _).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (to_equiv (range_mem_left_transversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm

/-- A left transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that left coset. -/
@[to_additive
      "A left transversal can be viewed as a function mapping each element of the group\n  to the chosen representative from that left coset."]
noncomputable def toFun (hS : S ∈ Subgroup.LeftTransversals (H : Set G)) : G → S :=
  toEquiv hS ∘ Quotientₓ.mk'

@[to_additive]
theorem inv_to_fun_mul_mem (hS : S ∈ Subgroup.LeftTransversals (H : Set G)) (g : G) : (toFun hS g : G)⁻¹ * g ∈ H :=
  QuotientGroup.left_rel_apply.mp <| Quotientₓ.exact' <| mk'_to_equiv _ _

@[to_additive]
theorem inv_mul_to_fun_mem (hS : S ∈ Subgroup.LeftTransversals (H : Set G)) (g : G) : g⁻¹ * toFun hS g ∈ H :=
  (congr_arg (· ∈ H)
        (by
          rw [mul_inv_rev, inv_invₓ])).mp
    (H.inv_mem (inv_to_fun_mul_mem hS g))

end MemLeftTransversals

namespace MemRightTransversals

/-- A right transversal is in bijection with right cosets. -/
@[to_additive "A right transversal is in bijection with right cosets."]
noncomputable def toEquiv (hS : S ∈ Subgroup.RightTransversals (H : Set G)) :
    Quotientₓ (QuotientGroup.rightRel H) ≃ S :=
  (Equivₓ.ofBijective _ (Subgroup.mem_right_transversals_iff_bijective.mp hS)).symm

@[to_additive]
theorem mk'_to_equiv (hS : S ∈ Subgroup.RightTransversals (H : Set G)) (q : Quotientₓ (QuotientGroup.rightRel H)) :
    Quotientₓ.mk' (toEquiv hS q : G) = q :=
  (toEquiv hS).symm_apply_apply q

@[to_additive]
theorem to_equiv_apply {f : Quotientₓ (QuotientGroup.rightRel H) → G} (hf : ∀ q, Quotientₓ.mk' (f q) = q)
    (q : Quotientₓ (QuotientGroup.rightRel H)) : (toEquiv (range_mem_right_transversals hf) q : G) = f q := by
  refine' (subtype.ext_iff.mp _).trans (Subtype.coe_mk (f q) ⟨q, rfl⟩)
  exact (to_equiv (range_mem_right_transversals hf)).apply_eq_iff_eq_symm_apply.mpr (hf q).symm

/-- A right transversal can be viewed as a function mapping each element of the group
  to the chosen representative from that right coset. -/
@[to_additive
      "A right transversal can be viewed as a function mapping each element of the group\n  to the chosen representative from that right coset."]
noncomputable def toFun (hS : S ∈ Subgroup.RightTransversals (H : Set G)) : G → S :=
  toEquiv hS ∘ Quotientₓ.mk'

@[to_additive]
theorem mul_inv_to_fun_mem (hS : S ∈ Subgroup.RightTransversals (H : Set G)) (g : G) : g * (toFun hS g : G)⁻¹ ∈ H :=
  QuotientGroup.right_rel_apply.mp <| Quotientₓ.exact' <| mk'_to_equiv _ _

@[to_additive]
theorem to_fun_mul_inv_mem (hS : S ∈ Subgroup.RightTransversals (H : Set G)) (g : G) : (toFun hS g : G) * g⁻¹ ∈ H :=
  (congr_arg (· ∈ H)
        (by
          rw [mul_inv_rev, inv_invₓ])).mp
    (H.inv_mem (mul_inv_to_fun_mem hS g))

end MemRightTransversals

section Action

open Pointwise

open MulAction MemLeftTransversals

variable {F : Type _} [Groupₓ F] [MulAction F G] [QuotientAction F H]

@[to_additive]
instance : MulAction F (LeftTransversals (H : Set G)) where
  smul := fun f T =>
    ⟨f • T, by
      refine' mem_left_transversals_iff_exists_unique_inv_mul_mem.mpr fun g => _
      obtain ⟨t, ht1, ht2⟩ := mem_left_transversals_iff_exists_unique_inv_mul_mem.mp T.2 (f⁻¹ • g)
      refine' ⟨⟨f • t, Set.smul_mem_smul_set t.2⟩, _, _⟩
      · exact (congr_arg _ (smul_inv_smul f g)).mp (quotient_action.inv_mul_mem f ht1)
        
      · rintro ⟨-, t', ht', rfl⟩ h
        replace h := quotient_action.inv_mul_mem f⁻¹ h
        simp only [← Subtype.ext_iff, ← Subtype.coe_mk, ← smul_left_cancel_iff, ← inv_smul_smul] at h⊢
        exact subtype.ext_iff.mp (ht2 ⟨t', ht'⟩ h)
        ⟩
  one_smul := fun T => Subtype.ext (one_smul F T)
  mul_smul := fun f₁ f₂ T => Subtype.ext (mul_smul f₁ f₂ T)

@[to_additive]
theorem smul_to_fun (f : F) (T : LeftTransversals (H : Set G)) (g : G) :
    (f • toFun T.2 g : G) = toFun (f • T).2 (f • g) :=
  Subtype.ext_iff.mp <|
    @unique_of_exists_unique (↥(f • T)) (fun s => (↑s)⁻¹ * f • g ∈ H)
      (mem_left_transversals_iff_exists_unique_inv_mul_mem.mp (f • T).2 (f • g))
      ⟨f • toFun T.2 g, Set.smul_mem_smul_set (Subtype.coe_prop _)⟩ (toFun (f • T).2 (f • g))
      (QuotientAction.inv_mul_mem f (inv_to_fun_mul_mem T.2 g)) (inv_to_fun_mul_mem (f • T).2 (f • g))

@[to_additive]
theorem smul_to_equiv (f : F) (T : LeftTransversals (H : Set G)) (q : G ⧸ H) :
    f • (toEquiv T.2 q : G) = toEquiv (f • T).2 (f • q) :=
  Quotientₓ.induction_on' q fun g => smul_to_fun f T g

@[to_additive]
theorem smul_apply_eq_smul_apply_inv_smul (f : F) (T : LeftTransversals (H : Set G)) (q : G ⧸ H) :
    (toEquiv (f • T).2 q : G) = f • (toEquiv T.2 (f⁻¹ • q) : G) := by
  rw [smul_to_equiv, smul_inv_smul]

end Action

@[to_additive]
instance : Inhabited (LeftTransversals (H : Set G)) :=
  ⟨⟨Set.Range Quotientₓ.out', range_mem_left_transversals Quotientₓ.out_eq'⟩⟩

@[to_additive]
instance : Inhabited (RightTransversals (H : Set G)) :=
  ⟨⟨Set.Range Quotientₓ.out', range_mem_right_transversals Quotientₓ.out_eq'⟩⟩

theorem IsComplement'.is_compl (h : IsComplement' H K) : IsCompl H K := by
  refine'
    ⟨fun g ⟨p, q⟩ =>
      let x : H × K := ⟨⟨g, p⟩, 1⟩
      let y : H × K := ⟨1, g, q⟩
      subtype.ext_iff.mp (prod.ext_iff.mp (show x = y from h.1 ((mul_oneₓ g).trans (one_mulₓ g).symm))).1,
      fun g _ => _⟩
  obtain ⟨⟨h, k⟩, rfl⟩ := h.2 g
  exact Subgroup.mul_mem_sup h.2 k.2

theorem IsComplement'.sup_eq_top (h : Subgroup.IsComplement' H K) : H⊔K = ⊤ :=
  h.IsCompl.sup_eq_top

theorem IsComplement'.disjoint (h : IsComplement' H K) : Disjoint H K :=
  h.IsCompl.Disjoint

theorem IsComplement.card_mul [Fintype G] [Fintype S] [Fintype T] (h : IsComplement S T) :
    Fintype.card S * Fintype.card T = Fintype.card G :=
  (Fintype.card_prod _ _).symm.trans (Fintype.card_of_bijective h)

theorem IsComplement'.card_mul [Fintype G] [Fintype H] [Fintype K] (h : IsComplement' H K) :
    Fintype.card H * Fintype.card K = Fintype.card G :=
  h.card_mul

theorem is_complement'_of_card_mul_and_disjoint [Fintype G] [Fintype H] [Fintype K]
    (h1 : Fintype.card H * Fintype.card K = Fintype.card G) (h2 : Disjoint H K) : IsComplement' H K := by
  refine' (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun x y h => _, (Fintype.card_prod H K).trans h1⟩
  rw [← eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_inv_eq_iff_eq_mul] at h
  change ↑(x.2 * y.2⁻¹) = ↑(x.1⁻¹ * y.1) at h
  rw [Prod.ext_iff, ← @inv_mul_eq_one H _ x.1 y.1, ← @mul_inv_eq_one K _ x.2 y.2, Subtype.ext_iff, Subtype.ext_iff,
    coe_one, coe_one, h, and_selfₓ, ← mem_bot, ← h2.eq_bot, mem_inf]
  exact ⟨Subtype.mem (x.1⁻¹ * y.1), (congr_arg (· ∈ K) h).mp (Subtype.mem (x.2 * y.2⁻¹))⟩

theorem is_complement'_iff_card_mul_and_disjoint [Fintype G] [Fintype H] [Fintype K] :
    IsComplement' H K ↔ Fintype.card H * Fintype.card K = Fintype.card G ∧ Disjoint H K :=
  ⟨fun h => ⟨h.card_mul, h.Disjoint⟩, fun h => is_complement'_of_card_mul_and_disjoint h.1 h.2⟩

theorem is_complement'_of_coprime [Fintype G] [Fintype H] [Fintype K]
    (h1 : Fintype.card H * Fintype.card K = Fintype.card G) (h2 : Nat.Coprime (Fintype.card H) (Fintype.card K)) :
    IsComplement' H K :=
  is_complement'_of_card_mul_and_disjoint h1 (disjoint_iff.mpr (inf_eq_bot_of_coprime h2))

theorem is_complement'_stabilizer {α : Type _} [MulAction G α] (a : α) (h1 : ∀ h : H, h • a = a → h = 1)
    (h2 : ∀ g : G, ∃ h : H, h • g • a = a) : IsComplement' H (MulAction.stabilizer G a) := by
  refine' is_complement_iff_exists_unique.mpr fun g => _
  obtain ⟨h, hh⟩ := h2 g
  have hh' : (↑h * g) • a = a := by
    rwa [mul_smul]
  refine' ⟨⟨h⁻¹, h * g, hh'⟩, inv_mul_cancel_leftₓ h g, _⟩
  rintro ⟨h', g, hg : g • a = a⟩ rfl
  specialize
    h1 (h * h')
      (by
        rwa [mul_smul, smul_def h', ← hg, ← mul_smul, hg])
  refine' Prod.extₓ (eq_inv_of_mul_eq_one_right h1) (Subtype.ext _)
  rwa [Subtype.ext_iff, coe_one, coe_mul, ← self_eq_mul_left, mul_assoc (↑h) (↑h') g] at h1

end Subgroup

