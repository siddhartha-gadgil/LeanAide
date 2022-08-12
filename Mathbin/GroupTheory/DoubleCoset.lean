/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathbin.Data.Setoid.Basic
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.GroupTheory.Coset
import Mathbin.GroupTheory.Subgroup.Pointwise
import Mathbin.Data.Set.Basic
import Mathbin.Tactic.Group

/-!
# Double cosets

This file defines double cosets for two subgroups `H K` of a group `G` and the quotient of `G` by
the double coset relation, i.e. `H \ G / K`. We also prove that `G` can be writen as a disjoint
union of the double cosets and that if one of `H` or `K` is the trivial group (i.e. `⊥` ) then
this is the usual left or right quotient of a group by a subgroup.

## Main definitions

* `rel`: The double coset relation defined by two subgroups `H K` of `G`.
* `double_coset.quotient`: The quotient of `G` by the double coset relation, i.e, ``H \ G / K`.
-/


variable {G : Type _} [Groupₓ G] {α : Type _} [Mul α] (J : Subgroup G) (g : G)

namespace Doset

open Pointwise

/-- The double_coset as an element of `set α` corresponding to `s a t` -/
def _root_.doset (a : α) (s t : Set α) : Set α :=
  s * {a} * t

theorem mem_doset {s t : Set α} {a b : α} : b ∈ Doset a s t ↔ ∃ x ∈ s, ∃ y ∈ t, b = x * a * y :=
  ⟨fun ⟨_, y, ⟨x, _, hx, rfl, rfl⟩, hy, h⟩ => ⟨x, hx, y, hy, h.symm⟩, fun ⟨x, hx, y, hy, h⟩ =>
    ⟨x * a, y, ⟨x, a, hx, rfl, rfl⟩, hy, h.symm⟩⟩

theorem mem_doset_self (H K : Subgroup G) (a : G) : a ∈ Doset a H K :=
  mem_doset.mpr ⟨1, H.one_mem, 1, K.one_mem, (one_mulₓ a).symm.trans (mul_oneₓ (1 * a)).symm⟩

theorem doset_eq_of_mem {H K : Subgroup G} {a b : G} (hb : b ∈ Doset a H K) : Doset b H K = Doset a H K := by
  obtain ⟨_, k, ⟨h, a, hh, rfl : _ = _, rfl⟩, hk, rfl⟩ := hb
  rw [Doset, Doset, ← Set.singleton_mul_singleton, ← Set.singleton_mul_singleton, mul_assoc, mul_assoc,
    Subgroup.singleton_mul_subgroup hk, ← mul_assoc, ← mul_assoc, Subgroup.subgroup_mul_singleton hh]

theorem mem_doset_of_not_disjoint {H K : Subgroup G} {a b : G} (h : ¬Disjoint (Doset a H K) (Doset b H K)) :
    b ∈ Doset a H K := by
  rw [Set.not_disjoint_iff] at h
  simp only [← mem_doset] at *
  obtain ⟨x, ⟨l, hl, r, hr, hrx⟩, y, hy, ⟨r', hr', rfl⟩⟩ := h
  refine' ⟨y⁻¹ * l, H.mul_mem (H.inv_mem hy) hl, r * r'⁻¹, K.mul_mem hr (K.inv_mem hr'), _⟩
  rwa [mul_assoc, mul_assoc, eq_inv_mul_iff_mul_eq, ← mul_assoc, ← mul_assoc, eq_mul_inv_iff_mul_eq]

theorem eq_of_not_disjoint {H K : Subgroup G} {a b : G} (h : ¬Disjoint (Doset a H K) (Doset b H K)) :
    Doset a H K = Doset b H K := by
  rw [Disjoint.comm] at h
  have ha : a ∈ Doset b H K := mem_doset_of_not_disjoint h
  apply doset_eq_of_mem ha

/-- The setoid defined by the double_coset relation -/
def setoid (H K : Set G) : Setoidₓ G :=
  Setoidₓ.ker fun x => Doset x H K

/-- Quotient of `G` by the double coset relation, i.e. `H \ G / K` -/
def Quotient (H K : Set G) : Type _ :=
  Quotientₓ (setoid H K)

theorem rel_iff {H K : Subgroup G} {x y : G} : (setoid ↑H ↑K).Rel x y ↔ ∃ a ∈ H, ∃ b ∈ K, y = a * x * b :=
  Iff.trans ⟨fun hxy => (congr_arg _ hxy).mpr (mem_doset_self H K y), fun hxy => (doset_eq_of_mem hxy).symm⟩ mem_doset

theorem bot_rel_eq_left_rel (H : Subgroup G) : (setoid ↑(⊥ : Subgroup G) ↑H).Rel = (QuotientGroup.leftRel H).Rel := by
  ext a b
  rw [rel_iff, Setoidₓ.Rel, QuotientGroup.left_rel_apply]
  constructor
  · rintro ⟨a, rfl : a = 1, b, hb, rfl⟩
    change a⁻¹ * (1 * a * b) ∈ H
    rwa [one_mulₓ, inv_mul_cancel_leftₓ]
    
  · rintro (h : a⁻¹ * b ∈ H)
    exact
      ⟨1, rfl, a⁻¹ * b, h, by
        rw [one_mulₓ, mul_inv_cancel_left]⟩
    

theorem rel_bot_eq_right_group_rel (H : Subgroup G) :
    (setoid ↑H ↑(⊥ : Subgroup G)).Rel = (QuotientGroup.rightRel H).Rel := by
  ext a b
  rw [rel_iff, Setoidₓ.Rel, QuotientGroup.right_rel_apply]
  constructor
  · rintro ⟨b, hb, a, rfl : a = 1, rfl⟩
    change b * a * 1 * a⁻¹ ∈ H
    rwa [mul_oneₓ, mul_inv_cancel_rightₓ]
    
  · rintro (h : b * a⁻¹ ∈ H)
    exact
      ⟨b * a⁻¹, h, 1, rfl, by
        rw [mul_oneₓ, inv_mul_cancel_right]⟩
    

/-- Create a doset out of an element of `H \ G / K`-/
def QuotToDoset (H K : Subgroup G) (q : Quotient ↑H ↑K) : Set G :=
  Doset q.out' H K

/-- Map from `G` to `H \ G / K`-/
abbrev mk (H K : Subgroup G) (a : G) : Quotient ↑H ↑K :=
  Quotientₓ.mk' a

instance (H K : Subgroup G) : Inhabited (Quotient ↑H ↑K) :=
  ⟨mk H K (1 : G)⟩

theorem eq (H K : Subgroup G) (a b : G) : mk H K a = mk H K b ↔ ∃ h ∈ H, ∃ k ∈ K, b = h * a * k := by
  rw [Quotientₓ.eq']
  apply rel_iff

theorem out_eq' (H K : Subgroup G) (q : Quotient ↑H ↑K) : mk H K q.out' = q :=
  Quotientₓ.out_eq' q

theorem mk_out'_eq_mul (H K : Subgroup G) (g : G) :
    ∃ h k : G, h ∈ H ∧ k ∈ K ∧ (mk H K g : Quotient ↑H ↑K).out' = h * g * k := by
  have := Eq H K (mk H K g : Quotientₓ ↑H ↑K).out' g
  rw [out_eq'] at this
  obtain ⟨h, h_h, k, hk, T⟩ := this.1 rfl
  refine' ⟨h⁻¹, k⁻¹, H.inv_mem h_h, K.inv_mem hk, eq_mul_inv_of_mul_eq (eq_inv_mul_of_mul_eq _)⟩
  rw [← mul_assoc, ← T]

theorem mk_eq_of_doset_eq {H K : Subgroup G} {a b : G} (h : Doset a H K = Doset b H K) : mk H K a = mk H K b := by
  rw [Eq]
  exact mem_doset.mp (h.symm ▸ mem_doset_self H K b)

theorem disjoint_out' {H K : Subgroup G} {a b : Quotient H.1 K} :
    a ≠ b → Disjoint (Doset a.out' H K) (Doset b.out' H K) := by
  contrapose!
  intro h
  simpa [← out_eq'] using mk_eq_of_doset_eq (eq_of_not_disjoint h)

theorem union_quot_to_doset (H K : Subgroup G) : (⋃ q, QuotToDoset H K q) = Set.Univ := by
  ext x
  simp only [← Set.mem_Union, ← quot_to_doset, ← mem_doset, ← SetLike.mem_coe, ← exists_prop, ← Set.mem_univ, ←
    iff_trueₓ]
  use mk H K x
  obtain ⟨h, k, h3, h4, h5⟩ := mk_out'_eq_mul H K x
  refine' ⟨h⁻¹, H.inv_mem h3, k⁻¹, K.inv_mem h4, _⟩
  simp only [← h5, ← Subgroup.coe_mk, mul_assoc, ← one_mulₓ, ← mul_left_invₓ, ← mul_inv_cancel_rightₓ]

theorem doset_union_right_coset (H K : Subgroup G) (a : G) : (⋃ k : K, RightCoset (↑H) (a * k)) = Doset a H K := by
  ext x
  simp only [← mem_right_coset_iff, ← exists_prop, ← mul_inv_rev, ← Set.mem_Union, ← mem_doset, ← Subgroup.mem_carrier,
    ← SetLike.mem_coe]
  constructor
  · rintro ⟨y, h_h⟩
    refine' ⟨x * (y⁻¹ * a⁻¹), h_h, y, y.2, _⟩
    simp only [mul_assoc, ← Subgroup.coe_mk, ← inv_mul_cancel_right]
    
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine' ⟨⟨y, hy⟩, _⟩
    simp only [← hxy, mul_assoc, ← hx, ← mul_inv_cancel_rightₓ, ← Subgroup.coe_mk]
    

theorem doset_union_left_coset (H K : Subgroup G) (a : G) : (⋃ h : H, LeftCoset (h * a : G) K) = Doset a H K := by
  ext x
  simp only [← mem_left_coset_iff, ← mul_inv_rev, ← Set.mem_Union, ← mem_doset]
  constructor
  · rintro ⟨y, h_h⟩
    refine' ⟨y, y.2, a⁻¹ * y⁻¹ * x, h_h, _⟩
    simp only [mul_assoc, ← one_mulₓ, ← mul_right_invₓ, ← mul_inv_cancel_rightₓ]
    
  · rintro ⟨x, hx, y, hy, hxy⟩
    refine' ⟨⟨x, hx⟩, _⟩
    simp only [← hxy, mul_assoc, ← hy, ← one_mulₓ, ← mul_left_invₓ, ← Subgroup.coe_mk, ← inv_mul_cancel_right]
    

theorem left_bot_eq_left_quot (H : Subgroup G) : Quotient (⊥ : Subgroup G).1 H = (G ⧸ H) := by
  unfold Quotientₓ
  congr
  ext
  simp_rw [← bot_rel_eq_left_rel H]
  rfl

theorem right_bot_eq_right_quot (H : Subgroup G) :
    Quotient H.1 (⊥ : Subgroup G) = Quotientₓ (QuotientGroup.rightRel H) := by
  unfold Quotientₓ
  congr
  ext
  simp_rw [← rel_bot_eq_right_group_rel H]
  rfl

end Doset

