/-
Copyright (c) 2018 Mitchell Rowett. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Rowett, Scott Morrison
-/
import Mathbin.Algebra.Quotient
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.Tactic.Group

/-!
# Cosets

This file develops the basic theory of left and right cosets.

## Main definitions

* `left_coset a s`: the left coset `a * s` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `left_add_coset a s`.
* `right_coset s a`: the right coset `s * a` for an element `a : α` and a subset `s ⊆ α`, for an
  `add_group` this is `right_add_coset s a`.
* `quotient_group.quotient s`: the quotient type representing the left cosets with respect to a
  subgroup `s`, for an `add_group` this is `quotient_add_group.quotient s`.
* `quotient_group.mk`: the canonical map from `α` to `α/s` for a subgroup `s` of `α`, for an
  `add_group` this is `quotient_add_group.mk`.
* `subgroup.left_coset_equiv_subgroup`: the natural bijection between a left coset and the subgroup,
  for an `add_group` this is `add_subgroup.left_coset_equiv_add_subgroup`.

## Notation

* `a *l s`: for `left_coset a s`.
* `a +l s`: for `left_add_coset a s`.
* `s *r a`: for `right_coset s a`.
* `s +r a`: for `right_add_coset s a`.

* `G ⧸ H` is the quotient of the (additive) group `G` by the (additive) subgroup `H`

## TODO

Add `to_additive` to `preimage_mk_equiv_subgroup_times_set`.
-/


open Set Function

variable {α : Type _}

/-- The left coset `a * s` for an element `a : α` and a subset `s : set α` -/
@[to_additive LeftAddCoset "The left coset `a+s` for an element `a : α`\nand a subset `s : set α`"]
def LeftCoset [Mul α] (a : α) (s : Set α) : Set α :=
  (fun x => a * x) '' s

/-- The right coset `s * a` for an element `a : α` and a subset `s : set α` -/
@[to_additive RightAddCoset "The right coset `s+a` for an element `a : α`\nand a subset `s : set α`"]
def RightCoset [Mul α] (s : Set α) (a : α) : Set α :=
  (fun x => x * a) '' s

-- mathport name: «expr *l »
localized [Coset] infixl:70 " *l " => LeftCoset

-- mathport name: «expr +l »
localized [Coset] infixl:70 " +l " => LeftAddCoset

-- mathport name: «expr *r »
localized [Coset] infixl:70 " *r " => RightCoset

-- mathport name: «expr +r »
localized [Coset] infixl:70 " +r " => RightAddCoset

section CosetMul

variable [Mul α]

@[to_additive mem_left_add_coset]
theorem mem_left_coset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : a * x ∈ a *l s :=
  mem_image_of_mem (fun b : α => a * b) hxS

@[to_additive mem_right_add_coset]
theorem mem_right_coset {s : Set α} {x : α} (a : α) (hxS : x ∈ s) : x * a ∈ s *r a :=
  mem_image_of_mem (fun b : α => b * a) hxS

/-- Equality of two left cosets `a * s` and `b * s`. -/
@[to_additive LeftAddCosetEquivalence "Equality of two left cosets `a + s` and `b + s`."]
def LeftCosetEquivalence (s : Set α) (a b : α) :=
  a *l s = b *l s

@[to_additive left_add_coset_equivalence_rel]
theorem left_coset_equivalence_rel (s : Set α) : Equivalenceₓ (LeftCosetEquivalence s) :=
  mk_equivalence (LeftCosetEquivalence s) (fun a => rfl) (fun a b => Eq.symm) fun a b c => Eq.trans

/-- Equality of two right cosets `s * a` and `s * b`. -/
@[to_additive RightAddCosetEquivalence "Equality of two right cosets `s + a` and `s + b`."]
def RightCosetEquivalence (s : Set α) (a b : α) :=
  s *r a = s *r b

@[to_additive right_add_coset_equivalence_rel]
theorem right_coset_equivalence_rel (s : Set α) : Equivalenceₓ (RightCosetEquivalence s) :=
  mk_equivalence (RightCosetEquivalence s) (fun a => rfl) (fun a b => Eq.symm) fun a b c => Eq.trans

end CosetMul

section CosetSemigroup

variable [Semigroupₓ α]

@[simp, to_additive left_add_coset_assoc]
theorem left_coset_assoc (s : Set α) (a b : α) : a *l (b *l s) = a * b *l s := by
  simp [← LeftCoset, ← RightCoset, ← (image_comp _ _ _).symm, ← Function.comp, ← mul_assoc]

@[simp, to_additive right_add_coset_assoc]
theorem right_coset_assoc (s : Set α) (a b : α) : s *r a *r b = s *r (a * b) := by
  simp [← LeftCoset, ← RightCoset, ← (image_comp _ _ _).symm, ← Function.comp, ← mul_assoc]

@[to_additive left_add_coset_right_add_coset]
theorem left_coset_right_coset (s : Set α) (a b : α) : a *l s *r b = a *l (s *r b) := by
  simp [← LeftCoset, ← RightCoset, ← (image_comp _ _ _).symm, ← Function.comp, ← mul_assoc]

end CosetSemigroup

section CosetMonoid

variable [Monoidₓ α] (s : Set α)

@[simp, to_additive zero_left_add_coset]
theorem one_left_coset : 1 *l s = s :=
  Set.ext <| by
    simp [← LeftCoset]

@[simp, to_additive right_add_coset_zero]
theorem right_coset_one : s *r 1 = s :=
  Set.ext <| by
    simp [← RightCoset]

end CosetMonoid

section CosetSubmonoid

open Submonoid

variable [Monoidₓ α] (s : Submonoid α)

@[to_additive mem_own_left_add_coset]
theorem mem_own_left_coset (a : α) : a ∈ a *l s :=
  suffices a * 1 ∈ a *l s by
    simpa
  mem_left_coset a (one_mem s : 1 ∈ s)

@[to_additive mem_own_right_add_coset]
theorem mem_own_right_coset (a : α) : a ∈ (s : Set α) *r a :=
  suffices 1 * a ∈ (s : Set α) *r a by
    simpa
  mem_right_coset a (one_mem s : 1 ∈ s)

@[to_additive mem_left_add_coset_left_add_coset]
theorem mem_left_coset_left_coset {a : α} (ha : a *l s = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha] <;> exact mem_own_left_coset s a

@[to_additive mem_right_add_coset_right_add_coset]
theorem mem_right_coset_right_coset {a : α} (ha : (s : Set α) *r a = s) : a ∈ s := by
  rw [← SetLike.mem_coe, ← ha] <;> exact mem_own_right_coset s a

end CosetSubmonoid

section CosetGroup

variable [Groupₓ α] {s : Set α} {x : α}

@[to_additive mem_left_add_coset_iff]
theorem mem_left_coset_iff (a : α) : x ∈ a *l s ↔ a⁻¹ * x ∈ s :=
  Iff.intro
    (fun ⟨b, hb, Eq⟩ => by
      simp [← Eq.symm, ← hb])
    fun h =>
    ⟨a⁻¹ * x, h, by
      simp ⟩

@[to_additive mem_right_add_coset_iff]
theorem mem_right_coset_iff (a : α) : x ∈ s *r a ↔ x * a⁻¹ ∈ s :=
  Iff.intro
    (fun ⟨b, hb, Eq⟩ => by
      simp [← Eq.symm, ← hb])
    fun h =>
    ⟨x * a⁻¹, h, by
      simp ⟩

end CosetGroup

section CosetSubgroup

open Subgroup

variable [Groupₓ α] (s : Subgroup α)

@[to_additive left_add_coset_mem_left_add_coset]
theorem left_coset_mem_left_coset {a : α} (ha : a ∈ s) : a *l s = s :=
  Set.ext <| by
    simp [← mem_left_coset_iff, ← mul_mem_cancel_left (s.inv_mem ha)]

@[to_additive right_add_coset_mem_right_add_coset]
theorem right_coset_mem_right_coset {a : α} (ha : a ∈ s) : (s : Set α) *r a = s :=
  Set.ext fun b => by
    simp [← mem_right_coset_iff, ← mul_mem_cancel_right (s.inv_mem ha)]

@[to_additive eq_add_cosets_of_normal]
theorem eq_cosets_of_normal (N : s.Normal) (g : α) : g *l s = s *r g :=
  Set.ext fun a => by
    simp [← mem_left_coset_iff, ← mem_right_coset_iff] <;> rw [N.mem_comm_iff]

@[to_additive normal_of_eq_add_cosets]
theorem normal_of_eq_cosets (h : ∀ g : α, g *l s = s *r g) : s.Normal :=
  ⟨fun a ha g =>
    show g * a * g⁻¹ ∈ (s : Set α) by
      rw [← mem_right_coset_iff, ← h] <;> exact mem_left_coset g ha⟩

@[to_additive normal_iff_eq_add_cosets]
theorem normal_iff_eq_cosets : s.Normal ↔ ∀ g : α, g *l s = s *r g :=
  ⟨@eq_cosets_of_normal _ _ s, normal_of_eq_cosets s⟩

@[to_additive left_add_coset_eq_iff]
theorem left_coset_eq_iff {x y : α} : LeftCoset x s = LeftCoset y s ↔ x⁻¹ * y ∈ s := by
  rw [Set.ext_iff]
  simp_rw [mem_left_coset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_left_invₓ]
    exact s.one_mem
    
  · intro h z
    rw [← mul_inv_cancel_rightₓ x⁻¹ y]
    rw [mul_assoc]
    exact s.mul_mem_cancel_left h
    

@[to_additive right_add_coset_eq_iff]
theorem right_coset_eq_iff {x y : α} : RightCoset (↑s) x = RightCoset s y ↔ y * x⁻¹ ∈ s := by
  rw [Set.ext_iff]
  simp_rw [mem_right_coset_iff, SetLike.mem_coe]
  constructor
  · intro h
    apply (h y).mpr
    rw [mul_right_invₓ]
    exact s.one_mem
    
  · intro h z
    rw [← inv_mul_cancel_leftₓ y x⁻¹]
    rw [← mul_assoc]
    exact s.mul_mem_cancel_right h
    

end CosetSubgroup

run_cmd
  to_additive.map_namespace `quotient_group `quotient_add_group

namespace QuotientGroup

variable [Groupₓ α] (s : Subgroup α)

/-- The equivalence relation corresponding to the partition of a group by left cosets
of a subgroup.-/
@[to_additive "The equivalence relation corresponding to the partition of a group by left cosets\nof a subgroup."]
def leftRel : Setoidₓ α :=
  MulAction.orbitRel s.opposite α

variable {s}

@[to_additive]
theorem left_rel_apply {x y : α} : @Setoidₓ.R _ (leftRel s) x y ↔ x⁻¹ * y ∈ s :=
  calc
    (∃ a : s.opposite, y * MulOpposite.unop a = x) ↔ ∃ a : s, y * a = x := s.oppositeEquiv.symm.exists_congr_left
    _ ↔ ∃ a : s, x⁻¹ * y = a⁻¹ := by
      simp only [← inv_mul_eq_iff_eq_mul, ← eq_mul_inv_iff_mul_eq]
    _ ↔ x⁻¹ * y ∈ s := by
      simp [← SetLike.exists]
    

variable (s)

@[to_additive]
theorem left_rel_eq : @Setoidₓ.R _ (leftRel s) = fun x y => x⁻¹ * y ∈ s :=
  funext₂ <| by
    simp only [← eq_iff_iff]
    apply left_rel_apply

theorem left_rel_r_eq_left_coset_equivalence : @Setoidₓ.R _ (QuotientGroup.leftRel s) = LeftCosetEquivalence s := by
  ext
  rw [left_rel_eq]
  exact (left_coset_eq_iff s).symm

@[to_additive]
instance leftRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (leftRel s).R := fun x y => by
  rw [left_rel_eq]
  exact ‹DecidablePred (· ∈ s)› _

/-- `α ⧸ s` is the quotient type representing the left cosets of `s`.
  If `s` is a normal subgroup, `α ⧸ s` is a group -/
@[to_additive
      "`α ⧸ s` is the quotient type representing the left cosets of `s`.  If `s` is a\nnormal subgroup, `α ⧸ s` is a group"]
instance : HasQuotient α (Subgroup α) :=
  ⟨fun s => Quotientₓ (leftRel s)⟩

/-- The equivalence relation corresponding to the partition of a group by right cosets of a
subgroup. -/
@[to_additive "The equivalence relation corresponding to the partition of a group by right cosets of\na subgroup."]
def rightRel : Setoidₓ α :=
  MulAction.orbitRel s α

variable {s}

@[to_additive]
theorem right_rel_apply {x y : α} : @Setoidₓ.R _ (rightRel s) x y ↔ y * x⁻¹ ∈ s :=
  calc
    (∃ a : s, (a : α) * y = x) ↔ ∃ a : s, y * x⁻¹ = a⁻¹ := by
      simp only [← mul_inv_eq_iff_eq_mul, ← eq_inv_mul_iff_mul_eq]
    _ ↔ y * x⁻¹ ∈ s := by
      simp [← SetLike.exists]
    

variable (s)

@[to_additive]
theorem right_rel_eq : @Setoidₓ.R _ (rightRel s) = fun x y => y * x⁻¹ ∈ s :=
  funext₂ <| by
    simp only [← eq_iff_iff]
    apply right_rel_apply

theorem right_rel_r_eq_right_coset_equivalence : @Setoidₓ.R _ (QuotientGroup.rightRel s) = RightCosetEquivalence s := by
  ext
  rw [right_rel_eq]
  exact (right_coset_eq_iff s).symm

@[to_additive]
instance rightRelDecidable [DecidablePred (· ∈ s)] : DecidableRel (rightRel s).R := fun x y => by
  rw [right_rel_eq]
  exact ‹DecidablePred (· ∈ s)› _

/-- Right cosets are in bijection with left cosets. -/
@[to_additive "Right cosets are in bijection with left cosets."]
def quotientRightRelEquivQuotientLeftRel : Quotientₓ (QuotientGroup.rightRel s) ≃ α ⧸ s where
  toFun :=
    Quotientₓ.map' (fun g => g⁻¹) fun a b => by
      rw [left_rel_apply, right_rel_apply]
      exact fun h =>
        (congr_arg (· ∈ s)
              (by
                group)).mp
          (s.inv_mem h)
  invFun :=
    Quotientₓ.map' (fun g => g⁻¹) fun a b => by
      rw [left_rel_apply, right_rel_apply]
      exact fun h =>
        (congr_arg (· ∈ s)
              (by
                group)).mp
          (s.inv_mem h)
  left_inv := fun g =>
    Quotientₓ.induction_on' g fun g =>
      Quotientₓ.sound'
        (by
          simp only [← inv_invₓ]
          exact Quotientₓ.exact' rfl)
  right_inv := fun g =>
    Quotientₓ.induction_on' g fun g =>
      Quotientₓ.sound'
        (by
          simp only [← inv_invₓ]
          exact Quotientₓ.exact' rfl)

@[to_additive]
instance fintypeQuotientRightRel [Fintype (α ⧸ s)] : Fintype (Quotientₓ (QuotientGroup.rightRel s)) :=
  Fintype.ofEquiv (α ⧸ s) (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

@[to_additive]
theorem card_quotient_right_rel [Fintype (α ⧸ s)] :
    Fintype.card (Quotientₓ (QuotientGroup.rightRel s)) = Fintype.card (α ⧸ s) :=
  Fintype.of_equiv_card (QuotientGroup.quotientRightRelEquivQuotientLeftRel s).symm

end QuotientGroup

namespace QuotientGroup

variable [Groupₓ α] {s : Subgroup α}

@[to_additive]
instance fintype [Fintype α] (s : Subgroup α) [DecidableRel (leftRel s).R] : Fintype (α ⧸ s) :=
  Quotientₓ.fintype (leftRel s)

/-- The canonical map from a group `α` to the quotient `α ⧸ s`. -/
@[to_additive "The canonical map from an `add_group` `α` to the quotient `α ⧸ s`."]
abbrev mk (a : α) : α ⧸ s :=
  Quotientₓ.mk' a

@[to_additive]
theorem mk_surjective : Function.Surjective <| @mk _ _ s :=
  Quotientₓ.surjective_quotient_mk'

@[elab_as_eliminator, to_additive]
theorem induction_on {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z, C (QuotientGroup.mk z)) : C x :=
  Quotientₓ.induction_on' x H

@[to_additive]
instance : CoeTₓ α (α ⧸ s) :=
  ⟨mk⟩

-- note [use has_coe_t]
@[elab_as_eliminator, to_additive]
theorem induction_on' {C : α ⧸ s → Prop} (x : α ⧸ s) (H : ∀ z : α, C z) : C x :=
  Quotientₓ.induction_on' x H

@[simp, to_additive]
theorem quotient_lift_on_coe {β} (f : α → β) (h) (x : α) : Quotientₓ.liftOn' (x : α ⧸ s) f h = f x :=
  rfl

@[to_additive]
theorem forall_coe {C : α ⧸ s → Prop} : (∀ x : α ⧸ s, C x) ↔ ∀ x : α, C x :=
  ⟨fun hx x => hx _, Quot.ind⟩

@[to_additive]
instance (s : Subgroup α) : Inhabited (α ⧸ s) :=
  ⟨((1 : α) : α ⧸ s)⟩

@[to_additive QuotientAddGroup.eq]
protected theorem eq {a b : α} : (a : α ⧸ s) = b ↔ a⁻¹ * b ∈ s :=
  calc
    _ ↔ @Setoidₓ.R _ (leftRel s) a b := Quotientₓ.eq'
    _ ↔ _ := by
      rw [left_rel_apply]
    

@[to_additive QuotientAddGroup.eq']
theorem eq' {a b : α} : (mk a : α ⧸ s) = mk b ↔ a⁻¹ * b ∈ s :=
  QuotientGroup.eq

@[to_additive QuotientAddGroup.out_eq']
theorem out_eq' (a : α ⧸ s) : mk a.out' = a :=
  Quotientₓ.out_eq' a

variable (s)

/- It can be useful to write `obtain ⟨h, H⟩ := mk_out'_eq_mul ...`, and then `rw [H]` or
  `simp_rw [H]` or `simp only [H]`. In order for `simp_rw` and `simp only` to work, this lemma is
  stated in terms of an arbitrary `h : s`, rathern that the specific `h = g⁻¹ * (mk g).out'`. -/
@[to_additive QuotientAddGroup.mk_out'_eq_mul]
theorem mk_out'_eq_mul (g : α) : ∃ h : s, (mk g : α ⧸ s).out' = g * h :=
  ⟨⟨g⁻¹ * (mk g).out', eq'.mp (mk g).out_eq'.symm⟩, by
    rw [SetLike.coe_mk, mul_inv_cancel_left]⟩

variable {s}

@[to_additive QuotientAddGroup.mk_mul_of_mem]
theorem mk_mul_of_mem (g₁ g₂ : α) (hg₂ : g₂ ∈ s) : (mk (g₁ * g₂) : α ⧸ s) = mk g₁ := by
  rwa [eq', mul_inv_rev, inv_mul_cancel_right, s.inv_mem_iff]

@[to_additive]
theorem eq_class_eq_left_coset (s : Subgroup α) (g : α) : { x : α | (x : α ⧸ s) = g } = LeftCoset g s :=
  Set.ext fun z => by
    rw [mem_left_coset_iff, Set.mem_set_of_eq, eq_comm, QuotientGroup.eq, SetLike.mem_coe]

@[to_additive]
theorem preimage_image_coe (N : Subgroup α) (s : Set α) :
    coe ⁻¹' ((coe : α → α ⧸ N) '' s) = ⋃ x : N, (fun y : α => y * x) ⁻¹' s := by
  ext x
  simp only [← QuotientGroup.eq, ← SetLike.exists, ← exists_prop, ← Set.mem_preimage, ← Set.mem_Union, ← Set.mem_image,
    ← SetLike.coe_mk, eq_inv_mul_iff_mul_eq]
  exact
    ⟨fun ⟨y, hs, hN⟩ =>
      ⟨_, N.inv_mem hN, by
        simpa using hs⟩,
      fun ⟨z, hz, hxz⟩ =>
      ⟨x * z, hxz, by
        simpa using hz⟩⟩

end QuotientGroup

namespace Subgroup

open QuotientGroup

variable [Groupₓ α] {s : Subgroup α}

/-- The natural bijection between a left coset `g * s` and `s`. -/
@[to_additive "The natural bijection between the cosets `g + s` and `s`."]
def leftCosetEquivSubgroup (g : α) : LeftCoset g s ≃ s :=
  ⟨fun x => ⟨g⁻¹ * x.1, (mem_left_coset_iff _).1 x.2⟩, fun x => ⟨g * x.1, x.1, x.2, rfl⟩, fun ⟨x, hx⟩ =>
    Subtype.eq <| by
      simp ,
    fun ⟨g, hg⟩ =>
    Subtype.eq <| by
      simp ⟩

/-- The natural bijection between a right coset `s * g` and `s`. -/
@[to_additive "The natural bijection between the cosets `s + g` and `s`."]
def rightCosetEquivSubgroup (g : α) : RightCoset (↑s) g ≃ s :=
  ⟨fun x => ⟨x.1 * g⁻¹, (mem_right_coset_iff _).1 x.2⟩, fun x => ⟨x.1 * g, x.1, x.2, rfl⟩, fun ⟨x, hx⟩ =>
    Subtype.eq <| by
      simp ,
    fun ⟨g, hg⟩ =>
    Subtype.eq <| by
      simp ⟩

/-- A (non-canonical) bijection between a group `α` and the product `(α/s) × s` -/
@[to_additive "A (non-canonical) bijection between an add_group `α` and the product `(α/s) × s`"]
noncomputable def groupEquivQuotientTimesSubgroup : α ≃ (α ⧸ s) × s :=
  calc
    α ≃ ΣL : α ⧸ s, { x : α // (x : α ⧸ s) = L } := (Equivₓ.sigmaFiberEquiv QuotientGroup.mk).symm
    _ ≃ ΣL : α ⧸ s, LeftCoset (Quotientₓ.out' L) s :=
      Equivₓ.sigmaCongrRight fun L => by
        rw [← eq_class_eq_left_coset]
        show
          (_root_.subtype fun x : α => Quotientₓ.mk' x = L) ≃
            _root_.subtype fun x : α => Quotientₓ.mk' x = Quotientₓ.mk' _
        simp [-Quotientₓ.eq']
    _ ≃ ΣL : α ⧸ s, s := Equivₓ.sigmaCongrRight fun L => leftCosetEquivSubgroup _
    _ ≃ (α ⧸ s) × s := Equivₓ.sigmaEquivProd _ _
    

variable {t : Subgroup α}

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse
of the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`. -/
@[to_additive
      "If `H ≤ K`, then `G/H ≃ G/K × K/H` constructively, using the provided right inverse\nof the quotient map `G → G/K`. The classical version is `quotient_equiv_prod_of_le`.",
  simps]
def quotientEquivProdOfLe' (h_le : s ≤ t) (f : α ⧸ t → α) (hf : Function.RightInverse f QuotientGroup.mk) :
    α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t where
  toFun := fun a =>
    ⟨a.map' id fun b c h => left_rel_apply.mpr (h_le (left_rel_apply.mp h)),
      a.map' (fun g : α => ⟨(f (Quotientₓ.mk' g))⁻¹ * g, left_rel_apply.mp (Quotientₓ.exact' (hf g))⟩) fun b c h => by
        rw [left_rel_apply]
        change ((f b)⁻¹ * b)⁻¹ * ((f c)⁻¹ * c) ∈ s
        have key : f b = f c := congr_arg f (Quotientₓ.sound' (left_rel_apply.mpr (h_le (left_rel_apply.mp h))))
        rwa [key, mul_inv_rev, inv_invₓ, mul_assoc, mul_inv_cancel_left, ← left_rel_apply]⟩
  invFun := fun a =>
    a.2.map' (fun b => f a.1 * b) fun b c h => by
      rw [left_rel_apply] at h⊢
      change (f a.1 * b)⁻¹ * (f a.1 * c) ∈ s
      rwa [mul_inv_rev, mul_assoc, inv_mul_cancel_leftₓ]
  left_inv := by
    refine' Quotientₓ.ind' fun a => _
    simp_rw [Quotientₓ.map'_mk', id.def, SetLike.coe_mk, mul_inv_cancel_left]
  right_inv := by
    refine' Prod.rec _
    refine' Quotientₓ.ind' fun a => _
    refine' Quotientₓ.ind' fun b => _
    have key : Quotientₓ.mk' (f (Quotientₓ.mk' a) * b) = Quotientₓ.mk' a :=
      (QuotientGroup.mk_mul_of_mem (f a) (↑b) b.2).trans (hf a)
    simp_rw [Quotientₓ.map'_mk', id.def, key, inv_mul_cancel_leftₓ, Subtype.coe_eta]

/-- If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.
The constructive version is `quotient_equiv_prod_of_le'`. -/
@[to_additive
      "If `H ≤ K`, then `G/H ≃ G/K × K/H` nonconstructively.\nThe constructive version is `quotient_equiv_prod_of_le'`.",
  simps]
noncomputable def quotientEquivProdOfLe (h_le : s ≤ t) : α ⧸ s ≃ (α ⧸ t) × t ⧸ s.subgroupOf t :=
  quotientEquivProdOfLe' h_le Quotientₓ.out' Quotientₓ.out_eq'

/-- If `K ≤ L`, then there is an embedding `K ⧸ (H.subgroup_of K) ↪ L ⧸ (H.subgroup_of L)`. -/
@[to_additive "If `K ≤ L`, then there is an embedding\n  `K ⧸ (H.add_subgroup_of K) ↪ L ⧸ (H.add_subgroup_of L)`."]
def quotientSubgroupOfEmbeddingOfLe (H : Subgroup α) {K L : Subgroup α} (h : K ≤ L) :
    K ⧸ H.subgroupOf K ↪ L ⧸ H.subgroupOf L where
  toFun :=
    Quotientₓ.map' (Set.inclusion h) fun a b => by
      simp [← left_rel_apply]
      exact id
  inj' := by
    refine' Quotientₓ.ind₂' fun a b => _
    refine' fun h => (quotient.eq'.mpr ∘ left_rel_apply.mpr) _
    have := left_rel_apply.mp (quotient.eq'.mp h)
    exact this

@[to_additive]
theorem card_eq_card_quotient_mul_card_subgroup [Fintype α] (s : Subgroup α) [Fintype s]
    [DecidablePred fun a => a ∈ s] : Fintype.card α = Fintype.card (α ⧸ s) * Fintype.card s := by
  rw [← Fintype.card_prod] <;> exact Fintype.card_congr Subgroup.groupEquivQuotientTimesSubgroup

/-- **Lagrange's Theorem**: The order of a subgroup divides the order of its ambient group. -/
@[to_additive]
theorem card_subgroup_dvd_card [Fintype α] (s : Subgroup α) [Fintype s] : Fintype.card s ∣ Fintype.card α := by
  classical <;> simp [← card_eq_card_quotient_mul_card_subgroup s, ← @dvd_mul_left ℕ]

@[to_additive]
theorem card_quotient_dvd_card [Fintype α] (s : Subgroup α) [DecidablePred fun a => a ∈ s] [Fintype s] :
    Fintype.card (α ⧸ s) ∣ Fintype.card α := by
  simp [← card_eq_card_quotient_mul_card_subgroup s, ← @dvd_mul_right ℕ]

open Fintype

variable {H : Type _} [Groupₓ H]

@[to_additive]
theorem card_dvd_of_injective [Fintype α] [Fintype H] (f : α →* H) (hf : Function.Injective f) : card α ∣ card H := by
  classical <;>
    calc card α = card (f.range : Subgroup H) := card_congr (Equivₓ.ofInjective f hf)_ ∣ card H :=
        card_subgroup_dvd_card _

@[to_additive]
theorem card_dvd_of_le {H K : Subgroup α} [Fintype H] [Fintype K] (hHK : H ≤ K) : card H ∣ card K :=
  card_dvd_of_injective (inclusion hHK) (inclusion_injective hHK)

@[to_additive]
theorem card_comap_dvd_of_injective (K : Subgroup H) [Fintype K] (f : α →* H) [Fintype (K.comap f)]
    (hf : Function.Injective f) : Fintype.card (K.comap f) ∣ Fintype.card K := by
  have : Fintype ((K.comap f).map f) := Fintype.ofEquiv _ (equiv_map_of_injective _ _ hf).toEquiv <;>
    calc Fintype.card (K.comap f) = Fintype.card ((K.comap f).map f) :=
        Fintype.card_congr (equiv_map_of_injective _ _ hf).toEquiv _ ∣ Fintype.card K :=
        card_dvd_of_le (map_comap_le _ _)

end Subgroup

namespace QuotientGroup

variable [Groupₓ α]

/-- If `s` is a subgroup of the group `α`, and `t` is a subset of `α/s`, then
there is a (typically non-canonical) bijection between the preimage of `t` in
`α` and the product `s × t`. -/
-- FIXME -- why is there no `to_additive`?
noncomputable def preimageMkEquivSubgroupTimesSet (s : Subgroup α) (t : Set (α ⧸ s)) : QuotientGroup.mk ⁻¹' t ≃ s × t :=
  have h :
    ∀ {x : α ⧸ s} {a : α},
      x ∈ t → a ∈ s → (Quotientₓ.mk' (Quotientₓ.out' x * a) : α ⧸ s) = Quotientₓ.mk' (Quotientₓ.out' x) :=
    fun x a hx ha =>
    Quotientₓ.sound' <| by
      rwa [left_rel_apply, ← s.inv_mem_iff, mul_inv_rev, inv_invₓ, ← mul_assoc, inv_mul_selfₓ, one_mulₓ]
  { toFun := fun ⟨a, ha⟩ =>
      ⟨⟨(Quotientₓ.out' (Quotientₓ.mk' a))⁻¹ * a,
          left_rel_apply.mp (@Quotientₓ.exact' _ (leftRel s) _ _ <| Quotientₓ.out_eq' _)⟩,
        ⟨Quotientₓ.mk' a, ha⟩⟩,
    invFun := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ =>
      ⟨Quotientₓ.out' x * a,
        show Quotientₓ.mk' _ ∈ t by
          simp [← h hx ha, ← hx]⟩,
    left_inv := fun ⟨a, ha⟩ =>
      Subtype.eq <|
        show _ * _ = a by
          simp ,
    right_inv := fun ⟨⟨a, ha⟩, ⟨x, hx⟩⟩ =>
      show (_, _) = _ by
        simp [← h hx ha] }

end QuotientGroup

library_note "use has_coe_t"/-- We use the class `has_coe_t` instead of `has_coe` if the first argument is a variable,
or if the second argument is a variable not occurring in the first.
Using `has_coe` would cause looping of type-class inference. See
<https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/remove.20all.20instances.20with.20variable.20domain>
-/


