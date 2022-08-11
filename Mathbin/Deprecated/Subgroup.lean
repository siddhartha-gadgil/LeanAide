/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mitchell Rowett, Scott Morrison, Johan Commelin, Mario Carneiro,
  Michael Howes
-/
import Mathbin.GroupTheory.Subgroup.Basic
import Mathbin.Deprecated.Submonoid

/-!
# Unbundled subgroups (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines unbundled multiplicative and additive subgroups. Instead of using this file,
please use `subgroup G` and `add_subgroup A`, defined in `group_theory.subgroup.basic`.

## Main definitions

`is_add_subgroup (S : set A)` : the predicate that `S` is the underlying subset of an additive
subgroup of `A`. The bundled variant `add_subgroup A` should be used in preference to this.

`is_subgroup (S : set G)` : the predicate that `S` is the underlying subset of a subgroup
of `G`. The bundled variant `subgroup G` should be used in preference to this.

## Tags

subgroup, subgroups, is_subgroup
-/


open Set Function

variable {G : Type _} {H : Type _} {A : Type _} {a a₁ a₂ b c : G}

section Groupₓ

variable [Groupₓ G] [AddGroupₓ A]

/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
structure IsAddSubgroup (s : Set A) extends IsAddSubmonoid s : Prop where
  neg_mem {a} : a ∈ s → -a ∈ s

/-- `s` is a subgroup: a set containing 1 and closed under multiplication and inverse. -/
@[to_additive]
structure IsSubgroup (s : Set G) extends IsSubmonoid s : Prop where
  inv_mem {a} : a ∈ s → a⁻¹ ∈ s

@[to_additive]
theorem IsSubgroup.div_mem {s : Set G} (hs : IsSubgroup s) {x y : G} (hx : x ∈ s) (hy : y ∈ s) : x / y ∈ s := by
  simpa only [← div_eq_mul_inv] using hs.mul_mem hx (hs.inv_mem hy)

theorem Additive.is_add_subgroup {s : Set G} (hs : IsSubgroup s) : @IsAddSubgroup (Additive G) _ s :=
  @IsAddSubgroup.mk (Additive G) _ _ (Additive.is_add_submonoid hs.to_is_submonoid) hs.inv_mem

theorem Additive.is_add_subgroup_iff {s : Set G} : @IsAddSubgroup (Additive G) _ s ↔ IsSubgroup s :=
  ⟨by
    rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact @IsSubgroup.mk G _ _ ⟨h₁, @h₂⟩ @h₃, fun h => Additive.is_add_subgroup h⟩

theorem Multiplicative.is_subgroup {s : Set A} (hs : IsAddSubgroup s) : @IsSubgroup (Multiplicative A) _ s :=
  @IsSubgroup.mk (Multiplicative A) _ _ (Multiplicative.is_submonoid hs.to_is_add_submonoid) hs.neg_mem

theorem Multiplicative.is_subgroup_iff {s : Set A} : @IsSubgroup (Multiplicative A) _ s ↔ IsAddSubgroup s :=
  ⟨by
    rintro ⟨⟨h₁, h₂⟩, h₃⟩ <;> exact @IsAddSubgroup.mk A _ _ ⟨h₁, @h₂⟩ @h₃, fun h => Multiplicative.is_subgroup h⟩

@[to_additive of_add_neg]
theorem IsSubgroup.of_div (s : Set G) (one_mem : (1 : G) ∈ s) (div_mem : ∀ {a b : G}, a ∈ s → b ∈ s → a * b⁻¹ ∈ s) :
    IsSubgroup s :=
  have inv_mem : ∀ a, a ∈ s → a⁻¹ ∈ s := fun a ha => by
    have : 1 * a⁻¹ ∈ s := div_mem one_mem ha
    simpa
  { inv_mem,
    mul_mem := fun a b ha hb => by
      have : a * b⁻¹⁻¹ ∈ s := div_mem ha (inv_mem b hb)
      simpa,
    one_mem }

theorem IsAddSubgroup.of_sub (s : Set A) (zero_mem : (0 : A) ∈ s) (sub_mem : ∀ {a b : A}, a ∈ s → b ∈ s → a - b ∈ s) :
    IsAddSubgroup s :=
  IsAddSubgroup.of_add_neg s zero_mem fun x y hx hy => by
    simpa only [← sub_eq_add_neg] using sub_mem hx hy

@[to_additive]
theorem IsSubgroup.inter {s₁ s₂ : Set G} (hs₁ : IsSubgroup s₁) (hs₂ : IsSubgroup s₂) : IsSubgroup (s₁ ∩ s₂) :=
  { IsSubmonoid.inter hs₁.to_is_submonoid hs₂.to_is_submonoid with
    inv_mem := fun x hx => ⟨hs₁.inv_mem hx.1, hs₂.inv_mem hx.2⟩ }

@[to_additive]
theorem IsSubgroup.Inter {ι : Sort _} {s : ι → Set G} (hs : ∀ y : ι, IsSubgroup (s y)) : IsSubgroup (Set.Inter s) :=
  { IsSubmonoid.Inter fun y => (hs y).to_is_submonoid with
    inv_mem := fun x h => Set.mem_Inter.2 fun y => IsSubgroup.inv_mem (hs _) (Set.mem_Inter.1 h y) }

@[to_additive]
theorem is_subgroup_Union_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set G} (hs : ∀ i, IsSubgroup (s i))
    (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) : IsSubgroup (⋃ i, s i) :=
  { inv_mem := fun a ha =>
      let ⟨i, hi⟩ := Set.mem_Union.1 ha
      Set.mem_Union.2 ⟨i, (hs i).inv_mem hi⟩,
    to_is_submonoid := is_submonoid_Union_of_directed (fun i => (hs i).to_is_submonoid) Directed }

end Groupₓ

namespace IsSubgroup

open IsSubmonoid

variable [Groupₓ G] {s : Set G} (hs : IsSubgroup s)

include hs

@[to_additive]
theorem inv_mem_iff : a⁻¹ ∈ s ↔ a ∈ s :=
  ⟨fun h => by
    simpa using hs.inv_mem h, inv_mem hs⟩

@[to_additive]
theorem mul_mem_cancel_right (h : a ∈ s) : b * a ∈ s ↔ b ∈ s :=
  ⟨fun hba => by
    simpa using hs.mul_mem hba (hs.inv_mem h), fun hb => hs.mul_mem hb h⟩

@[to_additive]
theorem mul_mem_cancel_left (h : a ∈ s) : a * b ∈ s ↔ b ∈ s :=
  ⟨fun hab => by
    simpa using hs.mul_mem (hs.inv_mem h) hab, hs.mul_mem h⟩

end IsSubgroup

/-- `is_normal_add_subgroup (s : set A)` expresses the fact that `s` is a normal additive subgroup
of the additive group `A`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : add_subgroup A` and `hs : S.normal`, and not via this structure. -/
structure IsNormalAddSubgroup [AddGroupₓ A] (s : Set A) extends IsAddSubgroup s : Prop where
  Normal : ∀, ∀ n ∈ s, ∀, ∀ g : A, g + n + -g ∈ s

/-- `is_normal_subgroup (s : set G)` expresses the fact that `s` is a normal subgroup
of the group `G`. Important: the preferred way to say this in Lean is via bundled
subgroups `S : subgroup G` and not via this structure. -/
@[to_additive]
structure IsNormalSubgroup [Groupₓ G] (s : Set G) extends IsSubgroup s : Prop where
  Normal : ∀, ∀ n ∈ s, ∀, ∀ g : G, g * n * g⁻¹ ∈ s

@[to_additive]
theorem is_normal_subgroup_of_comm_group [CommGroupₓ G] {s : Set G} (hs : IsSubgroup s) : IsNormalSubgroup s :=
  { hs with
    Normal := fun n hn g => by
      rwa [mul_right_commₓ, mul_right_invₓ, one_mulₓ] }

theorem Additive.is_normal_add_subgroup [Groupₓ G] {s : Set G} (hs : IsNormalSubgroup s) :
    @IsNormalAddSubgroup (Additive G) _ s :=
  @IsNormalAddSubgroup.mk (Additive G) _ _ (Additive.is_add_subgroup hs.to_is_subgroup) (IsNormalSubgroup.normal hs)

theorem Additive.is_normal_add_subgroup_iff [Groupₓ G] {s : Set G} :
    @IsNormalAddSubgroup (Additive G) _ s ↔ IsNormalSubgroup s :=
  ⟨by
    rintro ⟨h₁, h₂⟩ <;> exact @IsNormalSubgroup.mk G _ _ (Additive.is_add_subgroup_iff.1 h₁) @h₂, fun h =>
    Additive.is_normal_add_subgroup h⟩

theorem Multiplicative.is_normal_subgroup [AddGroupₓ A] {s : Set A} (hs : IsNormalAddSubgroup s) :
    @IsNormalSubgroup (Multiplicative A) _ s :=
  @IsNormalSubgroup.mk (Multiplicative A) _ _ (Multiplicative.is_subgroup hs.to_is_add_subgroup)
    (IsNormalAddSubgroup.normal hs)

theorem Multiplicative.is_normal_subgroup_iff [AddGroupₓ A] {s : Set A} :
    @IsNormalSubgroup (Multiplicative A) _ s ↔ IsNormalAddSubgroup s :=
  ⟨by
    rintro ⟨h₁, h₂⟩ <;> exact @IsNormalAddSubgroup.mk A _ _ (Multiplicative.is_subgroup_iff.1 h₁) @h₂, fun h =>
    Multiplicative.is_normal_subgroup h⟩

namespace IsSubgroup

variable [Groupₓ G]

-- Normal subgroup properties
@[to_additive]
theorem mem_norm_comm {s : Set G} (hs : IsNormalSubgroup s) {a b : G} (hab : a * b ∈ s) : b * a ∈ s := by
  have h : a⁻¹ * (a * b) * a⁻¹⁻¹ ∈ s := hs.Normal (a * b) hab a⁻¹
  simp at h <;> exact h

@[to_additive]
theorem mem_norm_comm_iff {s : Set G} (hs : IsNormalSubgroup s) {a b : G} : a * b ∈ s ↔ b * a ∈ s :=
  ⟨mem_norm_comm hs, mem_norm_comm hs⟩

/-- The trivial subgroup -/
@[to_additive "the trivial additive subgroup"]
def Trivial (G : Type _) [Groupₓ G] : Set G :=
  {1}

@[simp, to_additive]
theorem mem_trivial {g : G} : g ∈ Trivial G ↔ g = 1 :=
  mem_singleton_iff

@[to_additive]
theorem trivial_normal : IsNormalSubgroup (Trivial G) := by
  refine' { .. } <;> simp (config := { contextual := true })[← trivialₓ]

@[to_additive]
theorem eq_trivial_iff {s : Set G} (hs : IsSubgroup s) : s = Trivial G ↔ ∀, ∀ x ∈ s, ∀, x = (1 : G) := by
  simp only [← Set.ext_iff, ← IsSubgroup.mem_trivial] <;>
    exact ⟨fun h x => (h x).1, fun h x => ⟨h x, fun hx => hx.symm ▸ hs.to_is_submonoid.one_mem⟩⟩

@[to_additive]
theorem univ_subgroup : IsNormalSubgroup (@Univ G) := by
  refine' { .. } <;> simp

/-- The underlying set of the center of a group. -/
@[to_additive add_center "The underlying set of the center of an additive group."]
def Center (G : Type _) [Groupₓ G] : Set G :=
  { z | ∀ g, g * z = z * g }

@[to_additive mem_add_center]
theorem mem_center {a : G} : a ∈ Center G ↔ ∀ g, g * a = a * g :=
  Iff.rfl

@[to_additive add_center_normal]
theorem center_normal : IsNormalSubgroup (Center G) :=
  { one_mem := by
      simp [← center],
    mul_mem := fun a b ha hb g => by
      rw [← mul_assoc, mem_center.2 ha g, mul_assoc, mem_center.2 hb g, ← mul_assoc],
    inv_mem := fun a ha g =>
      calc
        g * a⁻¹ = a⁻¹ * (g * a) * a⁻¹ := by
          simp [← ha g]
        _ = a⁻¹ * g := by
          rw [← mul_assoc, mul_assoc] <;> simp
        ,
    Normal := fun n ha g h =>
      calc
        h * (g * n * g⁻¹) = h * n := by
          simp [← ha g, ← mul_assoc]
        _ = g * g⁻¹ * n * h := by
          rw [ha h] <;> simp
        _ = g * n * g⁻¹ * h := by
          rw [mul_assoc g, ha g⁻¹, ← mul_assoc]
         }

/-- The underlying set of the normalizer of a subset `S : set G` of a group `G`. That is,
  the elements `g : G` such that `g * S * g⁻¹ = S`. -/
@[to_additive add_normalizer
      "The underlying set of the normalizer of a subset `S : set A` of an\n  additive group `A`. That is, the elements `a : A` such that `a + S - a = S`."]
def Normalizer (s : Set G) : Set G :=
  { g : G | ∀ n, n ∈ s ↔ g * n * g⁻¹ ∈ s }

@[to_additive]
theorem normalizer_is_subgroup (s : Set G) : IsSubgroup (Normalizer s) :=
  { one_mem := by
      simp [← normalizer],
    mul_mem := fun a b (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) (hb : ∀ n, n ∈ s ↔ b * n * b⁻¹ ∈ s) n => by
      rw [mul_inv_rev, ← mul_assoc, mul_assoc a, mul_assoc a, ← ha, ← hb],
    inv_mem := fun a (ha : ∀ n, n ∈ s ↔ a * n * a⁻¹ ∈ s) n => by
      rw [ha (a⁻¹ * n * a⁻¹⁻¹)] <;> simp [← mul_assoc] }

@[to_additive subset_add_normalizer]
theorem subset_normalizer {s : Set G} (hs : IsSubgroup s) : s ⊆ Normalizer s := fun g hg n => by
  rw [IsSubgroup.mul_mem_cancel_right hs ((IsSubgroup.inv_mem_iff hs).2 hg), IsSubgroup.mul_mem_cancel_left hs hg]

end IsSubgroup

-- Homomorphism subgroups
namespace IsGroupHom

open IsSubmonoid IsSubgroup

/-- `ker f : set G` is the underlying subset of the kernel of a map `G → H`. -/
@[to_additive "`ker f : set A` is the underlying subset of the kernel of a map `A → B`"]
def Ker [Groupₓ H] (f : G → H) : Set G :=
  preimage f (trivialₓ H)

@[to_additive]
theorem mem_ker [Groupₓ H] (f : G → H) {x : G} : x ∈ Ker f ↔ f x = 1 :=
  mem_trivial

variable [Groupₓ G] [Groupₓ H]

@[to_additive]
theorem one_ker_inv {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f (a * b⁻¹) = 1) : f a = f b := by
  rw [hf.map_mul, hf.map_inv] at h
  rw [← inv_invₓ (f b), eq_inv_of_mul_eq_one_left h]

@[to_additive]
theorem one_ker_inv' {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f (a⁻¹ * b) = 1) : f a = f b := by
  rw [hf.map_mul, hf.map_inv] at h
  apply inv_injective
  rw [eq_inv_of_mul_eq_one_left h]

@[to_additive]
theorem inv_ker_one {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f a = f b) : f (a * b⁻¹) = 1 := by
  have : f a * (f b)⁻¹ = 1 := by
    rw [h, mul_right_invₓ]
  rwa [← hf.map_inv, ← hf.map_mul] at this

@[to_additive]
theorem inv_ker_one' {f : G → H} (hf : IsGroupHom f) {a b : G} (h : f a = f b) : f (a⁻¹ * b) = 1 := by
  have : (f a)⁻¹ * f b = 1 := by
    rw [h, mul_left_invₓ]
  rwa [← hf.map_inv, ← hf.map_mul] at this

@[to_additive]
theorem one_iff_ker_inv {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ f (a * b⁻¹) = 1 :=
  ⟨hf.inv_ker_one, hf.one_ker_inv⟩

@[to_additive]
theorem one_iff_ker_inv' {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ f (a⁻¹ * b) = 1 :=
  ⟨hf.inv_ker_one', hf.one_ker_inv'⟩

@[to_additive]
theorem inv_iff_ker {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ a * b⁻¹ ∈ Ker f := by
  rw [mem_ker] <;> exact one_iff_ker_inv hf _ _

@[to_additive]
theorem inv_iff_ker' {f : G → H} (hf : IsGroupHom f) (a b : G) : f a = f b ↔ a⁻¹ * b ∈ Ker f := by
  rw [mem_ker] <;> exact one_iff_ker_inv' hf _ _

@[to_additive]
theorem image_subgroup {f : G → H} (hf : IsGroupHom f) {s : Set G} (hs : IsSubgroup s) : IsSubgroup (f '' s) :=
  { mul_mem := fun a₁ a₂ ⟨b₁, hb₁, eq₁⟩ ⟨b₂, hb₂, eq₂⟩ =>
      ⟨b₁ * b₂, hs.mul_mem hb₁ hb₂, by
        simp [← eq₁, ← eq₂, ← hf.map_mul]⟩,
    one_mem := ⟨1, hs.to_is_submonoid.one_mem, hf.map_one⟩,
    inv_mem := fun a ⟨b, hb, Eq⟩ =>
      ⟨b⁻¹, hs.inv_mem hb, by
        rw [hf.map_inv]
        simp [*]⟩ }

@[to_additive]
theorem range_subgroup {f : G → H} (hf : IsGroupHom f) : IsSubgroup (Set.Range f) :=
  @Set.image_univ _ _ f ▸ hf.image_subgroup univ_subgroup.to_is_subgroup

attribute [local simp] one_mem inv_mem mul_mem IsNormalSubgroup.normal

@[to_additive]
theorem preimage {f : G → H} (hf : IsGroupHom f) {s : Set H} (hs : IsSubgroup s) : IsSubgroup (f ⁻¹' s) := by
  refine' { .. } <;>
    simp (config := { contextual := true })[← hs.one_mem, ← hs.mul_mem, ← hs.inv_mem, ← hf.map_mul, ← hf.map_one, ←
      hf.map_inv, ← InvMemClass.inv_mem]

@[to_additive]
theorem preimage_normal {f : G → H} (hf : IsGroupHom f) {s : Set H} (hs : IsNormalSubgroup s) :
    IsNormalSubgroup (f ⁻¹' s) :=
  { one_mem := by
      simp [← hf.map_one, ← hs.to_is_subgroup.one_mem],
    mul_mem := by
      simp (config := { contextual := true })[← hf.map_mul, ← hs.to_is_subgroup.mul_mem],
    inv_mem := by
      simp (config := { contextual := true })[← hf.map_inv, ← hs.to_is_subgroup.inv_mem],
    Normal := by
      simp (config := { contextual := true })[← hs.normal, ← hf.map_mul, ← hf.map_inv] }

@[to_additive]
theorem is_normal_subgroup_ker {f : G → H} (hf : IsGroupHom f) : IsNormalSubgroup (Ker f) :=
  hf.preimage_normal trivial_normal

@[to_additive]
theorem injective_of_trivial_ker {f : G → H} (hf : IsGroupHom f) (h : Ker f = trivialₓ G) : Function.Injective f := by
  intro a₁ a₂ hfa
  simp [← ext_iff, ← ker, ← IsSubgroup.Trivial] at h
  have ha : a₁ * a₂⁻¹ = 1 := by
    rw [← h] <;> exact hf.inv_ker_one hfa
  rw [eq_inv_of_mul_eq_one_left ha, inv_invₓ a₂]

@[to_additive]
theorem trivial_ker_of_injective {f : G → H} (hf : IsGroupHom f) (h : Function.Injective f) : Ker f = trivialₓ G :=
  Set.ext fun x =>
    Iff.intro
      (fun hx => by
        suffices f x = f 1 by
          simpa using h this
        simp [← hf.map_one] <;> rwa [mem_ker] at hx)
      (by
        simp (config := { contextual := true })[← mem_ker, ← hf.map_one])

@[to_additive]
theorem injective_iff_trivial_ker {f : G → H} (hf : IsGroupHom f) : Function.Injective f ↔ Ker f = trivialₓ G :=
  ⟨hf.trivial_ker_of_injective, hf.injective_of_trivial_ker⟩

@[to_additive]
theorem trivial_ker_iff_eq_one {f : G → H} (hf : IsGroupHom f) : Ker f = trivialₓ G ↔ ∀ x, f x = 1 → x = 1 := by
  rw [Set.ext_iff] <;>
    simp [← ker] <;>
      exact
        ⟨fun h x hx => (h x).1 hx, fun h x =>
          ⟨h x, fun hx => by
            rw [hx, hf.map_one]⟩⟩

end IsGroupHom

namespace AddGroupₓ

variable [AddGroupₓ A]

/-- If `A` is an additive group and `s : set A`, then `in_closure s : set A` is the underlying
subset of the subgroup generated by `s`. -/
inductive InClosure (s : Set A) : A → Prop
  | basic {a : A} : a ∈ s → in_closure a
  | zero : in_closure 0
  | neg {a : A} : in_closure a → in_closure (-a)
  | add {a b : A} : in_closure a → in_closure b → in_closure (a + b)

end AddGroupₓ

namespace Groupₓ

open IsSubmonoid IsSubgroup

variable [Groupₓ G] {s : Set G}

/-- If `G` is a group and `s : set G`, then `in_closure s : set G` is the underlying
subset of the subgroup generated by `s`. -/
@[to_additive]
inductive InClosure (s : Set G) : G → Prop
  | basic {a : G} : a ∈ s → in_closure a
  | one : in_closure 1
  | inv {a : G} : in_closure a → in_closure a⁻¹
  | mul {a b : G} : in_closure a → in_closure b → in_closure (a * b)

/-- `group.closure s` is the subgroup generated by `s`, i.e. the smallest subgroup containg `s`. -/
@[to_additive
      "`add_group.closure s` is the additive subgroup generated by `s`, i.e., the\n  smallest additive subgroup containing `s`."]
def Closure (s : Set G) : Set G :=
  { a | InClosure s a }

@[to_additive]
theorem mem_closure {a : G} : a ∈ s → a ∈ Closure s :=
  in_closure.basic

@[to_additive]
theorem Closure.is_subgroup (s : Set G) : IsSubgroup (Closure s) :=
  { one_mem := InClosure.one, mul_mem := fun a b => InClosure.mul, inv_mem := fun a => InClosure.inv }

@[to_additive]
theorem subset_closure {s : Set G} : s ⊆ Closure s := fun a => mem_closure

@[to_additive]
theorem closure_subset {s t : Set G} (ht : IsSubgroup t) (h : s ⊆ t) : Closure s ⊆ t := fun a ha => by
  induction ha <;> simp [← h _, *, ← ht.one_mem, ← ht.mul_mem, ← IsSubgroup.inv_mem_iff]

@[to_additive]
theorem closure_subset_iff {s t : Set G} (ht : IsSubgroup t) : Closure s ⊆ t ↔ s ⊆ t :=
  ⟨fun h b ha => h (mem_closure ha), fun h b ha => closure_subset ht h ha⟩

@[to_additive]
theorem closure_mono {s t : Set G} (h : s ⊆ t) : Closure s ⊆ Closure t :=
  closure_subset (Closure.is_subgroup _) <| Set.Subset.trans h subset_closure

@[simp, to_additive]
theorem closure_subgroup {s : Set G} (hs : IsSubgroup s) : Closure s = s :=
  Set.Subset.antisymm (closure_subset hs <| Set.Subset.refl s) subset_closure

@[to_additive]
theorem exists_list_of_mem_closure {s : Set G} {a : G} (h : a ∈ Closure s) :
    ∃ l : List G, (∀, ∀ x ∈ l, ∀, x ∈ s ∨ x⁻¹ ∈ s) ∧ l.Prod = a :=
  InClosure.rec_on h (fun x hxs => ⟨[x], List.forall_mem_singletonₓ.2 <| Or.inl hxs, one_mulₓ _⟩)
    ⟨[], List.forall_mem_nilₓ _, rfl⟩
    (fun x _ ⟨L, HL1, HL2⟩ =>
      ⟨L.reverse.map Inv.inv, fun x hx =>
        let ⟨y, hy1, hy2⟩ := List.exists_of_mem_mapₓ hx
        hy2 ▸
          Or.imp id
            (by
              rw [inv_invₓ] <;> exact id)
            (HL1 _ <| List.mem_reverseₓ.1 hy1).symm,
        HL2 ▸
          List.recOn L inv_one.symm fun hd tl ih => by
            rw [List.reverse_cons, List.map_append, List.prod_append, ih, List.map_singleton, List.prod_cons,
              List.prod_nil, mul_oneₓ, List.prod_cons, mul_inv_rev]⟩)
    fun x y hx hy ⟨L1, HL1, HL2⟩ ⟨L2, HL3, HL4⟩ =>
    ⟨L1 ++ L2, List.forall_mem_appendₓ.2 ⟨HL1, HL3⟩, by
      rw [List.prod_append, HL2, HL4]⟩

@[to_additive]
theorem image_closure [Groupₓ H] {f : G → H} (hf : IsGroupHom f) (s : Set G) : f '' Closure s = Closure (f '' s) :=
  le_antisymmₓ
    (by
      rintro _ ⟨x, hx, rfl⟩
      apply in_closure.rec_on hx <;> intros
      · solve_by_elim [← subset_closure, ← Set.mem_image_of_mem]
        
      · rw [hf.to_is_monoid_hom.map_one]
        apply IsSubmonoid.one_mem (closure.is_subgroup _).to_is_submonoid
        
      · rw [hf.map_inv]
        apply IsSubgroup.inv_mem (closure.is_subgroup _)
        assumption
        
      · rw [hf.to_is_monoid_hom.map_mul]
        solve_by_elim [← IsSubmonoid.mul_mem (closure.is_subgroup _).to_is_submonoid]
        )
    (closure_subset (hf.image_subgroup <| Closure.is_subgroup _) <| Set.image_subset _ subset_closure)

@[to_additive]
theorem mclosure_subset {s : Set G} : Monoidₓ.Closure s ⊆ Closure s :=
  Monoidₓ.closure_subset (Closure.is_subgroup _).to_is_submonoid <| subset_closure

@[to_additive]
theorem mclosure_inv_subset {s : Set G} : Monoidₓ.Closure (Inv.inv ⁻¹' s) ⊆ Closure s :=
  (Monoidₓ.closure_subset (Closure.is_subgroup _).to_is_submonoid) fun x hx =>
    inv_invₓ x ▸ ((Closure.is_subgroup _).inv_mem <| subset_closure hx)

@[to_additive]
theorem closure_eq_mclosure {s : Set G} : Closure s = Monoidₓ.Closure (s ∪ Inv.inv ⁻¹' s) :=
  Set.Subset.antisymm
    (@closure_subset _ _ _ (Monoidₓ.Closure (s ∪ Inv.inv ⁻¹' s))
      { one_mem := (Monoidₓ.Closure.is_submonoid _).one_mem, mul_mem := (Monoidₓ.Closure.is_submonoid _).mul_mem,
        inv_mem := fun x hx =>
          Monoidₓ.InClosure.rec_on hx
            (fun x hx =>
              Or.cases_on hx (fun hx => Monoidₓ.subset_closure <| Or.inr <| show x⁻¹⁻¹ ∈ s from (inv_invₓ x).symm ▸ hx)
                fun hx => Monoidₓ.subset_closure <| Or.inl hx)
            ((@inv_one G _).symm ▸ IsSubmonoid.one_mem (Monoidₓ.Closure.is_submonoid _)) fun x y hx hy ihx ihy =>
            (mul_inv_rev x y).symm ▸ IsSubmonoid.mul_mem (Monoidₓ.Closure.is_submonoid _) ihy ihx }
      (Set.Subset.trans (Set.subset_union_left _ _) Monoidₓ.subset_closure))
    (Monoidₓ.closure_subset (Closure.is_subgroup _).to_is_submonoid <|
      (Set.union_subset subset_closure) fun x hx =>
        inv_invₓ x ▸ (IsSubgroup.inv_mem (Closure.is_subgroup _) <| subset_closure hx))

@[to_additive]
theorem mem_closure_union_iff {G : Type _} [CommGroupₓ G] {s t : Set G} {x : G} :
    x ∈ Closure (s ∪ t) ↔ ∃ y ∈ Closure s, ∃ z ∈ Closure t, y * z = x := by
  simp only [← closure_eq_mclosure, ← Monoidₓ.mem_closure_union_iff, ← exists_prop, ← preimage_union]
  constructor
  · rintro ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, rfl⟩
    refine' ⟨_, ⟨_, hys, _, hzs, rfl⟩, _, ⟨_, hyt, _, hzt, rfl⟩, _⟩
    rw [mul_assoc, mul_assoc, mul_left_commₓ zs]
    
  · rintro ⟨_, ⟨ys, hys, zs, hzs, rfl⟩, _, ⟨yt, hyt, zt, hzt, rfl⟩, rfl⟩
    refine' ⟨_, ⟨ys, hys, yt, hyt, rfl⟩, _, ⟨zs, hzs, zt, hzt, rfl⟩, _⟩
    rw [mul_assoc, mul_assoc, mul_left_commₓ yt]
    

end Groupₓ

namespace IsSubgroup

variable [Groupₓ G]

@[to_additive]
theorem trivial_eq_closure : Trivial G = Groupₓ.Closure ∅ :=
  Subset.antisymm
    (by
      simp [← Set.subset_def, ← (Groupₓ.Closure.is_subgroup _).one_mem])
    (Groupₓ.closure_subset trivial_normal.to_is_subgroup <| by
      simp )

end IsSubgroup

/-The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
namespace Groupₓ

variable {s : Set G} [Groupₓ G]

theorem conjugates_of_subset {t : Set G} (ht : IsNormalSubgroup t) {a : G} (h : a ∈ t) : ConjugatesOf a ⊆ t :=
  fun x hc => by
  obtain ⟨c, w⟩ := is_conj_iff.1 hc
  have H := IsNormalSubgroup.normal ht a h c
  rwa [← w]

theorem conjugates_of_set_subset' {s t : Set G} (ht : IsNormalSubgroup t) (h : s ⊆ t) : ConjugatesOfSet s ⊆ t :=
  Set.Union₂_subset fun x H => conjugates_of_subset ht (h H)

/-- The normal closure of a set s is the subgroup closure of all the conjugates of
elements of s. It is the smallest normal subgroup containing s. -/
def NormalClosure (s : Set G) : Set G :=
  Closure (ConjugatesOfSet s)

theorem conjugates_of_set_subset_normal_closure : ConjugatesOfSet s ⊆ NormalClosure s :=
  subset_closure

theorem subset_normal_closure : s ⊆ NormalClosure s :=
  Set.Subset.trans subset_conjugates_of_set conjugates_of_set_subset_normal_closure

/-- The normal closure of a set is a subgroup. -/
theorem NormalClosure.is_subgroup (s : Set G) : IsSubgroup (NormalClosure s) :=
  Closure.is_subgroup (ConjugatesOfSet s)

/-- The normal closure of s is a normal subgroup. -/
theorem NormalClosure.is_normal : IsNormalSubgroup (NormalClosure s) :=
  { NormalClosure.is_subgroup _ with
    Normal := fun n h g => by
      induction' h with x hx x hx ihx x y hx hy ihx ihy
      · exact conjugates_of_set_subset_normal_closure (conj_mem_conjugates_of_set hx)
        
      · simpa using (normal_closure.is_subgroup s).one_mem
        
      · rw [← conj_inv]
        exact (normal_closure.is_subgroup _).inv_mem ihx
        
      · rw [← conj_mul]
        exact (normal_closure.is_subgroup _).to_is_submonoid.mul_mem ihx ihy
         }

/-- The normal closure of s is the smallest normal subgroup containing s. -/
theorem normal_closure_subset {s t : Set G} (ht : IsNormalSubgroup t) (h : s ⊆ t) : NormalClosure s ⊆ t := fun a w => by
  induction' w with x hx x hx ihx x y hx hy ihx ihy
  · exact conjugates_of_set_subset' ht h <| hx
    
  · exact ht.to_is_subgroup.to_is_submonoid.one_mem
    
  · exact ht.to_is_subgroup.inv_mem ihx
    
  · exact ht.to_is_subgroup.to_is_submonoid.mul_mem ihx ihy
    

theorem normal_closure_subset_iff {s t : Set G} (ht : IsNormalSubgroup t) : s ⊆ t ↔ NormalClosure s ⊆ t :=
  ⟨normal_closure_subset ht, Set.Subset.trans subset_normal_closure⟩

theorem normal_closure_mono {s t : Set G} : s ⊆ t → NormalClosure s ⊆ NormalClosure t := fun h =>
  normal_closure_subset NormalClosure.is_normal (Set.Subset.trans h subset_normal_closure)

end Groupₓ

/-- Create a bundled subgroup from a set `s` and `[is_subgroup s]`. -/
@[to_additive "Create a bundled additive subgroup from a set `s` and `[is_add_subgroup s]`."]
def Subgroup.of [Groupₓ G] {s : Set G} (h : IsSubgroup s) : Subgroup G where
  Carrier := s
  one_mem' := h.1.1
  mul_mem' := h.1.2
  inv_mem' := h.2

@[to_additive]
theorem Subgroup.is_subgroup [Groupₓ G] (K : Subgroup G) : IsSubgroup (K : Set G) :=
  { one_mem := K.one_mem', mul_mem := K.mul_mem', inv_mem := K.inv_mem' }

-- this will never fire if it's an instance
@[to_additive]
theorem Subgroup.of_normal [Groupₓ G] (s : Set G) (h : IsSubgroup s) (n : IsNormalSubgroup s) :
    Subgroup.Normal (Subgroup.of h) :=
  { conj_mem := n.Normal }

