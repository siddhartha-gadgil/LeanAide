/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Deprecated.Subgroup
import Mathbin.Deprecated.Group
import Mathbin.RingTheory.Subring.Basic

/-!
# Unbundled subrings (deprecated)

This file is deprecated, and is no longer imported by anything in mathlib other than other
deprecated files, and test files. You should not need to import it.

This file defines predicates for unbundled subrings. Instead of using this file, please use
`subring`, defined in `ring_theory.subring.basic`, for subrings of rings.

## Main definitions

`is_subring (S : set R) : Prop` : the predicate that `S` is the underlying set of a subring
of the ring `R`. The bundled variant `subring R` should be used in preference to this.

## Tags

is_subring
-/


universe u v

open Groupₓ

variable {R : Type u} [Ringₓ R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and additive
inverse. -/
structure IsSubring (S : Set R) extends IsAddSubgroup S, IsSubmonoid S : Prop

/-- Construct a `subring` from a set satisfying `is_subring`. -/
def IsSubring.subring {S : Set R} (hs : IsSubring S) : Subring R where
  Carrier := S
  one_mem' := hs.one_mem
  mul_mem' := hs.mul_mem
  zero_mem' := hs.zero_mem
  add_mem' := hs.add_mem
  neg_mem' := hs.neg_mem

namespace RingHom

theorem is_subring_preimage {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) {s : Set S} (hs : IsSubring s) :
    IsSubring (f ⁻¹' s) :=
  { IsAddGroupHom.preimage f.to_is_add_group_hom hs.to_is_add_subgroup,
    IsSubmonoid.preimage f.to_is_monoid_hom hs.to_is_submonoid with }

theorem is_subring_image {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) {s : Set R} (hs : IsSubring s) :
    IsSubring (f '' s) :=
  { IsAddGroupHom.image_add_subgroup f.to_is_add_group_hom hs.to_is_add_subgroup,
    IsSubmonoid.image f.to_is_monoid_hom hs.to_is_submonoid with }

theorem is_subring_set_range {R : Type u} {S : Type v} [Ringₓ R] [Ringₓ S] (f : R →+* S) : IsSubring (Set.Range f) :=
  { IsAddGroupHom.range_add_subgroup f.to_is_add_group_hom, Range.is_submonoid f.to_is_monoid_hom with }

end RingHom

variable {cR : Type u} [CommRingₓ cR]

theorem IsSubring.inter {S₁ S₂ : Set R} (hS₁ : IsSubring S₁) (hS₂ : IsSubring S₂) : IsSubring (S₁ ∩ S₂) :=
  { IsAddSubgroup.inter hS₁.to_is_add_subgroup hS₂.to_is_add_subgroup,
    IsSubmonoid.inter hS₁.to_is_submonoid hS₂.to_is_submonoid with }

theorem IsSubring.Inter {ι : Sort _} {S : ι → Set R} (h : ∀ y : ι, IsSubring (S y)) : IsSubring (Set.Inter S) :=
  { IsAddSubgroup.Inter fun i => (h i).to_is_add_subgroup, IsSubmonoid.Inter fun i => (h i).to_is_submonoid with }

theorem is_subring_Union_of_directed {ι : Type _} [hι : Nonempty ι] {s : ι → Set R} (h : ∀ i, IsSubring (s i))
    (directed : ∀ i j, ∃ k, s i ⊆ s k ∧ s j ⊆ s k) : IsSubring (⋃ i, s i) :=
  { to_is_add_subgroup := is_add_subgroup_Union_of_directed (fun i => (h i).to_is_add_subgroup) Directed,
    to_is_submonoid := is_submonoid_Union_of_directed (fun i => (h i).to_is_submonoid) Directed }

namespace Ringₓ

/-- The smallest subring containing a given subset of a ring, considered as a set. This function
is deprecated; use `subring.closure`. -/
def Closure (s : Set R) :=
  AddGroupₓ.Closure (Monoidₓ.Closure s)

variable {s : Set R}

attribute [local reducible] closure

theorem exists_list_of_mem_closure {a : R} (h : a ∈ Closure s) :
    ∃ L : List (List R), (∀, ∀ l ∈ L, ∀, ∀, ∀ x ∈ l, ∀, x ∈ s ∨ x = (-1 : R)) ∧ (L.map List.prod).Sum = a :=
  AddGroupₓ.InClosure.rec_on h
    (fun x hx =>
      match x, Monoidₓ.exists_list_of_mem_closure hx with
      | _, ⟨L, h1, rfl⟩ => ⟨[L], List.forall_mem_singletonₓ.2 fun r hr => Or.inl (h1 r hr), zero_addₓ _⟩)
    ⟨[], List.forall_mem_nilₓ _, rfl⟩
    (fun b _ ih =>
      match b, ih with
      | _, ⟨L1, h1, rfl⟩ =>
        ⟨L1.map (List.cons (-1)), fun L2 h2 =>
          match L2, List.mem_mapₓ.1 h2 with
          | _, ⟨L3, h3, rfl⟩ => List.forall_mem_consₓ.2 ⟨Or.inr rfl, h1 L3 h3⟩,
          by
          simp only [← List.map_mapₓ, ← (· ∘ ·), ← List.prod_cons, ← neg_one_mul] <;>
            exact
              List.recOn L1 neg_zero.symm fun hd tl ih => by
                rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons, neg_add]⟩)
    fun r1 r2 hr1 hr2 ih1 ih2 =>
    match r1, r2, ih1, ih2 with
    | _, _, ⟨L1, h1, rfl⟩, ⟨L2, h2, rfl⟩ =>
      ⟨L1 ++ L2, List.forall_mem_appendₓ.2 ⟨h1, h2⟩, by
        rw [List.map_append, List.sum_append]⟩

@[elab_as_eliminator]
protected theorem InClosure.rec_on {C : R → Prop} {x : R} (hx : x ∈ Closure s) (h1 : C 1) (hneg1 : C (-1))
    (hs : ∀, ∀ z ∈ s, ∀, ∀ n, C n → C (z * n)) (ha : ∀ {x y}, C x → C y → C (x + y)) : C x := by
  have h0 : C 0 := add_neg_selfₓ (1 : R) ▸ ha h1 hneg1
  rcases exists_list_of_mem_closure hx with ⟨L, HL, rfl⟩
  clear hx
  induction' L with hd tl ih
  · exact h0
    
  rw [List.forall_mem_consₓ] at HL
  suffices C (List.prod hd) by
    rw [List.map_cons, List.sum_cons]
    exact ha this (ih HL.2)
  replace HL := HL.1
  clear ih tl
  suffices ∃ L : List R, (∀, ∀ x ∈ L, ∀, x ∈ s) ∧ (List.prod hd = List.prod L ∨ List.prod hd = -List.prod L) by
    rcases this with ⟨L, HL', HP | HP⟩
    · rw [HP]
      clear HP HL hd
      induction' L with hd tl ih
      · exact h1
        
      rw [List.forall_mem_consₓ] at HL'
      rw [List.prod_cons]
      exact hs _ HL'.1 _ (ih HL'.2)
      
    rw [HP]
    clear HP HL hd
    induction' L with hd tl ih
    · exact hneg1
      
    rw [List.prod_cons, neg_mul_eq_mul_neg]
    rw [List.forall_mem_consₓ] at HL'
    exact hs _ HL'.1 _ (ih HL'.2)
  induction' hd with hd tl ih
  · exact ⟨[], List.forall_mem_nilₓ _, Or.inl rfl⟩
    
  rw [List.forall_mem_consₓ] at HL
  rcases ih HL.2 with ⟨L, HL', HP | HP⟩ <;> cases' HL.1 with hhd hhd
  · exact
      ⟨hd :: L, List.forall_mem_consₓ.2 ⟨hhd, HL'⟩,
        Or.inl <| by
          rw [List.prod_cons, List.prod_cons, HP]⟩
    
  · exact
      ⟨L, HL',
        Or.inr <| by
          rw [List.prod_cons, hhd, neg_one_mul, HP]⟩
    
  · exact
      ⟨hd :: L, List.forall_mem_consₓ.2 ⟨hhd, HL'⟩,
        Or.inr <| by
          rw [List.prod_cons, List.prod_cons, HP, neg_mul_eq_mul_neg]⟩
    
  · exact
      ⟨L, HL',
        Or.inl <| by
          rw [List.prod_cons, hhd, HP, neg_one_mul, neg_negₓ]⟩
    

theorem Closure.is_subring : IsSubring (Closure s) :=
  { AddGroupₓ.Closure.is_add_subgroup _ with
    one_mem := AddGroupₓ.mem_closure <| IsSubmonoid.one_mem <| Monoidₓ.Closure.is_submonoid _,
    mul_mem := fun a b ha hb =>
      AddGroupₓ.InClosure.rec_on hb
        (fun c hc =>
          AddGroupₓ.InClosure.rec_on ha
            (fun d hd => AddGroupₓ.subset_closure ((Monoidₓ.Closure.is_submonoid _).mul_mem hd hc))
            ((zero_mul c).symm ▸ (AddGroupₓ.Closure.is_add_subgroup _).zero_mem)
            (fun d hd hdc => neg_mul_eq_neg_mulₓ d c ▸ (AddGroupₓ.Closure.is_add_subgroup _).neg_mem hdc)
            fun d e hd he hdc hec => (add_mulₓ d e c).symm ▸ (AddGroupₓ.Closure.is_add_subgroup _).add_mem hdc hec)
        ((mul_zero a).symm ▸ (AddGroupₓ.Closure.is_add_subgroup _).zero_mem)
        (fun c hc hac => neg_mul_eq_mul_neg a c ▸ (AddGroupₓ.Closure.is_add_subgroup _).neg_mem hac)
        fun c d hc hd hac had => (mul_addₓ a c d).symm ▸ (AddGroupₓ.Closure.is_add_subgroup _).add_mem hac had }

theorem mem_closure {a : R} : a ∈ s → a ∈ Closure s :=
  AddGroupₓ.mem_closure ∘ @Monoidₓ.subset_closure _ _ _ _

theorem subset_closure : s ⊆ Closure s := fun _ => mem_closure

theorem closure_subset {t : Set R} (ht : IsSubring t) : s ⊆ t → Closure s ⊆ t :=
  AddGroupₓ.closure_subset ht.to_is_add_subgroup ∘ Monoidₓ.closure_subset ht.to_is_submonoid

theorem closure_subset_iff {s t : Set R} (ht : IsSubring t) : Closure s ⊆ t ↔ s ⊆ t :=
  (AddGroupₓ.closure_subset_iff ht.to_is_add_subgroup).trans
    ⟨Set.Subset.trans Monoidₓ.subset_closure, Monoidₓ.closure_subset ht.to_is_submonoid⟩

theorem closure_mono {s t : Set R} (H : s ⊆ t) : Closure s ⊆ Closure t :=
  closure_subset Closure.is_subring <| Set.Subset.trans H subset_closure

theorem image_closure {S : Type _} [Ringₓ S] (f : R →+* S) (s : Set R) : f '' Closure s = Closure (f '' s) :=
  le_antisymmₓ
    (by
      rintro _ ⟨x, hx, rfl⟩
      apply in_closure.rec_on hx <;> intros
      · rw [f.map_one]
        apply closure.is_subring.to_is_submonoid.one_mem
        
      · rw [f.map_neg, f.map_one]
        apply closure.is_subring.to_is_add_subgroup.neg_mem
        apply closure.is_subring.to_is_submonoid.one_mem
        
      · rw [f.map_mul]
        apply closure.is_subring.to_is_submonoid.mul_mem <;> solve_by_elim [← subset_closure, ← Set.mem_image_of_mem]
        
      · rw [f.map_add]
        apply closure.is_subring.to_is_add_submonoid.add_mem
        assumption'
        )
    (closure_subset (RingHom.is_subring_image _ Closure.is_subring) <| Set.image_subset _ subset_closure)

end Ringₓ

