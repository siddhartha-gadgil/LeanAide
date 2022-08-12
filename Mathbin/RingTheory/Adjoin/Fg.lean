/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathbin.RingTheory.Polynomial.Basic
import Mathbin.RingTheory.PrincipalIdealDomain
import Mathbin.Data.MvPolynomial.Basic

/-!
# Adjoining elements to form subalgebras

This file develops the basic theory of finitely-generated subalgebras.

## Definitions

* `fg (S : subalgebra R A)` : A predicate saying that the subalgebra is finitely-generated
as an A-algebra

## Tags

adjoin, algebra, finitely-generated algebra

-/


universe u v w

open Subsemiring Ringₓ Submodule

open Pointwise

namespace Algebra

variable {R : Type u} {A : Type v} {B : Type w} [CommSemiringₓ R] [CommSemiringₓ A] [Algebra R A] {s t : Set A}

theorem fg_trans (h1 : (adjoin R s).toSubmodule.Fg) (h2 : (adjoin (adjoin R s) t).toSubmodule.Fg) :
    (adjoin R (s ∪ t)).toSubmodule.Fg := by
  rcases fg_def.1 h1 with ⟨p, hp, hp'⟩
  rcases fg_def.1 h2 with ⟨q, hq, hq'⟩
  refine' fg_def.2 ⟨p * q, hp.mul hq, le_antisymmₓ _ _⟩
  · rw [span_le]
    rintro _ ⟨x, y, hx, hy, rfl⟩
    change x * y ∈ _
    refine' Subalgebra.mul_mem _ _ _
    · have : x ∈ (adjoin R s).toSubmodule := by
        rw [← hp']
        exact subset_span hx
      exact adjoin_mono (Set.subset_union_left _ _) this
      
    have : y ∈ (adjoin (adjoin R s) t).toSubmodule := by
      rw [← hq']
      exact subset_span hy
    change y ∈ adjoin R (s ∪ t)
    rwa [adjoin_union_eq_adjoin_adjoin]
    
  · intro r hr
    change r ∈ adjoin R (s ∪ t) at hr
    rw [adjoin_union_eq_adjoin_adjoin] at hr
    change r ∈ (adjoin (adjoin R s) t).toSubmodule at hr
    rw [← hq', ← Set.image_id q, Finsupp.mem_span_image_iff_total (adjoin R s)] at hr
    rcases hr with ⟨l, hlq, rfl⟩
    have := @Finsupp.total_apply A A (adjoin R s)
    rw [this, Finsupp.sum]
    refine' sum_mem _
    intro z hz
    change (l z).1 * _ ∈ _
    have : (l z).1 ∈ (adjoin R s).toSubmodule := (l z).2
    rw [← hp', ← Set.image_id p, Finsupp.mem_span_image_iff_total R] at this
    rcases this with ⟨l2, hlp, hl⟩
    have := @Finsupp.total_apply A A R
    rw [this] at hl
    rw [← hl, Finsupp.sum_mul]
    refine' sum_mem _
    intro t ht
    change _ * _ ∈ _
    rw [smul_mul_assoc]
    refine' smul_mem _ _ _
    exact subset_span ⟨t, z, hlp ht, hlq hz, rfl⟩
    

end Algebra

namespace Subalgebra

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [Semiringₓ B] [Algebra R B]

/-- A subalgebra `S` is finitely generated if there exists `t : finset A` such that
`algebra.adjoin R t = S`. -/
def Fg (S : Subalgebra R A) : Prop :=
  ∃ t : Finset A, Algebra.adjoin R ↑t = S

theorem fg_adjoin_finset (s : Finset A) : (Algebra.adjoin R (↑s : Set A)).Fg :=
  ⟨s, rfl⟩

theorem fg_def {S : Subalgebra R A} : S.Fg ↔ ∃ t : Set A, Set.Finite t ∧ Algebra.adjoin R t = S :=
  Iff.symm Set.exists_finite_iff_finset

theorem fg_bot : (⊥ : Subalgebra R A).Fg :=
  ⟨∅, Algebra.adjoin_empty R A⟩

theorem fg_of_fg_to_submodule {S : Subalgebra R A} : S.toSubmodule.Fg → S.Fg := fun ⟨t, ht⟩ =>
  ⟨t,
    le_antisymmₓ (Algebra.adjoin_le fun x hx => show x ∈ S.toSubmodule from ht ▸ subset_span hx) <|
      show S.toSubmodule ≤ (Algebra.adjoin R ↑t).toSubmodule from fun x hx =>
        span_le.mpr (fun x hx => Algebra.subset_adjoin hx)
          (show x ∈ span R ↑t by
            rw [ht]
            exact hx)⟩

theorem fg_of_noetherian [IsNoetherian R A] (S : Subalgebra R A) : S.Fg :=
  fg_of_fg_to_submodule (IsNoetherian.noetherian S.toSubmodule)

theorem fg_of_submodule_fg (h : (⊤ : Submodule R A).Fg) : (⊤ : Subalgebra R A).Fg :=
  let ⟨s, hs⟩ := h
  ⟨s,
    to_submodule_injective <| by
      rw [Algebra.top_to_submodule, eq_top_iff, ← hs, span_le]
      exact Algebra.subset_adjoin⟩

theorem Fg.prod {S : Subalgebra R A} {T : Subalgebra R B} (hS : S.Fg) (hT : T.Fg) : (S.Prod T).Fg := by
  obtain ⟨s, hs⟩ := fg_def.1 hS
  obtain ⟨t, ht⟩ := fg_def.1 hT
  rw [← hs.2, ← ht.2]
  exact
    fg_def.2
      ⟨LinearMap.inl R A B '' (s ∪ {1}) ∪ LinearMap.inr R A B '' (t ∪ {1}),
        Set.Finite.union (Set.Finite.image _ (Set.Finite.union hs.1 (Set.finite_singleton _)))
          (Set.Finite.image _ (Set.Finite.union ht.1 (Set.finite_singleton _))),
        Algebra.adjoin_inl_union_inr_eq_prod R s t⟩

section

open Classical

theorem Fg.map {S : Subalgebra R A} (f : A →ₐ[R] B) (hs : S.Fg) : (S.map f).Fg :=
  let ⟨s, hs⟩ := hs
  ⟨s.Image f, by
    rw [Finset.coe_image, Algebra.adjoin_image, hs]⟩

end

theorem fg_of_fg_map (S : Subalgebra R A) (f : A →ₐ[R] B) (hf : Function.Injective f) (hs : (S.map f).Fg) : S.Fg :=
  let ⟨s, hs⟩ := hs
  ⟨(s.Preimage f) fun _ _ _ _ h => hf h,
    map_injective f hf <| by
      rw [← Algebra.adjoin_image, Finset.coe_preimage, Set.image_preimage_eq_of_subset, hs]
      rw [← AlgHom.coe_range, ← Algebra.adjoin_le_iff, hs, ← Algebra.map_top]
      exact map_mono le_top⟩

theorem fg_top (S : Subalgebra R A) : (⊤ : Subalgebra R S).Fg ↔ S.Fg :=
  ⟨fun h => by
    rw [← S.range_val, ← Algebra.map_top]
    exact fg.map _ h, fun h =>
    fg_of_fg_map _ S.val Subtype.val_injective <| by
      rw [Algebra.map_top, range_val]
      exact h⟩

theorem induction_on_adjoin [IsNoetherian R A] (P : Subalgebra R A → Prop) (base : P ⊥)
    (ih : ∀ (S : Subalgebra R A) (x : A), P S → P (Algebra.adjoin R (insert x S))) (S : Subalgebra R A) : P S := by
  classical
  obtain ⟨t, rfl⟩ := S.fg_of_noetherian
  refine' Finset.induction_on t _ _
  · simpa using base
    
  intro x t hxt h
  rw [Finset.coe_insert]
  simpa only [← Algebra.adjoin_insert_adjoin] using ih _ x h

end Subalgebra

section Semiringₓ

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommSemiringₓ R] [CommRingₓ A] [CommRingₓ B] [Algebra R A] [Algebra R B]

/-- The image of a Noetherian R-algebra under an R-algebra map is a Noetherian ring. -/
instance AlgHom.is_noetherian_ring_range (f : A →ₐ[R] B) [IsNoetherianRing A] : IsNoetherianRing f.range :=
  is_noetherian_ring_range f.toRingHom

end Semiringₓ

section Ringₓ

variable {R : Type u} {A : Type v} {B : Type w}

variable [CommRingₓ R] [CommRingₓ A] [CommRingₓ B] [Algebra R A] [Algebra R B]

theorem is_noetherian_ring_of_fg {S : Subalgebra R A} (HS : S.Fg) [IsNoetherianRing R] : IsNoetherianRing S :=
  let ⟨t, ht⟩ := HS
  ht ▸
    (Algebra.adjoin_eq_range R (↑t : Set A)).symm ▸ by
      have : IsNoetherianRing (MvPolynomial (↑t : Set A) R) := MvPolynomial.is_noetherian_ring <;>
        convert AlgHom.is_noetherian_ring_range _ <;> infer_instance

theorem is_noetherian_subring_closure (s : Set R) (hs : s.Finite) : IsNoetherianRing (Subring.closure s) :=
  show IsNoetherianRing (subalgebraOfSubring (Subring.closure s)) from
    Algebra.adjoin_int s ▸ is_noetherian_ring_of_fg (Subalgebra.fg_def.2 ⟨s, hs, rfl⟩)

end Ringₓ

