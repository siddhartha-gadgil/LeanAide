/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import Mathbin.Data.Polynomial.Basic

/-!
# Univariate monomials

Preparatory lemmas for degree_basic.
-/


noncomputable section

namespace Polynomial

open Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}

variable [Semiringₓ R] {p q r : R[X]}

theorem monomial_one_eq_iff [Nontrivial R] {i j : ℕ} : (monomial i 1 : R[X]) = monomial j 1 ↔ i = j := by
  simp_rw [← of_finsupp_single]
  exact add_monoid_algebra.of_injective.eq_iff

instance [Nontrivial R] : Infinite R[X] :=
  (Infinite.of_injective fun i => monomial i 1) fun m n h => by
    simpa [← monomial_one_eq_iff] using h

theorem card_support_le_one_iff_monomial {f : R[X]} : Finset.card f.Support ≤ 1 ↔ ∃ n a, f = monomial n a := by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine' ⟨n, f.coeff n, _⟩
    ext i
    by_cases' hi : i = n
    · simp [← hi, ← coeff_monomial]
      
    · have : f.coeff i = 0 := by
        rw [← not_mem_support_iff]
        exact fun hi' => hi (Finset.mem_singleton.1 (hn hi'))
      simp [← this, ← Ne.symm hi, ← coeff_monomial]
      
    
  · rintro ⟨n, a, rfl⟩
    rw [← Finset.card_singleton n]
    apply Finset.card_le_of_subset
    exact support_monomial' _ _
    

theorem ring_hom_ext {S} [Semiringₓ S] {f g : R[X] →+* S} (h₁ : ∀ a, f (c a) = g (c a)) (h₂ : f x = g x) : f = g := by
  set f' := f.comp (to_finsupp_iso R).symm.toRingHom with hf'
  set g' := g.comp (to_finsupp_iso R).symm.toRingHom with hg'
  have A : f' = g' := by
    ext
    · simp [← h₁, ← RingEquiv.to_ring_hom_eq_coe]
      
    · simpa [← RingEquiv.to_ring_hom_eq_coe] using h₂
      
  have B : f = f'.comp (to_finsupp_iso R) := by
    rw [hf', RingHom.comp_assoc]
    ext x
    simp only [← RingEquiv.to_ring_hom_eq_coe, ← RingEquiv.symm_apply_apply, ← Function.comp_app, ← RingHom.coe_comp, ←
      RingEquiv.coe_to_ring_hom]
  have C : g = g'.comp (to_finsupp_iso R) := by
    rw [hg', RingHom.comp_assoc]
    ext x
    simp only [← RingEquiv.to_ring_hom_eq_coe, ← RingEquiv.symm_apply_apply, ← Function.comp_app, ← RingHom.coe_comp, ←
      RingEquiv.coe_to_ring_hom]
  rw [B, C, A]

@[ext]
theorem ring_hom_ext' {S} [Semiringₓ S] {f g : R[X] →+* S} (h₁ : f.comp c = g.comp c) (h₂ : f x = g x) : f = g :=
  ring_hom_ext (RingHom.congr_fun h₁) h₂

end Polynomial

