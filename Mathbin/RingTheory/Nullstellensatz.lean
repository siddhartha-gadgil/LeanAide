/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import Mathbin.RingTheory.Jacobson
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.FieldTheory.MvPolynomial
import Mathbin.AlgebraicGeometry.PrimeSpectrum.Basic

/-!
# Nullstellensatz
This file establishes a version of Hilbert's classical Nullstellensatz for `mv_polynomial`s.
The main statement of the theorem is `vanishing_ideal_zero_locus_eq_radical`.

The statement is in terms of new definitions `vanishing_ideal` and `zero_locus`.
Mathlib already has versions of these in terms of the prime spectrum of a ring,
  but those are not well-suited for expressing this result.
Suggestions for better ways to state this theorem or organize things are welcome.

The machinery around `vanishing_ideal` and `zero_locus` is also minimal, I only added lemmas
  directly needed in this proof, since I'm not sure if they are the right approach.
-/


open Ideal

noncomputable section

namespace MvPolynomial

open MvPolynomial

variable {k : Type _} [Field k]

variable {σ : Type _}

/-- Set of points that are zeroes of all polynomials in an ideal -/
def ZeroLocus (I : Ideal (MvPolynomial σ k)) : Set (σ → k) :=
  { x : σ → k | ∀, ∀ p ∈ I, ∀, eval x p = 0 }

@[simp]
theorem mem_zero_locus_iff {I : Ideal (MvPolynomial σ k)} {x : σ → k} : x ∈ ZeroLocus I ↔ ∀, ∀ p ∈ I, ∀, eval x p = 0 :=
  Iff.rfl

theorem zero_locus_anti_mono {I J : Ideal (MvPolynomial σ k)} (h : I ≤ J) : ZeroLocus J ≤ ZeroLocus I :=
  fun x hx p hp => hx p <| h hp

theorem zero_locus_bot : ZeroLocus (⊥ : Ideal (MvPolynomial σ k)) = ⊤ :=
  eq_top_iff.2 fun x hx p hp => trans (congr_arg (eval x) (mem_bot.1 hp)) (eval x).map_zero

theorem zero_locus_top : ZeroLocus (⊤ : Ideal (MvPolynomial σ k)) = ⊥ :=
  eq_bot_iff.2 fun x hx => one_ne_zero ((eval x).map_one ▸ hx 1 Submodule.mem_top : (1 : k) = 0)

/-- Ideal of polynomials with common zeroes at all elements of a set -/
def vanishingIdeal (V : Set (σ → k)) : Ideal (MvPolynomial σ k) where
  Carrier := { p | ∀, ∀ x ∈ V, ∀, eval x p = 0 }
  zero_mem' := fun x hx => RingHom.map_zero _
  add_mem' := fun p q hp hq x hx => by
    simp only [← hq x hx, ← hp x hx, ← add_zeroₓ, ← RingHom.map_add]
  smul_mem' := fun p q hq x hx => by
    simp only [← hq x hx, ← Algebra.id.smul_eq_mul, ← mul_zero, ← RingHom.map_mul]

@[simp]
theorem mem_vanishing_ideal_iff {V : Set (σ → k)} {p : MvPolynomial σ k} :
    p ∈ vanishingIdeal V ↔ ∀, ∀ x ∈ V, ∀, eval x p = 0 :=
  Iff.rfl

theorem vanishing_ideal_anti_mono {A B : Set (σ → k)} (h : A ≤ B) : vanishingIdeal B ≤ vanishingIdeal A :=
  fun p hp x hx => hp x <| h hx

theorem vanishing_ideal_empty : vanishingIdeal (∅ : Set (σ → k)) = ⊤ :=
  le_antisymmₓ le_top fun p hp x hx => absurd hx (Set.not_mem_empty x)

theorem le_vanishing_ideal_zero_locus (I : Ideal (MvPolynomial σ k)) : I ≤ vanishingIdeal (ZeroLocus I) :=
  fun p hp x hx => hx p hp

theorem zero_locus_vanishing_ideal_le (V : Set (σ → k)) : V ≤ ZeroLocus (vanishingIdeal V) := fun V hV p hp => hp V hV

theorem zero_locus_vanishing_ideal_galois_connection :
    @GaloisConnection (Ideal (MvPolynomial σ k)) (Set (σ → k))ᵒᵈ _ _ ZeroLocus vanishingIdeal := fun I V =>
  ⟨fun h => le_transₓ (le_vanishing_ideal_zero_locus I) (vanishing_ideal_anti_mono h), fun h =>
    le_transₓ (zero_locus_anti_mono h) (zero_locus_vanishing_ideal_le V)⟩

theorem mem_vanishing_ideal_singleton_iff (x : σ → k) (p : MvPolynomial σ k) :
    p ∈ (vanishingIdeal {x} : Ideal (MvPolynomial σ k)) ↔ eval x p = 0 :=
  ⟨fun h => h x rfl, fun hpx y hy => hy.symm ▸ hpx⟩

instance vanishing_ideal_singleton_is_maximal {x : σ → k} : (vanishingIdeal {x} : Ideal (MvPolynomial σ k)).IsMaximal :=
  by
  have : MvPolynomial σ k ⧸ vanishing_ideal {x} ≃+* k :=
    RingEquiv.ofBijective (Ideal.Quotient.lift _ (eval x) fun p h => (mem_vanishing_ideal_singleton_iff x p).mp h)
      (by
        refine'
          ⟨(injective_iff_map_eq_zero _).mpr fun p hp => _, fun z =>
            ⟨(Ideal.Quotient.mk (vanishing_ideal {x} : Ideal (MvPolynomial σ k))) (C z), by
              simp ⟩⟩
        obtain ⟨q, rfl⟩ := quotient.mk_surjective p
        rwa [Ideal.Quotient.lift_mk, ← mem_vanishing_ideal_singleton_iff, ← quotient.eq_zero_iff_mem] at hp)
  rw [← bot_quotient_is_maximal_iff, ring_equiv.bot_maximal_iff this]
  exact bot_is_maximal

theorem radical_le_vanishing_ideal_zero_locus (I : Ideal (MvPolynomial σ k)) :
    I.radical ≤ vanishingIdeal (ZeroLocus I) := by
  intro p hp x hx
  rw [← mem_vanishing_ideal_singleton_iff]
  rw [radical_eq_Inf] at hp
  refine'
    (mem_Inf.mp hp)
      ⟨le_transₓ (le_vanishing_ideal_zero_locus I) (vanishing_ideal_anti_mono fun y hy => hy.symm ▸ hx),
        is_maximal.is_prime' _⟩

/-- The point in the prime spectrum assosiated to a given point -/
def pointToPoint (x : σ → k) : PrimeSpectrum (MvPolynomial σ k) :=
  ⟨(vanishingIdeal {x} : Ideal (MvPolynomial σ k)), by
    infer_instance⟩

@[simp]
theorem vanishing_ideal_point_to_point (V : Set (σ → k)) :
    PrimeSpectrum.vanishingIdeal (point_to_point '' V) = MvPolynomial.vanishingIdeal V :=
  le_antisymmₓ
    (fun p hp x hx =>
      (((PrimeSpectrum.mem_vanishing_ideal _ _).1 hp)
          ⟨vanishingIdeal {x}, by
            infer_instance⟩
          ⟨x, ⟨hx, rfl⟩⟩)
        x rfl)
    fun p hp =>
    (PrimeSpectrum.mem_vanishing_ideal _ _).2 fun I hI =>
      let ⟨x, hx⟩ := hI
      hx.2 ▸ fun x' hx' => (Set.mem_singleton_iff.1 hx').symm ▸ hp x hx.1

theorem point_to_point_zero_locus_le (I : Ideal (MvPolynomial σ k)) :
    point_to_point '' MvPolynomial.ZeroLocus I ≤ PrimeSpectrum.ZeroLocus ↑I := fun J hJ =>
  let ⟨x, hx⟩ := hJ
  (le_transₓ (le_vanishing_ideal_zero_locus I) (hx.2 ▸ vanishing_ideal_anti_mono (Set.singleton_subset_iff.2 hx.1)) :
    I ≤ J.asIdeal)

variable [IsAlgClosed k] [Fintype σ]

theorem is_maximal_iff_eq_vanishing_ideal_singleton (I : Ideal (MvPolynomial σ k)) :
    I.IsMaximal ↔ ∃ x : σ → k, I = vanishingIdeal {x} := by
  refine'
    ⟨fun hI => _, fun h =>
      let ⟨x, hx⟩ := h
      hx.symm ▸ MvPolynomial.vanishing_ideal_singleton_is_maximal⟩
  let this : I.is_maximal := hI
  let this : Field (MvPolynomial σ k ⧸ I) := quotient.field I
  let ϕ : k →+* MvPolynomial σ k ⧸ I := (Ideal.Quotient.mk I).comp C
  have hϕ : Function.Bijective ϕ :=
    ⟨quotient_mk_comp_C_injective _ _ I hI.ne_top,
      IsAlgClosed.algebra_map_surjective_of_is_integral' ϕ
        (mv_polynomial.comp_C_integral_of_surjective_of_jacobson _ quotient.mk_surjective)⟩
  obtain ⟨φ, hφ⟩ := Function.Surjective.has_right_inverse hϕ.2
  let x : σ → k := fun s => φ ((Ideal.Quotient.mk I) (X s))
  have hx : ∀ s : σ, ϕ (x s) = (Ideal.Quotient.mk I) (X s) := fun s => hφ ((Ideal.Quotient.mk I) (X s))
  refine'
    ⟨x,
      (is_maximal.eq_of_le
          (by
            infer_instance)
          hI.ne_top _).symm⟩
  intro p hp
  rw [← quotient.eq_zero_iff_mem, map_mv_polynomial_eq_eval₂ (Ideal.Quotient.mk I) p, eval₂_eq']
  rw [mem_vanishing_ideal_singleton_iff, eval_eq'] at hp
  simpa only [← ϕ.map_sum, ← ϕ.map_mul, ← ϕ.map_prod, ← ϕ.map_pow, ← ϕ.map_zero, ← hx] using congr_arg ϕ hp

/-- Main statement of the Nullstellensatz -/
@[simp]
theorem vanishing_ideal_zero_locus_eq_radical (I : Ideal (MvPolynomial σ k)) :
    vanishingIdeal (ZeroLocus I) = I.radical := by
  rw [I.radical_eq_jacobson]
  refine' le_antisymmₓ (le_Inf _) fun p hp x hx => _
  · rintro J ⟨hJI, hJ⟩
    obtain ⟨x, hx⟩ := (is_maximal_iff_eq_vanishing_ideal_singleton J).1 hJ
    refine' hx.symm ▸ vanishing_ideal_anti_mono fun y hy p hp => _
    rw [← mem_vanishing_ideal_singleton_iff, Set.mem_singleton_iff.1 hy, ← hx]
    refine' hJI hp
    
  · rw [← mem_vanishing_ideal_singleton_iff x p]
    refine'
      (mem_Inf.mp hp)
        ⟨le_transₓ (le_vanishing_ideal_zero_locus I) (vanishing_ideal_anti_mono fun y hy => hy.symm ▸ hx),
          MvPolynomial.vanishing_ideal_singleton_is_maximal⟩
    

@[simp]
theorem IsPrime.vanishing_ideal_zero_locus (P : Ideal (MvPolynomial σ k)) [h : P.IsPrime] :
    vanishingIdeal (ZeroLocus P) = P :=
  trans (vanishing_ideal_zero_locus_eq_radical P) h.radical

end MvPolynomial

