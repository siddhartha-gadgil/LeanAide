/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
import Mathbin.Data.W.Cardinal
import Mathbin.RingTheory.AlgebraicIndependent
import Mathbin.FieldTheory.IsAlgClosed.Basic
import Mathbin.FieldTheory.IntermediateField
import Mathbin.Data.Polynomial.Cardinal
import Mathbin.Data.MvPolynomial.Cardinal
import Mathbin.Data.Zmod.Algebra

/-!
# Classification of Algebraically closed fields

This file contains results related to classifying algebraically closed fields.

## Main statements

* `is_alg_closed.equiv_of_transcendence_basis` Two fields with the same characteristic and the same
  cardinality of transcendence basis are isomorphic.
* `is_alg_closed.ring_equiv_of_cardinal_eq_of_char_eq` Two uncountable algebraically closed fields
  are isomorphic if they have the same characteristic and the same cardinality.
-/


universe u

open Cardinal Polynomial

open Cardinal

section AlgebraicClosure

namespace Algebra.IsAlgebraic

variable (R L : Type u) [CommRingₓ R] [CommRingₓ L] [IsDomain L] [Algebra R L]

variable [NoZeroSmulDivisors R L] (halg : Algebra.IsAlgebraic R L)

theorem cardinal_mk_le_sigma_polynomial : # L ≤ # (Σp : R[X], { x : L // x ∈ (p.map (algebraMap R L)).roots }) :=
  @mk_le_of_injective L (Σp : R[X], { x : L | x ∈ (p.map (algebraMap R L)).roots })
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (halg x)
      ⟨p.1, x, by
        dsimp'
        have h : p.1.map (algebraMap R L) ≠ 0 := by
          rw [Ne.def, ← Polynomial.degree_eq_bot,
            Polynomial.degree_map_eq_of_injective (NoZeroSmulDivisors.algebra_map_injective R L),
            Polynomial.degree_eq_bot]
          exact p.2.1
        erw [Polynomial.mem_roots h, Polynomial.IsRoot, Polynomial.eval_map, ← Polynomial.aeval_def, p.2.2]⟩)
    fun x y => by
    intro h
    simp only at h
    refine' (Subtype.heq_iff_coe_eq _).1 h.2
    simp only [← h.1, ← iff_selfₓ, ← forall_true_iff]

/-- The cardinality of an algebraic extension is at most the maximum of the cardinality
of the base ring or `ℵ₀` -/
theorem cardinal_mk_le_max : # L ≤ max (# R) ℵ₀ :=
  calc
    # L ≤ # (Σp : R[X], { x : L // x ∈ (p.map (algebraMap R L)).roots }) := cardinal_mk_le_sigma_polynomial R L halg
    _ = Cardinal.sum fun p : R[X] => # { x : L | x ∈ (p.map (algebraMap R L)).roots } := by
      rw [← mk_sigma] <;> rfl
    _ ≤ Cardinal.sum.{u, u} fun p : R[X] => ℵ₀ := (sum_le_sum _ _) fun p => (Multiset.finite_to_set _).lt_aleph_0.le
    _ = # R[X] * ℵ₀ := sum_const' _ _
    _ ≤ max (max (# R[X]) ℵ₀) ℵ₀ := mul_le_max _ _
    _ ≤ max (max (max (# R) ℵ₀) ℵ₀) ℵ₀ := max_le_max (max_le_max Polynomial.cardinal_mk_le_max le_rfl) le_rfl
    _ = max (# R) ℵ₀ := by
      simp only [← max_assocₓ, ← max_commₓ ℵ₀, ← max_left_commₓ ℵ₀, ← max_selfₓ]
    

end Algebra.IsAlgebraic

end AlgebraicClosure

namespace IsAlgClosed

section Classification

noncomputable section

variable {R L K : Type _} [CommRingₓ R]

variable [Field K] [Algebra R K]

variable [Field L] [Algebra R L]

variable {ι : Type _} (v : ι → K)

variable {κ : Type _} (w : κ → L)

variable (hv : AlgebraicIndependent R v)

theorem is_alg_closure_of_transcendence_basis [IsAlgClosed K] (hv : IsTranscendenceBasis R v) :
    IsAlgClosure (Algebra.adjoin R (Set.Range v)) K := by
  let this := RingHom.domain_nontrivial (algebraMap R K) <;>
    exact
      { alg_closed := by
          infer_instance,
        algebraic := hv.is_algebraic }

variable (hw : AlgebraicIndependent R w)

/-- setting `R` to be `zmod (ring_char R)` this result shows that if two algebraically
closed fields have equipotent transcendence bases and the same characteristic then they are
isomorphic. -/
def equivOfTranscendenceBasis [IsAlgClosed K] [IsAlgClosed L] (e : ι ≃ κ) (hv : IsTranscendenceBasis R v)
    (hw : IsTranscendenceBasis R w) : K ≃+* L := by
  let this := is_alg_closure_of_transcendence_basis v hv <;>
    let this := is_alg_closure_of_transcendence_basis w hw <;>
      have e : Algebra.adjoin R (Set.Range v) ≃+* Algebra.adjoin R (Set.Range w)
  · refine' hv.1.aevalEquiv.symm.toRingEquiv.trans _
    refine' (AlgEquiv.ofAlgHom (MvPolynomial.rename e) (MvPolynomial.rename e.symm) _ _).toRingEquiv.trans _
    · ext
      simp
      
    · ext
      simp
      
    exact hw.1.aevalEquiv.toRingEquiv
    
  exact IsAlgClosure.equivOfEquiv K L e

end Classification

section Cardinal

variable {R L K : Type u} [CommRingₓ R]

variable [Field K] [Algebra R K] [IsAlgClosed K]

variable {ι : Type u} (v : ι → K)

variable (hv : IsTranscendenceBasis R v)

theorem cardinal_le_max_transcendence_basis (hv : IsTranscendenceBasis R v) : # K ≤ max (max (# R) (# ι)) ℵ₀ :=
  calc
    # K ≤ max (# (Algebra.adjoin R (Set.Range v))) ℵ₀ := by
      let this := is_alg_closure_of_transcendence_basis v hv <;>
        exact Algebra.IsAlgebraic.cardinal_mk_le_max _ _ IsAlgClosure.algebraic
    _ = max (# (MvPolynomial ι R)) ℵ₀ := by
      rw [Cardinal.eq.2 ⟨hv.1.aevalEquiv.toEquiv⟩]
    _ ≤ max (max (max (# R) (# ι)) ℵ₀) ℵ₀ := max_le_max MvPolynomial.cardinal_mk_le_max le_rfl
    _ = _ := by
      simp [← max_assocₓ]
    

/-- If `K` is an uncountable algebraically closed field, then its
cardinality is the same as that of a transcendence basis. -/
theorem cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt [Nontrivial R] (hv : IsTranscendenceBasis R v)
    (hR : # R ≤ ℵ₀) (hK : ℵ₀ < # K) : # K = # ι :=
  have : ℵ₀ ≤ # ι :=
    le_of_not_ltₓ fun h =>
      not_le_of_gtₓ hK <|
        calc
          # K ≤ max (max (# R) (# ι)) ℵ₀ := cardinal_le_max_transcendence_basis v hv
          _ ≤ _ := max_leₓ (max_leₓ hR (le_of_ltₓ h)) le_rfl
          
  le_antisymmₓ
    (calc
      # K ≤ max (max (# R) (# ι)) ℵ₀ := cardinal_le_max_transcendence_basis v hv
      _ = # ι := by
        rw [max_eq_leftₓ, max_eq_rightₓ]
        · exact le_transₓ hR this
          
        · exact le_max_of_le_right this
          
      )
    (mk_le_of_injective (show Function.Injective v from hv.1.Injective))

end Cardinal

variable {K L : Type} [Field K] [Field L] [IsAlgClosed K] [IsAlgClosed L]

/-- Two uncountable algebraically closed fields of characteristic zero are isomorphic
if they have the same cardinality. -/
@[nolint def_lemma]
theorem ringEquivOfCardinalEqOfCharZero [CharZero K] [CharZero L] (hK : ℵ₀ < # K) (hKL : # K = # L) : K ≃+* L := by
  apply Classical.choice
  cases' exists_is_transcendence_basis ℤ (show Function.Injective (algebraMap ℤ K) from Int.cast_injective) with s hs
  cases' exists_is_transcendence_basis ℤ (show Function.Injective (algebraMap ℤ L) from Int.cast_injective) with t ht
  have : # s = # t := by
    rw [← cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt _ hs (le_of_eqₓ mk_int) hK, ←
      cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt _ ht (le_of_eqₓ mk_int), hKL]
    rwa [← hKL]
  cases' Cardinal.eq.1 this with e
  exact ⟨equiv_of_transcendence_basis _ _ e hs ht⟩

private theorem ring_equiv_of_cardinal_eq_of_char_p (p : ℕ) [Fact p.Prime] [CharP K p] [CharP L p] (hK : ℵ₀ < # K)
    (hKL : # K = # L) : K ≃+* L := by
  apply Classical.choice
  cases'
    exists_is_transcendence_basis (Zmod p)
      (show Function.Injective (algebraMap (Zmod p) K) from RingHom.injective _) with
    s hs
  cases'
    exists_is_transcendence_basis (Zmod p)
      (show Function.Injective (algebraMap (Zmod p) L) from RingHom.injective _) with
    t ht
  have : # s = # t := by
    rw [← cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt _ hs (lt_aleph_0_of_finite (Zmod p)).le hK, ←
      cardinal_eq_cardinal_transcendence_basis_of_aleph_0_lt _ ht (lt_aleph_0_of_finite (Zmod p)).le, hKL]
    rwa [← hKL]
  cases' Cardinal.eq.1 this with e
  exact ⟨equiv_of_transcendence_basis _ _ e hs ht⟩

/-- Two uncountable algebraically closed fields are isomorphic
if they have the same cardinality and the same characteristic. -/
@[nolint def_lemma]
theorem ringEquivOfCardinalEqOfCharEq (p : ℕ) [CharP K p] [CharP L p] (hK : ℵ₀ < # K) (hKL : # K = # L) : K ≃+* L := by
  apply Classical.choice
  rcases CharP.char_is_prime_or_zero K p with (hp | hp)
  · have : Fact p.prime := ⟨hp⟩
    exact ⟨ring_equiv_of_cardinal_eq_of_char_p p hK hKL⟩
    
  · rw [hp] at *
    skip
    let this : CharZero K := CharP.char_p_to_char_zero K
    let this : CharZero L := CharP.char_p_to_char_zero L
    exact ⟨ring_equiv_of_cardinal_eq_of_char_zero hK hKL⟩
    

end IsAlgClosed

