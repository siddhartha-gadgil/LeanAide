/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Data.Polynomial.AlgebraMap
import Mathbin.Data.Polynomial.Inductions

/-!
# Polynomials and limits

In this file we prove the following lemmas.

* `polynomial.continuous_eval₂: `polynomial.eval₂` defines a continuous function.
* `polynomial.continuous_aeval: `polynomial.aeval` defines a continuous function;
  we also prove convenience lemmas `polynomial.continuous_at_aeval`,
  `polynomial.continuous_within_at_aeval`, `polynomial.continuous_on_aeval`.
* `polynomial.continuous`:  `polynomial.eval` defines a continuous functions;
  we also prove convenience lemmas `polynomial.continuous_at`, `polynomial.continuous_within_at`,
  `polynomial.continuous_on`.
* `polynomial.tendsto_norm_at_top`: `λ x, ∥polynomial.eval (z x) p∥` tends to infinity provided that
  `λ x, ∥z x∥` tends to infinity and `0 < degree p`;
* `polynomial.tendsto_abv_eval₂_at_top`, `polynomial.tendsto_abv_at_top`,
  `polynomial.tendsto_abv_aeval_at_top`: a few versions of the previous statement for
  `is_absolute_value abv` instead of norm.

## Tags

polynomial, continuity
-/


open IsAbsoluteValue Filter

namespace Polynomial

open Polynomial

section TopologicalSemiring

variable {R S : Type _} [Semiringₓ R] [TopologicalSpace R] [TopologicalSemiring R] (p : R[X])

@[continuity]
protected theorem continuous_eval₂ [Semiringₓ S] (p : S[X]) (f : S →+* R) : Continuous fun x => p.eval₂ f x := by
  dsimp' only [← eval₂_eq_sum, ← Finsupp.sum]
  exact continuous_finset_sum _ fun c hc => continuous_const.mul (continuous_pow _)

@[continuity]
protected theorem continuous : Continuous fun x => p.eval x :=
  p.continuous_eval₂ _

protected theorem continuous_at {a : R} : ContinuousAt (fun x => p.eval x) a :=
  p.Continuous.ContinuousAt

protected theorem continuous_within_at {s a} : ContinuousWithinAt (fun x => p.eval x) s a :=
  p.Continuous.ContinuousWithinAt

protected theorem continuous_on {s} : ContinuousOn (fun x => p.eval x) s :=
  p.Continuous.ContinuousOn

end TopologicalSemiring

section TopologicalAlgebra

variable {R A : Type _} [CommSemiringₓ R] [Semiringₓ A] [Algebra R A] [TopologicalSpace A] [TopologicalSemiring A]
  (p : R[X])

@[continuity]
protected theorem continuous_aeval : Continuous fun x : A => aeval x p :=
  p.continuous_eval₂ _

protected theorem continuous_at_aeval {a : A} : ContinuousAt (fun x : A => aeval x p) a :=
  p.continuous_aeval.ContinuousAt

protected theorem continuous_within_at_aeval {s a} : ContinuousWithinAt (fun x : A => aeval x p) s a :=
  p.continuous_aeval.ContinuousWithinAt

protected theorem continuous_on_aeval {s} : ContinuousOn (fun x : A => aeval x p) s :=
  p.continuous_aeval.ContinuousOn

end TopologicalAlgebra

theorem tendsto_abv_eval₂_at_top {R S k α : Type _} [Semiringₓ R] [Ringₓ S] [LinearOrderedField k] (f : R →+* S)
    (abv : S → k) [IsAbsoluteValue abv] (p : R[X]) (hd : 0 < degree p) (hf : f p.leadingCoeff ≠ 0) {l : Filter α}
    {z : α → S} (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fun x => abv (p.eval₂ f (z x))) l atTop := by
  revert hf
  refine' degree_pos_induction_on p hd _ _ _ <;> clear hd p
  · rintro c - hc
    rw [leading_coeff_mul_X, leading_coeff_C] at hc
    simpa [← abv_mul abv] using hz.const_mul_at_top ((abv_pos abv).2 hc)
    
  · intro p hpd ihp hf
    rw [leading_coeff_mul_X] at hf
    simpa [← abv_mul abv] using (ihp hf).at_top_mul_at_top hz
    
  · intro p a hd ihp hf
    rw [add_commₓ, leading_coeff_add_of_degree_lt (degree_C_le.trans_lt hd)] at hf
    refine' tendsto_at_top_of_add_const_right (abv (-f a)) _
    refine' tendsto_at_top_mono (fun _ => abv_add abv _ _) _
    simpa using ihp hf
    

theorem tendsto_abv_at_top {R k α : Type _} [Ringₓ R] [LinearOrderedField k] (abv : R → k) [IsAbsoluteValue abv]
    (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α → R} (hz : Tendsto (abv ∘ z) l atTop) :
    Tendsto (fun x => abv (p.eval (z x))) l atTop :=
  tendsto_abv_eval₂_at_top _ _ _ h (mt leading_coeff_eq_zero.1 <| ne_zero_of_degree_gt h) hz

theorem tendsto_abv_aeval_at_top {R A k α : Type _} [CommSemiringₓ R] [Ringₓ A] [Algebra R A] [LinearOrderedField k]
    (abv : A → k) [IsAbsoluteValue abv] (p : R[X]) (hd : 0 < degree p) (h₀ : algebraMap R A p.leadingCoeff ≠ 0)
    {l : Filter α} {z : α → A} (hz : Tendsto (abv ∘ z) l atTop) : Tendsto (fun x => abv (aeval (z x) p)) l atTop :=
  tendsto_abv_eval₂_at_top _ abv p hd h₀ hz

variable {α R : Type _} [NormedRing R] [IsAbsoluteValue (norm : R → ℝ)]

theorem tendsto_norm_at_top (p : R[X]) (h : 0 < degree p) {l : Filter α} {z : α → R}
    (hz : Tendsto (fun x => ∥z x∥) l atTop) : Tendsto (fun x => ∥p.eval (z x)∥) l atTop :=
  p.tendsto_abv_at_top norm h hz

theorem exists_forall_norm_le [ProperSpace R] (p : R[X]) : ∃ x, ∀ y, ∥p.eval x∥ ≤ ∥p.eval y∥ :=
  if hp0 : 0 < degree p then
    p.Continuous.norm.exists_forall_le <| p.tendsto_norm_at_top hp0 tendsto_norm_cocompact_at_top
  else
    ⟨p.coeff 0, by
      rw [eq_C_of_degree_le_zero (le_of_not_gtₓ hp0)] <;> simp ⟩

end Polynomial

