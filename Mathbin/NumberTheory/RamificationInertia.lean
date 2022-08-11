/-
Copyright (c) 2022 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathbin.Algebra.IsPrimePow
import Mathbin.FieldTheory.Separable
import Mathbin.LinearAlgebra.FreeModule.Finite.Rank
import Mathbin.LinearAlgebra.FreeModule.Pid
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.RingTheory.DedekindDomain.Ideal
import Mathbin.RingTheory.Localization.Module

/-!
# Ramification index and inertia degree

Given `P : ideal S` lying over `p : ideal R` for the ring extension `f : R →+* S`
(assuming `P` and `p` are prime or maximal where needed),
the **ramification index** `ideal.ramification_idx f p P` is the multiplicity of `P` in `map f p`,
and the **inertia degree** `ideal.inertia_deg f p P` is the degree of the field extension
`(S / P) : (R / p)`.

## TODO (#12287)

The main theorem `ideal.sum_ramification_inertia` states that for all coprime `P` lying over `p`,
`Σ P, ramification_idx f p P * inertia_deg f p P` equals the degree of the field extension
`Frac(S) : Frac(R)`.

## Implementation notes

Often the above theory is set up in the case where:
 * `R` is the ring of integers of a number field `K`,
 * `L` is a finite separable extension of `K`,
 * `S` is the integral closure of `R` in `L`,
 * `p` and `P` are maximal ideals,
 * `P` is an ideal lying over `p`
We will try to relax the above hypotheses as much as possible.

-/


namespace Ideal

universe u v

variable {R : Type u} [CommRingₓ R]

variable {S : Type v} [CommRingₓ S] (f : R →+* S)

variable (p : Ideal R) (P : Ideal S)

open FiniteDimensional

open UniqueFactorizationMonoid

section DecEq

open Classical

/-- The ramification index of `P` over `p` is the largest exponent `n` such that
`p` is contained in `P^n`.

In particular, if `p` is not contained in `P^n`, then the ramification index is 0.

If there is no largest such `n` (e.g. because `p = ⊥`), then `ramification_idx` is
defined to be 0.
-/
noncomputable def ramificationIdx : ℕ :=
  sup { n | map f p ≤ P ^ n }

variable {f p P}

theorem ramification_idx_eq_find (h : ∃ n, ∀ k, map f p ≤ P ^ k → k ≤ n) : ramificationIdx f p P = Nat.findₓ h :=
  Nat.Sup_def h

theorem ramification_idx_eq_zero (h : ∀ n : ℕ, ∃ k, map f p ≤ P ^ k ∧ n < k) : ramificationIdx f p P = 0 :=
  dif_neg
    (by
      push_neg <;> exact h)

theorem ramification_idx_spec {n : ℕ} (hle : map f p ≤ P ^ n) (hgt : ¬map f p ≤ P ^ (n + 1)) :
    ramificationIdx f p P = n := by
  have : ∀ k : ℕ, map f p ≤ P ^ k → k ≤ n := by
    intro k hk
    refine' le_of_not_ltₓ fun hnk => _
    exact hgt (hk.trans (Ideal.pow_le_pow hnk))
  rw [ramification_idx_eq_find ⟨n, this⟩]
  · refine' le_antisymmₓ (Nat.find_min'ₓ _ this) (le_of_not_gtₓ fun h : Nat.findₓ _ < n => _)
    obtain this' := Nat.find_specₓ ⟨n, this⟩
    exact h.not_le (this' _ hle)
    

theorem ramification_idx_lt {n : ℕ} (hgt : ¬map f p ≤ P ^ n) : ramificationIdx f p P < n := by
  cases n
  · simpa using hgt
    
  rw [Nat.lt_succ_iffₓ]
  have : ∀ k, map f p ≤ P ^ k → k ≤ n := by
    refine' fun k hk => le_of_not_ltₓ fun hnk => _
    exact hgt (hk.trans (Ideal.pow_le_pow hnk))
  rw [ramification_idx_eq_find ⟨n, this⟩]
  exact Nat.find_min'ₓ ⟨n, this⟩ this

@[simp]
theorem ramification_idx_bot : ramificationIdx f ⊥ P = 0 :=
  dif_neg <|
    not_exists.mpr fun n hn =>
      n.lt_succ_self.not_le
        (hn _
          (by
            simp ))

@[simp]
theorem ramification_idx_of_not_le (h : ¬map f p ≤ P) : ramificationIdx f p P = 0 :=
  ramification_idx_spec
    (by
      simp )
    (by
      simpa using h)

theorem ramification_idx_ne_zero {e : ℕ} (he : e ≠ 0) (hle : map f p ≤ P ^ e) (hnle : ¬map f p ≤ P ^ (e + 1)) :
    ramificationIdx f p P ≠ 0 := by
  rwa [ramification_idx_spec hle hnle]

theorem le_pow_of_le_ramification_idx {n : ℕ} (hn : n ≤ ramificationIdx f p P) : map f p ≤ P ^ n := by
  contrapose! hn
  exact ramification_idx_lt hn

theorem le_pow_ramification_idx : map f p ≤ P ^ ramificationIdx f p P :=
  le_pow_of_le_ramification_idx (le_reflₓ _)

namespace IsDedekindDomain

variable [IsDomain S] [IsDedekindDomain S]

theorem ramification_idx_eq_normalized_factors_count (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx f p P = (normalizedFactors (map f p)).count P := by
  have hPirr := (Ideal.prime_of_is_prime hP0 hP).Irreducible
  refine' ramification_idx_spec (Ideal.le_of_dvd _) (mt ideal.dvd_iff_le.mpr _) <;>
    rw [dvd_iff_normalized_factors_le_normalized_factors (pow_ne_zero _ hP0) hp0, normalized_factors_pow,
      normalized_factors_irreducible hPirr, normalize_eq, Multiset.nsmul_singleton, ← Multiset.le_count_iff_repeat_le]
  · exact (Nat.lt_succ_selfₓ _).not_le
    

theorem ramification_idx_eq_factors_count (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ramificationIdx f p P = (factors (map f p)).count P := by
  rw [is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0, factors_eq_normalized_factors]

theorem ramification_idx_ne_zero (hp0 : map f p ≠ ⊥) (hP : P.IsPrime) (le : map f p ≤ P) : ramificationIdx f p P ≠ 0 :=
  by
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    have := le_bot_iff.mp le
    contradiction
  have hPirr := (Ideal.prime_of_is_prime hP0 hP).Irreducible
  rw [is_dedekind_domain.ramification_idx_eq_normalized_factors_count hp0 hP hP0]
  obtain ⟨P', hP', P'_eq⟩ := exists_mem_normalized_factors_of_dvd hp0 hPirr (ideal.dvd_iff_le.mpr le)
  rwa [Multiset.count_ne_zero, associated_iff_eq.mp P'_eq]

end IsDedekindDomain

variable (f p P)

attribute [local instance] Ideal.Quotient.field

/-- The inertia degree of `P : ideal S` lying over `p : ideal R` is the degree of the
extension `(S / P) : (R / p)`.

We do not assume `P` lies over `p` in the definition; we return `0` instead.

See `inertia_deg_algebra_map` for the common case where `f = algebra_map R S`
and there is an algebra structure `R / p → S / P`.
-/
noncomputable def inertiaDeg [hp : p.IsMaximal] : ℕ :=
  if hPp : comap f P = p then
    @finrank (R ⧸ p) (S ⧸ P) _ _ <|
      @Algebra.toModule _ _ _ _ <|
        RingHom.toAlgebra <|
          (Ideal.Quotient.lift p (P f)) fun a ha => Quotient.eq_zero_iff_mem.mpr <| mem_comap.mp <| hPp.symm ▸ ha
  else 0

-- Useful for the `nontriviality` tactic using `comap_eq_of_scalar_tower_quotient`.
@[simp]
theorem inertia_deg_of_subsingleton [hp : p.IsMaximal] [hQ : Subsingleton (S ⧸ P)] : inertiaDeg f p P = 0 := by
  have := ideal.quotient.subsingleton_iff.mp hQ
  subst this
  exact dif_neg fun h => hp.ne_top <| h.symm.trans comap_top

@[simp]
theorem inertia_deg_algebra_map [Algebra R S] [Algebra (R ⧸ p) (S ⧸ P)] [IsScalarTower R (R ⧸ p) (S ⧸ P)]
    [hp : p.IsMaximal] : inertiaDeg (algebraMap R S) p P = finrank (R ⧸ p) (S ⧸ P) := by
  nontriviality S ⧸ P using ← inertia_deg_of_subsingleton, ← finrank_zero_of_subsingleton
  have := comap_eq_of_scalar_tower_quotient (algebraMap (R ⧸ p) (S ⧸ P)).Injective
  rw [inertia_deg, dif_pos this]
  congr
  refine' Algebra.algebra_ext _ _ fun x' => (Quotientₓ.induction_on' x') fun x => _
  change Ideal.Quotient.lift p _ _ (Ideal.Quotient.mk p x) = algebraMap _ _ (Ideal.Quotient.mk p x)
  rw [Ideal.Quotient.lift_mk, ← Ideal.Quotient.algebra_map_eq, ← IsScalarTower.algebra_map_eq, ←
    Ideal.Quotient.algebra_map_eq, ← IsScalarTower.algebra_map_apply]

end DecEq

end Ideal

