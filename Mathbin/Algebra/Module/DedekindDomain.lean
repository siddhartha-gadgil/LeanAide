/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
import Mathbin.Algebra.Module.Torsion
import Mathbin.RingTheory.DedekindDomain.Ideal

/-!
# Modules over a Dedekind domain

Over a Dedekind domain, a `I`-torsion module is the internal direct sum of its `p i ^ e i`-torsion
submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals.
Therefore, as any finitely generated torsion module is `I`-torsion for some `I`, it is an internal
direct sum of its `p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.
-/


universe u v

open BigOperators

variable {R : Type u} [CommRingₓ R] [IsDomain R] {M : Type v} [AddCommGroupₓ M] [Module R M]

open DirectSum

namespace Submodule

variable [IsDedekindDomain R]

open UniqueFactorizationMonoid

/-- Over a Dedekind domain, a `I`-torsion module is the internal direct sum of its `p i ^ e i`-
torsion submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals.-/
theorem is_internal_prime_power_torsion_of_is_torsion_by_ideal {I : Ideal R} (hI : I ≠ ⊥)
    (hM : Module.IsTorsionBySet R M I) :
    ∃ (P : Finset <| Ideal R)(_ : DecidableEq P)(_ : ∀, ∀ p ∈ P, ∀, Prime p)(e : P → ℕ),
      DirectSum.IsInternal fun p : P => torsion_by_set R M (p ^ e p : Ideal R) :=
  by
  classical
  let P := factors I
  have prime_of_mem := fun p (hp : p ∈ P.to_finset) => prime_of_factor p (multiset.mem_to_finset.mp hp)
  refine' ⟨P.to_finset, inferInstance, prime_of_mem, fun i => P.count i, _⟩
  apply @torsion_by_set_is_internal _ _ _ _ _ _ _ _ (fun p => p ^ P.count p) _
  · convert hM
    rw [← Finset.inf_eq_infi, IsDedekindDomain.inf_prime_pow_eq_prod, ← Finset.prod_multiset_count, ← associated_iff_eq]
    · exact factors_prod hI
      
    · exact prime_of_mem
      
    · exact fun _ _ _ _ ij => ij
      
    
  · intro p hp q hq pq
    dsimp'
    rw [irreducible_pow_sup]
    · suffices (normalized_factors _).count p = 0 by
        rw [this, zero_min, pow_zeroₓ, Ideal.one_eq_top]
      · rw [Multiset.count_eq_zero, normalized_factors_of_irreducible_pow (prime_of_mem q hq).Irreducible,
          Multiset.mem_repeat]
        exact fun H => pq <| H.2.trans <| normalize_eq q
        
      
    · rw [← Ideal.zero_eq_bot]
      apply pow_ne_zero
      exact (prime_of_mem q hq).ne_zero
      
    · exact (prime_of_mem p hp).Irreducible
      
    

/-- A finitely generated torsion module over a Dedekind domain is an internal direct sum of its
`p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.-/
theorem is_internal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (P : Finset <| Ideal R)(_ : DecidableEq P)(_ : ∀, ∀ p ∈ P, ∀, Prime p)(e : P → ℕ),
      DirectSum.IsInternal fun p : P => torsion_by_set R M (p ^ e p : Ideal R) :=
  by
  obtain ⟨I, hI, hM'⟩ := is_torsion_by_ideal_of_finite_of_is_torsion hM
  refine' is_internal_prime_power_torsion_of_is_torsion_by_ideal _ hM'
  rw [Set.ne_empty_iff_nonempty] at hI
  rw [Submodule.ne_bot_iff]
  obtain ⟨x, H, hx⟩ := hI
  exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩

end Submodule

