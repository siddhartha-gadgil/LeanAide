/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Alex J. Best, Johan Commelin, Eric Rodriguez, Ruben Van de Velde
-/
import Mathbin.Algebra.CharP.Algebra
import Mathbin.FieldTheory.Finite.Basic
import Mathbin.FieldTheory.Galois

/-!
# Galois fields

If `p` is a prime number, and `n` a natural number,
then `galois_field p n` is defined as the splitting field of `X^(p^n) - X` over `zmod p`.
It is a finite field with `p ^ n` elements.

## Main definition

* `galois_field p n` is a field with `p ^ n` elements

## Main Results

- `galois_field.alg_equiv_galois_field`: Any finite field is isomorphic to some Galois field
- `finite_field.alg_equiv_of_card_eq`: Uniqueness of finite fields : algebra isomorphism
- `finite_field.ring_equiv_of_card_eq`: Uniqueness of finite fields : ring isomorphism

-/


noncomputable section

open Polynomial

open Polynomial

theorem galois_poly_separable {K : Type _} [Field K] (p q : ℕ) [CharP K p] (h : p ∣ q) : Separable (X ^ q - X : K[X]) :=
  by
  use 1, X ^ q - X - 1
  rw [← CharP.cast_eq_zero_iff K[X] p] at h
  rw [derivative_sub, derivative_pow, derivative_X, h]
  ring

/-- A finite field with `p ^ n` elements.
Every field with the same cardinality is (non-canonically)
isomorphic to this field. -/
def GaloisField (p : ℕ) [Fact p.Prime] (n : ℕ) :=
  SplittingField (X ^ p ^ n - X : (Zmod p)[X])deriving Field

instance : Inhabited (@GaloisField 2 (Fact.mk Nat.prime_two) 1) :=
  ⟨37⟩

namespace GaloisField

variable (p : ℕ) [Fact p.Prime] (n : ℕ)

instance : Algebra (Zmod p) (GaloisField p n) :=
  SplittingField.algebra _

instance : IsSplittingField (Zmod p) (GaloisField p n) (X ^ p ^ n - X) :=
  Polynomial.IsSplittingField.splitting_field _

instance : CharP (GaloisField p n) p :=
  (Algebra.char_p_iff (Zmod p) (GaloisField p n) p).mp
    (by
      infer_instance)

instance : Fintype (GaloisField p n) := by
  dsimp' only [← GaloisField]
  exact FiniteDimensional.fintypeOfFintype (Zmod p) (GaloisField p n)

theorem finrank {n} (h : n ≠ 0) : FiniteDimensional.finrank (Zmod p) (GaloisField p n) = n := by
  set g_poly := (X ^ p ^ n - X : (Zmod p)[X])
  have hp : 1 < p := (Fact.out (Nat.Prime p)).one_lt
  have aux : g_poly ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero _ h hp
  have key : Fintype.card (g_poly.RootSet (GaloisField p n)) = g_poly.natDegree :=
    card_root_set_eq_nat_degree (galois_poly_separable p _ (dvd_pow (dvd_refl p) h)) (splitting_field.splits g_poly)
  have nat_degree_eq : g_poly.natDegree = p ^ n := FiniteField.X_pow_card_pow_sub_X_nat_degree_eq _ h hp
  rw [nat_degree_eq] at key
  suffices g_poly.RootSet (GaloisField p n) = Set.Univ by
    simp_rw [this, ← Fintype.of_equiv_card (Equivₓ.Set.univ _)] at key
    rw [@card_eq_pow_finrank (Zmod p), Zmod.card] at key
    exact Nat.pow_right_injective (Nat.Prime.one_lt' p).out key
  rw [Set.eq_univ_iff_forall]
  suffices
    ∀ (x) (hx : x ∈ (⊤ : Subalgebra (Zmod p) (GaloisField p n))),
      x ∈ (X ^ p ^ n - X : (Zmod p)[X]).RootSet (GaloisField p n)
    by
    simpa
  rw [← splitting_field.adjoin_root_set]
  simp_rw [Algebra.mem_adjoin_iff]
  intro x hx
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `zmod p`.
  cases p
  cases hp
  apply Subring.closure_induction hx <;> clear! x <;> simp_rw [mem_root_set aux]
  · rintro x (⟨r, rfl⟩ | hx)
    · simp only [← aeval_X_pow, ← aeval_X, ← AlgHom.map_sub]
      rw [← map_pow, Zmod.pow_card_pow, sub_self]
      
    · dsimp' only [← GaloisField]  at hx
      rwa [mem_root_set aux] at hx
      
    
  · dsimp' only [← g_poly]
    rw [← coeff_zero_eq_aeval_zero']
    simp only [← coeff_X_pow, ← coeff_X_zero, ← sub_zero, ← RingHom.map_eq_zero, ← ite_eq_right_iff, ← one_ne_zero, ←
      coeff_sub]
    intro hn
    exact Nat.not_lt_zeroₓ 1 (pow_eq_zero hn.symm ▸ hp)
    
  · simp
    
  · simp only [← aeval_X_pow, ← aeval_X, ← AlgHom.map_sub, ← add_pow_char_pow, ← sub_eq_zero]
    intro x y hx hy
    rw [hx, hy]
    
  · intro x hx
    simp only [← sub_eq_zero, ← aeval_X_pow, ← aeval_X, ← AlgHom.map_sub, ← sub_neg_eq_add] at *
    rw [neg_pow, hx, CharP.neg_one_pow_char_pow]
    simp
    
  · simp only [← aeval_X_pow, ← aeval_X, ← AlgHom.map_sub, ← mul_powₓ, ← sub_eq_zero]
    intro x y hx hy
    rw [hx, hy]
    

theorem card (h : n ≠ 0) : Fintype.card (GaloisField p n) = p ^ n := by
  let b := IsNoetherian.finsetBasis (Zmod p) (GaloisField p n)
  rw [Module.card_fintype b, ← FiniteDimensional.finrank_eq_card_basis b, Zmod.card, finrank p h]

theorem splits_zmod_X_pow_sub_X : Splits (RingHom.id (Zmod p)) (X ^ p - X) := by
  have hp : 1 < p := (Fact.out (Nat.Prime p)).one_lt
  have h1 : roots (X ^ p - X : (Zmod p)[X]) = finset.univ.val := by
    convert FiniteField.roots_X_pow_card_sub_X _
    exact (Zmod.card p).symm
  have h2 := FiniteField.X_pow_card_sub_X_nat_degree_eq (Zmod p) hp
  -- We discharge the `p = 0` separately, to avoid typeclass issues on `zmod p`.
  cases p
  cases hp
  rw [splits_iff_card_roots, h1, ← Finset.card_def, Finset.card_univ, h2, Zmod.card]

/-- A Galois field with exponent 1 is equivalent to `zmod` -/
def equivZmodP : GaloisField p 1 ≃ₐ[Zmod p] Zmod p :=
  have h : (X ^ p ^ 1 : (Zmod p)[X]) = X ^ Fintype.card (Zmod p) := by
    rw [pow_oneₓ, Zmod.card p]
  have inst : IsSplittingField (Zmod p) (Zmod p) (X ^ p ^ 1 - X) := by
    rw [h]
    infer_instance
  (is_splitting_field.alg_equiv (Zmod p) (X ^ p ^ 1 - X : (Zmod p)[X])).symm

variable {K : Type _} [Field K] [Fintype K] [Algebra (Zmod p) K]

theorem splits_X_pow_card_sub_X : Splits (algebraMap (Zmod p) K) (X ^ Fintype.card K - X) :=
  (FiniteField.HasSub.Sub.Polynomial.is_splitting_field K (Zmod p)).Splits

theorem is_splitting_field_of_card_eq (h : Fintype.card K = p ^ n) : IsSplittingField (Zmod p) K (X ^ p ^ n - X) :=
  h ▸ FiniteField.HasSub.Sub.Polynomial.is_splitting_field K (Zmod p)

instance (priority := 100) {K K' : Type _} [Field K] [Field K'] [Fintype K'] [Algebra K K'] : IsGalois K K' := by
  obtain ⟨p, hp⟩ := CharP.exists K
  have : CharP K p := hp
  have : CharP K' p := char_p_of_injective_algebra_map' K K' p
  exact
    IsGalois.of_separable_splitting_field
      (galois_poly_separable p (Fintype.card K')
        (let ⟨n, hp, hn⟩ := FiniteField.card K' p
        hn.symm ▸ dvd_pow_self p n.ne_zero))

/-- Any finite field is (possibly non canonically) isomorphic to some Galois field. -/
def algEquivGaloisField (h : Fintype.card K = p ^ n) : K ≃ₐ[Zmod p] GaloisField p n :=
  have := is_splitting_field_of_card_eq _ _ h
  is_splitting_field.alg_equiv _ _

end GaloisField

namespace FiniteField

variable {K : Type _} [Field K] [Fintype K] {K' : Type _} [Field K'] [Fintype K']

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def algEquivOfCardEq (p : ℕ) [Fact p.Prime] [Algebra (Zmod p) K] [Algebra (Zmod p) K']
    (hKK' : Fintype.card K = Fintype.card K') : K ≃ₐ[Zmod p] K' := by
  have : CharP K p := by
    rw [← Algebra.char_p_iff (Zmod p) K p]
    exact Zmod.char_p p
  have : CharP K' p := by
    rw [← Algebra.char_p_iff (Zmod p) K' p]
    exact Zmod.char_p p
  choose n a hK using FiniteField.card K p
  choose n' a' hK' using FiniteField.card K' p
  rw [hK, hK'] at hKK'
  have hGalK := GaloisField.algEquivGaloisField p n hK
  have hK'Gal := (GaloisField.algEquivGaloisField p n' hK').symm
  rw [Nat.pow_right_injective (Fact.out (Nat.Prime p)).one_lt hKK'] at *
  use AlgEquiv.trans hGalK hK'Gal

/-- Uniqueness of finite fields:
  Any two finite fields of the same cardinality are (possibly non canonically) isomorphic-/
def ringEquivOfCardEq (hKK' : Fintype.card K = Fintype.card K') : K ≃+* K' := by
  choose p _char_p_K using CharP.exists K
  choose p' _char_p'_K' using CharP.exists K'
  skip
  choose n hp hK using FiniteField.card K p
  choose n' hp' hK' using FiniteField.card K' p'
  have hpp' : p = p' := by
    -- := eq_prime_of_eq_prime_pow
    by_contra hne
    have h2 := Nat.coprime_pow_primes n n' hp hp' hne
    rw [(Eq.congr hK hK').mp hKK', Nat.coprime_selfₓ, pow_eq_one_iff (Pnat.ne_zero n')] at h2
    exact Nat.Prime.ne_one hp' h2
    all_goals
      infer_instance
  rw [← hpp'] at *
  have := fact_iff.2 hp
  exact alg_equiv_of_card_eq p hKK'

end FiniteField

