/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathbin.RingTheory.WittVector.FrobeniusFractionField

/-!

## F-isocrystals over a perfect field

When `k` is an integral domain, so is `𝕎 k`, and we can consider its field of fractions `K(p, k)`.
The endomorphism `witt_vector.frobenius` lifts to `φ : K(p, k) → K(p, k)`; if `k` is perfect, `φ` is
an automorphism.

Let `k` be a perfect integral domain. Let `V` be a vector space over `K(p,k)`.
An *isocrystal* is a bijective map `V → V` that is `φ`-semilinear.
A theorem of Dieudonné and Manin classifies the finite-dimensional isocrystals over algebraically
closed fields. In the one-dimensional case, this classification states that the isocrystal
structures are parametrized by their "slope" `m : ℤ`.
Any one-dimensional isocrystal is isomorphic to `φ(p^m • x) : K(p,k) → K(p,k)` for some `m`.

This file proves this one-dimensional case of the classification theorem.
The construction is described in Dupuis, Lewis, and Macbeth,
[Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022].

## Main declarations

* `witt_vector.isocrystal`: a vector space over the field `K(p, k)` additionally equipped with a
  Frobenius-linear automorphism.
* `witt_vector.isocrystal_classification`: a one-dimensional isocrystal admits an isomorphism to one
  of the standard one-dimensional isocrystals.

## Notation

This file introduces notation in the locale `isocrystal`.
* `K(p, k)`: `fraction_ring (witt_vector p k)`
* `φ(p, k)`: `witt_vector.fraction_ring.frobenius_ring_hom p k`
* `M →ᶠˡ[p, k] M₂`: `linear_map (witt_vector.fraction_ring.frobenius_ring_hom p k) M M₂`
* `M ≃ᶠˡ[p, k] M₂`: `linear_equiv (witt_vector.fraction_ring.frobenius_ring_hom p k) M M₂`
* `Φ(p, k)`: `witt_vector.isocrystal.frobenius p k`
* `M →ᶠⁱ[p, k] M₂`: `witt_vector.isocrystal_hom p k M M₂`
* `M ≃ᶠⁱ[p, k] M₂`: `witt_vector.isocrystal_equiv p k M M₂`

## References

* [Formalized functional analysis via semilinear maps][dupuis-lewis-macbeth2022]
* [Theory of commutative formal groups over fields of finite characteristic][manin1963]
* <https://www.math.ias.edu/~lurie/205notes/Lecture26-Isocrystals.pdf>

-/


noncomputable section

open FiniteDimensional

namespace WittVector

variable (p : ℕ) [Fact p.Prime]

variable (k : Type _) [CommRingₓ k]

-- mathport name: «exprK( , )»
localized [Isocrystal] notation "K(" p "," k ")" => FractionRing (WittVector p k)

section PerfectRing

variable [IsDomain k] [CharP k p] [PerfectRing k p]

/-! ### Frobenius-linear maps -/


/-- The Frobenius automorphism of `k` induces an automorphism of `K`. -/
def FractionRing.frobenius : K(p,k) ≃+* K(p,k) :=
  IsFractionRing.fieldEquivOfRingEquiv (frobeniusEquiv p k)

/-- The Frobenius automorphism of `k` induces an endomorphism of `K`. For notation purposes. -/
def FractionRing.frobeniusRingHom : K(p,k) →+* K(p,k) :=
  FractionRing.frobenius p k

-- mathport name: «exprφ( , )»
localized [Isocrystal] notation "φ(" p "," k ")" => WittVector.FractionRing.frobeniusRingHom p k

instance inv_pair₁ : RingHomInvPair φ(p,k) _ :=
  RingHomInvPair.of_ring_equiv (FractionRing.frobenius p k)

instance inv_pair₂ : RingHomInvPair ((FractionRing.frobenius p k).symm : K(p,k) →+* K(p,k)) _ :=
  RingHomInvPair.of_ring_equiv (FractionRing.frobenius p k).symm

-- mathport name: «expr →ᶠˡ[ , ] »
localized [Isocrystal]
  notation:50 M " →ᶠˡ[" p "," k "] " M₂ => LinearMap (WittVector.FractionRing.frobeniusRingHom p k) M M₂

-- mathport name: «expr ≃ᶠˡ[ , ] »
localized [Isocrystal]
  notation:50 M " ≃ᶠˡ[" p "," k "] " M₂ => LinearEquiv (WittVector.FractionRing.frobeniusRingHom p k) M M₂

/-! ### Isocrystals -/


/-- An isocrystal is a vector space over the field `K(p, k)` additionally equipped with a
Frobenius-linear automorphism.
-/
class Isocrystal (V : Type _) [AddCommGroupₓ V] extends Module K(p,k) V where
  frob : V ≃ᶠˡ[p,k] V

variable (V : Type _) [AddCommGroupₓ V] [Isocrystal p k V]

variable (V₂ : Type _) [AddCommGroupₓ V₂] [Isocrystal p k V₂]

variable {V}

/-- Project the Frobenius automorphism from an isocrystal. Denoted by `Φ(p, k)` when V can be inferred.
-/
def Isocrystal.frobenius : V ≃ᶠˡ[p,k] V :=
  @Isocrystal.frob p _ k _ _ _ _ _ _ _

variable (V)

-- mathport name: «exprΦ( , )»
localized [Isocrystal] notation "Φ(" p "," k ")" => WittVector.Isocrystal.frobenius p k

/-- A homomorphism between isocrystals respects the Frobenius map. -/
@[nolint has_inhabited_instance]
structure IsocrystalHom extends V →ₗ[K(p,k)] V₂ where
  frob_equivariant : ∀ x : V, Φ(p,k) (to_linear_map x) = to_linear_map (Φ(p,k) x)

/-- An isomorphism between isocrystals respects the Frobenius map. -/
@[nolint has_inhabited_instance]
structure IsocrystalEquiv extends V ≃ₗ[K(p,k)] V₂ where
  frob_equivariant : ∀ x : V, Φ(p,k) (to_linear_equiv x) = to_linear_equiv (Φ(p,k) x)

-- mathport name: «expr →ᶠⁱ[ , ] »
localized [Isocrystal] notation:50 M " →ᶠⁱ[" p "," k "] " M₂ => WittVector.IsocrystalHom p k M M₂

-- mathport name: «expr ≃ᶠⁱ[ , ] »
localized [Isocrystal] notation:50 M " ≃ᶠⁱ[" p "," k "] " M₂ => WittVector.IsocrystalEquiv p k M M₂

end PerfectRing

open Isocrystal

/-! ### Classification of isocrystals in dimension 1 -/


/-- A helper instance for type class inference. -/
@[local instance]
def FractionRing.module : Module K(p,k) K(p,k) :=
  Semiringₓ.toModule

-- ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module «exprK( , )»(p, k)
/-- Type synonym for `K(p, k)` to carry the standard 1-dimensional isocrystal structure
of slope `m : ℤ`.
-/
@[nolint unused_arguments has_inhabited_instance]
def StandardOneDimIsocrystal (m : ℤ) : Type _ :=
  K(p,k)deriving AddCommGroupₓ,
  ./././Mathport/Syntax/Translate/Basic.lean:1153:9: unsupported derive handler module «exprK( , )»(p, k)

section PerfectRing

variable [IsDomain k] [CharP k p] [PerfectRing k p]

/-- The standard one-dimensional isocrystal of slope `m : ℤ` is an isocrystal. -/
instance (m : ℤ) :
    Isocrystal p k
      (StandardOneDimIsocrystal p k
        m) where frob :=
    (FractionRing.frobenius p k).toSemilinearEquiv.trans
      (LinearEquiv.smulOfNeZero _ _ _ (zpow_ne_zero m (WittVector.FractionRing.p_nonzero p k)))

@[simp]
theorem StandardOneDimIsocrystal.frobenius_apply (m : ℤ) (x : StandardOneDimIsocrystal p k m) :
    Φ(p,k) x = (p : K(p,k)) ^ m • φ(p,k) x :=
  rfl

end PerfectRing

-- ./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr * »(«exprφ( , )»(p, k) c, hmb)], []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args
/-- A one-dimensional isocrystal over an algebraically closed field
admits an isomorphism to one of the standard (indexed by `m : ℤ`) one-dimensional isocrystals. -/
theorem isocrystal_classification (k : Type _) [Field k] [IsAlgClosed k] [CharP k p] (V : Type _) [AddCommGroupₓ V]
    [Isocrystal p k V] (h_dim : finrank K(p,k) V = 1) : ∃ m : ℤ, Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p,k] V) :=
  by
  have : Nontrivial V := FiniteDimensional.nontrivial_of_finrank_eq_succ h_dim
  obtain ⟨x, hx⟩ : ∃ x : V, x ≠ 0 := exists_ne 0
  have : Φ(p,k) x ≠ 0 := by
    simpa only [← map_zero] using Φ(p,k).Injective.Ne hx
  obtain ⟨a, ha, hax⟩ : ∃ a : K(p,k), a ≠ 0 ∧ Φ(p,k) x = a • x := by
    rw [finrank_eq_one_iff_of_nonzero' x hx] at h_dim
    obtain ⟨a, ha⟩ := h_dim (Φ(p,k) x)
    refine' ⟨a, _, ha.symm⟩
    intro ha'
    apply this
    simp only [ha, ← ha', ← zero_smul]
  obtain ⟨b, hb, m, hmb⟩ := WittVector.exists_frobenius_solution_fraction_ring p ha
  replace hmb : φ(p,k) b * a = p ^ m * b := by
    convert hmb
  use m
  let F₀ : standard_one_dim_isocrystal p k m →ₗ[K(p,k)] V := LinearMap.toSpanSingleton K(p,k) V x
  let F : standard_one_dim_isocrystal p k m ≃ₗ[K(p,k)] V := by
    refine' LinearEquiv.ofBijective F₀ _ _
    · rw [← LinearMap.ker_eq_bot]
      exact LinearMap.ker_to_span_singleton K(p,k) V hx
      
    · rw [← LinearMap.range_eq_top]
      rw [← (finrank_eq_one_iff_of_nonzero x hx).mp h_dim]
      rw [LinearMap.span_singleton_eq_range]
      
  refine' ⟨⟨(LinearEquiv.smulOfNeZero K(p,k) _ _ hb).trans F, _⟩⟩
  intro c
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.smul_of_ne_zero_apply,
    LinearEquiv.smul_of_ne_zero_apply, LinearEquiv.map_smul, LinearEquiv.map_smul]
  simp only [← hax, ← LinearEquiv.of_bijective_apply, ← LinearMap.to_span_singleton_apply, ← LinearEquiv.map_smulₛₗ, ←
    standard_one_dim_isocrystal.frobenius_apply, ← Algebra.id.smul_eq_mul]
  simp only [mul_smul]
  congr 1
  trace
    "./././Mathport/Syntax/Translate/Basic.lean:646:40: in linear_combination #[[expr «expr * »(«exprφ( , )»(p, k) c, hmb)], []]: ./././Mathport/Syntax/Translate/Basic.lean:319:22: unsupported: too many args"

end WittVector

