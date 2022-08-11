/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.RingTheory.Ideal.Operations
import Mathbin.RingTheory.Localization.Basic

/-!
# Ideals in localizations of commutative rings

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


namespace IsLocalization

section CommSemiringₓ

variable {R : Type _} [CommSemiringₓ R] (M : Submonoid R) (S : Type _) [CommSemiringₓ S]

variable [Algebra R S] [IsLocalization M S]

include M

/-- Explicit characterization of the ideal given by `ideal.map (algebra_map R S) I`.
In practice, this ideal differs only in that the carrier set is defined explicitly.
This definition is only meant to be used in proving `mem_map_algebra_map_iff`,
and any proof that needs to refer to the explicit carrier set should use that theorem. -/
private def map_ideal (I : Ideal R) : Ideal S where
  Carrier := { z : S | ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 }
  zero_mem' :=
    ⟨⟨0, 1⟩, by
      simp ⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    use ⟨a'.2 * b'.1 + b'.2 * a'.1, I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩
    use a'.2 * b'.2
    simp only [← RingHom.map_add, ← Submodule.coe_mk, ← Submonoid.coe_mul, ← RingHom.map_mul]
    rw [add_mulₓ, ← mul_assoc a, ha, mul_comm (algebraMap R S a'.2) (algebraMap R S b'.2), ← mul_assoc b, hb]
    ring
  smul_mem' := by
    rintro c x ⟨x', hx⟩
    obtain ⟨c', hc⟩ := IsLocalization.surj M c
    use ⟨c'.1 * x'.1, I.mul_mem_left c'.1 x'.1.2⟩
    use c'.2 * x'.2
    simp only [hx, hc, ← smul_eq_mul, ← Submodule.coe_mk, ← Submonoid.coe_mul, ← RingHom.map_mul]
    ring

theorem mem_map_algebra_map_iff {I : Ideal R} {z} :
    z ∈ Ideal.map (algebraMap R S) I ↔ ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 := by
  constructor
  · change _ → z ∈ map_ideal M S I
    refine' fun h => Ideal.mem_Inf.1 h fun z hz => _
    obtain ⟨y, hy⟩ := hz
    use
      ⟨⟨⟨y, hy.left⟩, 1⟩, by
        simp [← hy.right]⟩
    
  · rintro ⟨⟨a, s⟩, h⟩
    rw [← Ideal.unit_mul_mem_iff_mem _ (map_units S s), mul_comm]
    exact h.symm ▸ Ideal.mem_map_of_mem _ a.2
    

theorem map_comap (J : Ideal S) : Ideal.map (algebraMap R S) (Ideal.comap (algebraMap R S) J) = J :=
  (le_antisymmₓ (Ideal.map_le_iff_le_comap.2 le_rfl)) fun x hJ => by
    obtain ⟨r, s, hx⟩ := mk'_surjective M x
    rw [← hx] at hJ⊢
    exact
      Ideal.mul_mem_right _ _
        (Ideal.mem_map_of_mem _
          (show (algebraMap R S) r ∈ J from mk'_spec S r s ▸ J.mul_mem_right ((algebraMap R S) s) hJ))

theorem comap_map_of_is_prime_disjoint (I : Ideal R) (hI : I.IsPrime) (hM : Disjoint (M : Set R) I) :
    Ideal.comap (algebraMap R S) (Ideal.map (algebraMap R S) I) = I := by
  refine' le_antisymmₓ (fun a ha => _) Ideal.le_comap_map
  obtain ⟨⟨b, s⟩, h⟩ := (mem_map_algebra_map_iff M S).1 (Ideal.mem_comap.1 ha)
  replace h : algebraMap R S (a * s) = algebraMap R S b := by
    simpa only [map_mul] using h
  obtain ⟨c, hc⟩ := (eq_iff_exists M S).1 h
  have : a * (s * c) ∈ I := by
    rw [← mul_assoc, hc]
    exact I.mul_mem_right c b.2
  exact (hI.mem_or_mem this).resolve_right fun hsc => hM ⟨(s * c).2, hsc⟩

/-- If `S` is the localization of `R` at a submonoid, the ordering of ideals of `S` is
embedded in the ordering of ideals of `R`. -/
def orderEmbedding : Ideal S ↪o Ideal R where
  toFun := fun J => Ideal.comap (algebraMap R S) J
  inj' := Function.LeftInverse.injective (map_comap M S)
  map_rel_iff' := fun J₁ J₂ => ⟨fun hJ => (map_comap M S) J₁ ▸ (map_comap M S) J₂ ▸ Ideal.map_mono hJ, Ideal.comap_mono⟩

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its comap,
see `le_rel_iso_of_prime` for the more general relation isomorphism -/
theorem is_prime_iff_is_prime_disjoint (J : Ideal S) :
    J.IsPrime ↔ (Ideal.comap (algebraMap R S) J).IsPrime ∧ Disjoint (M : Set R) ↑(Ideal.comap (algebraMap R S) J) := by
  constructor
  · refine' fun h => ⟨⟨_, _⟩, fun m hm => h.ne_top (Ideal.eq_top_of_is_unit_mem _ hm.2 (map_units S ⟨m, hm.left⟩))⟩
    · refine' fun hJ => h.ne_top _
      rw [eq_top_iff, ← (OrderEmbedding M S).le_iff_le]
      exact le_of_eqₓ hJ.symm
      
    · intro x y hxy
      rw [Ideal.mem_comap, RingHom.map_mul] at hxy
      exact h.mem_or_mem hxy
      
    
  · refine' fun h => ⟨fun hJ => h.left.ne_top (eq_top_iff.2 _), _⟩
    · rwa [eq_top_iff, ← (OrderEmbedding M S).le_iff_le] at hJ
      
    · intro x y hxy
      obtain ⟨a, s, ha⟩ := mk'_surjective M x
      obtain ⟨b, t, hb⟩ := mk'_surjective M y
      have : mk' S (a * b) (s * t) ∈ J := by
        rwa [mk'_mul, ha, hb]
      rw [mk'_mem_iff, ← Ideal.mem_comap] at this
      replace this := h.left.mem_or_mem this
      rw [Ideal.mem_comap, Ideal.mem_comap] at this
      rwa [← ha, ← hb, mk'_mem_iff, mk'_mem_iff]
      
    

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M`.
This lemma gives the particular case for an ideal and its map,
see `le_rel_iso_of_prime` for the more general relation isomorphism, and the reverse implication -/
theorem is_prime_of_is_prime_disjoint (I : Ideal R) (hp : I.IsPrime) (hd : Disjoint (M : Set R) ↑I) :
    (Ideal.map (algebraMap R S) I).IsPrime := by
  rw [is_prime_iff_is_prime_disjoint M S, comap_map_of_is_prime_disjoint M S I hp hd]
  exact ⟨hp, hd⟩

/-- If `R` is a ring, then prime ideals in the localization at `M`
correspond to prime ideals in the original ring `R` that are disjoint from `M` -/
def orderIsoOfPrime : { p : Ideal S // p.IsPrime } ≃o { p : Ideal R // p.IsPrime ∧ Disjoint (M : Set R) ↑p } where
  toFun := fun p => ⟨Ideal.comap (algebraMap R S) p.1, (is_prime_iff_is_prime_disjoint M S p.1).1 p.2⟩
  invFun := fun p => ⟨Ideal.map (algebraMap R S) p.1, is_prime_of_is_prime_disjoint M S p.1 p.2.1 p.2.2⟩
  left_inv := fun J => Subtype.eq (map_comap M S J)
  right_inv := fun I => Subtype.eq (comap_map_of_is_prime_disjoint M S I.1 I.2.1 I.2.2)
  map_rel_iff' := fun I I' =>
    ⟨fun h => show I.val ≤ I'.val from map_comap M S I.val ▸ map_comap M S I'.val ▸ Ideal.map_mono h, fun h x hx =>
      h hx⟩

end CommSemiringₓ

section CommRingₓ

variable {R : Type _} [CommRingₓ R] (M : Submonoid R) (S : Type _) [CommRingₓ S]

variable [Algebra R S] [IsLocalization M S]

include M

/-- `quotient_map` applied to maximal ideals of a localization is `surjective`.
  The quotient by a maximal ideal is a field, so inverses to elements already exist,
  and the localization necessarily maps the equivalence class of the inverse in the localization -/
theorem surjective_quotient_map_of_maximal_of_localization {I : Ideal S} [I.IsPrime] {J : Ideal R}
    {H : J ≤ I.comap (algebraMap R S)} (hI : (I.comap (algebraMap R S)).IsMaximal) :
    Function.Surjective (I.quotientMap (algebraMap R S) H) := by
  intro s
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
  obtain ⟨r, ⟨m, hm⟩, rfl⟩ := mk'_surjective M s
  by_cases' hM : (Ideal.Quotient.mk (I.comap (algebraMap R S))) m = 0
  · have : I = ⊤ := by
      rw [Ideal.eq_top_iff_one]
      rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_comap] at hM
      convert I.mul_mem_right (mk' S (1 : R) ⟨m, hm⟩) hM
      rw [← mk'_eq_mul_mk'_one, mk'_self]
    exact
      ⟨0,
        eq_comm.1
          (by
            simp [← Ideal.Quotient.eq_zero_iff_mem, ← this])⟩
    
  · rw [Ideal.Quotient.maximal_ideal_iff_is_field_quotient] at hI
    obtain ⟨n, hn⟩ := hI.3 hM
    obtain ⟨rn, rfl⟩ := Ideal.Quotient.mk_surjective n
    refine' ⟨(Ideal.Quotient.mk J) (r * rn), _⟩
    -- The rest of the proof is essentially just algebraic manipulations to prove the equality
    rw [← RingHom.map_mul] at hn
    replace hn := congr_arg (Ideal.quotientMap I (algebraMap R S) le_rfl) hn
    simp only [← RingHom.map_one, ← Ideal.quotient_map_mk, ← RingHom.map_mul] at hn
    rw [Ideal.quotient_map_mk, ← sub_eq_zero, ← RingHom.map_sub, Ideal.Quotient.eq_zero_iff_mem, ←
      Ideal.Quotient.eq_zero_iff_mem, RingHom.map_sub, sub_eq_zero, mk'_eq_mul_mk'_one]
    simp only [← mul_eq_mul_left_iff, ← RingHom.map_mul]
    exact
      Or.inl
        (mul_left_cancel₀
          (fun hn => hM (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 hn))))
          (trans hn
            (by
              rw [← RingHom.map_mul, ← mk'_eq_mul_mk'_one, mk'_self, RingHom.map_one])))
    

end CommRingₓ

end IsLocalization

