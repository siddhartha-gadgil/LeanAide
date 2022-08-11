/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen
-/
import Mathbin.RingTheory.Localization.AtPrime
import Mathbin.RingTheory.Localization.Basic
import Mathbin.RingTheory.Localization.FractionRing

/-!
# Localizations of localizations

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRingₓ R] (M : Submonoid R) {S : Type _} [CommRingₓ S]

variable [Algebra R S] {P : Type _} [CommRingₓ P]

open Function

open BigOperators

namespace IsLocalization

section LocalizationLocalization

variable (M)

variable (N : Submonoid S) (T : Type _) [CommRingₓ T] [Algebra R T]

section

variable [Algebra S T] [IsScalarTower R S T]

/-- Localizing wrt `M ⊆ R` and then wrt `N ⊆ S = M⁻¹R` is equal to the localization of `R` wrt this
module. See `localization_localization_is_localization`.
-/
-- This should only be defined when `S` is the localization `M⁻¹R`, hence the nolint.
@[nolint unused_arguments]
def localizationLocalizationSubmodule : Submonoid R :=
  (N⊔M.map (algebraMap R S)).comap (algebraMap R S)

variable {M N}

@[simp]
theorem mem_localization_localization_submodule {x : R} :
    x ∈ localizationLocalizationSubmodule M N ↔ ∃ (y : N)(z : M), algebraMap R S x = y * algebraMap R S z := by
  rw [localization_localization_submodule, Submonoid.mem_comap, Submonoid.mem_sup]
  constructor
  · rintro ⟨y, hy, _, ⟨z, hz, rfl⟩, e⟩
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, e.symm⟩
    
  · rintro ⟨y, z, e⟩
    exact ⟨y, y.prop, _, ⟨z, z.prop, rfl⟩, e.symm⟩
    

variable (M N) [IsLocalization M S]

theorem localization_localization_map_units [IsLocalization N T] (y : localizationLocalizationSubmodule M N) :
    IsUnit (algebraMap R T y) := by
  obtain ⟨y', z, eq⟩ := mem_localization_localization_submodule.mp y.prop
  rw [IsScalarTower.algebra_map_apply R S T, Eq, RingHom.map_mul, IsUnit.mul_iff]
  exact ⟨IsLocalization.map_units T y', (IsLocalization.map_units _ z).map (algebraMap S T)⟩

theorem localization_localization_surj [IsLocalization N T] (x : T) :
    ∃ y : R × localizationLocalizationSubmodule M N, x * algebraMap R T y.2 = algebraMap R T y.1 := by
  rcases IsLocalization.surj N x with ⟨⟨y, s⟩, eq₁⟩
  -- x = y / s
  rcases IsLocalization.surj M y with ⟨⟨z, t⟩, eq₂⟩
  -- y = z / t
  rcases IsLocalization.surj M (s : S) with ⟨⟨z', t'⟩, eq₃⟩
  -- s = z' / t'
  dsimp' only  at eq₁ eq₂ eq₃
  use z * t'
  use z' * t
  -- x = y / s = (z * t') / (z' * t)
  · rw [mem_localization_localization_submodule]
    refine' ⟨s, t * t', _⟩
    rw [RingHom.map_mul, ← eq₃, mul_assoc, ← RingHom.map_mul, mul_comm t, Submonoid.coe_mul]
    
  · simp only [← Subtype.coe_mk, ← RingHom.map_mul, ← IsScalarTower.algebra_map_apply R S T, eq₃, eq₂, eq₁]
    ring
    

theorem localization_localization_eq_iff_exists [IsLocalization N T] (x y : R) :
    algebraMap R T x = algebraMap R T y ↔ ∃ c : localizationLocalizationSubmodule M N, x * c = y * c := by
  rw [IsScalarTower.algebra_map_apply R S T, IsScalarTower.algebra_map_apply R S T, IsLocalization.eq_iff_exists N T]
  constructor
  · rintro ⟨z, eq₁⟩
    rcases IsLocalization.surj M (z : S) with ⟨⟨z', s⟩, eq₂⟩
    dsimp' only  at eq₂
    obtain ⟨c, eq₃ : x * z' * ↑c = y * z' * ↑c⟩ := (IsLocalization.eq_iff_exists M S).mp _
    swap
    · rw [RingHom.map_mul, RingHom.map_mul, ← eq₂, ← mul_assoc, ← mul_assoc, ← eq₁]
      
    use z' * c
    · rw [mem_localization_localization_submodule]
      refine' ⟨z, s * c, _⟩
      rw [RingHom.map_mul, ← eq₂, mul_assoc, ← RingHom.map_mul, Submonoid.coe_mul]
      
    · simpa only [← mul_assoc] using eq₃
      
    
  · rintro ⟨⟨c, hc⟩, eq₁ : x * c = y * c⟩
    rw [mem_localization_localization_submodule] at hc
    rcases hc with ⟨z₁, z, eq₂⟩
    use z₁
    refine' (IsLocalization.map_units S z).mul_left_inj.mp _
    rw [mul_assoc, mul_assoc, ← eq₂, ← RingHom.map_mul, ← RingHom.map_mul, eq₁]
    

/-- Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, we have
`N ⁻¹ S = T = (f⁻¹ (N • f(M))) ⁻¹ R`. I.e., the localization of a localization is a localization.
-/
theorem localization_localization_is_localization [IsLocalization N T] :
    IsLocalization (localizationLocalizationSubmodule M N) T :=
  { map_units := localization_localization_map_units M N T, surj := localization_localization_surj M N T,
    eq_iff_exists := localization_localization_eq_iff_exists M N T }

include M

/-- Given submodules `M ⊆ R` and `N ⊆ S = M⁻¹R`, with `f : R →+* S` the localization map, if
`N` contains all the units of `S`, then `N ⁻¹ S = T = (f⁻¹ N) ⁻¹ R`. I.e., the localization of a
localization is a localization.
-/
theorem localization_localization_is_localization_of_has_all_units [IsLocalization N T]
    (H : ∀ x : S, IsUnit x → x ∈ N) : IsLocalization (N.comap (algebraMap R S)) T := by
  convert localization_localization_is_localization M N T
  symm
  rw [sup_eq_left]
  rintro _ ⟨x, hx, rfl⟩
  exact H _ (IsLocalization.map_units _ ⟨x, hx⟩)

/-- Given a submodule `M ⊆ R` and a prime ideal `p` of `S = M⁻¹R`, with `f : R →+* S` the localization
map, then `T = Sₚ` is the localization of `R` at `f⁻¹(p)`.
-/
theorem is_localization_is_localization_at_prime_is_localization (p : Ideal S) [Hp : p.IsPrime]
    [IsLocalization.AtPrime T p] : IsLocalization.AtPrime T (p.comap (algebraMap R S)) := by
  apply localization_localization_is_localization_of_has_all_units M p.prime_compl T
  intro x hx hx'
  exact (Hp.1 : ¬_) (p.eq_top_of_is_unit_mem hx' hx)

instance (p : Ideal (Localization M)) [p.IsPrime] : Algebra R (Localization.AtPrime p) :=
  Localization.algebra

instance (p : Ideal (Localization M)) [p.IsPrime] : IsScalarTower R (Localization M) (Localization.AtPrime p) :=
  IsScalarTower.of_algebra_map_eq' rfl

instance localization_localization_at_prime_is_localization (p : Ideal (Localization M)) [p.IsPrime] :
    IsLocalization.AtPrime (Localization.AtPrime p) (p.comap (algebraMap R _)) :=
  is_localization_is_localization_at_prime_is_localization M _ _

/-- Given a submodule `M ⊆ R` and a prime ideal `p` of `M⁻¹R`, with `f : R →+* S` the localization
map, then `(M⁻¹R)ₚ` is isomorphic (as an `R`-algebra) to the localization of `R` at `f⁻¹(p)`.
-/
noncomputable def localizationLocalizationAtPrimeIsoLocalization (p : Ideal (Localization M)) [p.IsPrime] :
    Localization.AtPrime (p.comap (algebraMap R (Localization M))) ≃ₐ[R] Localization.AtPrime p :=
  IsLocalization.algEquiv (p.comap (algebraMap R (Localization M))).primeCompl _ _

end

variable (S)

/-- Given submonoids `M ≤ N` of `R`, this is the canonical algebra structure
of `M⁻¹S` acting on `N⁻¹S`. -/
noncomputable def localizationAlgebraOfSubmonoidLe (M N : Submonoid R) (h : M ≤ N) [IsLocalization M S]
    [IsLocalization N T] : Algebra S T :=
  (IsLocalization.lift fun y => (map_units T ⟨↑y, h y.Prop⟩ : _) : S →+* T).toAlgebra

/-- If `M ≤ N` are submonoids of `R`, then the natural map `M⁻¹S →+* N⁻¹S` commutes with the
localization maps -/
theorem localization_is_scalar_tower_of_submonoid_le (M N : Submonoid R) (h : M ≤ N) [IsLocalization M S]
    [IsLocalization N T] : @IsScalarTower R S T _ (localizationAlgebraOfSubmonoidLe S T M N h).toHasSmul _ := by
  let this := localization_algebra_of_submonoid_le S T M N h
  exact IsScalarTower.of_algebra_map_eq' (IsLocalization.lift_comp _).symm

noncomputable instance (x : Ideal R) [H : x.IsPrime] [IsDomain R] :
    Algebra (Localization.AtPrime x) (Localization (nonZeroDivisors R)) :=
  localizationAlgebraOfSubmonoidLe _ _ x.primeCompl (nonZeroDivisors R)
    (by
      intro a ha
      rw [mem_non_zero_divisors_iff_ne_zero]
      exact fun h => ha (h.symm ▸ x.zero_mem))

/-- If `M ≤ N` are submonoids of `R`, then `N⁻¹S` is also the localization of `M⁻¹S` at `N`. -/
theorem is_localization_of_submonoid_le (M N : Submonoid R) (h : M ≤ N) [IsLocalization M S] [IsLocalization N T]
    [Algebra S T] [IsScalarTower R S T] : IsLocalization (N.map (algebraMap R S).toMonoidHom) T :=
  { map_units := by
      rintro ⟨_, ⟨y, hy, rfl⟩⟩
      convert IsLocalization.map_units T ⟨y, hy⟩
      exact (IsScalarTower.algebra_map_apply _ _ _ _).symm,
    surj := fun y => by
      obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj N y
      refine' ⟨⟨algebraMap _ _ x, _, _, s.prop, rfl⟩, _⟩
      simpa [IsScalarTower.algebra_map_apply] using e,
    eq_iff_exists := fun x₁ x₂ => by
      obtain ⟨⟨y₁, s₁⟩, e₁⟩ := IsLocalization.surj M x₁
      obtain ⟨⟨y₂, s₂⟩, e₂⟩ := IsLocalization.surj M x₂
      refine' Iff.trans _ (Set.exists_image_iff (algebraMap R S) N fun c => x₁ * c = x₂ * c).symm
      dsimp' only  at e₁ e₂⊢
      suffices
        algebraMap R T (y₁ * s₂) = algebraMap R T (y₂ * s₁) ↔
          ∃ a : N, algebraMap R S (a * (y₁ * s₂)) = algebraMap R S (a * (y₂ * s₁))
        by
        have h₁ := (IsLocalization.map_units T ⟨_, h s₁.prop⟩).mul_left_inj
        have h₂ := (IsLocalization.map_units T ⟨_, h s₂.prop⟩).mul_left_inj
        simp only [← IsScalarTower.algebra_map_apply R S T, ← Subtype.coe_mk] at h₁ h₂
        simp only [← IsScalarTower.algebra_map_apply R S T, ← map_mul, e₁, e₂, mul_assoc, ←
          mul_right_commₓ _ (algebraMap R S s₂), ← mul_right_commₓ _ (algebraMap S T (algebraMap R S s₂)), ←
          (IsLocalization.map_units S s₁).mul_left_inj, ← (IsLocalization.map_units S s₂).mul_left_inj] at this
        rw [h₂, h₁] at this
        simpa only [← mul_comm] using this
      simp_rw [IsLocalization.eq_iff_exists N T, IsLocalization.eq_iff_exists M S]
      constructor
      · rintro ⟨a, e⟩
        exact
          ⟨a, 1, by
            convert e using 1 <;> simp <;> ring⟩
        
      · rintro ⟨a, b, e⟩
        exact
          ⟨a * (⟨_, h b.prop⟩ : N), by
            convert e using 1 <;> simp <;> ring⟩
         }

/-- If `M ≤ N` are submonoids of `R` such that `∀ x : N, ∃ m : R, m * x ∈ M`, then the
localization at `N` is equal to the localizaton of `M`. -/
theorem is_localization_of_is_exists_mul_mem (M N : Submonoid R) [IsLocalization M S] (h : M ≤ N)
    (h' : ∀ x : N, ∃ m : R, m * x ∈ M) : IsLocalization N S :=
  { map_units := fun y => by
      obtain ⟨m, hm⟩ := h' y
      have := IsLocalization.map_units S ⟨_, hm⟩
      erw [map_mul] at this
      exact (is_unit.mul_iff.mp this).2,
    surj := fun z => by
      obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M z
      exact ⟨⟨y, _, h s.prop⟩, e⟩,
    eq_iff_exists := fun x₁ x₂ => by
      rw [IsLocalization.eq_iff_exists M]
      refine' ⟨fun ⟨x, hx⟩ => ⟨⟨_, h x.Prop⟩, hx⟩, _⟩
      rintro ⟨x, h⟩
      obtain ⟨m, hm⟩ := h' x
      refine' ⟨⟨_, hm⟩, _⟩
      simp [← mul_comm m, mul_assoc, ← h] }

end LocalizationLocalization

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable (M)

theorem is_fraction_ring_of_is_localization (S T : Type _) [CommRingₓ S] [CommRingₓ T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] [IsLocalization M S] [IsFractionRing R T] (hM : M ≤ nonZeroDivisors R) :
    IsFractionRing S T := by
  have := is_localization_of_submonoid_le S T M (nonZeroDivisors R) _
  refine' @is_localization_of_is_exists_mul_mem _ _ _ _ _ _ this _ _
  · exact map_non_zero_divisors_le M S
    
  · rintro ⟨x, hx⟩
    obtain ⟨⟨y, s⟩, e⟩ := IsLocalization.surj M x
    use algebraMap R S s
    rw [mul_comm, Subtype.coe_mk, e]
    refine' Set.mem_image_of_mem (algebraMap R S) _
    intro z hz
    apply IsLocalization.injective S hM
    rw [map_zero]
    apply hx
    rw [← (map_units S s).mul_left_inj, mul_assoc, e, ← map_mul, hz, map_zero, zero_mul]
    
  · exact hM
    

theorem is_fraction_ring_of_is_domain_of_is_localization [IsDomain R] (S T : Type _) [CommRingₓ S] [CommRingₓ T]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T] [IsLocalization M S] [IsFractionRing R T] :
    IsFractionRing S T := by
  have := IsFractionRing.nontrivial R T
  have := (algebraMap S T).domain_nontrivial
  apply is_fraction_ring_of_is_localization M S T
  intro x hx
  rw [mem_non_zero_divisors_iff_ne_zero]
  intro hx'
  apply @zero_ne_one S
  rw [← (algebraMap R S).map_one, ← @mk'_one R _ M, @comm _ Eq, mk'_eq_zero_iff]
  exact ⟨⟨_, hx⟩, (one_mulₓ x).symm ▸ hx'⟩

end IsFractionRing

