/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathbin.Algebra.Associated
import Mathbin.Algebra.GroupPower.Lemmas

/-!
# Monoids with normalization functions, `gcd`, and `lcm`

This file defines extra structures on `cancel_comm_monoid_with_zero`s, including `is_domain`s.

## Main Definitions

* `normalization_monoid`
* `gcd_monoid`
* `normalized_gcd_monoid`
* `gcd_monoid_of_gcd`, `gcd_monoid_of_exists_gcd`, `normalized_gcd_monoid_of_gcd`,
  `normalized_gcd_monoid_of_exists_gcd`
* `gcd_monoid_of_lcm`, `gcd_monoid_of_exists_lcm`, `normalized_gcd_monoid_of_lcm`,
  `normalized_gcd_monoid_of_exists_lcm`

For the `normalized_gcd_monoid` instances on `ℕ` and `ℤ`, see `ring_theory.int.basic`.

## Implementation Notes

* `normalization_monoid` is defined by assigning to each element a `norm_unit` such that multiplying
by that unit normalizes the monoid, and `normalize` is an idempotent monoid homomorphism. This
definition as currently implemented does casework on `0`.

* `gcd_monoid` contains the definitions of `gcd` and `lcm` with the usual properties. They are
  both determined up to a unit.

* `normalized_gcd_monoid` extends `normalization_monoid`, so the `gcd` and `lcm` are always
  normalized. This makes `gcd`s of polynomials easier to work with, but excludes Euclidean domains,
  and monoids without zero.

* `gcd_monoid_of_gcd` and `normalized_gcd_monoid_of_gcd` noncomputably construct a `gcd_monoid`
  (resp. `normalized_gcd_monoid`) structure just from the `gcd` and its properties.

* `gcd_monoid_of_exists_gcd` and `normalized_gcd_monoid_of_exists_gcd` noncomputably construct a
  `gcd_monoid` (resp. `normalized_gcd_monoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `gcd`.

* `gcd_monoid_of_lcm` and `normalized_gcd_monoid_of_lcm` noncomputably construct a `gcd_monoid`
  (resp. `normalized_gcd_monoid`) structure just from the `lcm` and its properties.

* `gcd_monoid_of_exists_lcm` and `normalized_gcd_monoid_of_exists_lcm` noncomputably construct a
  `gcd_monoid` (resp. `normalized_gcd_monoid`) structure just from a proof that any two elements
  have a (not necessarily normalized) `lcm`.

## TODO

* Port GCD facts about nats, definition of coprime
* Generalize normalization monoids to commutative (cancellative) monoids with or without zero

## Tags

divisibility, gcd, lcm, normalize
-/


variable {α : Type _}

/-- Normalization monoid: multiplying with `norm_unit` gives a normal form for associated
elements. -/
@[protect_proj]
class NormalizationMonoid (α : Type _) [CancelCommMonoidWithZero α] where
  normUnit : α → αˣ
  norm_unit_zero : norm_unit 0 = 1
  norm_unit_mul : ∀ {a b}, a ≠ 0 → b ≠ 0 → norm_unit (a * b) = norm_unit a * norm_unit b
  norm_unit_coe_units : ∀ u : αˣ, norm_unit u = u⁻¹

export NormalizationMonoid (normUnit norm_unit_zero norm_unit_mul norm_unit_coe_units)

attribute [simp] norm_unit_coe_units norm_unit_zero norm_unit_mul

section NormalizationMonoid

variable [CancelCommMonoidWithZero α] [NormalizationMonoid α]

@[simp]
theorem norm_unit_one : normUnit (1 : α) = 1 :=
  norm_unit_coe_units 1

/-- Chooses an element of each associate class, by multiplying by `norm_unit` -/
def normalize : α →*₀ α where
  toFun := fun x => x * normUnit x
  map_zero' := by
    simp
  map_one' := by
    rw [norm_unit_one, Units.coe_one, mul_oneₓ]
  map_mul' := fun x y =>
    (Classical.by_cases fun hx : x = 0 => by
        rw [hx, zero_mul, zero_mul, zero_mul])
      fun hx =>
      (Classical.by_cases fun hy : y = 0 => by
          rw [hy, mul_zero, zero_mul, mul_zero])
        fun hy => by
        simp only [← norm_unit_mul hx hy, ← Units.coe_mul] <;> simp only [← mul_assoc, ← mul_left_commₓ y]

theorem associated_normalize (x : α) : Associated x (normalize x) :=
  ⟨_, rfl⟩

theorem normalize_associated (x : α) : Associated (normalize x) x :=
  (associated_normalize _).symm

theorem Associates.mk_normalize (x : α) : Associates.mk (normalize x) = Associates.mk x :=
  Associates.mk_eq_mk_iff_associated.2 (normalize_associated _)

@[simp]
theorem normalize_apply (x : α) : normalize x = x * normUnit x :=
  rfl

@[simp]
theorem normalize_zero : normalize (0 : α) = 0 :=
  normalize.map_zero

@[simp]
theorem normalize_one : normalize (1 : α) = 1 :=
  normalize.map_one

theorem normalize_coe_units (u : αˣ) : normalize (u : α) = 1 := by
  simp

theorem normalize_eq_zero {x : α} : normalize x = 0 ↔ x = 0 :=
  ⟨fun hx => (associated_zero_iff_eq_zero x).1 <| hx ▸ associated_normalize _, by
    rintro rfl <;> exact normalize_zero⟩

theorem normalize_eq_one {x : α} : normalize x = 1 ↔ IsUnit x :=
  ⟨fun hx => is_unit_iff_exists_inv.2 ⟨_, hx⟩, fun ⟨u, hu⟩ => hu ▸ normalize_coe_units u⟩

@[simp]
theorem norm_unit_mul_norm_unit (a : α) : normUnit (a * normUnit a) = 1 := by
  nontriviality α using ← Subsingleton.elimₓ a 0
  obtain rfl | h := eq_or_ne a 0
  · rw [norm_unit_zero, zero_mul, norm_unit_zero]
    
  · rw [norm_unit_mul h (Units.ne_zero _), norm_unit_coe_units, mul_inv_eq_one]
    

theorem normalize_idem (x : α) : normalize (normalize x) = normalize x := by
  simp

theorem normalize_eq_normalize {a b : α} (hab : a ∣ b) (hba : b ∣ a) : normalize a = normalize b := by
  nontriviality α
  rcases associated_of_dvd_dvd hab hba with ⟨u, rfl⟩
  refine'
    Classical.by_cases
      (by
        rintro rfl <;> simp only [← zero_mul])
      fun ha : a ≠ 0 => _
  suffices a * ↑(norm_unit a) = a * ↑u * ↑(norm_unit a) * ↑u⁻¹ by
    simpa only [← normalize_apply, ← mul_assoc, ← norm_unit_mul ha u.ne_zero, ← norm_unit_coe_units]
  calc a * ↑(norm_unit a) = a * ↑(norm_unit a) * ↑u * ↑u⁻¹ :=
      (Units.mul_inv_cancel_right _ _).symm _ = a * ↑u * ↑(norm_unit a) * ↑u⁻¹ := by
      rw [mul_right_commₓ a]

theorem normalize_eq_normalize_iff {x y : α} : normalize x = normalize y ↔ x ∣ y ∧ y ∣ x :=
  ⟨fun h => ⟨Units.dvd_mul_right.1 ⟨_, h.symm⟩, Units.dvd_mul_right.1 ⟨_, h⟩⟩, fun ⟨hxy, hyx⟩ =>
    normalize_eq_normalize hxy hyx⟩

theorem dvd_antisymm_of_normalize_eq {a b : α} (ha : normalize a = a) (hb : normalize b = b) (hab : a ∣ b)
    (hba : b ∣ a) : a = b :=
  ha ▸ hb ▸ normalize_eq_normalize hab hba

--can be proven by simp
theorem dvd_normalize_iff {a b : α} : a ∣ normalize b ↔ a ∣ b :=
  Units.dvd_mul_right

--can be proven by simp
theorem normalize_dvd_iff {a b : α} : normalize a ∣ b ↔ a ∣ b :=
  Units.mul_right_dvd

end NormalizationMonoid

namespace Associates

variable [CancelCommMonoidWithZero α] [NormalizationMonoid α]

attribute [local instance] Associated.setoid

/-- Maps an element of `associates` back to the normalized element of its associate class -/
protected def out : Associates α → α :=
  (Quotientₓ.lift (normalize : α → α)) fun a b ⟨u, hu⟩ =>
    hu ▸ normalize_eq_normalize ⟨_, rfl⟩ (Units.mul_right_dvd.2 <| dvd_refl a)

@[simp]
theorem out_mk (a : α) : (Associates.mk a).out = normalize a :=
  rfl

@[simp]
theorem out_one : (1 : Associates α).out = 1 :=
  normalize_one

theorem out_mul (a b : Associates α) : (a * b).out = a.out * b.out :=
  (Quotientₓ.induction_on₂ a b) fun a b => by
    simp only [← Associates.quotient_mk_eq_mk, ← out_mk, ← mk_mul_mk, ← normalize.map_mul]

theorem dvd_out_iff (a : α) (b : Associates α) : a ∣ b.out ↔ Associates.mk a ≤ b :=
  Quotientₓ.induction_on b <| by
    simp [← Associates.out_mk, ← Associates.quotient_mk_eq_mk, ← mk_le_mk_iff_dvd_iff]

theorem out_dvd_iff (a : α) (b : Associates α) : b.out ∣ a ↔ b ≤ Associates.mk a :=
  Quotientₓ.induction_on b <| by
    simp [← Associates.out_mk, ← Associates.quotient_mk_eq_mk, ← mk_le_mk_iff_dvd_iff]

@[simp]
theorem out_top : (⊤ : Associates α).out = 0 :=
  normalize_zero

@[simp]
theorem normalize_out (a : Associates α) : normalize a.out = a.out :=
  Quotientₓ.induction_on a normalize_idem

@[simp]
theorem mk_out (a : Associates α) : Associates.mk a.out = a :=
  Quotientₓ.induction_on a mk_normalize

theorem out_injective : Function.Injective (Associates.out : _ → α) :=
  Function.LeftInverse.injective mk_out

end Associates

/-- GCD monoid: a `cancel_comm_monoid_with_zero` with `gcd` (greatest common divisor) and
`lcm` (least common multiple) operations, determined up to a unit. The type class focuses on `gcd`
and we derive the corresponding `lcm` facts from `gcd`.
-/
@[protect_proj]
class GcdMonoid (α : Type _) [CancelCommMonoidWithZero α] where
  gcd : α → α → α
  lcm : α → α → α
  gcd_dvd_left : ∀ a b, gcd a b ∣ a
  gcd_dvd_right : ∀ a b, gcd a b ∣ b
  dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b
  gcd_mul_lcm : ∀ a b, Associated (gcd a b * lcm a b) (a * b)
  lcm_zero_left : ∀ a, lcm 0 a = 0
  lcm_zero_right : ∀ a, lcm a 0 = 0

/-- Normalized GCD monoid: a `cancel_comm_monoid_with_zero` with normalization and `gcd`
(greatest common divisor) and `lcm` (least common multiple) operations. In this setting `gcd` and
`lcm` form a bounded lattice on the associated elements where `gcd` is the infimum, `lcm` is the
supremum, `1` is bottom, and `0` is top. The type class focuses on `gcd` and we derive the
corresponding `lcm` facts from `gcd`.
-/
class NormalizedGcdMonoid (α : Type _) [CancelCommMonoidWithZero α] extends NormalizationMonoid α, GcdMonoid α where
  normalize_gcd : ∀ a b, normalize (gcd a b) = gcd a b
  normalize_lcm : ∀ a b, normalize (lcm a b) = lcm a b

export GcdMonoid (gcd lcm gcd_dvd_left gcd_dvd_right dvd_gcd lcm_zero_left lcm_zero_right)

attribute [simp] lcm_zero_left lcm_zero_right

section GcdMonoid

variable [CancelCommMonoidWithZero α]

@[simp]
theorem normalize_gcd [NormalizedGcdMonoid α] : ∀ a b : α, normalize (gcd a b) = gcd a b :=
  NormalizedGcdMonoid.normalize_gcd

theorem gcd_mul_lcm [GcdMonoid α] : ∀ a b : α, Associated (gcd a b * lcm a b) (a * b) :=
  GcdMonoid.gcd_mul_lcm

section Gcd

theorem dvd_gcd_iff [GcdMonoid α] (a b c : α) : a ∣ gcd b c ↔ a ∣ b ∧ a ∣ c :=
  Iff.intro (fun h => ⟨h.trans (gcd_dvd_left _ _), h.trans (gcd_dvd_right _ _)⟩) fun ⟨hab, hac⟩ => dvd_gcd hab hac

theorem gcd_comm [NormalizedGcdMonoid α] (a b : α) : gcd a b = gcd b a :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_comm' [GcdMonoid α] (a b : α) : Associated (gcd a b) (gcd b a) :=
  associated_of_dvd_dvd (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))
    (dvd_gcd (gcd_dvd_right _ _) (gcd_dvd_left _ _))

theorem gcd_assoc [NormalizedGcdMonoid α] (m n k : α) : gcd (gcd m n) k = gcd m (gcd n k) :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _)
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

theorem gcd_assoc' [GcdMonoid α] (m n k : α) : Associated (gcd (gcd m n) k) (gcd m (gcd n k)) :=
  associated_of_dvd_dvd
    (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_left m n))
      (dvd_gcd ((gcd_dvd_left (gcd m n) k).trans (gcd_dvd_right m n)) (gcd_dvd_right (gcd m n) k)))
    (dvd_gcd (dvd_gcd (gcd_dvd_left m (gcd n k)) ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_left n k)))
      ((gcd_dvd_right m (gcd n k)).trans (gcd_dvd_right n k)))

instance [NormalizedGcdMonoid α] : IsCommutative α gcd :=
  ⟨gcd_comm⟩

instance [NormalizedGcdMonoid α] : IsAssociative α gcd :=
  ⟨gcd_assoc⟩

theorem gcd_eq_normalize [NormalizedGcdMonoid α] {a b c : α} (habc : gcd a b ∣ c) (hcab : c ∣ gcd a b) :
    gcd a b = normalize c :=
  normalize_gcd a b ▸ normalize_eq_normalize habc hcab

@[simp]
theorem gcd_zero_left [NormalizedGcdMonoid α] (a : α) : gcd 0 a = normalize a :=
  gcd_eq_normalize (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

theorem gcd_zero_left' [GcdMonoid α] (a : α) : Associated (gcd 0 a) a :=
  associated_of_dvd_dvd (gcd_dvd_right 0 a) (dvd_gcd (dvd_zero _) (dvd_refl a))

@[simp]
theorem gcd_zero_right [NormalizedGcdMonoid α] (a : α) : gcd a 0 = normalize a :=
  gcd_eq_normalize (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

theorem gcd_zero_right' [GcdMonoid α] (a : α) : Associated (gcd a 0) a :=
  associated_of_dvd_dvd (gcd_dvd_left a 0) (dvd_gcd (dvd_refl a) (dvd_zero _))

@[simp]
theorem gcd_eq_zero_iff [GcdMonoid α] (a b : α) : gcd a b = 0 ↔ a = 0 ∧ b = 0 :=
  Iff.intro
    (fun h => by
      let ⟨ca, ha⟩ := gcd_dvd_left a b
      let ⟨cb, hb⟩ := gcd_dvd_right a b
      rw [h, zero_mul] at ha hb <;> exact ⟨ha, hb⟩)
    fun ⟨ha, hb⟩ => by
    rw [ha, hb, ← zero_dvd_iff]
    apply dvd_gcd <;> rfl

@[simp]
theorem gcd_one_left [NormalizedGcdMonoid α] (a : α) : gcd 1 a = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_left _ _) (one_dvd _)

@[simp]
theorem gcd_one_left' [GcdMonoid α] (a : α) : Associated (gcd 1 a) 1 :=
  associated_of_dvd_dvd (gcd_dvd_left _ _) (one_dvd _)

@[simp]
theorem gcd_one_right [NormalizedGcdMonoid α] (a : α) : gcd a 1 = 1 :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) normalize_one (gcd_dvd_right _ _) (one_dvd _)

@[simp]
theorem gcd_one_right' [GcdMonoid α] (a : α) : Associated (gcd a 1) 1 :=
  associated_of_dvd_dvd (gcd_dvd_right _ _) (one_dvd _)

theorem gcd_dvd_gcd [GcdMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : gcd a c ∣ gcd b d :=
  dvd_gcd ((gcd_dvd_left _ _).trans hab) ((gcd_dvd_right _ _).trans hcd)

@[simp]
theorem gcd_same [NormalizedGcdMonoid α] (a : α) : gcd a a = normalize a :=
  gcd_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_refl a))

@[simp]
theorem gcd_mul_left [NormalizedGcdMonoid α] (a b c : α) : gcd (a * b) (a * c) = normalize a * gcd b c :=
  (Classical.by_cases
      (by
        rintro rfl <;> simp only [← zero_mul, ← gcd_zero_left, ← normalize_zero]))
    fun ha : a ≠ 0 =>
    suffices gcd (a * b) (a * c) = normalize (a * gcd b c) by
      simpa only [← normalize.map_mul, ← normalize_gcd]
    let ⟨d, Eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
    gcd_eq_normalize
      (Eq.symm ▸ mul_dvd_mul_left a <|
        show d ∣ gcd b c from
          dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| Eq ▸ gcd_dvd_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| Eq ▸ gcd_dvd_right _ _))
      (dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _))

theorem gcd_mul_left' [GcdMonoid α] (a b c : α) : Associated (gcd (a * b) (a * c)) (a * gcd b c) := by
  obtain rfl | ha := eq_or_ne a 0
  · simp only [← zero_mul, ← gcd_zero_left']
    
  obtain ⟨d, eq⟩ := dvd_gcd (dvd_mul_right a b) (dvd_mul_right a c)
  apply associated_of_dvd_dvd
  · rw [Eq]
    apply mul_dvd_mul_left
    exact
      dvd_gcd ((mul_dvd_mul_iff_left ha).1 <| Eq ▸ gcd_dvd_left _ _)
        ((mul_dvd_mul_iff_left ha).1 <| Eq ▸ gcd_dvd_right _ _)
    
  · exact dvd_gcd (mul_dvd_mul_left a <| gcd_dvd_left _ _) (mul_dvd_mul_left a <| gcd_dvd_right _ _)
    

@[simp]
theorem gcd_mul_right [NormalizedGcdMonoid α] (a b c : α) : gcd (b * a) (c * a) = gcd b c * normalize a := by
  simp only [← mul_comm, ← gcd_mul_left]

@[simp]
theorem gcd_mul_right' [GcdMonoid α] (a b c : α) : Associated (gcd (b * a) (c * a)) (gcd b c * a) := by
  simp only [← mul_comm, ← gcd_mul_left']

theorem gcd_eq_left_iff [NormalizedGcdMonoid α] (a b : α) (h : normalize a = a) : gcd a b = a ↔ a ∣ b :=
  (Iff.intro fun eq => Eq ▸ gcd_dvd_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_gcd _ _) h (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) hab)

theorem gcd_eq_right_iff [NormalizedGcdMonoid α] (a b : α) (h : normalize b = b) : gcd a b = b ↔ b ∣ a := by
  simpa only [← gcd_comm a b] using gcd_eq_left_iff b a h

theorem gcd_dvd_gcd_mul_left [GcdMonoid α] (m n k : α) : gcd m n ∣ gcd (k * m) n :=
  gcd_dvd_gcd (dvd_mul_left _ _) dvd_rfl

theorem gcd_dvd_gcd_mul_right [GcdMonoid α] (m n k : α) : gcd m n ∣ gcd (m * k) n :=
  gcd_dvd_gcd (dvd_mul_right _ _) dvd_rfl

theorem gcd_dvd_gcd_mul_left_right [GcdMonoid α] (m n k : α) : gcd m n ∣ gcd m (k * n) :=
  gcd_dvd_gcd dvd_rfl (dvd_mul_left _ _)

theorem gcd_dvd_gcd_mul_right_right [GcdMonoid α] (m n k : α) : gcd m n ∣ gcd m (n * k) :=
  gcd_dvd_gcd dvd_rfl (dvd_mul_right _ _)

theorem Associated.gcd_eq_left [NormalizedGcdMonoid α] {m n : α} (h : Associated m n) (k : α) : gcd m k = gcd n k :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd h.Dvd dvd_rfl)
    (gcd_dvd_gcd h.symm.Dvd dvd_rfl)

theorem Associated.gcd_eq_right [NormalizedGcdMonoid α] {m n : α} (h : Associated m n) (k : α) : gcd k m = gcd k n :=
  dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) (gcd_dvd_gcd dvd_rfl h.Dvd)
    (gcd_dvd_gcd dvd_rfl h.symm.Dvd)

theorem dvd_gcd_mul_of_dvd_mul [GcdMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ gcd k m * n :=
  (dvd_gcd (dvd_mul_right _ n) H).trans (gcd_mul_right' n k m).Dvd

theorem dvd_mul_gcd_of_dvd_mul [GcdMonoid α] {m n k : α} (H : k ∣ m * n) : k ∣ m * gcd k n := by
  rw [mul_comm] at H⊢
  exact dvd_gcd_mul_of_dvd_mul H

/-- Represent a divisor of `m * n` as a product of a divisor of `m` and a divisor of `n`.

 Note: In general, this representation is highly non-unique. -/
theorem exists_dvd_and_dvd_of_dvd_mul [GcdMonoid α] {m n k : α} (H : k ∣ m * n) :
    ∃ (d₁ : _)(hd₁ : d₁ ∣ m)(d₂ : _)(hd₂ : d₂ ∣ n), k = d₁ * d₂ := by
  by_cases' h0 : gcd k m = 0
  · rw [gcd_eq_zero_iff] at h0
    rcases h0 with ⟨rfl, rfl⟩
    refine' ⟨0, dvd_refl 0, n, dvd_refl n, _⟩
    simp
    
  · obtain ⟨a, ha⟩ := gcd_dvd_left k m
    refine' ⟨gcd k m, gcd_dvd_right _ _, a, _, ha⟩
    suffices h : gcd k m * a ∣ gcd k m * n
    · cases' h with b hb
      use b
      rw [mul_assoc] at hb
      apply mul_left_cancel₀ h0 hb
      
    rw [← ha]
    exact dvd_gcd_mul_of_dvd_mul H
    

theorem gcd_mul_dvd_mul_gcd [GcdMonoid α] (k m n : α) : gcd k (m * n) ∣ gcd k m * gcd k n := by
  obtain ⟨m', hm', n', hn', h⟩ := exists_dvd_and_dvd_of_dvd_mul <| gcd_dvd_right k (m * n)
  replace h : gcd k (m * n) = m' * n' := h
  rw [h]
  have hm'n' : m' * n' ∣ k := h ▸ gcd_dvd_left _ _
  apply mul_dvd_mul
  · have hm'k : m' ∣ k := (dvd_mul_right m' n').trans hm'n'
    exact dvd_gcd hm'k hm'
    
  · have hn'k : n' ∣ k := (dvd_mul_left n' m').trans hm'n'
    exact dvd_gcd hn'k hn'
    

theorem gcd_pow_right_dvd_pow_gcd [GcdMonoid α] {a b : α} {k : ℕ} : gcd a (b ^ k) ∣ gcd a b ^ k := by
  by_cases' hg : gcd a b = 0
  · rw [gcd_eq_zero_iff] at hg
    rcases hg with ⟨rfl, rfl⟩
    exact (gcd_zero_left' (0 ^ k : α)).Dvd.trans (pow_dvd_pow_of_dvd (gcd_zero_left' (0 : α)).symm.Dvd _)
    
  · induction' k with k hk
    · simp only [← pow_zeroₓ]
      exact (gcd_one_right' a).Dvd
      
    rw [pow_succₓ, pow_succₓ]
    trans gcd a b * gcd a (b ^ k)
    apply gcd_mul_dvd_mul_gcd a b (b ^ k)
    exact (mul_dvd_mul_iff_left hg).mpr hk
    

theorem gcd_pow_left_dvd_pow_gcd [GcdMonoid α] {a b : α} {k : ℕ} : gcd (a ^ k) b ∣ gcd a b ^ k :=
  calc
    gcd (a ^ k) b ∣ gcd b (a ^ k) := (gcd_comm' _ _).Dvd
    _ ∣ gcd b a ^ k := gcd_pow_right_dvd_pow_gcd
    _ ∣ gcd a b ^ k := pow_dvd_pow_of_dvd (gcd_comm' _ _).Dvd _
    

theorem pow_dvd_of_mul_eq_pow [GcdMonoid α] {a b c d₁ d₂ : α} (ha : a ≠ 0) (hab : IsUnit (gcd a b)) {k : ℕ}
    (h : a * b = c ^ k) (hc : c = d₁ * d₂) (hd₁ : d₁ ∣ a) : d₁ ^ k ≠ 0 ∧ d₁ ^ k ∣ a := by
  have h1 : IsUnit (gcd (d₁ ^ k) b) := by
    apply is_unit_of_dvd_one
    trans gcd d₁ b ^ k
    · exact gcd_pow_left_dvd_pow_gcd
      
    · apply IsUnit.dvd
      apply IsUnit.pow
      apply is_unit_of_dvd_one
      apply dvd_trans _ hab.dvd
      apply gcd_dvd_gcd hd₁ (dvd_refl b)
      
  have h2 : d₁ ^ k ∣ a * b := by
    use d₂ ^ k
    rw [h, hc]
    exact mul_powₓ d₁ d₂ k
  rw [mul_comm] at h2
  have h3 : d₁ ^ k ∣ a := by
    apply (dvd_gcd_mul_of_dvd_mul h2).trans
    rw [IsUnit.mul_left_dvd _ _ _ h1]
  have h4 : d₁ ^ k ≠ 0 := by
    intro hdk
    rw [hdk] at h3
    apply absurd (zero_dvd_iff.mp h3) ha
  exact ⟨h4, h3⟩

theorem exists_associated_pow_of_mul_eq_pow [GcdMonoid α] {a b c : α} (hab : IsUnit (gcd a b)) {k : ℕ}
    (h : a * b = c ^ k) : ∃ d : α, Associated (d ^ k) a := by
  cases subsingleton_or_nontrivial α
  · use 0
    rw [Subsingleton.elimₓ a (0 ^ k)]
    
  by_cases' ha : a = 0
  · use 0
    rw [ha]
    obtain rfl | hk := k.eq_zero_or_pos
    · exfalso
      revert h
      rw [ha, zero_mul, pow_zeroₓ]
      apply zero_ne_one
      
    · rw [zero_pow hk]
      
    
  by_cases' hb : b = 0
  · use 1
    rw [one_pow]
    apply (associated_one_iff_is_unit.mpr hab).symm.trans
    rw [hb]
    exact gcd_zero_right' a
    
  obtain rfl | hk := k.eq_zero_or_pos
  · use 1
    rw [pow_zeroₓ] at h⊢
    use Units.mkOfMulEqOne _ _ h
    rw [Units.coe_mk_of_mul_eq_one, one_mulₓ]
    
  have hc : c ∣ a * b := by
    rw [h]
    exact dvd_pow_self _ hk.ne'
  obtain ⟨d₁, hd₁, d₂, hd₂, hc⟩ := exists_dvd_and_dvd_of_dvd_mul hc
  use d₁
  obtain ⟨h0₁, ⟨a', ha'⟩⟩ := pow_dvd_of_mul_eq_pow ha hab h hc hd₁
  rw [mul_comm] at h hc
  rw [(gcd_comm' a b).is_unit_iff] at hab
  obtain ⟨h0₂, ⟨b', hb'⟩⟩ := pow_dvd_of_mul_eq_pow hb hab h hc hd₂
  rw [ha', hb', hc, mul_powₓ] at h
  have h' : a' * b' = 1 := by
    apply (mul_right_inj' h0₁).mp
    rw [mul_oneₓ]
    apply (mul_right_inj' h0₂).mp
    rw [← h]
    rw [mul_assoc, mul_comm a', ← mul_assoc _ b', ← mul_assoc b', mul_comm b']
  use Units.mkOfMulEqOne _ _ h'
  rw [Units.coe_mk_of_mul_eq_one, ha']

theorem exists_eq_pow_of_mul_eq_pow [GcdMonoid α] [Unique αˣ] {a b c : α} (hab : IsUnit (gcd a b)) {k : ℕ}
    (h : a * b = c ^ k) : ∃ d : α, a = d ^ k :=
  let ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow hab h
  ⟨d, (associated_iff_eq.mp hd).symm⟩

theorem gcd_greatest {α : Type _} [CancelCommMonoidWithZero α] [NormalizedGcdMonoid α] {a b d : α} (hda : d ∣ a)
    (hdb : d ∣ b) (hd : ∀ e : α, e ∣ a → e ∣ b → e ∣ d) : GcdMonoid.gcd a b = normalize d := by
  have h := hd _ (GcdMonoid.gcd_dvd_left a b) (GcdMonoid.gcd_dvd_right a b)
  exact gcd_eq_normalize h (GcdMonoid.dvd_gcd hda hdb)

theorem gcd_greatest_associated {α : Type _} [CancelCommMonoidWithZero α] [GcdMonoid α] {a b d : α} (hda : d ∣ a)
    (hdb : d ∣ b) (hd : ∀ e : α, e ∣ a → e ∣ b → e ∣ d) : Associated d (GcdMonoid.gcd a b) := by
  have h := hd _ (GcdMonoid.gcd_dvd_left a b) (GcdMonoid.gcd_dvd_right a b)
  exact associated_of_dvd_dvd (GcdMonoid.dvd_gcd hda hdb) h

theorem is_unit_gcd_of_eq_mul_gcd {α : Type _} [CancelCommMonoidWithZero α] [GcdMonoid α] {x y x' y' : α}
    (ex : x = gcd x y * x') (ey : y = gcd x y * y') (h : gcd x y ≠ 0) : IsUnit (gcd x' y') := by
  rw [← associated_one_iff_is_unit]
  refine' Associated.of_mul_left _ (Associated.refl <| gcd x y) h
  convert (gcd_mul_left' _ _ _).symm using 1
  rw [← ex, ← ey, mul_oneₓ]

theorem extract_gcd {α : Type _} [CancelCommMonoidWithZero α] [GcdMonoid α] (x y : α) :
    ∃ x' y' d : α, x = d * x' ∧ y = d * y' ∧ IsUnit (gcd x' y') := by
  cases' eq_or_ne (gcd x y) 0 with h h
  · obtain ⟨rfl, rfl⟩ := (gcd_eq_zero_iff x y).1 h
    simp_rw [← associated_one_iff_is_unit]
    exact ⟨1, 1, 0, (zero_mul 1).symm, (zero_mul 1).symm, gcd_one_left' 1⟩
    
  obtain ⟨x', ex⟩ := gcd_dvd_left x y
  obtain ⟨y', ey⟩ := gcd_dvd_right x y
  exact ⟨x', y', gcd x y, ex, ey, is_unit_gcd_of_eq_mul_gcd ex ey h⟩

end Gcd

section Lcm

theorem lcm_dvd_iff [GcdMonoid α] {a b c : α} : lcm a b ∣ c ↔ a ∣ c ∧ b ∣ c := by
  by_cases' this : a = 0 ∨ b = 0
  · rcases this with (rfl | rfl) <;>
      simp (config := { contextual := true })only [← iff_def, ← lcm_zero_left, ← lcm_zero_right, ← zero_dvd_iff, ←
        dvd_zero, ← eq_self_iff_true, ← and_trueₓ, ← imp_true_iff]
    
  · obtain ⟨h1, h2⟩ := not_or_distrib.1 this
    have h : gcd a b ≠ 0 := fun H => h1 ((gcd_eq_zero_iff _ _).1 H).1
    rw [← mul_dvd_mul_iff_left h, (gcd_mul_lcm a b).dvd_iff_dvd_left, ← (gcd_mul_right' c a b).dvd_iff_dvd_right,
      dvd_gcd_iff, mul_comm b c, mul_dvd_mul_iff_left h1, mul_dvd_mul_iff_right h2, and_comm]
    

theorem dvd_lcm_left [GcdMonoid α] (a b : α) : a ∣ lcm a b :=
  (lcm_dvd_iff.1 (dvd_refl (lcm a b))).1

theorem dvd_lcm_right [GcdMonoid α] (a b : α) : b ∣ lcm a b :=
  (lcm_dvd_iff.1 (dvd_refl (lcm a b))).2

theorem lcm_dvd [GcdMonoid α] {a b c : α} (hab : a ∣ b) (hcb : c ∣ b) : lcm a c ∣ b :=
  lcm_dvd_iff.2 ⟨hab, hcb⟩

@[simp]
theorem lcm_eq_zero_iff [GcdMonoid α] (a b : α) : lcm a b = 0 ↔ a = 0 ∨ b = 0 :=
  Iff.intro
    (fun h : lcm a b = 0 => by
      have : Associated (a * b) 0 :=
        (gcd_mul_lcm a b).symm.trans <| by
          rw [h, mul_zero]
      simpa only [← associated_zero_iff_eq_zero, ← mul_eq_zero] )
    (by
      rintro (rfl | rfl) <;> [apply lcm_zero_left, apply lcm_zero_right])

@[simp]
theorem normalize_lcm [NormalizedGcdMonoid α] (a b : α) : normalize (lcm a b) = lcm a b :=
  NormalizedGcdMonoid.normalize_lcm a b

theorem lcm_comm [NormalizedGcdMonoid α] (a b : α) : lcm a b = lcm b a :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_comm' [GcdMonoid α] (a b : α) : Associated (lcm a b) (lcm b a) :=
  associated_of_dvd_dvd (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))
    (lcm_dvd (dvd_lcm_right _ _) (dvd_lcm_left _ _))

theorem lcm_assoc [NormalizedGcdMonoid α] (m n k : α) : lcm (lcm m n) k = lcm m (lcm n k) :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _)
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

theorem lcm_assoc' [GcdMonoid α] (m n k : α) : Associated (lcm (lcm m n) k) (lcm m (lcm n k)) :=
  associated_of_dvd_dvd
    (lcm_dvd (lcm_dvd (dvd_lcm_left _ _) ((dvd_lcm_left _ _).trans (dvd_lcm_right _ _)))
      ((dvd_lcm_right _ _).trans (dvd_lcm_right _ _)))
    (lcm_dvd ((dvd_lcm_left _ _).trans (dvd_lcm_left _ _))
      (lcm_dvd ((dvd_lcm_right _ _).trans (dvd_lcm_left _ _)) (dvd_lcm_right _ _)))

instance [NormalizedGcdMonoid α] : IsCommutative α lcm :=
  ⟨lcm_comm⟩

instance [NormalizedGcdMonoid α] : IsAssociative α lcm :=
  ⟨lcm_assoc⟩

theorem lcm_eq_normalize [NormalizedGcdMonoid α] {a b c : α} (habc : lcm a b ∣ c) (hcab : c ∣ lcm a b) :
    lcm a b = normalize c :=
  normalize_lcm a b ▸ normalize_eq_normalize habc hcab

theorem lcm_dvd_lcm [GcdMonoid α] {a b c d : α} (hab : a ∣ b) (hcd : c ∣ d) : lcm a c ∣ lcm b d :=
  lcm_dvd (hab.trans (dvd_lcm_left _ _)) (hcd.trans (dvd_lcm_right _ _))

@[simp]
theorem lcm_units_coe_left [NormalizedGcdMonoid α] (u : αˣ) (a : α) : lcm (↑u) a = normalize a :=
  lcm_eq_normalize (lcm_dvd Units.coe_dvd dvd_rfl) (dvd_lcm_right _ _)

@[simp]
theorem lcm_units_coe_right [NormalizedGcdMonoid α] (a : α) (u : αˣ) : lcm a ↑u = normalize a :=
  (lcm_comm a u).trans <| lcm_units_coe_left _ _

@[simp]
theorem lcm_one_left [NormalizedGcdMonoid α] (a : α) : lcm 1 a = normalize a :=
  lcm_units_coe_left 1 a

@[simp]
theorem lcm_one_right [NormalizedGcdMonoid α] (a : α) : lcm a 1 = normalize a :=
  lcm_units_coe_right a 1

@[simp]
theorem lcm_same [NormalizedGcdMonoid α] (a : α) : lcm a a = normalize a :=
  lcm_eq_normalize (lcm_dvd dvd_rfl dvd_rfl) (dvd_lcm_left _ _)

@[simp]
theorem lcm_eq_one_iff [NormalizedGcdMonoid α] (a b : α) : lcm a b = 1 ↔ a ∣ 1 ∧ b ∣ 1 :=
  Iff.intro (fun eq => Eq ▸ ⟨dvd_lcm_left _ _, dvd_lcm_right _ _⟩) fun ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ =>
    show lcm (Units.mkOfMulEqOne a c hc.symm : α) (Units.mkOfMulEqOne b d hd.symm) = 1 by
      rw [lcm_units_coe_left, normalize_coe_units]

@[simp]
theorem lcm_mul_left [NormalizedGcdMonoid α] (a b c : α) : lcm (a * b) (a * c) = normalize a * lcm b c :=
  (Classical.by_cases
      (by
        rintro rfl <;> simp only [← zero_mul, ← lcm_zero_left, ← normalize_zero]))
    fun ha : a ≠ 0 =>
    suffices lcm (a * b) (a * c) = normalize (a * lcm b c) by
      simpa only [← normalize.map_mul, ← normalize_lcm]
    have : a ∣ lcm (a * b) (a * c) := (dvd_mul_right _ _).trans (dvd_lcm_left _ _)
    let ⟨d, Eq⟩ := this
    lcm_eq_normalize (lcm_dvd (mul_dvd_mul_left a (dvd_lcm_left _ _)) (mul_dvd_mul_left a (dvd_lcm_right _ _)))
      (Eq.symm ▸
        (mul_dvd_mul_left a <|
          lcm_dvd ((mul_dvd_mul_iff_left ha).1 <| Eq ▸ dvd_lcm_left _ _)
            ((mul_dvd_mul_iff_left ha).1 <| Eq ▸ dvd_lcm_right _ _)))

@[simp]
theorem lcm_mul_right [NormalizedGcdMonoid α] (a b c : α) : lcm (b * a) (c * a) = lcm b c * normalize a := by
  simp only [← mul_comm, ← lcm_mul_left]

theorem lcm_eq_left_iff [NormalizedGcdMonoid α] (a b : α) (h : normalize a = a) : lcm a b = a ↔ b ∣ a :=
  (Iff.intro fun eq => Eq ▸ dvd_lcm_right _ _) fun hab =>
    dvd_antisymm_of_normalize_eq (normalize_lcm _ _) h (lcm_dvd (dvd_refl a) hab) (dvd_lcm_left _ _)

theorem lcm_eq_right_iff [NormalizedGcdMonoid α] (a b : α) (h : normalize b = b) : lcm a b = b ↔ a ∣ b := by
  simpa only [← lcm_comm b a] using lcm_eq_left_iff b a h

theorem lcm_dvd_lcm_mul_left [GcdMonoid α] (m n k : α) : lcm m n ∣ lcm (k * m) n :=
  lcm_dvd_lcm (dvd_mul_left _ _) dvd_rfl

theorem lcm_dvd_lcm_mul_right [GcdMonoid α] (m n k : α) : lcm m n ∣ lcm (m * k) n :=
  lcm_dvd_lcm (dvd_mul_right _ _) dvd_rfl

theorem lcm_dvd_lcm_mul_left_right [GcdMonoid α] (m n k : α) : lcm m n ∣ lcm m (k * n) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_left _ _)

theorem lcm_dvd_lcm_mul_right_right [GcdMonoid α] (m n k : α) : lcm m n ∣ lcm m (n * k) :=
  lcm_dvd_lcm dvd_rfl (dvd_mul_right _ _)

theorem lcm_eq_of_associated_left [NormalizedGcdMonoid α] {m n : α} (h : Associated m n) (k : α) : lcm m k = lcm n k :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm h.Dvd dvd_rfl)
    (lcm_dvd_lcm h.symm.Dvd dvd_rfl)

theorem lcm_eq_of_associated_right [NormalizedGcdMonoid α] {m n : α} (h : Associated m n) (k : α) : lcm k m = lcm k n :=
  dvd_antisymm_of_normalize_eq (normalize_lcm _ _) (normalize_lcm _ _) (lcm_dvd_lcm dvd_rfl h.Dvd)
    (lcm_dvd_lcm dvd_rfl h.symm.Dvd)

end Lcm

namespace GcdMonoid

theorem prime_of_irreducible [GcdMonoid α] {x : α} (hi : Irreducible x) : Prime x :=
  ⟨hi.ne_zero,
    ⟨hi.1, fun a b h => by
      cases' gcd_dvd_left x a with y hy
      cases' hi.is_unit_or_is_unit hy with hu hu
      · right
        trans gcd (x * b) (a * b)
        apply dvd_gcd (dvd_mul_right x b) h
        rw [(gcd_mul_right' b x a).dvd_iff_dvd_left]
        exact (associated_unit_mul_left _ _ hu).Dvd
        
      · left
        rw [hy]
        exact dvd_trans (associated_mul_unit_left _ _ hu).Dvd (gcd_dvd_right x a)
        ⟩⟩

theorem irreducible_iff_prime [GcdMonoid α] {p : α} : Irreducible p ↔ Prime p :=
  ⟨prime_of_irreducible, Prime.irreducible⟩

end GcdMonoid

end GcdMonoid

section UniqueUnit

variable [CancelCommMonoidWithZero α] [Unique αˣ]

-- see Note [lower instance priority]
instance (priority := 100) normalizationMonoidOfUniqueUnits : NormalizationMonoid α where
  normUnit := fun x => 1
  norm_unit_zero := rfl
  norm_unit_mul := fun x y hx hy => (mul_oneₓ 1).symm
  norm_unit_coe_units := fun u => Subsingleton.elimₓ _ _

@[simp]
theorem norm_unit_eq_one (x : α) : normUnit x = 1 :=
  rfl

@[simp]
theorem normalize_eq (x : α) : normalize x = x :=
  mul_oneₓ x

/-- If a monoid's only unit is `1`, then it is isomorphic to its associates. -/
@[simps]
def associatesEquivOfUniqueUnits : Associates α ≃* α where
  toFun := Associates.out
  invFun := Associates.mk
  left_inv := Associates.mk_out
  right_inv := fun t => (Associates.out_mk _).trans <| normalize_eq _
  map_mul' := Associates.out_mul

end UniqueUnit

section IsDomain

variable [CommRingₓ α] [IsDomain α] [NormalizedGcdMonoid α]

theorem gcd_eq_of_dvd_sub_right {a b c : α} (h : a ∣ b - c) : gcd a b = gcd a c := by
  apply dvd_antisymm_of_normalize_eq (normalize_gcd _ _) (normalize_gcd _ _) <;>
    rw [dvd_gcd_iff] <;> refine' ⟨gcd_dvd_left _ _, _⟩
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a b with ⟨e, he⟩
    rcases gcd_dvd_left a b with ⟨f, hf⟩
    use e - f * d
    rw [mul_sub, ← he, ← mul_assoc, ← hf, ← hd, sub_sub_cancel]
    
  · rcases h with ⟨d, hd⟩
    rcases gcd_dvd_right a c with ⟨e, he⟩
    rcases gcd_dvd_left a c with ⟨f, hf⟩
    use e + f * d
    rw [mul_addₓ, ← he, ← mul_assoc, ← hf, ← hd, ← add_sub_assoc, add_commₓ c b, add_sub_cancel]
    

theorem gcd_eq_of_dvd_sub_left {a b c : α} (h : a ∣ b - c) : gcd b a = gcd c a := by
  rw [gcd_comm _ a, gcd_comm _ a, gcd_eq_of_dvd_sub_right h]

end IsDomain

section Constructors

noncomputable section

open Associates

variable [CancelCommMonoidWithZero α]

private theorem map_mk_unit_aux [DecidableEq α] {f : Associates α →* α} (hinv : Function.RightInverse f Associates.mk)
    (a : α) : a * ↑(Classical.some (associated_map_mk hinv a)) = f (Associates.mk a) :=
  Classical.some_spec (associated_map_mk hinv a)

/-- Define `normalization_monoid` on a structure from a `monoid_hom` inverse to `associates.mk`. -/
def normalizationMonoidOfMonoidHomRightInverse [DecidableEq α] (f : Associates α →* α)
    (hinv : Function.RightInverse f Associates.mk) : NormalizationMonoid α where
  normUnit := fun a =>
    if a = 0 then 1 else Classical.some (Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm)
  norm_unit_zero := if_pos rfl
  norm_unit_mul := fun a b ha hb => by
    rw [if_neg (mul_ne_zero ha hb), if_neg ha, if_neg hb, Units.ext_iff, Units.coe_mul]
    suffices
      a * b * ↑(Classical.some (associated_map_mk hinv (a * b))) =
        a * ↑(Classical.some (associated_map_mk hinv a)) * (b * ↑(Classical.some (associated_map_mk hinv b)))
      by
      apply mul_left_cancel₀ (mul_ne_zero ha hb) _
      simpa only [← mul_assoc, ← mul_comm, ← mul_left_commₓ] using this
    rw [map_mk_unit_aux hinv a, map_mk_unit_aux hinv (a * b), map_mk_unit_aux hinv b, ← MonoidHom.map_mul,
      Associates.mk_mul_mk]
  norm_unit_coe_units := fun u => by
    nontriviality α
    rw [if_neg (Units.ne_zero u), Units.ext_iff]
    apply mul_left_cancel₀ (Units.ne_zero u)
    rw [Units.mul_inv, map_mk_unit_aux hinv u,
      Associates.mk_eq_mk_iff_associated.2 (associated_one_iff_is_unit.2 ⟨u, rfl⟩), Associates.mk_one,
      MonoidHom.map_one]

/-- Define `gcd_monoid` on a structure just from the `gcd` and its properties. -/
noncomputable def gcdMonoidOfGcd [DecidableEq α] (gcd : α → α → α) (gcd_dvd_left : ∀ a b, gcd a b ∣ a)
    (gcd_dvd_right : ∀ a b, gcd a b ∣ b) (dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b) : GcdMonoid α :=
  { gcd, gcd_dvd_left, gcd_dvd_right, dvd_gcd := fun a b c => dvd_gcd,
    lcm := fun a b => if a = 0 then 0 else Classical.some ((gcd_dvd_left a b).trans (Dvd.intro b rfl)),
    gcd_mul_lcm := fun a b => by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
        
      · rw [← Classical.some_spec ((gcd_dvd_left a b).trans (Dvd.intro b rfl))]
        ,
    lcm_zero_left := fun a => if_pos rfl,
    lcm_zero_right := fun a => by
      split_ifs with a0
      · rfl
        
      have h := (Classical.some_spec ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl))).symm
      have a0' : gcd a 0 ≠ 0 := by
        contrapose! a0
        rw [← associated_zero_iff_eq_zero, ← a0]
        exact associated_of_dvd_dvd (dvd_gcd (dvd_refl a) (dvd_zero a)) (gcd_dvd_left _ _)
      apply Or.resolve_left (mul_eq_zero.1 _) a0'
      rw [h, mul_zero] }

/-- Define `normalized_gcd_monoid` on a structure just from the `gcd` and its properties. -/
noncomputable def normalizedGcdMonoidOfGcd [NormalizationMonoid α] [DecidableEq α] (gcd : α → α → α)
    (gcd_dvd_left : ∀ a b, gcd a b ∣ a) (gcd_dvd_right : ∀ a b, gcd a b ∣ b)
    (dvd_gcd : ∀ {a b c}, a ∣ c → a ∣ b → a ∣ gcd c b) (normalize_gcd : ∀ a b, normalize (gcd a b) = gcd a b) :
    NormalizedGcdMonoid α :=
  { (inferInstance : NormalizationMonoid α) with gcd, gcd_dvd_left, gcd_dvd_right, dvd_gcd := fun a b c => dvd_gcd,
    normalize_gcd,
    lcm := fun a b =>
      if a = 0 then 0 else Classical.some (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl))),
    normalize_lcm := fun a b => by
      dsimp' [← normalize]
      split_ifs with a0
      · exact @normalize_zero α _ _
        
      · have := (Classical.some_spec (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))).symm
        set l := Classical.some (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))
        obtain rfl | hb := eq_or_ne b 0
        · simp only [← normalize_zero, ← mul_zero, ← mul_eq_zero] at this
          obtain ha | hl := this
          · apply (a0 _).elim
            rw [← zero_dvd_iff, ← ha]
            exact gcd_dvd_left _ _
            
          · convert @normalize_zero α _ _
            
          
        have h1 : gcd a b ≠ 0 := by
          have hab : a * b ≠ 0 := mul_ne_zero a0 hb
          contrapose! hab
          rw [← normalize_eq_zero, ← this, hab, zero_mul]
        have h2 : normalize (gcd a b * l) = gcd a b * l := by
          rw [this, normalize_idem]
        rw [← normalize_gcd] at this
        rwa [normalize.map_mul, normalize_gcd, mul_right_inj' h1] at h2
        ,
    gcd_mul_lcm := fun a b => by
      split_ifs with a0
      · rw [mul_zero, a0, zero_mul]
        
      · rw [← Classical.some_spec (dvd_normalize_iff.2 ((gcd_dvd_left a b).trans (Dvd.intro b rfl)))]
        exact normalize_associated (a * b)
        ,
    lcm_zero_left := fun a => if_pos rfl,
    lcm_zero_right := fun a => by
      split_ifs with a0
      · rfl
        
      rw [← normalize_eq_zero] at a0
      have h := (Classical.some_spec (dvd_normalize_iff.2 ((gcd_dvd_left a 0).trans (Dvd.intro 0 rfl)))).symm
      have gcd0 : gcd a 0 = normalize a := by
        rw [← normalize_gcd]
        exact normalize_eq_normalize (gcd_dvd_left _ _) (dvd_gcd (dvd_refl a) (dvd_zero a))
      rw [← gcd0] at a0
      apply Or.resolve_left (mul_eq_zero.1 _) a0
      rw [h, mul_zero, normalize_zero] }

/-- Define `gcd_monoid` on a structure just from the `lcm` and its properties. -/
noncomputable def gcdMonoidOfLcm [DecidableEq α] (lcm : α → α → α) (dvd_lcm_left : ∀ a b, a ∣ lcm a b)
    (dvd_lcm_right : ∀ a b, b ∣ lcm a b) (lcm_dvd : ∀ {a b c}, c ∣ a → b ∣ a → lcm c b ∣ a) : GcdMonoid α :=
  let exists_gcd := fun a b => lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
  { lcm, gcd := fun a b => if a = 0 then b else if b = 0 then a else Classical.some (exists_gcd a b),
    gcd_mul_lcm := fun a b => by
      split_ifs
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
        
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero]
        
      rw [mul_comm, ← Classical.some_spec (exists_gcd a b)],
    lcm_zero_left := fun a => eq_zero_of_zero_dvd (dvd_lcm_left _ _),
    lcm_zero_right := fun a => eq_zero_of_zero_dvd (dvd_lcm_right _ _),
    gcd_dvd_left := fun a b => by
      split_ifs with h h_1
      · rw [h]
        apply dvd_zero
        
      · exact dvd_rfl
        
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h <;> tauto
      rw [← mul_dvd_mul_iff_left h0, ← Classical.some_spec (exists_gcd a b), mul_comm, mul_dvd_mul_iff_right h]
      apply dvd_lcm_right,
    gcd_dvd_right := fun a b => by
      split_ifs with h h_1
      · exact dvd_rfl
        
      · rw [h_1]
        apply dvd_zero
        
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h <;> tauto
      rw [← mul_dvd_mul_iff_left h0, ← Classical.some_spec (exists_gcd a b), mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left,
    dvd_gcd := fun a b c ac ab => by
      split_ifs
      · exact ab
        
      · exact ac
        
      have h0 : lcm c b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h <;> tauto
      rw [← mul_dvd_mul_iff_left h0, ← Classical.some_spec (exists_gcd c b)]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at h_1
      push_neg  at h_1
      rw [mul_comm a, ← mul_assoc, mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm, mul_dvd_mul_iff_right h_1.2]
      apply ac }

/-- Define `normalized_gcd_monoid` on a structure just from the `lcm` and its properties. -/
noncomputable def normalizedGcdMonoidOfLcm [NormalizationMonoid α] [DecidableEq α] (lcm : α → α → α)
    (dvd_lcm_left : ∀ a b, a ∣ lcm a b) (dvd_lcm_right : ∀ a b, b ∣ lcm a b)
    (lcm_dvd : ∀ {a b c}, c ∣ a → b ∣ a → lcm c b ∣ a) (normalize_lcm : ∀ a b, normalize (lcm a b) = lcm a b) :
    NormalizedGcdMonoid α :=
  let exists_gcd := fun a b => dvd_normalize_iff.2 (lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl))
  { (inferInstance : NormalizationMonoid α) with lcm,
    gcd := fun a b => if a = 0 then normalize b else if b = 0 then normalize a else Classical.some (exists_gcd a b),
    gcd_mul_lcm := fun a b => by
      split_ifs with h h_1
      · rw [h, eq_zero_of_zero_dvd (dvd_lcm_left _ _), mul_zero, zero_mul]
        
      · rw [h_1, eq_zero_of_zero_dvd (dvd_lcm_right _ _), mul_zero, mul_zero]
        
      rw [mul_comm, ← Classical.some_spec (exists_gcd a b)]
      exact normalize_associated (a * b),
    normalize_lcm,
    normalize_gcd := fun a b => by
      dsimp' [← normalize]
      split_ifs with h h_1
      · apply normalize_idem
        
      · apply normalize_idem
        
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h <;> tauto
      apply mul_left_cancel₀ h0
      refine' trans _ (Classical.some_spec (exists_gcd a b))
      conv_lhs => congr rw [← normalize_lcm a b]
      erw [← normalize.map_mul, ← Classical.some_spec (exists_gcd a b), normalize_idem],
    lcm_zero_left := fun a => eq_zero_of_zero_dvd (dvd_lcm_left _ _),
    lcm_zero_right := fun a => eq_zero_of_zero_dvd (dvd_lcm_right _ _),
    gcd_dvd_left := fun a b => by
      split_ifs
      · rw [h]
        apply dvd_zero
        
      · exact (normalize_associated _).Dvd
        
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h <;> tauto
      rw [← mul_dvd_mul_iff_left h0, ← Classical.some_spec (exists_gcd a b), normalize_dvd_iff, mul_comm,
        mul_dvd_mul_iff_right h]
      apply dvd_lcm_right,
    gcd_dvd_right := fun a b => by
      split_ifs
      · exact (normalize_associated _).Dvd
        
      · rw [h_1]
        apply dvd_zero
        
      have h0 : lcm a b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left a rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h <;> tauto
      rw [← mul_dvd_mul_iff_left h0, ← Classical.some_spec (exists_gcd a b), normalize_dvd_iff,
        mul_dvd_mul_iff_right h_1]
      apply dvd_lcm_left,
    dvd_gcd := fun a b c ac ab => by
      split_ifs
      · apply dvd_normalize_iff.2 ab
        
      · apply dvd_normalize_iff.2 ac
        
      have h0 : lcm c b ≠ 0 := by
        intro con
        have h := lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl)
        rw [con, zero_dvd_iff, mul_eq_zero] at h
        cases h <;> tauto
      rw [← mul_dvd_mul_iff_left h0, ←
        Classical.some_spec (dvd_normalize_iff.2 (lcm_dvd (Dvd.intro b rfl) (Dvd.intro_left c rfl))), dvd_normalize_iff]
      rcases ab with ⟨d, rfl⟩
      rw [mul_eq_zero] at h_1
      push_neg  at h_1
      rw [mul_comm a, ← mul_assoc, mul_dvd_mul_iff_right h_1.1]
      apply lcm_dvd (Dvd.intro d rfl)
      rw [mul_comm, mul_dvd_mul_iff_right h_1.2]
      apply ac }

/-- Define a `gcd_monoid` structure on a monoid just from the existence of a `gcd`. -/
noncomputable def gcdMonoidOfExistsGcd [DecidableEq α] (h : ∀ a b : α, ∃ c : α, ∀ d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) :
    GcdMonoid α :=
  gcdMonoidOfGcd (fun a b => Classical.some (h a b))
    (fun a b => ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).2) fun a b c ac ab =>
    (Classical.some_spec (h c b) a).1 ⟨ac, ab⟩

/-- Define a `normalized_gcd_monoid` structure on a monoid just from the existence of a `gcd`. -/
noncomputable def normalizedGcdMonoidOfExistsGcd [NormalizationMonoid α] [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, d ∣ a ∧ d ∣ b ↔ d ∣ c) : NormalizedGcdMonoid α :=
  normalizedGcdMonoidOfGcd (fun a b => normalize (Classical.some (h a b)))
    (fun a b => normalize_dvd_iff.2 ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).1)
    (fun a b => normalize_dvd_iff.2 ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).2)
    (fun a b c ac ab => dvd_normalize_iff.2 ((Classical.some_spec (h c b) a).1 ⟨ac, ab⟩)) fun a b => normalize_idem _

/-- Define a `gcd_monoid` structure on a monoid just from the existence of an `lcm`. -/
noncomputable def gcdMonoidOfExistsLcm [DecidableEq α] (h : ∀ a b : α, ∃ c : α, ∀ d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) :
    GcdMonoid α :=
  gcdMonoidOfLcm (fun a b => Classical.some (h a b))
    (fun a b => ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).1)
    (fun a b => ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).2) fun a b c ac ab =>
    (Classical.some_spec (h c b) a).1 ⟨ac, ab⟩

/-- Define a `normalized_gcd_monoid` structure on a monoid just from the existence of an `lcm`. -/
noncomputable def normalizedGcdMonoidOfExistsLcm [NormalizationMonoid α] [DecidableEq α]
    (h : ∀ a b : α, ∃ c : α, ∀ d : α, a ∣ d ∧ b ∣ d ↔ c ∣ d) : NormalizedGcdMonoid α :=
  normalizedGcdMonoidOfLcm (fun a b => normalize (Classical.some (h a b)))
    (fun a b => dvd_normalize_iff.2 ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).1)
    (fun a b => dvd_normalize_iff.2 ((Classical.some_spec (h a b) (Classical.some (h a b))).2 dvd_rfl).2)
    (fun a b c ac ab => normalize_dvd_iff.2 ((Classical.some_spec (h c b) a).1 ⟨ac, ab⟩)) fun a b => normalize_idem _

end Constructors

namespace CommGroupWithZero

variable (G₀ : Type _) [CommGroupWithZero G₀] [DecidableEq G₀]

-- see Note [lower instance priority]
instance (priority := 100) : NormalizedGcdMonoid G₀ where
  normUnit := fun x => if h : x = 0 then 1 else (Units.mk0 x h)⁻¹
  norm_unit_zero := dif_pos rfl
  norm_unit_mul := fun x y x0 y0 =>
    Units.eq_iff.1
      (by
        simp [← x0, ← y0, ← mul_comm])
  norm_unit_coe_units := fun u => by
    rw [dif_neg (Units.ne_zero _), Units.mk0_coe]
    infer_instance
  gcd := fun a b => if a = 0 ∧ b = 0 then 0 else 1
  lcm := fun a b => if a = 0 ∨ b = 0 then 0 else 1
  gcd_dvd_left := fun a b => by
    split_ifs with h
    · rw [h.1]
      
    · exact one_dvd _
      
  gcd_dvd_right := fun a b => by
    split_ifs with h
    · rw [h.2]
      
    · exact one_dvd _
      
  dvd_gcd := fun a b c hac hab => by
    split_ifs with h
    · apply dvd_zero
      
    cases' not_and_distrib.mp h with h h <;>
      refine' is_unit_iff_dvd_one.mp (is_unit_of_dvd_unit _ (IsUnit.mk0 _ h)) <;> assumption
  gcd_mul_lcm := fun a b => by
    by_cases' ha : a = 0
    · simp [← ha]
      
    by_cases' hb : b = 0
    · simp [← hb]
      
    rw [if_neg (not_and_of_not_left _ ha), one_mulₓ, if_neg (not_orₓ ha hb)]
    exact (associated_one_iff_is_unit.mpr ((IsUnit.mk0 _ ha).mul (IsUnit.mk0 _ hb))).symm
  lcm_zero_left := fun b => if_pos (Or.inl rfl)
  lcm_zero_right := fun a => if_pos (Or.inr rfl)
  -- `split_ifs` wants to split `normalize`, so handle the cases manually
  normalize_gcd := fun a b =>
    if h : a = 0 ∧ b = 0 then by
      simp [← if_pos h]
    else by
      simp [← if_neg h]
  normalize_lcm := fun a b =>
    if h : a = 0 ∨ b = 0 then by
      simp [← if_pos h]
    else by
      simp [← if_neg h]

@[simp]
theorem coe_norm_unit {a : G₀} (h0 : a ≠ 0) : (↑(normUnit a) : G₀) = a⁻¹ := by
  simp [← norm_unit, ← h0]

theorem normalize_eq_one {a : G₀} (h0 : a ≠ 0) : normalize a = 1 := by
  simp [← normalize_apply, ← h0]

end CommGroupWithZero

