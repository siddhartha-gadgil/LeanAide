/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Jens Wagemaker
-/
import Mathbin.Algebra.Divisibility
import Mathbin.Algebra.GroupPower.Lemmas
import Mathbin.Algebra.Invertible
import Mathbin.Order.Atoms

/-!
# Associated, prime, and irreducible elements.
-/


variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

section Prime

variable [CommMonoidWithZero α]

/-- prime element of a `comm_monoid_with_zero` -/
def Prime (p : α) : Prop :=
  p ≠ 0 ∧ ¬IsUnit p ∧ ∀ a b, p ∣ a * b → p ∣ a ∨ p ∣ b

namespace Prime

variable {p : α} (hp : Prime p)

include hp

theorem ne_zero : p ≠ 0 :=
  hp.1

theorem not_unit : ¬IsUnit p :=
  hp.2.1

theorem not_dvd_one : ¬p ∣ 1 :=
  mt (is_unit_of_dvd_one _) hp.not_unit

theorem ne_one : p ≠ 1 := fun h => hp.2.1 (h.symm ▸ is_unit_one)

theorem dvd_or_dvd (hp : Prime p) {a b : α} (h : p ∣ a * b) : p ∣ a ∨ p ∣ b :=
  hp.2.2 a b h

theorem dvd_of_dvd_pow (hp : Prime p) {a : α} {n : ℕ} (h : p ∣ a ^ n) : p ∣ a := by
  induction' n with n ih
  · rw [pow_zeroₓ] at h
    have := is_unit_of_dvd_one _ h
    have := not_unit hp
    contradiction
    
  rw [pow_succₓ] at h
  cases' dvd_or_dvd hp h with dvd_a dvd_pow
  · assumption
    
  exact ih dvd_pow

end Prime

@[simp]
theorem not_prime_zero : ¬Prime (0 : α) := fun h => h.ne_zero rfl

@[simp]
theorem not_prime_one : ¬Prime (1 : α) := fun h => h.not_unit is_unit_one

section Map

variable [CommMonoidWithZero β] {F : Type _} {G : Type _} [MonoidWithZeroHomClass F α β] [MulHomClass G β α] (f : F)
  (g : G) {p : α}

theorem comap_prime (hinv : ∀ a, g (f a : β) = a) (hp : Prime (f p)) : Prime p :=
  ⟨fun h =>
    hp.1 <| by
      simp [← h],
    fun h => hp.2.1 <| h.map f, fun a b h => by
    refine'
        (hp.2.2 (f a) (f b) <| by
              convert map_dvd f h
              simp ).imp
          _ _ <;>
      · intro h
        convert ← map_dvd g h <;> apply hinv
        ⟩

theorem MulEquiv.prime_iff (e : α ≃* β) : Prime p ↔ Prime (e p) :=
  ⟨fun h =>
    (comap_prime e.symm e fun a => by
        simp ) <|
      (e.symm_apply_apply p).substr h,
    comap_prime e e.symm fun a => by
      simp ⟩

end Map

end Prime

theorem Prime.left_dvd_or_dvd_right_of_dvd_mul [CancelCommMonoidWithZero α] {p : α} (hp : Prime p) {a b : α} :
    a ∣ p * b → p ∣ a ∨ a ∣ b := by
  rintro ⟨c, hc⟩
  rcases hp.2.2 a c (hc ▸ dvd_mul_right _ _) with (h | ⟨x, rfl⟩)
  · exact Or.inl h
    
  · rw [mul_left_commₓ, mul_right_inj' hp.ne_zero] at hc
    exact Or.inr (hc.symm ▸ dvd_mul_right _ _)
    

theorem Prime.pow_dvd_of_dvd_mul_left [CancelCommMonoidWithZero α] {p a b : α} (hp : Prime p) (n : ℕ) (h : ¬p ∣ a)
    (h' : p ^ n ∣ a * b) : p ^ n ∣ b := by
  induction' n with n ih
  · rw [pow_zeroₓ]
    exact one_dvd b
    
  · obtain ⟨c, rfl⟩ := ih (dvd_trans (pow_dvd_pow p n.le_succ) h')
    rw [pow_succ'ₓ]
    apply mul_dvd_mul_left _ ((hp.dvd_or_dvd _).resolve_left h)
    rwa [← mul_dvd_mul_iff_left (pow_ne_zero n hp.ne_zero), ← pow_succ'ₓ, mul_left_commₓ]
    

theorem Prime.pow_dvd_of_dvd_mul_right [CancelCommMonoidWithZero α] {p a b : α} (hp : Prime p) (n : ℕ) (h : ¬p ∣ b)
    (h' : p ^ n ∣ a * b) : p ^ n ∣ a := by
  rw [mul_comm] at h'
  exact hp.pow_dvd_of_dvd_mul_left n h h'

theorem Prime.dvd_of_pow_dvd_pow_mul_pow_of_square_not_dvd [CancelCommMonoidWithZero α] {p a b : α} {n : ℕ}
    (hp : Prime p) (hpow : p ^ n.succ ∣ a ^ n.succ * b ^ n) (hb : ¬p ^ 2 ∣ b) : p ∣ a := by
  -- Suppose `p ∣ b`, write `b = p * x` and `hy : a ^ n.succ * b ^ n = p ^ n.succ * y`.
  cases' hp.dvd_or_dvd ((dvd_pow_self p (Nat.succ_ne_zero n)).trans hpow) with H hbdiv
  · exact hp.dvd_of_dvd_pow H
    
  obtain ⟨x, rfl⟩ := hp.dvd_of_dvd_pow hbdiv
  obtain ⟨y, hy⟩ := hpow
  -- Then we can divide out a common factor of `p ^ n` from the equation `hy`.
  have : a ^ n.succ * x ^ n = p * y := by
    refine' mul_left_cancel₀ (pow_ne_zero n hp.ne_zero) _
    rw [← mul_assoc _ p, ← pow_succ'ₓ, ← hy, mul_powₓ, ← mul_assoc (a ^ n.succ), mul_comm _ (p ^ n), mul_assoc]
  -- So `p ∣ a` (and we're done) or `p ∣ x`, which can't be the case since it implies `p^2 ∣ b`.
  refine' hp.dvd_of_dvd_pow ((hp.dvd_or_dvd ⟨_, this⟩).resolve_right fun hdvdx => hb _)
  obtain ⟨z, rfl⟩ := hp.dvd_of_dvd_pow hdvdx
  rw [pow_two, ← mul_assoc]
  exact dvd_mul_right _ _

/-- `irreducible p` states that `p` is non-unit and only factors into units.

We explicitly avoid stating that `p` is non-zero, this would require a semiring. Assuming only a
monoid allows us to reuse irreducible for associated elements.
-/
structure Irreducible [Monoidₓ α] (p : α) : Prop where
  not_unit : ¬IsUnit p
  is_unit_or_is_unit' : ∀ a b, p = a * b → IsUnit a ∨ IsUnit b

namespace Irreducible

theorem not_dvd_one [CommMonoidₓ α] {p : α} (hp : Irreducible p) : ¬p ∣ 1 :=
  mt (is_unit_of_dvd_one _) hp.not_unit

theorem is_unit_or_is_unit [Monoidₓ α] {p : α} (hp : Irreducible p) {a b : α} (h : p = a * b) : IsUnit a ∨ IsUnit b :=
  hp.is_unit_or_is_unit' a b h

end Irreducible

theorem irreducible_iff [Monoidₓ α] {p : α} : Irreducible p ↔ ¬IsUnit p ∧ ∀ a b, p = a * b → IsUnit a ∨ IsUnit b :=
  ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

@[simp]
theorem not_irreducible_one [Monoidₓ α] : ¬Irreducible (1 : α) := by
  simp [← irreducible_iff]

theorem Irreducible.ne_one [Monoidₓ α] : ∀ {p : α}, Irreducible p → p ≠ 1
  | _, hp, rfl => not_irreducible_one hp

@[simp]
theorem not_irreducible_zero [MonoidWithZeroₓ α] : ¬Irreducible (0 : α)
  | ⟨hn0, h⟩ =>
    have : IsUnit (0 : α) ∨ IsUnit (0 : α) := h 0 0 (mul_zero 0).symm
    this.elim hn0 hn0

theorem Irreducible.ne_zero [MonoidWithZeroₓ α] : ∀ {p : α}, Irreducible p → p ≠ 0
  | _, hp, rfl => not_irreducible_zero hp

theorem of_irreducible_mul {α} [Monoidₓ α] {x y : α} : Irreducible (x * y) → IsUnit x ∨ IsUnit y
  | ⟨_, h⟩ => h _ _ rfl

theorem of_irreducible_pow {α} [Monoidₓ α] {x : α} {n : ℕ} (hn : n ≠ 1) : Irreducible (x ^ n) → IsUnit x := by
  obtain hn | hn := hn.lt_or_lt
  · simp only [← nat.lt_one_iff.mp hn, ← IsEmpty.forall_iff, ← not_irreducible_one, ← pow_zeroₓ]
    
  intro h
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [pow_succₓ, add_commₓ] at h
  exact (or_iff_left_of_imp (is_unit_pos_pow_iff (Nat.succ_posₓ _)).mp).mp (of_irreducible_mul h)

theorem irreducible_or_factor {α} [Monoidₓ α] (x : α) (h : ¬IsUnit x) :
    Irreducible x ∨ ∃ a b, ¬IsUnit a ∧ ¬IsUnit b ∧ a * b = x := by
  have := Classical.dec
  refine' or_iff_not_imp_right.2 fun H => _
  simp [← h, ← irreducible_iff] at H⊢
  refine' fun a b h => Classical.by_contradiction fun o => _
  simp [← not_or_distrib] at o
  exact H _ o.1 _ o.2 h.symm

protected theorem Prime.irreducible [CancelCommMonoidWithZero α] {p : α} (hp : Prime p) : Irreducible p :=
  ⟨hp.not_unit, fun a b hab =>
    (show a * b ∣ a ∨ a * b ∣ b from hab ▸ hp.dvd_or_dvd (hab ▸ dvd_rfl)).elim
      (fun ⟨x, hx⟩ =>
        Or.inr
          (is_unit_iff_dvd_one.2
            ⟨x,
              mul_right_cancel₀
                  (show a ≠ 0 from fun h => by
                    simp_all [← Prime]) <|
                by
                conv => lhs rw [hx] <;> simp [← mul_comm, ← mul_assoc, ← mul_left_commₓ]⟩))
      fun ⟨x, hx⟩ =>
      Or.inl
        (is_unit_iff_dvd_one.2
          ⟨x,
            mul_right_cancel₀
                (show b ≠ 0 from fun h => by
                  simp_all [← Prime]) <|
              by
              conv => lhs rw [hx] <;> simp [← mul_comm, ← mul_assoc, ← mul_left_commₓ]⟩)⟩

theorem succ_dvd_or_succ_dvd_of_succ_sum_dvd_mul [CancelCommMonoidWithZero α] {p : α} (hp : Prime p) {a b : α}
    {k l : ℕ} : p ^ k ∣ a → p ^ l ∣ b → p ^ (k + l + 1) ∣ a * b → p ^ (k + 1) ∣ a ∨ p ^ (l + 1) ∣ b :=
  fun ⟨x, hx⟩ ⟨y, hy⟩ ⟨z, hz⟩ =>
  have h : p ^ (k + l) * (x * y) = p ^ (k + l) * (p * z) := by
    simpa [← mul_comm, ← pow_addₓ, ← hx, ← hy, ← mul_assoc, ← mul_left_commₓ] using hz
  have hp0 : p ^ (k + l) ≠ 0 := pow_ne_zero _ hp.ne_zero
  have hpd : p ∣ x * y :=
    ⟨z, by
      rwa [mul_right_inj' hp0] at h⟩
  (hp.dvd_or_dvd hpd).elim
    (fun ⟨d, hd⟩ =>
      Or.inl
        ⟨d, by
          simp [*, ← pow_succₓ, ← mul_comm, ← mul_left_commₓ, ← mul_assoc]⟩)
    fun ⟨d, hd⟩ =>
    Or.inr
      ⟨d, by
        simp [*, ← pow_succₓ, ← mul_comm, ← mul_left_commₓ, ← mul_assoc]⟩

/-- If `p` and `q` are irreducible, then `p ∣ q` implies `q ∣ p`. -/
theorem Irreducible.dvd_symm [Monoidₓ α] {p q : α} (hp : Irreducible p) (hq : Irreducible q) : p ∣ q → q ∣ p := by
  rintro ⟨q', rfl⟩
  rw [IsUnit.mul_right_dvd (Or.resolve_left (of_irreducible_mul hq) hp.not_unit)]

theorem Irreducible.dvd_comm [Monoidₓ α] {p q : α} (hp : Irreducible p) (hq : Irreducible q) : p ∣ q ↔ q ∣ p :=
  ⟨hp.dvd_symm hq, hq.dvd_symm hp⟩

section

variable [Monoidₓ α]

theorem irreducible_units_mul (a : αˣ) (b : α) : Irreducible (↑a * b) ↔ Irreducible b := by
  simp only [← irreducible_iff, ← Units.is_unit_units_mul, ← And.congr_right_iff]
  refine' fun hu => ⟨fun h A B HAB => _, fun h A B HAB => _⟩
  · rw [← a.is_unit_units_mul]
    apply h
    rw [mul_assoc, ← HAB]
    
  · rw [← a⁻¹.is_unit_units_mul]
    apply h
    rw [mul_assoc, ← HAB, Units.inv_mul_cancel_left]
    

theorem irreducible_is_unit_mul {a b : α} (h : IsUnit a) : Irreducible (a * b) ↔ Irreducible b :=
  let ⟨a, ha⟩ := h
  ha ▸ irreducible_units_mul a b

theorem irreducible_mul_units (a : αˣ) (b : α) : Irreducible (b * ↑a) ↔ Irreducible b := by
  simp only [← irreducible_iff, ← Units.is_unit_mul_units, ← And.congr_right_iff]
  refine' fun hu => ⟨fun h A B HAB => _, fun h A B HAB => _⟩
  · rw [← Units.is_unit_mul_units B a]
    apply h
    rw [← mul_assoc, ← HAB]
    
  · rw [← Units.is_unit_mul_units B a⁻¹]
    apply h
    rw [← mul_assoc, ← HAB, Units.mul_inv_cancel_right]
    

theorem irreducible_mul_is_unit {a b : α} (h : IsUnit a) : Irreducible (b * a) ↔ Irreducible b :=
  let ⟨a, ha⟩ := h
  ha ▸ irreducible_mul_units a b

theorem irreducible_mul_iff {a b : α} : Irreducible (a * b) ↔ Irreducible a ∧ IsUnit b ∨ Irreducible b ∧ IsUnit a := by
  constructor
  · refine' fun h => Or.imp (fun h' => ⟨_, h'⟩) (fun h' => ⟨_, h'⟩) (h.is_unit_or_is_unit rfl).symm
    · rwa [irreducible_mul_is_unit h'] at h
      
    · rwa [irreducible_is_unit_mul h'] at h
      
    
  · rintro (⟨ha, hb⟩ | ⟨hb, ha⟩)
    · rwa [irreducible_mul_is_unit hb]
      
    · rwa [irreducible_is_unit_mul ha]
      
    

end

theorem pow_not_prime [CancelCommMonoidWithZero α] {x : α} {n : ℕ} (hn : n ≠ 1) : ¬Prime (x ^ n) := fun hp =>
  hp.not_unit <| IsUnit.pow _ <| of_irreducible_pow hn <| hp.Irreducible

/-- Two elements of a `monoid` are `associated` if one of them is another one
multiplied by a unit on the right. -/
def Associated [Monoidₓ α] (x y : α) : Prop :=
  ∃ u : αˣ, x * u = y

-- mathport name: «expr ~ᵤ »
local infixl:50 " ~ᵤ " => Associated

namespace Associated

@[refl]
protected theorem refl [Monoidₓ α] (x : α) : x ~ᵤ x :=
  ⟨1, by
    simp ⟩

instance [Monoidₓ α] : IsRefl α Associated :=
  ⟨Associated.refl⟩

@[symm]
protected theorem symm [Monoidₓ α] : ∀ {x y : α}, x ~ᵤ y → y ~ᵤ x
  | x, _, ⟨u, rfl⟩ =>
    ⟨u⁻¹, by
      rw [mul_assoc, Units.mul_inv, mul_oneₓ]⟩

instance [Monoidₓ α] : IsSymm α Associated :=
  ⟨fun a b => Associated.symm⟩

@[trans]
protected theorem trans [Monoidₓ α] : ∀ {x y z : α}, x ~ᵤ y → y ~ᵤ z → x ~ᵤ z
  | x, _, _, ⟨u, rfl⟩, ⟨v, rfl⟩ =>
    ⟨u * v, by
      rw [Units.coe_mul, mul_assoc]⟩

instance [Monoidₓ α] : IsTrans α Associated :=
  ⟨fun a b c => Associated.trans⟩

/-- The setoid of the relation `x ~ᵤ y` iff there is a unit `u` such that `x * u = y` -/
protected def setoid (α : Type _) [Monoidₓ α] : Setoidₓ α where
  R := Associated
  iseqv := ⟨Associated.refl, fun a b => Associated.symm, fun a b c => Associated.trans⟩

end Associated

attribute [local instance] Associated.setoid

theorem unit_associated_one [Monoidₓ α] {u : αˣ} : (u : α) ~ᵤ 1 :=
  ⟨u⁻¹, Units.mul_inv u⟩

theorem associated_one_iff_is_unit [Monoidₓ α] {a : α} : (a : α) ~ᵤ 1 ↔ IsUnit a :=
  Iff.intro
    (fun h =>
      let ⟨c, h⟩ := h.symm
      h ▸ ⟨c, (one_mulₓ _).symm⟩)
    fun ⟨c, h⟩ =>
    Associated.symm
      ⟨c, by
        simp [← h]⟩

theorem associated_zero_iff_eq_zero [MonoidWithZeroₓ α] (a : α) : a ~ᵤ 0 ↔ a = 0 :=
  Iff.intro
    (fun h => by
      let ⟨u, h⟩ := h.symm
      simpa using h.symm)
    fun h => h ▸ Associated.refl a

theorem associated_one_of_mul_eq_one [CommMonoidₓ α] {a : α} (b : α) (hab : a * b = 1) : a ~ᵤ 1 :=
  show (Units.mkOfMulEqOne a b hab : α) ~ᵤ 1 from unit_associated_one

theorem associated_one_of_associated_mul_one [CommMonoidₓ α] {a b : α} : a * b ~ᵤ 1 → a ~ᵤ 1
  | ⟨u, h⟩ =>
    associated_one_of_mul_eq_one (b * u) <| by
      simpa [← mul_assoc] using h

theorem associated_mul_unit_left {β : Type _} [Monoidₓ β] (a u : β) (hu : IsUnit u) : Associated (a * u) a :=
  let ⟨u', hu⟩ := hu
  ⟨u'⁻¹, hu ▸ Units.mul_inv_cancel_right _ _⟩

theorem associated_unit_mul_left {β : Type _} [CommMonoidₓ β] (a u : β) (hu : IsUnit u) : Associated (u * a) a := by
  rw [mul_comm]
  exact associated_mul_unit_left _ _ hu

theorem associated_mul_unit_right {β : Type _} [Monoidₓ β] (a u : β) (hu : IsUnit u) : Associated a (a * u) :=
  (associated_mul_unit_left a u hu).symm

theorem associated_unit_mul_right {β : Type _} [CommMonoidₓ β] (a u : β) (hu : IsUnit u) : Associated a (u * a) :=
  (associated_unit_mul_left a u hu).symm

theorem Associated.mul_mul [CommMonoidₓ α] {a₁ a₂ b₁ b₂ : α} : a₁ ~ᵤ b₁ → a₂ ~ᵤ b₂ → a₁ * a₂ ~ᵤ b₁ * b₂
  | ⟨c₁, h₁⟩, ⟨c₂, h₂⟩ =>
    ⟨c₁ * c₂, by
      simp [← h₁.symm, ← h₂.symm, ← mul_assoc, ← mul_comm, ← mul_left_commₓ]⟩

theorem Associated.mul_left [CommMonoidₓ α] (a : α) {b c : α} (h : b ~ᵤ c) : a * b ~ᵤ a * c :=
  (Associated.refl a).mul_mul h

theorem Associated.mul_right [CommMonoidₓ α] {a b : α} (h : a ~ᵤ b) (c : α) : a * c ~ᵤ b * c :=
  h.mul_mul (Associated.refl c)

theorem Associated.pow_pow [CommMonoidₓ α] {a b : α} {n : ℕ} (h : a ~ᵤ b) : a ^ n ~ᵤ b ^ n := by
  induction' n with n ih
  · simp [← h]
    
  convert h.mul_mul ih <;> rw [pow_succₓ]

protected theorem Associated.dvd [Monoidₓ α] {a b : α} : a ~ᵤ b → a ∣ b := fun ⟨u, hu⟩ => ⟨u, hu.symm⟩

protected theorem Associated.dvd_dvd [Monoidₓ α] {a b : α} (h : a ~ᵤ b) : a ∣ b ∧ b ∣ a :=
  ⟨h.Dvd, h.symm.Dvd⟩

theorem associated_of_dvd_dvd [CancelMonoidWithZero α] {a b : α} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b := by
  rcases hab with ⟨c, rfl⟩
  rcases hba with ⟨d, a_eq⟩
  by_cases' ha0 : a = 0
  · simp_all
    
  have hac0 : a * c ≠ 0 := by
    intro con
    rw [con, zero_mul] at a_eq
    apply ha0 a_eq
  have : a * (c * d) = a * 1 := by
    rw [← mul_assoc, ← a_eq, mul_oneₓ]
  have hcd : c * d = 1 := mul_left_cancel₀ ha0 this
  have : a * c * (d * c) = a * c * 1 := by
    rw [← mul_assoc, ← a_eq, mul_oneₓ]
  have hdc : d * c = 1 := mul_left_cancel₀ hac0 this
  exact ⟨⟨c, d, hcd, hdc⟩, rfl⟩

theorem dvd_dvd_iff_associated [CancelMonoidWithZero α] {a b : α} : a ∣ b ∧ b ∣ a ↔ a ~ᵤ b :=
  ⟨fun ⟨h1, h2⟩ => associated_of_dvd_dvd h1 h2, Associated.dvd_dvd⟩

instance [CancelMonoidWithZero α] [DecidableRel ((· ∣ ·) : α → α → Prop)] : DecidableRel ((· ~ᵤ ·) : α → α → Prop) :=
  fun a b => decidableOfIff _ dvd_dvd_iff_associated

theorem Associated.dvd_iff_dvd_left [Monoidₓ α] {a b c : α} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c :=
  let ⟨u, hu⟩ := h
  hu ▸ Units.mul_right_dvd.symm

theorem Associated.dvd_iff_dvd_right [Monoidₓ α] {a b c : α} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c :=
  let ⟨u, hu⟩ := h
  hu ▸ Units.dvd_mul_right.symm

theorem Associated.eq_zero_iff [MonoidWithZeroₓ α] {a b : α} (h : a ~ᵤ b) : a = 0 ↔ b = 0 :=
  ⟨fun ha => by
    let ⟨u, hu⟩ := h
    simp [← hu.symm, ← ha], fun hb => by
    let ⟨u, hu⟩ := h.symm
    simp [← hu.symm, ← hb]⟩

theorem Associated.ne_zero_iff [MonoidWithZeroₓ α] {a b : α} (h : a ~ᵤ b) : a ≠ 0 ↔ b ≠ 0 :=
  not_congr h.eq_zero_iff

protected theorem Associated.prime [CommMonoidWithZero α] {p q : α} (h : p ~ᵤ q) (hp : Prime p) : Prime q :=
  ⟨h.ne_zero_iff.1 hp.ne_zero,
    let ⟨u, hu⟩ := h
    ⟨fun ⟨v, hv⟩ =>
      hp.not_unit
        ⟨v * u⁻¹, by
          simp [← hv, ← hu.symm]⟩,
      hu ▸ by
        simp [← Units.mul_right_dvd]
        intro a b
        exact hp.dvd_or_dvd⟩⟩

theorem Irreducible.associated_of_dvd [CancelMonoidWithZero α] {p q : α} (p_irr : Irreducible p) (q_irr : Irreducible q)
    (dvd : p ∣ q) : Associated p q :=
  associated_of_dvd_dvd dvd (p_irr.dvd_symm q_irr dvd)

theorem Irreducible.dvd_irreducible_iff_associated [CancelMonoidWithZero α] {p q : α} (pp : Irreducible p)
    (qp : Irreducible q) : p ∣ q ↔ Associated p q :=
  ⟨Irreducible.associated_of_dvd pp qp, Associated.dvd⟩

theorem Prime.associated_of_dvd [CancelCommMonoidWithZero α] {p q : α} (p_prime : Prime p) (q_prime : Prime q)
    (dvd : p ∣ q) : Associated p q :=
  p_prime.Irreducible.associated_of_dvd q_prime.Irreducible dvd

theorem Prime.dvd_prime_iff_associated [CancelCommMonoidWithZero α] {p q : α} (pp : Prime p) (qp : Prime q) :
    p ∣ q ↔ Associated p q :=
  pp.Irreducible.dvd_irreducible_iff_associated qp.Irreducible

theorem Associated.prime_iff [CommMonoidWithZero α] {p q : α} (h : p ~ᵤ q) : Prime p ↔ Prime q :=
  ⟨h.Prime, h.symm.Prime⟩

protected theorem Associated.is_unit [Monoidₓ α] {a b : α} (h : a ~ᵤ b) : IsUnit a → IsUnit b :=
  let ⟨u, hu⟩ := h
  fun ⟨v, hv⟩ =>
  ⟨v * u, by
    simp [← hv, ← hu.symm]⟩

theorem Associated.is_unit_iff [Monoidₓ α] {a b : α} (h : a ~ᵤ b) : IsUnit a ↔ IsUnit b :=
  ⟨h.IsUnit, h.symm.IsUnit⟩

protected theorem Associated.irreducible [Monoidₓ α] {p q : α} (h : p ~ᵤ q) (hp : Irreducible p) : Irreducible q :=
  ⟨mt h.symm.IsUnit hp.1,
    let ⟨u, hu⟩ := h
    fun a b hab =>
    have hpab : p = a * (b * (u⁻¹ : αˣ)) :=
      calc
        p = p * u * (u⁻¹ : αˣ) := by
          simp
        _ = _ := by
          rw [hu] <;> simp [← hab, ← mul_assoc]
        
    (hp.is_unit_or_is_unit hpab).elim Or.inl fun ⟨v, hv⟩ =>
      Or.inr
        ⟨v * u, by
          simp [← hv]⟩⟩

protected theorem Associated.irreducible_iff [Monoidₓ α] {p q : α} (h : p ~ᵤ q) : Irreducible p ↔ Irreducible q :=
  ⟨h.Irreducible, h.symm.Irreducible⟩

theorem Associated.of_mul_left [CancelCommMonoidWithZero α] {a b c d : α} (h : a * b ~ᵤ c * d) (h₁ : a ~ᵤ c)
    (ha : a ≠ 0) : b ~ᵤ d :=
  let ⟨u, hu⟩ := h
  let ⟨v, hv⟩ := Associated.symm h₁
  ⟨u * (v : αˣ),
    mul_left_cancel₀ ha
      (by
        rw [← hv, mul_assoc c (v : α) d, mul_left_commₓ c, ← hu]
        simp [← hv.symm, ← mul_assoc, ← mul_comm, ← mul_left_commₓ])⟩

theorem Associated.of_mul_right [CancelCommMonoidWithZero α] {a b c d : α} : a * b ~ᵤ c * d → b ~ᵤ d → b ≠ 0 → a ~ᵤ c :=
  by
  rw [mul_comm a, mul_comm c] <;> exact Associated.of_mul_left

theorem Associated.of_pow_associated_of_prime [CancelCommMonoidWithZero α] {p₁ p₂ : α} {k₁ k₂ : ℕ} (hp₁ : Prime p₁)
    (hp₂ : Prime p₂) (hk₁ : 0 < k₁) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ := by
  have : p₁ ∣ p₂ ^ k₂ := by
    rw [← h.dvd_iff_dvd_right]
    apply dvd_pow_self _ hk₁.ne'
  rw [← hp₁.dvd_prime_iff_associated hp₂]
  exact hp₁.dvd_of_dvd_pow this

theorem Associated.of_pow_associated_of_prime' [CancelCommMonoidWithZero α] {p₁ p₂ : α} {k₁ k₂ : ℕ} (hp₁ : Prime p₁)
    (hp₂ : Prime p₂) (hk₂ : 0 < k₂) (h : p₁ ^ k₁ ~ᵤ p₂ ^ k₂) : p₁ ~ᵤ p₂ :=
  (h.symm.of_pow_associated_of_prime hp₂ hp₁ hk₂).symm

section UniqueUnits

variable [Monoidₓ α] [Unique αˣ]

theorem units_eq_one (u : αˣ) : u = 1 :=
  Subsingleton.elimₓ u 1

theorem associated_iff_eq {x y : α} : x ~ᵤ y ↔ x = y := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [units_eq_one c, Units.coe_one, mul_oneₓ]
    
  · rintro rfl
    rfl
    

theorem associated_eq_eq : (Associated : α → α → Prop) = Eq := by
  ext
  rw [associated_iff_eq]

theorem prime_dvd_prime_iff_eq {M : Type _} [CancelCommMonoidWithZero M] [Unique Mˣ] {p q : M} (pp : Prime p)
    (qp : Prime q) : p ∣ q ↔ p = q := by
  rw [pp.dvd_prime_iff_associated qp, ← associated_eq_eq]

end UniqueUnits

/-- The quotient of a monoid by the `associated` relation. Two elements `x` and `y`
  are associated iff there is a unit `u` such that `x * u = y`. There is a natural
  monoid structure on `associates α`. -/
def Associates (α : Type _) [Monoidₓ α] : Type _ :=
  Quotientₓ (Associated.setoid α)

namespace Associates

open Associated

/-- The canonical quotient map from a monoid `α` into the `associates` of `α` -/
protected def mk {α : Type _} [Monoidₓ α] (a : α) : Associates α :=
  ⟦a⟧

instance [Monoidₓ α] : Inhabited (Associates α) :=
  ⟨⟦1⟧⟩

theorem mk_eq_mk_iff_associated [Monoidₓ α] {a b : α} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b :=
  Iff.intro Quotientₓ.exact Quot.sound

theorem quotient_mk_eq_mk [Monoidₓ α] (a : α) : ⟦a⟧ = Associates.mk a :=
  rfl

theorem quot_mk_eq_mk [Monoidₓ α] (a : α) : Quot.mk Setoidₓ.R a = Associates.mk a :=
  rfl

theorem forall_associated [Monoidₓ α] {p : Associates α → Prop} : (∀ a, p a) ↔ ∀ a, p (Associates.mk a) :=
  Iff.intro (fun h a => h _) fun h a => Quotientₓ.induction_on a h

theorem mk_surjective [Monoidₓ α] : Function.Surjective (@Associates.mk α _) :=
  forall_associated.2 fun a => ⟨a, rfl⟩

instance [Monoidₓ α] : One (Associates α) :=
  ⟨⟦1⟧⟩

@[simp]
theorem mk_one [Monoidₓ α] : Associates.mk (1 : α) = 1 :=
  rfl

theorem one_eq_mk_one [Monoidₓ α] : (1 : Associates α) = Associates.mk 1 :=
  rfl

instance [Monoidₓ α] : HasBot (Associates α) :=
  ⟨1⟩

theorem bot_eq_one [Monoidₓ α] : (⊥ : Associates α) = 1 :=
  rfl

theorem exists_rep [Monoidₓ α] (a : Associates α) : ∃ a0 : α, Associates.mk a0 = a :=
  Quot.exists_rep a

instance [Monoidₓ α] [Subsingleton α] : Unique (Associates α) where
  default := 1
  uniq := fun a => by
    apply Quotientₓ.recOnSubsingleton₂
    intro a b
    congr

theorem mk_injective [Monoidₓ α] [Unique (Units α)] : Function.Injective (@Associates.mk α _) := fun a b h =>
  associated_iff_eq.mp (Associates.mk_eq_mk_iff_associated.mp h)

section CommMonoidₓ

variable [CommMonoidₓ α]

instance : Mul (Associates α) :=
  ⟨fun a' b' =>
    (Quotientₓ.liftOn₂ a' b' fun a b => ⟦a * b⟧) fun a₁ a₂ b₁ b₂ ⟨c₁, h₁⟩ ⟨c₂, h₂⟩ =>
      Quotientₓ.sound <|
        ⟨c₁ * c₂, by
          simp [← h₁.symm, ← h₂.symm, ← mul_assoc, ← mul_comm, ← mul_left_commₓ]⟩⟩

theorem mk_mul_mk {x y : α} : Associates.mk x * Associates.mk y = Associates.mk (x * y) :=
  rfl

instance : CommMonoidₓ (Associates α) where
  one := 1
  mul := (· * ·)
  mul_one := fun a' =>
    (Quotientₓ.induction_on a') fun a =>
      show ⟦a * 1⟧ = ⟦a⟧ by
        simp
  one_mul := fun a' =>
    (Quotientₓ.induction_on a') fun a =>
      show ⟦1 * a⟧ = ⟦a⟧ by
        simp
  mul_assoc := fun a' b' c' =>
    (Quotientₓ.induction_on₃ a' b' c') fun a b c =>
      show ⟦a * b * c⟧ = ⟦a * (b * c)⟧ by
        rw [mul_assoc]
  mul_comm := fun a' b' =>
    (Quotientₓ.induction_on₂ a' b') fun a b =>
      show ⟦a * b⟧ = ⟦b * a⟧ by
        rw [mul_comm]

instance : Preorderₓ (Associates α) where
  le := Dvd.Dvd
  le_refl := dvd_refl
  le_trans := fun a b c => dvd_trans

/-- `associates.mk` as a `monoid_hom`. -/
protected def mkMonoidHom : α →* Associates α :=
  ⟨Associates.mk, mk_one, fun x y => mk_mul_mk⟩

@[simp]
theorem mk_monoid_hom_apply (a : α) : Associates.mkMonoidHom a = Associates.mk a :=
  rfl

theorem associated_map_mk {f : Associates α →* α} (hinv : Function.RightInverse f Associates.mk) (a : α) :
    a ~ᵤ f (Associates.mk a) :=
  Associates.mk_eq_mk_iff_associated.1 (hinv (Associates.mk a)).symm

theorem mk_pow (a : α) (n : ℕ) : Associates.mk (a ^ n) = Associates.mk a ^ n := by
  induction n <;> simp [*, ← pow_succₓ, ← associates.mk_mul_mk.symm]

theorem dvd_eq_le : ((· ∣ ·) : Associates α → Associates α → Prop) = (· ≤ ·) :=
  rfl

theorem mul_eq_one_iff {x y : Associates α} : x * y = 1 ↔ x = 1 ∧ y = 1 :=
  Iff.intro
    ((Quotientₓ.induction_on₂ x y) fun a b h =>
      have : a * b ~ᵤ 1 := Quotientₓ.exact h
      ⟨Quotientₓ.sound <| associated_one_of_associated_mul_one this,
        Quotientₓ.sound <|
          associated_one_of_associated_mul_one <| by
            rwa [mul_comm] at this⟩)
    (by
      simp (config := { contextual := true }))

theorem units_eq_one (u : (Associates α)ˣ) : u = 1 :=
  Units.ext (mul_eq_one_iff.1 u.val_inv).1

instance uniqueUnits : Unique (Associates α)ˣ where
  default := 1
  uniq := Associates.units_eq_one

theorem coe_unit_eq_one (u : (Associates α)ˣ) : (u : Associates α) = 1 := by
  simp

theorem is_unit_iff_eq_one (a : Associates α) : IsUnit a ↔ a = 1 :=
  Iff.intro (fun ⟨u, h⟩ => h ▸ coe_unit_eq_one _) fun h => h.symm ▸ is_unit_one

theorem is_unit_iff_eq_bot {a : Associates α} : IsUnit a ↔ a = ⊥ := by
  rw [Associates.is_unit_iff_eq_one, bot_eq_one]

theorem is_unit_mk {a : α} : IsUnit (Associates.mk a) ↔ IsUnit a :=
  calc
    IsUnit (Associates.mk a) ↔ a ~ᵤ 1 := by
      rw [is_unit_iff_eq_one, one_eq_mk_one, mk_eq_mk_iff_associated]
    _ ↔ IsUnit a := associated_one_iff_is_unit
    

section Order

theorem mul_mono {a b c d : Associates α} (h₁ : a ≤ b) (h₂ : c ≤ d) : a * c ≤ b * d :=
  let ⟨x, hx⟩ := h₁
  let ⟨y, hy⟩ := h₂
  ⟨x * y, by
    simp [← hx, ← hy, ← mul_comm, ← mul_assoc, ← mul_left_commₓ]⟩

theorem one_le {a : Associates α} : 1 ≤ a :=
  Dvd.intro _ (one_mulₓ a)

theorem le_mul_right {a b : Associates α} : a ≤ a * b :=
  ⟨b, rfl⟩

theorem le_mul_left {a b : Associates α} : a ≤ b * a := by
  rw [mul_comm] <;> exact le_mul_right

instance : OrderBot (Associates α) where
  bot := 1
  bot_le := fun a => one_le

end Order

theorem dvd_of_mk_le_mk {a b : α} : Associates.mk a ≤ Associates.mk b → a ∣ b
  | ⟨c', hc'⟩ =>
    ((Quotientₓ.induction_on c') fun c hc =>
        let ⟨d, hd⟩ := (Quotientₓ.exact hc).symm
        ⟨↑d * c,
          calc
            b = a * c * ↑d := hd.symm
            _ = a * (↑d * c) := by
              ac_rfl
            ⟩)
      hc'

theorem mk_le_mk_of_dvd {a b : α} : a ∣ b → Associates.mk a ≤ Associates.mk b := fun ⟨c, hc⟩ =>
  ⟨Associates.mk c, by
    simp [← hc] <;> rfl⟩

theorem mk_le_mk_iff_dvd_iff {a b : α} : Associates.mk a ≤ Associates.mk b ↔ a ∣ b :=
  Iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

theorem mk_dvd_mk {a b : α} : Associates.mk a ∣ Associates.mk b ↔ a ∣ b :=
  Iff.intro dvd_of_mk_le_mk mk_le_mk_of_dvd

end CommMonoidₓ

instance [Zero α] [Monoidₓ α] : Zero (Associates α) :=
  ⟨⟦0⟧⟩

instance [Zero α] [Monoidₓ α] : HasTop (Associates α) :=
  ⟨0⟩

section MonoidWithZeroₓ

variable [MonoidWithZeroₓ α]

@[simp]
theorem mk_eq_zero {a : α} : Associates.mk a = 0 ↔ a = 0 :=
  ⟨fun h => (associated_zero_iff_eq_zero a).1 <| Quotientₓ.exact h, fun h => h.symm ▸ rfl⟩

theorem mk_ne_zero {a : α} : Associates.mk a ≠ 0 ↔ a ≠ 0 :=
  not_congr mk_eq_zero

instance [Nontrivial α] : Nontrivial (Associates α) :=
  ⟨⟨0, 1, fun h =>
      have : (0 : α) ~ᵤ 1 := Quotientₓ.exact h
      have : (0 : α) = 1 := ((associated_zero_iff_eq_zero 1).1 this.symm).symm
      zero_ne_one this⟩⟩

theorem exists_non_zero_rep {a : Associates α} : a ≠ 0 → ∃ a0 : α, a0 ≠ 0 ∧ Associates.mk a0 = a :=
  Quotientₓ.induction_on a fun b nz => ⟨b, mt (congr_arg Quotientₓ.mk) nz, rfl⟩

end MonoidWithZeroₓ

section CommMonoidWithZero

variable [CommMonoidWithZero α]

instance : CommMonoidWithZero (Associates α) :=
  { Associates.commMonoid, Associates.hasZero with
    zero_mul := by
      rintro ⟨a⟩
      show Associates.mk (0 * a) = Associates.mk 0
      rw [zero_mul],
    mul_zero := by
      rintro ⟨a⟩
      show Associates.mk (a * 0) = Associates.mk 0
      rw [mul_zero] }

instance : OrderTop (Associates α) where
  top := 0
  le_top := fun a => ⟨0, (mul_zero a).symm⟩

instance : BoundedOrder (Associates α) :=
  { Associates.orderTop, Associates.orderBot with }

instance [DecidableRel ((· ∣ ·) : α → α → Prop)] : DecidableRel ((· ∣ ·) : Associates α → Associates α → Prop) :=
  fun a b => Quotientₓ.recOnSubsingleton₂ a b fun a b => decidableOfIff' _ mk_dvd_mk

theorem Prime.le_or_le {p : Associates α} (hp : Prime p) {a b : Associates α} (h : p ≤ a * b) : p ≤ a ∨ p ≤ b :=
  hp.2.2 a b h

theorem prime_mk (p : α) : Prime (Associates.mk p) ↔ Prime p := by
  rw [Prime, _root_.prime, forall_associated]
  trans
  · apply and_congr
    rfl
    apply and_congr
    rfl
    apply forall_congrₓ
    intro a
    exact forall_associated
    
  apply and_congr mk_ne_zero
  apply and_congr
  · rw [is_unit_mk]
    
  refine' forall₂_congrₓ fun a b => _
  rw [mk_mul_mk, mk_dvd_mk, mk_dvd_mk, mk_dvd_mk]

theorem irreducible_mk (a : α) : Irreducible (Associates.mk a) ↔ Irreducible a := by
  simp only [← irreducible_iff, ← is_unit_mk]
  apply and_congr Iff.rfl
  constructor
  · rintro h x y rfl
    simpa [← is_unit_mk] using h (Associates.mk x) (Associates.mk y) rfl
    
  · intro h x y
    refine' Quotientₓ.induction_on₂ x y fun x y a_eq => _
    rcases Quotientₓ.exact a_eq.symm with ⟨u, a_eq⟩
    rw [mul_assoc] at a_eq
    show IsUnit (Associates.mk x) ∨ IsUnit (Associates.mk y)
    simpa [← is_unit_mk] using h _ _ a_eq.symm
    

theorem mk_dvd_not_unit_mk_iff {a b : α} : DvdNotUnit (Associates.mk a) (Associates.mk b) ↔ DvdNotUnit a b := by
  rw [DvdNotUnit, DvdNotUnit, mk_ne_zero]
  apply and_congr_right
  intro ane0
  constructor
  · contrapose!
    rw [forall_associated]
    intro h x hx hbax
    rw [mk_mul_mk, mk_eq_mk_iff_associated] at hbax
    cases' hbax with u hu
    apply h (x * ↑u⁻¹)
    · rw [is_unit_mk] at hx
      rw [Associated.is_unit_iff]
      apply hx
      use u
      simp
      
    simp [mul_assoc, hu]
    
  · rintro ⟨x, ⟨hx, rfl⟩⟩
    use Associates.mk x
    simp [← is_unit_mk, ← mk_mul_mk, ← hx]
    

theorem dvd_not_unit_of_lt {a b : Associates α} (hlt : a < b) : DvdNotUnit a b := by
  constructor
  · rintro rfl
    apply not_lt_of_le _ hlt
    apply dvd_zero
    
  rcases hlt with ⟨⟨x, rfl⟩, ndvd⟩
  refine' ⟨x, _, rfl⟩
  contrapose! ndvd
  rcases ndvd with ⟨u, rfl⟩
  simp

theorem irreducible_iff_prime_iff : (∀ a : α, Irreducible a ↔ Prime a) ↔ ∀ a : Associates α, Irreducible a ↔ Prime a :=
  by
  simp_rw [forall_associated, irreducible_mk, prime_mk]

end CommMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero α]

instance : PartialOrderₓ (Associates α) :=
  { Associates.preorder with
    le_antisymm := fun a' b' =>
      Quotientₓ.induction_on₂ a' b' fun a b hab hba =>
        Quot.sound <| associated_of_dvd_dvd (dvd_of_mk_le_mk hab) (dvd_of_mk_le_mk hba) }

instance : OrderedCommMonoid (Associates α) :=
  { Associates.commMonoid, Associates.partialOrder with
    mul_le_mul_left := fun a b ⟨d, hd⟩ c => hd.symm ▸ mul_assoc c a d ▸ le_mul_right }

instance : NoZeroDivisors (Associates α) :=
  ⟨fun x y =>
    (Quotientₓ.induction_on₂ x y) fun a b h =>
      have : a * b = 0 := (associated_zero_iff_eq_zero _).1 (Quotientₓ.exact h)
      have : a = 0 ∨ b = 0 := mul_eq_zero.1 this
      this.imp (fun h => h.symm ▸ rfl) fun h => h.symm ▸ rfl⟩

theorem eq_of_mul_eq_mul_left : ∀ a b c : Associates α, a ≠ 0 → a * b = a * c → b = c := by
  rintro ⟨a⟩ ⟨b⟩ ⟨c⟩ ha h
  rcases Quotientₓ.exact' h with ⟨u, hu⟩
  have hu : a * (b * ↑u) = a * c := by
    rwa [← mul_assoc]
  exact Quotientₓ.sound' ⟨u, mul_left_cancel₀ (mk_ne_zero.1 ha) hu⟩

theorem eq_of_mul_eq_mul_right : ∀ a b c : Associates α, b ≠ 0 → a * b = c * b → a = c := fun a b c bne0 =>
  mul_comm b a ▸ mul_comm b c ▸ eq_of_mul_eq_mul_left b a c bne0

theorem le_of_mul_le_mul_left (a b c : Associates α) (ha : a ≠ 0) : a * b ≤ a * c → b ≤ c
  | ⟨d, hd⟩ =>
    ⟨d,
      eq_of_mul_eq_mul_left a _ _ ha <| by
        rwa [← mul_assoc]⟩

theorem one_or_eq_of_le_of_prime : ∀ p m : Associates α, Prime p → m ≤ p → m = 1 ∨ m = p
  | _, m, ⟨hp0, hp1, h⟩, ⟨d, rfl⟩ =>
    match h m d dvd_rfl with
    | Or.inl h =>
      (Classical.by_cases fun this : m = 0 => by
          simp [← this])
        fun this : m ≠ 0 => by
        have : m * d ≤ m * 1 := by
          simpa using h
        have : d ≤ 1 := Associates.le_of_mul_le_mul_left m d 1 ‹m ≠ 0› this
        have : d = 1 := bot_unique this
        simp [← this]
    | Or.inr h =>
      (Classical.by_cases fun this : d = 0 => by
          simp [← this] at hp0 <;> contradiction)
        fun this : d ≠ 0 =>
        have : d * m ≤ d * 1 := by
          simpa [← mul_comm] using h
        Or.inl <| bot_unique <| Associates.le_of_mul_le_mul_left d m 1 ‹d ≠ 0› this

instance : CancelCommMonoidWithZero (Associates α) :=
  { (inferInstance : CommMonoidWithZero (Associates α)) with mul_left_cancel_of_ne_zero := eq_of_mul_eq_mul_left,
    mul_right_cancel_of_ne_zero := eq_of_mul_eq_mul_right }

instance : CanonicallyOrderedMonoid (Associates α) :=
  { Associates.cancelCommMonoidWithZero, Associates.boundedOrder, Associates.orderedCommMonoid with
    exists_mul_of_le := fun a b => id, le_self_mul := fun a b => ⟨b, rfl⟩ }

theorem dvd_not_unit_iff_lt {a b : Associates α} : DvdNotUnit a b ↔ a < b :=
  dvd_and_not_dvd_iff.symm

theorem le_one_iff {p : Associates α} : p ≤ 1 ↔ p = 1 := by
  rw [← Associates.bot_eq_one, le_bot_iff]

end CancelCommMonoidWithZero

end Associates

section CommMonoidWithZero

theorem DvdNotUnit.is_unit_of_irreducible_right [CommMonoidWithZero α] {p q : α} (h : DvdNotUnit p q)
    (hq : Irreducible q) : IsUnit p := by
  obtain ⟨hp', x, hx, hx'⟩ := h
  exact Or.resolve_right ((irreducible_iff.1 hq).right p x hx') hx

theorem not_irreducible_of_not_unit_dvd_not_unit [CommMonoidWithZero α] {p q : α} (hp : ¬IsUnit p)
    (h : DvdNotUnit p q) : ¬Irreducible q :=
  mt h.is_unit_of_irreducible_right hp

theorem DvdNotUnit.not_unit [CommMonoidWithZero α] {p q : α} (hp : DvdNotUnit p q) : ¬IsUnit q := by
  obtain ⟨-, x, hx, rfl⟩ := hp
  exact fun hc => hx (is_unit_iff_dvd_one.mpr (dvd_of_mul_left_dvd (is_unit_iff_dvd_one.mp hc)))

theorem dvd_not_unit_of_dvd_not_unit_associated [CommMonoidWithZero α] [Nontrivial α] {p q r : α} (h : DvdNotUnit p q)
    (h' : Associated q r) : DvdNotUnit p r := by
  obtain ⟨u, rfl⟩ := Associated.symm h'
  obtain ⟨hp, x, hx⟩ := h
  refine' ⟨hp, x * ↑u⁻¹, DvdNotUnit.not_unit ⟨u⁻¹.ne_zero, x, hx.left, mul_comm _ _⟩, _⟩
  rw [← mul_assoc, ← hx.right, mul_assoc, Units.mul_inv, mul_oneₓ]

end CommMonoidWithZero

section CancelCommMonoidWithZero

theorem is_unit_of_associated_mul [CancelCommMonoidWithZero α] {p b : α} (h : Associated (p * b) p) (hp : p ≠ 0) :
    IsUnit b := by
  cases' h with a ha
  refine' is_unit_of_mul_eq_one b a ((mul_right_inj' hp).mp _)
  rwa [← mul_assoc, mul_oneₓ]

theorem Associates.is_atom_iff [CancelCommMonoidWithZero α] {p : Associates α} (h₁ : p ≠ 0) :
    IsAtom p ↔ Irreducible p :=
  ⟨fun hp =>
    ⟨by
      simpa only [← Associates.is_unit_iff_eq_one] using hp.1, fun a b h =>
      (hp.le_iff.mp ⟨_, h⟩).casesOn (fun ha => Or.inl (a.is_unit_iff_eq_one.mpr ha)) fun ha =>
        Or.inr
          (show IsUnit b by
            rw [ha] at h
            apply
              is_unit_of_associated_mul
                (show Associated (p * b) p by
                  conv_rhs => rw [h])
                h₁)⟩,
    fun hp =>
    ⟨by
      simpa only [← Associates.is_unit_iff_eq_one, ← Associates.bot_eq_one] using hp.1, fun b ⟨⟨a, hab⟩, hb⟩ =>
      (hp.is_unit_or_is_unit hab).casesOn
        (fun hb =>
          show b = ⊥ by
            rwa [Associates.is_unit_iff_eq_one, ← Associates.bot_eq_one] at hb)
        fun ha =>
        absurd
          (show p ∣ b from
            ⟨(ha.Unit⁻¹ : Units _), by
              simp [← hab] <;> rw [mul_assoc] <;> rw [IsUnit.mul_coe_inv ha] <;> rw [mul_oneₓ]⟩)
          hb⟩⟩

theorem DvdNotUnit.not_associated [CancelCommMonoidWithZero α] {p q : α} (h : DvdNotUnit p q) : ¬Associated p q := by
  rintro ⟨a, rfl⟩
  obtain ⟨hp, x, hx, hx'⟩ := h
  rcases(mul_right_inj' hp).mp hx' with rfl
  exact hx a.is_unit

theorem DvdNotUnit.ne [CancelCommMonoidWithZero α] {p q : α} (h : DvdNotUnit p q) : p ≠ q := by
  by_contra hcontra
  obtain ⟨hp, x, hx', hx''⟩ := h
  conv_lhs at hx'' => rw [← hcontra, ← mul_oneₓ p]
  rw [(mul_left_cancel₀ hp hx'').symm] at hx'
  exact hx' is_unit_one

theorem pow_injective_of_not_unit [CancelCommMonoidWithZero α] {q : α} (hq : ¬IsUnit q) (hq' : q ≠ 0) :
    Function.Injective fun n : ℕ => q ^ n := by
  refine' injective_of_lt_imp_ne fun n m h => DvdNotUnit.ne ⟨pow_ne_zero n hq', q ^ (m - n), _, _⟩
  · exact not_is_unit_of_not_is_unit_dvd hq (dvd_pow (dvd_refl _) (Nat.sub_pos_of_ltₓ h).ne')
    
  · exact (pow_mul_pow_sub q h.le).symm
    

theorem dvd_prime_pow [CancelCommMonoidWithZero α] {p q : α} (hp : Prime p) (n : ℕ) :
    q ∣ p ^ n ↔ ∃ i ≤ n, Associated q (p ^ i) := by
  induction' n with n ih generalizing q
  · simp [is_unit_iff_dvd_one, ← associated_one_iff_is_unit]
    
  refine' ⟨fun h => _, fun ⟨i, hi, hq⟩ => hq.dvd.trans (pow_dvd_pow p hi)⟩
  rw [pow_succₓ] at h
  rcases hp.left_dvd_or_dvd_right_of_dvd_mul h with (⟨q, rfl⟩ | hno)
  · rw [mul_dvd_mul_iff_left hp.ne_zero, ih] at h
    rcases h with ⟨i, hi, hq⟩
    refine' ⟨i + 1, Nat.succ_le_succₓ hi, (hq.mul_left p).trans _⟩
    rw [pow_succₓ]
    
  · obtain ⟨i, hi, hq⟩ := ih.mp hno
    exact ⟨i, hi.trans n.le_succ, hq⟩
    

end CancelCommMonoidWithZero

