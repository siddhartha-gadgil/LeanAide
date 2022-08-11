/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.Int.Basic
import Mathbin.Data.Nat.Gcd
import Mathbin.Logic.Encodable.Basic

/-!
# Basics for the Rational Numbers

## Summary

We define a rational number `q` as a structure `{ num, denom, pos, cop }`, where
- `num` is the numerator of `q`,
- `denom` is the denominator of `q`,
- `pos` is a proof that `denom > 0`, and
- `cop` is a proof `num` and `denom` are coprime.

We then define the integral domain structure on `ℚ` and prove basic lemmas about it.
The definition of the field structure on `ℚ` will be done in `data.rat.basic` once the
`field` class has been defined.

## Main Definitions

- `rat` is the structure encoding `ℚ`.
- `rat.mk n d` constructs a rational number `q = n / d` from `n d : ℤ`.

## Notations

- `/.` is infix notation for `rat.mk`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/


/-- `rat`, or `ℚ`, is the type of rational numbers. It is defined
  as the set of pairs ⟨n, d⟩ of integers such that `d` is positive and `n` and
  `d` are coprime. This representation is preferred to the quotient
  because without periodic reduction, the numerator and denominator can grow
  exponentially (for example, adding 1/2 to itself repeatedly). -/
structure Rat where mk' ::
  num : ℤ
  denom : ℕ
  Pos : 0 < denom
  cop : num.natAbs.Coprime denom

-- mathport name: «exprℚ»
notation "ℚ" => Rat

namespace Rat

/-- String representation of a rational numbers, used in `has_repr`, `has_to_string`, and
`has_to_format` instances. -/
protected def repr : ℚ → Stringₓ
  | ⟨n, d, _, _⟩ => if d = 1 then reprₓ n else reprₓ n ++ "/" ++ reprₓ d

instance : HasRepr ℚ :=
  ⟨Rat.repr⟩

instance : HasToString ℚ :=
  ⟨Rat.repr⟩

unsafe instance : has_to_format ℚ :=
  ⟨coe ∘ Rat.repr⟩

instance : Encodable ℚ :=
  Encodable.ofEquiv (Σn : ℤ, { d : ℕ // 0 < d ∧ n.natAbs.Coprime d })
    ⟨fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => ⟨a, b, c, d⟩, fun ⟨a, b, c, d⟩ => rfl, fun ⟨a, b, c, d⟩ =>
      rfl⟩

/-- Embed an integer as a rational number -/
def ofInt (n : ℤ) : ℚ :=
  ⟨n, 1, Nat.one_posₓ, Nat.coprime_one_rightₓ _⟩

instance : Zero ℚ :=
  ⟨ofInt 0⟩

instance : One ℚ :=
  ⟨ofInt 1⟩

instance : Inhabited ℚ :=
  ⟨0⟩

theorem ext_iff {p q : ℚ} : p = q ↔ p.num = q.num ∧ p.denom = q.denom := by
  cases p
  cases q
  simp

@[ext]
theorem ext {p q : ℚ} (hn : p.num = q.num) (hd : p.denom = q.denom) : p = q :=
  Rat.ext_iff.mpr ⟨hn, hd⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ+` (not necessarily coprime) -/
def mkPnat (n : ℤ) : ℕ+ → ℚ
  | ⟨d, dpos⟩ =>
    let n' := n.natAbs
    let g := n'.gcd d
    ⟨n / g, d / g, by
      apply (Nat.le_div_iff_mul_leₓ (Nat.gcd_pos_of_pos_rightₓ _ dpos)).2
      rw [one_mulₓ]
      exact Nat.le_of_dvdₓ dpos (Nat.gcd_dvd_rightₓ _ _), by
      have : Int.natAbs (n / ↑g) = n' / g := by
        cases' Int.nat_abs_eq n with e e <;> rw [e]
        · rfl
          
        rw [Int.neg_div_of_dvd, Int.nat_abs_neg]
        · rfl
          
        exact Int.coe_nat_dvd.2 (Nat.gcd_dvd_leftₓ _ _)
      rw [this]
      exact Nat.coprime_div_gcd_div_gcdₓ (Nat.gcd_pos_of_pos_rightₓ _ dpos)⟩

/-- Form the quotient `n / d` where `n:ℤ` and `d:ℕ`. In the case `d = 0`, we
  define `n / 0 = 0` by convention. -/
def mkNat (n : ℤ) (d : ℕ) : ℚ :=
  if d0 : d = 0 then 0 else mkPnat n ⟨d, Nat.pos_of_ne_zeroₓ d0⟩

/-- Form the quotient `n / d` where `n d : ℤ`. -/
def mk : ℤ → ℤ → ℚ
  | n, (d : ℕ) => mkNat n d
  | n, -[1+ d] => mkPnat (-n) d.succPnat

-- mathport name: «expr /. »
localized [Rat] infixl:70 " /. " => Rat.mk

theorem mk_pnat_eq (n d h) : mkPnat n ⟨d, h⟩ = n /. d := by
  change n /. d with dite _ _ _ <;> simp [← ne_of_gtₓ h]

theorem mk_nat_eq (n d) : mkNat n d = n /. d :=
  rfl

@[simp]
theorem mk_zero (n) : n /. 0 = 0 :=
  rfl

@[simp]
theorem zero_mk_pnat (n) : mkPnat 0 n = 0 := by
  cases' n with n npos
  simp only [← mk_pnat, ← Int.nat_abs_zero, ← Nat.div_selfₓ npos, ← Nat.gcd_zero_leftₓ, ← Int.zero_div]
  rfl

@[simp]
theorem zero_mk_nat (n) : mkNat 0 n = 0 := by
  by_cases' n = 0 <;> simp [*, ← mk_nat]

@[simp]
theorem zero_mk (n) : 0 /. n = 0 := by
  cases n <;> simp [← mk]

private theorem gcd_abs_dvd_left {a b} : (Nat.gcdₓ (Int.natAbs a) b : ℤ) ∣ a :=
  Int.dvd_nat_abs.1 <| Int.coe_nat_dvd.2 <| Nat.gcd_dvd_leftₓ (Int.natAbs a) b

@[simp]
theorem mk_eq_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b = 0 ↔ a = 0 := by
  refine'
    ⟨fun h => _, by
      rintro rfl
      simp ⟩
  have : ∀ {a b}, mk_pnat a b = 0 → a = 0 := by
    rintro a ⟨b, h⟩ e
    injection e with e
    apply Int.eq_mul_of_div_eq_right gcd_abs_dvd_left e
  cases' b with b <;> simp only [← mk, ← mk_nat, ← Int.of_nat_eq_coe, ← dite_eq_left_iff] at h
  · simp only [← mt (congr_arg Int.ofNat) b0, ← not_false_iff, ← forall_true_left] at h
    exact this h
    
  · apply neg_injective
    simp [← this h]
    

theorem mk_ne_zero {a b : ℤ} (b0 : b ≠ 0) : a /. b ≠ 0 ↔ a ≠ 0 :=
  (mk_eq_zero b0).Not

theorem mk_eq : ∀ {a b c d : ℤ} (hb : b ≠ 0) (hd : d ≠ 0), a /. b = c /. d ↔ a * d = c * b := by
  suffices ∀ a b c d hb hd, mkPnat a ⟨b, hb⟩ = mkPnat c ⟨d, hd⟩ ↔ a * d = c * b by
    intros
    cases' b with b b <;> simp [← mk, ← mk_nat, ← Nat.succPnat]
    simp [← mt (congr_arg Int.ofNat) hb]
    all_goals
      cases' d with d d <;> simp [← mk, ← mk_nat, ← Nat.succPnat]
      simp [← mt (congr_arg Int.ofNat) hd]
      all_goals
        rw [this]
        try
          rfl
    · change a * ↑d.succ = -c * ↑b ↔ a * -d.succ = c * b
      constructor <;>
        intro h <;>
          apply neg_injective <;>
            simpa [← left_distrib, ← neg_add_eq_iff_eq_add, ← eq_neg_iff_add_eq_zero, ← neg_eq_iff_add_eq_zero] using h
      
    · change -a * ↑d = c * b.succ ↔ a * d = c * -b.succ
      constructor <;> intro h <;> apply neg_injective <;> simpa [← left_distrib, ← eq_comm] using h
      
    · change -a * d.succ = -c * b.succ ↔ a * -d.succ = c * -b.succ
      simp [← left_distrib, ← sub_eq_add_neg]
      cc
      
  intros
  simp [← mk_pnat]
  constructor <;> intro h
  · cases' h with ha hb
    have ha := by
      have dv := @gcd_abs_dvd_left
      have := Int.eq_mul_of_div_eq_right dv ha
      rw [← Int.mul_div_assoc _ dv] at this
      exact Int.eq_mul_of_div_eq_left (dv.mul_left _) this.symm
    have hb := by
      have dv := fun {a b} => Nat.gcd_dvd_rightₓ (Int.natAbs a) b
      have := Nat.eq_mul_of_div_eq_right dv hb
      rw [← Nat.mul_div_assocₓ _ dv] at this
      exact Nat.eq_mul_of_div_eq_left (dv.mul_left _) this.symm
    have m0 : (a.nat_abs.gcd b * c.nat_abs.gcd d : ℤ) ≠ 0 := by
      refine' Int.coe_nat_ne_zero.2 (ne_of_gtₓ _)
      apply mul_pos <;> apply Nat.gcd_pos_of_pos_rightₓ <;> assumption
    apply mul_right_cancel₀ m0
    simpa [← mul_comm, ← mul_left_commₓ] using congr (congr_arg (· * ·) ha.symm) (congr_arg coe hb)
    
  · suffices ∀ a c, a * d = c * b → a / a.gcd b = c / c.gcd d ∧ b / a.gcd b = d / c.gcd d by
      cases'
        this a.nat_abs c.nat_abs
          (by
            simpa [← Int.nat_abs_mul] using congr_arg Int.natAbs h) with
        h₁ h₂
      have hs := congr_arg Int.sign h
      simp [← Int.sign_eq_one_of_posₓ (Int.coe_nat_lt.2 hb), ← Int.sign_eq_one_of_posₓ (Int.coe_nat_lt.2 hd)] at hs
      conv in a => rw [← Int.sign_mul_nat_abs a]
      conv in c => rw [← Int.sign_mul_nat_abs c]
      rw [Int.mul_div_assoc, Int.mul_div_assoc]
      exact ⟨congr (congr_arg (· * ·) hs) (congr_arg coe h₁), h₂⟩
      all_goals
        exact Int.coe_nat_dvd.2 (Nat.gcd_dvd_leftₓ _ _)
    intro a c h
    suffices bd : b / a.gcd b = d / c.gcd d
    · refine' ⟨_, bd⟩
      apply Nat.eq_of_mul_eq_mul_leftₓ hb
      rw [← Nat.mul_div_assocₓ _ (Nat.gcd_dvd_leftₓ _ _), mul_comm, Nat.mul_div_assocₓ _ (Nat.gcd_dvd_rightₓ _ _), bd, ←
        Nat.mul_div_assocₓ _ (Nat.gcd_dvd_rightₓ _ _), h, mul_comm, Nat.mul_div_assocₓ _ (Nat.gcd_dvd_leftₓ _ _)]
      
    suffices ∀ {a c : ℕ}, ∀ b > 0, ∀, ∀ d > 0, ∀, a * d = c * b → b / a.gcd b ≤ d / c.gcd d by
      exact le_antisymmₓ (this _ hb _ hd h) (this _ hd _ hb h.symm)
    intro a c b hb d hd h
    have gb0 := Nat.gcd_pos_of_pos_rightₓ a hb
    have gd0 := Nat.gcd_pos_of_pos_rightₓ c hd
    apply Nat.le_of_dvdₓ
    apply (Nat.le_div_iff_mul_leₓ gd0).2
    simp
    apply Nat.le_of_dvdₓ hd (Nat.gcd_dvd_rightₓ _ _)
    apply (Nat.coprime_div_gcd_div_gcdₓ gb0).symm.dvd_of_dvd_mul_left
    refine' ⟨c / c.gcd d, _⟩
    rw [← Nat.mul_div_assocₓ _ (Nat.gcd_dvd_leftₓ _ _), ← Nat.mul_div_assocₓ _ (Nat.gcd_dvd_rightₓ _ _)]
    apply congr_arg (· / c.gcd d)
    rw [mul_comm, ← Nat.mul_div_assocₓ _ (Nat.gcd_dvd_leftₓ _ _), mul_comm, h,
      Nat.mul_div_assocₓ _ (Nat.gcd_dvd_rightₓ _ _), mul_comm]
    

@[simp]
theorem div_mk_div_cancel_left {a b c : ℤ} (c0 : c ≠ 0) : a * c /. (b * c) = a /. b := by
  by_cases' b0 : b = 0
  · subst b0
    simp
    
  apply (mk_eq (mul_ne_zero b0 c0) b0).2
  simp [← mul_comm, ← mul_assoc]

@[simp]
theorem num_denom : ∀ {a : ℚ}, a.num /. a.denom = a
  | ⟨n, d, h, (c : _ = 1)⟩ =>
    show mkNat n d = _ by
      simp [← mk_nat, ← ne_of_gtₓ h, ← mk_pnat, ← c]

theorem num_denom' {n d h c} : (⟨n, d, h, c⟩ : ℚ) = n /. d :=
  num_denom.symm

theorem of_int_eq_mk (z : ℤ) : ofInt z = z /. 1 :=
  num_denom'

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `0 < d` and coprime `n`, `d`. -/
@[elab_as_eliminator]
def numDenomCasesOn.{u} {C : ℚ → Sort u} : ∀ (a : ℚ) (H : ∀ n d, 0 < d → (Int.natAbs n).Coprime d → C (n /. d)), C a
  | ⟨n, d, h, c⟩, H => by
    rw [num_denom'] <;> exact H n d h c

/-- Define a (dependent) function or prove `∀ r : ℚ, p r` by dealing with rational
numbers of the form `n /. d` with `d ≠ 0`. -/
@[elab_as_eliminator]
def numDenomCasesOn'.{u} {C : ℚ → Sort u} (a : ℚ) (H : ∀ (n : ℤ) (d : ℕ), d ≠ 0 → C (n /. d)) : C a :=
  (numDenomCasesOn a) fun n d h c => H n d h.ne'

theorem num_dvd (a) {b : ℤ} (b0 : b ≠ 0) : (a /. b).num ∣ a := by
  cases' e : a /. b with n d h c
  rw [Rat.num_denom', Rat.mk_eq b0 (ne_of_gtₓ (Int.coe_nat_pos.2 h))] at e
  refine' Int.nat_abs_dvd.1 <| Int.dvd_nat_abs.1 <| Int.coe_nat_dvd.2 <| c.dvd_of_dvd_mul_right _
  have := congr_arg Int.natAbs e
  simp only [← Int.nat_abs_mul, ← Int.nat_abs_of_nat] at this
  simp [← this]

theorem denom_dvd (a b : ℤ) : ((a /. b).denom : ℤ) ∣ b := by
  by_cases' b0 : b = 0
  · simp [← b0]
    
  cases' e : a /. b with n d h c
  rw [num_denom', mk_eq b0 (ne_of_gtₓ (Int.coe_nat_pos.2 h))] at e
  refine' Int.dvd_nat_abs.1 <| Int.coe_nat_dvd.2 <| c.symm.dvd_of_dvd_mul_left _
  rw [← Int.nat_abs_mul, ← Int.coe_nat_dvd, Int.dvd_nat_abs, ← e]
  simp

/-- Addition of rational numbers. Use `(+)` instead. -/
protected def add : ℚ → ℚ → ℚ
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => mkPnat (n₁ * d₂ + n₂ * d₁) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : Add ℚ :=
  ⟨Rat.add⟩

theorem lift_binop_eq (f : ℚ → ℚ → ℚ) (f₁ : ℤ → ℤ → ℤ → ℤ → ℤ) (f₂ : ℤ → ℤ → ℤ → ℤ → ℤ)
    (fv : ∀ {n₁ d₁ h₁ c₁ n₂ d₂ h₂ c₂}, f ⟨n₁, d₁, h₁, c₁⟩ ⟨n₂, d₂, h₂, c₂⟩ = f₁ n₁ d₁ n₂ d₂ /. f₂ n₁ d₁ n₂ d₂)
    (f0 : ∀ {n₁ d₁ n₂ d₂} (d₁0 : d₁ ≠ 0) (d₂0 : d₂ ≠ 0), f₂ n₁ d₁ n₂ d₂ ≠ 0) (a b c d : ℤ) (b0 : b ≠ 0) (d0 : d ≠ 0)
    (H :
      ∀ {n₁ d₁ n₂ d₂} (h₁ : a * d₁ = n₁ * b) (h₂ : c * d₂ = n₂ * d),
        f₁ n₁ d₁ n₂ d₂ * f₂ a b c d = f₁ a b c d * f₂ n₁ d₁ n₂ d₂) :
    f (a /. b) (c /. d) = f₁ a b c d /. f₂ a b c d := by
  generalize ha : a /. b = x
  cases' x with n₁ d₁ h₁ c₁
  rw [num_denom'] at ha
  generalize hc : c /. d = x
  cases' x with n₂ d₂ h₂ c₂
  rw [num_denom'] at hc
  rw [fv]
  have d₁0 := ne_of_gtₓ (Int.coe_nat_lt.2 h₁)
  have d₂0 := ne_of_gtₓ (Int.coe_nat_lt.2 h₂)
  exact (mk_eq (f0 d₁0 d₂0) (f0 b0 d0)).2 (H ((mk_eq b0 d₁0).1 ha) ((mk_eq d0 d₂0).1 hc))

@[simp]
theorem add_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : a /. b + c /. d = (a * d + c * b) /. (b * d) := by
  apply lift_binop_eq Rat.add <;>
    intros <;>
      try
        assumption
  · apply mk_pnat_eq
    
  · apply mul_ne_zero d₁0 d₂0
    
  calc (n₁ * d₂ + n₂ * d₁) * (b * d) = n₁ * b * d₂ * d + n₂ * d * (d₁ * b) := by
      simp [← mul_addₓ, ← mul_comm, ← mul_left_commₓ]_ = a * d₁ * d₂ * d + c * d₂ * (d₁ * b) := by
      rw [h₁, h₂]_ = (a * d + c * b) * (d₁ * d₂) := by
      simp [← mul_addₓ, ← mul_comm, ← mul_left_commₓ]

/-- Negation of rational numbers. Use `-r` instead. -/
protected def neg (r : ℚ) : ℚ :=
  ⟨-r.num, r.denom, r.Pos, by
    simp [← r.cop]⟩

instance : Neg ℚ :=
  ⟨Rat.neg⟩

@[simp]
theorem neg_def {a b : ℤ} : -(a /. b) = -a /. b := by
  by_cases' b0 : b = 0
  · subst b0
    simp
    rfl
    
  generalize ha : a /. b = x
  cases' x with n₁ d₁ h₁ c₁
  rw [num_denom'] at ha
  show Rat.mk' _ _ _ _ = _
  rw [num_denom']
  have d0 := ne_of_gtₓ (Int.coe_nat_lt.2 h₁)
  apply (mk_eq d0 b0).2
  have h₁ := (mk_eq b0 d0).1 ha
  simp only [← neg_mul, ← congr_arg Neg.neg h₁]

@[simp]
theorem mk_neg_denom (n d : ℤ) : n /. -d = -n /. d := by
  by_cases' hd : d = 0 <;> simp [← Rat.mk_eq, ← hd]

/-- Multiplication of rational numbers. Use `(*)` instead. -/
protected def mul : ℚ → ℚ → ℚ
  | ⟨n₁, d₁, h₁, c₁⟩, ⟨n₂, d₂, h₂, c₂⟩ => mkPnat (n₁ * n₂) ⟨d₁ * d₂, mul_pos h₁ h₂⟩

instance : Mul ℚ :=
  ⟨Rat.mul⟩

@[simp]
theorem mul_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : a /. b * (c /. d) = a * c /. (b * d) := by
  apply lift_binop_eq Rat.mul <;>
    intros <;>
      try
        assumption
  · apply mk_pnat_eq
    
  · apply mul_ne_zero d₁0 d₂0
    
  cc

/-- Inverse rational number. Use `r⁻¹` instead. -/
protected def inv : ℚ → ℚ
  | ⟨(n + 1 : ℕ), d, h, c⟩ => ⟨d, n + 1, n.succ_pos, c.symm⟩
  | ⟨0, d, h, c⟩ => 0
  | ⟨-[1+ n], d, h, c⟩ =>
    ⟨-d, n + 1, n.succ_pos,
      Nat.Coprime.symm <| by
        simp <;> exact c⟩

instance : Inv ℚ :=
  ⟨Rat.inv⟩

instance : Div ℚ :=
  ⟨fun a b => a * b⁻¹⟩

@[simp]
theorem inv_def {a b : ℤ} : (a /. b)⁻¹ = b /. a := by
  by_cases' a0 : a = 0
  · subst a0
    simp
    rfl
    
  by_cases' b0 : b = 0
  · subst b0
    simp
    rfl
    
  generalize ha : a /. b = x
  cases' x with n d h c
  rw [num_denom'] at ha
  refine' Eq.trans (_ : Rat.inv ⟨n, d, h, c⟩ = d /. n) _
  · cases' n with n <;> [cases' n with n, skip]
    · rfl
      
    · change Int.ofNat n.succ with (n + 1 : ℕ)
      unfold Rat.inv
      rw [num_denom']
      
    · unfold Rat.inv
      rw [num_denom']
      rfl
      
    
  have n0 : n ≠ 0 := by
    rintro rfl
    rw [Rat.zero_mk, mk_eq_zero b0] at ha
    exact a0 ha
  have d0 := ne_of_gtₓ (Int.coe_nat_lt.2 h)
  have ha := (mk_eq b0 d0).1 ha
  apply (mk_eq n0 a0).2
  cc

variable (a b c : ℚ)

protected theorem add_zero : a + 0 = a :=
  (numDenomCasesOn' a) fun n d h => by
    rw [← zero_mk d] <;> simp [← h, -zero_mk]

protected theorem zero_add : 0 + a = a :=
  (numDenomCasesOn' a) fun n d h => by
    rw [← zero_mk d] <;> simp [← h, -zero_mk]

protected theorem add_comm : a + b = b + a :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ => by
      simp [← h₁, ← h₂] <;> cc

protected theorem add_assoc : a + b + c = a + (b + c) :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ =>
      (numDenomCasesOn' c) fun n₃ d₃ h₃ => by
        simp [← h₁, ← h₂, ← h₃, ← mul_ne_zero, ← mul_addₓ, ← mul_comm, ← mul_left_commₓ, ← add_left_commₓ, ← add_assocₓ]

protected theorem add_left_neg : -a + a = 0 :=
  (numDenomCasesOn' a) fun n d h => by
    simp [← h]

@[simp]
theorem mk_zero_one : 0 /. 1 = 0 :=
  show mkPnat _ _ = _ by
    rw [mk_pnat]
    simp
    rfl

@[simp]
theorem mk_one_one : 1 /. 1 = 1 :=
  show mkPnat _ _ = _ by
    rw [mk_pnat]
    simp
    rfl

@[simp]
theorem mk_neg_one_one : -1 /. 1 = -1 :=
  show mkPnat _ _ = _ by
    rw [mk_pnat]
    simp
    rfl

protected theorem mul_one : a * 1 = a :=
  (numDenomCasesOn' a) fun n d h => by
    rw [← mk_one_one]
    simp [← h, -mk_one_one]

protected theorem one_mul : 1 * a = a :=
  (numDenomCasesOn' a) fun n d h => by
    rw [← mk_one_one]
    simp [← h, -mk_one_one]

protected theorem mul_comm : a * b = b * a :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ => by
      simp [← h₁, ← h₂, ← mul_comm]

protected theorem mul_assoc : a * b * c = a * (b * c) :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ =>
      (numDenomCasesOn' c) fun n₃ d₃ h₃ => by
        simp [← h₁, ← h₂, ← h₃, ← mul_ne_zero, ← mul_comm, ← mul_left_commₓ]

protected theorem add_mul : (a + b) * c = a * c + b * c :=
  (numDenomCasesOn' a) fun n₁ d₁ h₁ =>
    (numDenomCasesOn' b) fun n₂ d₂ h₂ =>
      (numDenomCasesOn' c) fun n₃ d₃ h₃ => by
        simp [← h₁, ← h₂, ← h₃, ← mul_ne_zero] <;>
          refine' (div_mk_div_cancel_left (Int.coe_nat_ne_zero.2 h₃)).symm.trans _ <;>
            simp [← mul_addₓ, ← mul_comm, ← mul_assoc, ← mul_left_commₓ]

protected theorem mul_add : a * (b + c) = a * b + a * c := by
  rw [Rat.mul_comm, Rat.add_mul, Rat.mul_comm, Rat.mul_comm c a]

protected theorem zero_ne_one : 0 ≠ (1 : ℚ) := by
  rw [ne_comm, ← mk_one_one, mk_ne_zero one_ne_zero]
  exact one_ne_zero

protected theorem mul_inv_cancel : a ≠ 0 → a * a⁻¹ = 1 :=
  (numDenomCasesOn' a) fun n d h a0 => by
    have n0 : n ≠ 0 :=
      mt
        (by
          rintro rfl
          simp )
        a0
    simpa [← h, ← n0, ← mul_comm] using @div_mk_div_cancel_left 1 1 _ n0

protected theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 :=
  Eq.trans (Rat.mul_comm _ _) (Rat.mul_inv_cancel _ h)

instance : DecidableEq ℚ := by
  run_tac
    tactic.mk_dec_eq_instance

/-! At this point in the import hierarchy we have not defined the `field` typeclass.
Instead we'll instantiate `comm_ring` and `comm_group_with_zero` at this point.
The `rat.field` instance and any field-specific lemmas can be found in `data.rat.basic`.
-/


instance : CommRingₓ ℚ where
  zero := 0
  add := (· + ·)
  neg := Neg.neg
  one := 1
  mul := (· * ·)
  zero_add := Rat.zero_add
  add_zero := Rat.add_zero
  add_comm := Rat.add_comm
  add_assoc := Rat.add_assoc
  add_left_neg := Rat.add_left_neg
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  mul_comm := Rat.mul_comm
  mul_assoc := Rat.mul_assoc
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  natCast := fun n => Rat.ofInt n
  nat_cast_zero := rfl
  nat_cast_succ := fun n =>
    show ofInt _ = ofInt _ + 1 by
      simp only [← of_int_eq_mk, ← add_def one_ne_zero one_ne_zero, mk_one_one] <;> simp

instance : CommGroupWithZero ℚ :=
  { Rat.commRing with zero := 0, one := 1, mul := (· * ·), inv := Inv.inv, div := (· / ·),
    exists_pair_ne := ⟨0, 1, Rat.zero_ne_one⟩, inv_zero := rfl, mul_inv_cancel := Rat.mul_inv_cancel,
    mul_zero := mul_zero, zero_mul := zero_mul }

instance : IsDomain ℚ :=
  { Rat.commGroupWithZero, (inferInstance : NoZeroDivisors ℚ) with }

-- Extra instances to short-circuit type class resolution 
-- TODO(Mario): this instance slows down data.real.basic
instance : Nontrivial ℚ := by
  infer_instance

--instance : ring ℚ             := by apply_instance
instance : CommSemiringₓ ℚ := by
  infer_instance

instance : Semiringₓ ℚ := by
  infer_instance

instance : AddCommGroupₓ ℚ := by
  infer_instance

instance : AddGroupₓ ℚ := by
  infer_instance

instance : AddCommMonoidₓ ℚ := by
  infer_instance

instance : AddMonoidₓ ℚ := by
  infer_instance

instance : AddLeftCancelSemigroup ℚ := by
  infer_instance

instance : AddRightCancelSemigroup ℚ := by
  infer_instance

instance : AddCommSemigroupₓ ℚ := by
  infer_instance

instance : AddSemigroupₓ ℚ := by
  infer_instance

instance : CommMonoidₓ ℚ := by
  infer_instance

instance : Monoidₓ ℚ := by
  infer_instance

instance : CommSemigroupₓ ℚ := by
  infer_instance

instance : Semigroupₓ ℚ := by
  infer_instance

theorem sub_def {a b c d : ℤ} (b0 : b ≠ 0) (d0 : d ≠ 0) : a /. b - c /. d = (a * d - c * b) /. (b * d) := by
  simp [← b0, ← d0, ← sub_eq_add_neg]

@[simp]
theorem denom_neg_eq_denom (q : ℚ) : (-q).denom = q.denom :=
  rfl

@[simp]
theorem num_neg_eq_neg_num (q : ℚ) : (-q).num = -q.num :=
  rfl

@[simp]
theorem num_zero : Rat.num 0 = 0 :=
  rfl

@[simp]
theorem denom_zero : Rat.denom 0 = 1 :=
  rfl

theorem zero_of_num_zero {q : ℚ} (hq : q.num = 0) : q = 0 := by
  have : q = q.num /. q.denom := num_denom.symm
  simpa [← hq]

theorem zero_iff_num_zero {q : ℚ} : q = 0 ↔ q.num = 0 :=
  ⟨fun _ => by
    simp [*], zero_of_num_zero⟩

theorem num_ne_zero_of_ne_zero {q : ℚ} (h : q ≠ 0) : q.num ≠ 0 := fun this : q.num = 0 => h <| zero_of_num_zero this

@[simp]
theorem num_one : (1 : ℚ).num = 1 :=
  rfl

@[simp]
theorem denom_one : (1 : ℚ).denom = 1 :=
  rfl

theorem denom_ne_zero (q : ℚ) : q.denom ≠ 0 :=
  ne_of_gtₓ q.Pos

theorem eq_iff_mul_eq_mul {p q : ℚ} : p = q ↔ p.num * q.denom = q.num * p.denom := by
  conv => lhs rw [← @num_denom p, ← @num_denom q]
  apply Rat.mk_eq <;> rw [← Nat.cast_zeroₓ, Ne, Int.coe_nat_eq_coe_nat_iff] <;> apply denom_ne_zero

theorem mk_num_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : n ≠ 0 := fun this : n = 0 =>
  hq <| by
    simpa [← this] using hqnd

theorem mk_denom_ne_zero_of_ne_zero {q : ℚ} {n d : ℤ} (hq : q ≠ 0) (hqnd : q = n /. d) : d ≠ 0 := fun this : d = 0 =>
  hq <| by
    simpa [← this] using hqnd

theorem mk_ne_zero_of_ne_zero {n d : ℤ} (h : n ≠ 0) (hd : d ≠ 0) : n /. d ≠ 0 :=
  (mk_ne_zero hd).mpr h

theorem mul_num_denom (q r : ℚ) : q * r = q.num * r.num /. ↑(q.denom * r.denom) := by
  have hq' : (↑q.denom : ℤ) ≠ 0 := by
    have := denom_ne_zero q <;> simpa
  have hr' : (↑r.denom : ℤ) ≠ 0 := by
    have := denom_ne_zero r <;> simpa
  suffices q.num /. ↑q.denom * (r.num /. ↑r.denom) = q.num * r.num /. ↑(q.denom * r.denom) by
    simpa using this
  simp [← mul_def hq' hr', -num_denom]

theorem div_num_denom (q r : ℚ) : q / r = q.num * r.denom /. (q.denom * r.num) :=
  if hr : r.num = 0 then by
    have hr' : r = 0 := zero_of_num_zero hr
    simp [*]
  else
    calc
      q / r = q * r⁻¹ := div_eq_mul_inv q r
      _ = q.num /. q.denom * (r.num /. r.denom)⁻¹ := by
        simp
      _ = q.num /. q.denom * (r.denom /. r.num) := by
        rw [inv_def]
      _ = q.num * r.denom /. (q.denom * r.num) :=
        mul_def
          (by
            simpa using denom_ne_zero q)
          hr
      

theorem num_denom_mk {q : ℚ} {n d : ℤ} (hd : d ≠ 0) (qdf : q = n /. d) : ∃ c : ℤ, n = c * q.num ∧ d = c * q.denom := by
  obtain rfl | hn := eq_or_ne n 0
  · simp [← qdf]
    
  have : q.num * d = n * ↑q.denom := by
    refine' (Rat.mk_eq _ hd).mp _
    · exact int.coe_nat_ne_zero.mpr (Rat.denom_ne_zero _)
      
    · rwa [num_denom]
      
  have hqdn : q.num ∣ n := by
    rw [qdf]
    exact Rat.num_dvd _ hd
  refine' ⟨n / q.num, _, _⟩
  · rw [Int.div_mul_cancel hqdn]
    
  · refine' Int.eq_mul_div_of_mul_eq_mul_of_dvd_left _ hqdn this
    rw [qdf]
    exact Rat.num_ne_zero_of_ne_zero ((mk_ne_zero hd).mpr hn)
    

theorem mk_pnat_num (n : ℤ) (d : ℕ+) : (mkPnat n d).num = n / Nat.gcdₓ n.natAbs d := by
  cases d <;> rfl

theorem mk_pnat_denom (n : ℤ) (d : ℕ+) : (mkPnat n d).denom = d / Nat.gcdₓ n.natAbs d := by
  cases d <;> rfl

theorem num_mk (n d : ℤ) : (n /. d).num = d.sign * n / n.gcd d := by
  rcases d with ((_ | _) | _) <;>
    simp [← Rat.mk, ← mk_nat, ← mk_pnat, ← Nat.succPnat, ← Int.sign, ← Int.gcdₓ, -Nat.cast_succₓ, -Int.coe_nat_succ, ←
      Int.zero_div]

theorem denom_mk (n d : ℤ) : (n /. d).denom = if d = 0 then 1 else d.natAbs / n.gcd d := by
  rcases d with ((_ | _) | _) <;>
    simp [← Rat.mk, ← mk_nat, ← mk_pnat, ← Nat.succPnat, ← Int.sign, ← Int.gcdₓ, -Nat.cast_succₓ, -Int.coe_nat_succ]

theorem mk_pnat_denom_dvd (n : ℤ) (d : ℕ+) : (mkPnat n d).denom ∣ d.1 := by
  rw [mk_pnat_denom]
  apply Nat.div_dvd_of_dvd
  apply Nat.gcd_dvd_rightₓ

theorem add_denom_dvd (q₁ q₂ : ℚ) : (q₁ + q₂).denom ∣ q₁.denom * q₂.denom := by
  cases q₁
  cases q₂
  apply mk_pnat_denom_dvd

theorem mul_denom_dvd (q₁ q₂ : ℚ) : (q₁ * q₂).denom ∣ q₁.denom * q₂.denom := by
  cases q₁
  cases q₂
  apply mk_pnat_denom_dvd

theorem mul_num (q₁ q₂ : ℚ) :
    (q₁ * q₂).num = q₁.num * q₂.num / Nat.gcdₓ (q₁.num * q₂.num).natAbs (q₁.denom * q₂.denom) := by
  cases q₁ <;> cases q₂ <;> rfl

theorem mul_denom (q₁ q₂ : ℚ) :
    (q₁ * q₂).denom = q₁.denom * q₂.denom / Nat.gcdₓ (q₁.num * q₂.num).natAbs (q₁.denom * q₂.denom) := by
  cases q₁ <;> cases q₂ <;> rfl

theorem mul_self_num (q : ℚ) : (q * q).num = q.num * q.num := by
  rw [mul_num, Int.nat_abs_mul, Nat.Coprime.gcd_eq_one, Int.coe_nat_one, Int.div_one] <;>
    exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

theorem mul_self_denom (q : ℚ) : (q * q).denom = q.denom * q.denom := by
  rw [Rat.mul_denom, Int.nat_abs_mul, Nat.Coprime.gcd_eq_one, Nat.div_oneₓ] <;>
    exact (q.cop.mul_right q.cop).mul (q.cop.mul_right q.cop)

theorem add_num_denom (q r : ℚ) : q + r = (q.num * r.denom + q.denom * r.num : ℤ) /. (↑q.denom * ↑r.denom : ℤ) := by
  have hqd : (q.denom : ℤ) ≠ 0 := Int.coe_nat_ne_zero_iff_pos.2 q.3
  have hrd : (r.denom : ℤ) ≠ 0 := Int.coe_nat_ne_zero_iff_pos.2 r.3
  conv_lhs => rw [← @num_denom q, ← @num_denom r, Rat.add_def hqd hrd] <;> simp [← mul_comm]

section Casts

protected theorem add_mk (a b c : ℤ) : (a + b) /. c = a /. c + b /. c :=
  if h : c = 0 then by
    simp [← h]
  else by
    rw [add_def h h, mk_eq h (mul_ne_zero h h)]
    simp [← add_mulₓ, ← mul_assoc]

theorem coe_int_eq_mk : ∀ z : ℤ, ↑z = z /. 1
  | (n : ℕ) => of_int_eq_mk _
  | -[1+ n] =>
    show -ofInt _ = _ by
      simp [← of_int_eq_mk, ← neg_def, ← Int.neg_succ_of_nat_coe]

theorem mk_eq_div (n d : ℤ) : n /. d = (n : ℚ) / d := by
  by_cases' d0 : d = 0
  · simp [← d0, ← div_zero]
    
  simp [← division_def, ← coe_int_eq_mk, ← mul_def one_ne_zero d0]

theorem mk_mul_mk_cancel {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x * (x /. d) = n /. d := by
  by_cases' hd : d = 0
  · rw [hd]
    simp
    
  rw [mul_def hx hd, mul_comm x, div_mk_div_cancel_left hx]

theorem mk_div_mk_cancel_left {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : n /. x / (d /. x) = n /. d := by
  rw [div_eq_mul_inv, inv_def, mk_mul_mk_cancel hx]

theorem mk_div_mk_cancel_right {x : ℤ} (hx : x ≠ 0) (n d : ℤ) : x /. n / (x /. d) = d /. n := by
  rw [div_eq_mul_inv, inv_def, mul_comm, mk_mul_mk_cancel hx]

theorem coe_int_div_eq_mk {n d : ℤ} : (n : ℚ) / ↑d = n /. d := by
  repeat'
    rw [coe_int_eq_mk]
  exact mk_div_mk_cancel_left one_ne_zero n d

@[simp]
theorem num_div_denom (r : ℚ) : (r.num / r.denom : ℚ) = r := by
  rw [← Int.cast_coe_nat, ← mk_eq_div, num_denom]

theorem exists_eq_mul_div_num_and_eq_mul_div_denom (n : ℤ) {d : ℤ} (d_ne_zero : d ≠ 0) :
    ∃ c : ℤ, n = c * ((n : ℚ) / d).num ∧ (d : ℤ) = c * ((n : ℚ) / d).denom := by
  have : (n : ℚ) / d = Rat.mk n d := by
    rw [← Rat.mk_eq_div]
  exact Rat.num_denom_mk d_ne_zero this

theorem mul_num_denom' (q r : ℚ) : (q * r).num * q.denom * r.denom = q.num * r.num * (q * r).denom := by
  let s := q.num * r.num /. (q.denom * r.denom : ℤ)
  have hs : (q.denom * r.denom : ℤ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_denom⟩⟩ := exists_eq_mul_div_num_and_eq_mul_div_denom (q.num * r.num) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 0[c_mul_denom]
  repeat'
    rw [mul_assoc]
  apply mul_eq_mul_left_iff.2
  rw [or_iff_not_imp_right]
  intro c_pos
  have h : _ = s :=
    @mul_def q.num q.denom r.num r.denom (int.coe_nat_ne_zero_iff_pos.mpr q.pos) (int.coe_nat_ne_zero_iff_pos.mpr r.pos)
  rw [num_denom, num_denom] at h
  rw [h]
  rw [mul_comm]
  apply rat.eq_iff_mul_eq_mul.mp
  rw [← mk_eq_div]

theorem add_num_denom' (q r : ℚ) :
    (q + r).num * q.denom * r.denom = (q.num * r.denom + r.num * q.denom) * (q + r).denom := by
  let s := mk (q.num * r.denom + r.num * q.denom) (q.denom * r.denom : ℤ)
  have hs : (q.denom * r.denom : ℤ) ≠ 0 := int.coe_nat_ne_zero_iff_pos.mpr (mul_pos q.pos r.pos)
  obtain ⟨c, ⟨c_mul_num, c_mul_denom⟩⟩ :=
    exists_eq_mul_div_num_and_eq_mul_div_denom (q.num * r.denom + r.num * q.denom) hs
  rw [c_mul_num, mul_assoc, mul_comm]
  nth_rw 0[c_mul_denom]
  repeat'
    rw [mul_assoc]
  apply mul_eq_mul_left_iff.2
  rw [or_iff_not_imp_right]
  intro c_pos
  have h : _ = s :=
    @add_def q.num q.denom r.num r.denom (int.coe_nat_ne_zero_iff_pos.mpr q.pos) (int.coe_nat_ne_zero_iff_pos.mpr r.pos)
  rw [num_denom, num_denom] at h
  rw [h]
  rw [mul_comm]
  apply rat.eq_iff_mul_eq_mul.mp
  rw [← mk_eq_div]

theorem substr_num_denom' (q r : ℚ) :
    (q - r).num * q.denom * r.denom = (q.num * r.denom - r.num * q.denom) * (q - r).denom := by
  rw [sub_eq_add_neg, sub_eq_add_neg, ← neg_mul, ← num_neg_eq_neg_num, ← denom_neg_eq_denom r, add_num_denom' q (-r)]

theorem coe_int_eq_of_int (z : ℤ) : ↑z = ofInt z :=
  (coe_int_eq_mk z).trans (of_int_eq_mk z).symm

@[simp, norm_cast]
theorem coe_int_num (n : ℤ) : (n : ℚ).num = n := by
  rw [coe_int_eq_of_int] <;> rfl

@[simp, norm_cast]
theorem coe_int_denom (n : ℤ) : (n : ℚ).denom = 1 := by
  rw [coe_int_eq_of_int] <;> rfl

theorem coe_int_num_of_denom_eq_one {q : ℚ} (hq : q.denom = 1) : ↑q.num = q := by
  conv_rhs => rw [← @num_denom q, hq]
  rw [coe_int_eq_mk]
  rfl

theorem denom_eq_one_iff (r : ℚ) : r.denom = 1 ↔ ↑r.num = r :=
  ⟨Rat.coe_int_num_of_denom_eq_one, fun h => h ▸ Rat.coe_int_denom r.num⟩

instance : CanLift ℚ ℤ :=
  ⟨coe, fun q => q.denom = 1, fun q hq => ⟨q.num, coe_int_num_of_denom_eq_one hq⟩⟩

theorem coe_nat_eq_mk (n : ℕ) : ↑n = n /. 1 := by
  rw [← Int.cast_coe_nat, coe_int_eq_mk]

@[simp, norm_cast]
theorem coe_nat_num (n : ℕ) : (n : ℚ).num = n := by
  rw [← Int.cast_coe_nat, coe_int_num]

@[simp, norm_cast]
theorem coe_nat_denom (n : ℕ) : (n : ℚ).denom = 1 := by
  rw [← Int.cast_coe_nat, coe_int_denom]

-- Will be subsumed by `int.coe_inj` after we have defined
-- `linear_ordered_field ℚ` (which implies characteristic zero).
theorem coe_int_inj (m n : ℤ) : (m : ℚ) = n ↔ m = n :=
  ⟨fun h => by
    simpa using congr_arg num h, congr_arg _⟩

end Casts

theorem inv_def' {q : ℚ} : q⁻¹ = (q.denom : ℚ) / q.num := by
  conv_lhs => rw [← @num_denom q]
  cases q
  simp [← div_num_denom]

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
-- ./././Mathport/Syntax/Translate/Basic.lean:646:40: in rw #[["<-", expr @num_denom q]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg
@[simp]
theorem mul_denom_eq_num {q : ℚ} : q * q.denom = q.num := by
  suffices mk q.num ↑q.denom * mk (↑q.denom) 1 = mk q.num 1 by
    conv =>
      for q [1] =>
        trace
          "./././Mathport/Syntax/Translate/Basic.lean:646:40: in rw #[[\"<-\", expr @num_denom q]]: ./././Mathport/Syntax/Translate/Tactic/Basic.lean:54:35: expecting parse arg"
    rwa [coe_int_eq_mk, coe_nat_eq_mk]
  have : (q.denom : ℤ) ≠ 0 :=
    ne_of_gtₓ
      (by
        exact_mod_cast q.pos)
  rw [Rat.mul_def this one_ne_zero, mul_comm (q.denom : ℤ) 1, div_mk_div_cancel_left this]

theorem denom_div_cast_eq_one_iff (m n : ℤ) (hn : n ≠ 0) : ((m : ℚ) / n).denom = 1 ↔ n ∣ m := by
  replace hn : (n : ℚ) ≠ 0
  · rwa [Ne.def, ← Int.cast_zeroₓ, coe_int_inj]
    
  constructor
  · intro h
    lift (m : ℚ) / n to ℤ using h with k hk
    use k
    rwa [eq_div_iff_mul_eq hn, ← Int.cast_mul, mul_comm, eq_comm, coe_int_inj] at hk
    
  · rintro ⟨d, rfl⟩
    rw [Int.cast_mul, mul_comm, mul_div_cancel _ hn, Rat.coe_int_denom]
    

theorem num_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) : (a / b : ℚ).num = a := by
  lift b to ℕ using le_of_ltₓ hb0
  norm_cast  at hb0 h
  rw [← Rat.mk_eq_div, ← Rat.mk_pnat_eq a b hb0, Rat.mk_pnat_num, Pnat.mk_coe, h.gcd_eq_one, Int.coe_nat_one,
    Int.div_one]

theorem denom_div_eq_of_coprime {a b : ℤ} (hb0 : 0 < b) (h : Nat.Coprime a.natAbs b.natAbs) :
    ((a / b : ℚ).denom : ℤ) = b := by
  lift b to ℕ using le_of_ltₓ hb0
  norm_cast  at hb0 h
  rw [← Rat.mk_eq_div, ← Rat.mk_pnat_eq a b hb0, Rat.mk_pnat_denom, Pnat.mk_coe, h.gcd_eq_one, Nat.div_oneₓ]

theorem div_int_inj {a b c d : ℤ} (hb0 : 0 < b) (hd0 : 0 < d) (h1 : Nat.Coprime a.natAbs b.natAbs)
    (h2 : Nat.Coprime c.natAbs d.natAbs) (h : (a : ℚ) / b = (c : ℚ) / d) : a = c ∧ b = d := by
  apply And.intro
  · rw [← num_div_eq_of_coprime hb0 h1, h, num_div_eq_of_coprime hd0 h2]
    
  · rw [← denom_div_eq_of_coprime hb0 h1, h, denom_div_eq_of_coprime hd0 h2]
    

@[norm_cast]
theorem coe_int_div_self (n : ℤ) : ((n / n : ℤ) : ℚ) = n / n := by
  by_cases' hn : n = 0
  · subst hn
    simp only [← Int.cast_zeroₓ, ← Int.zero_div, ← zero_div]
    
  · have : (n : ℚ) ≠ 0 := by
      rwa [← coe_int_inj] at hn
    simp only [← Int.div_self hn, ← Int.cast_oneₓ, ← Ne.def, ← not_false_iff, ← div_self this]
    

@[norm_cast]
theorem coe_nat_div_self (n : ℕ) : ((n / n : ℕ) : ℚ) = n / n :=
  coe_int_div_self n

theorem coe_int_div (a b : ℤ) (h : b ∣ a) : ((a / b : ℤ) : ℚ) = a / b := by
  rcases h with ⟨c, rfl⟩
  simp only [← mul_comm b, ← Int.mul_div_assoc c (dvd_refl b), ← Int.cast_mul, ← mul_div_assoc, ← coe_int_div_self]

theorem coe_nat_div (a b : ℕ) (h : b ∣ a) : ((a / b : ℕ) : ℚ) = a / b := by
  rcases h with ⟨c, rfl⟩
  simp only [← mul_comm b, ← Nat.mul_div_assocₓ c (dvd_refl b), ← Nat.cast_mulₓ, ← mul_div_assoc, ← coe_nat_div_self]

theorem inv_coe_int_num {a : ℤ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 := by
  rw [Rat.inv_def', Rat.coe_int_num, Rat.coe_int_denom, Nat.cast_oneₓ, ← Int.cast_oneₓ]
  apply num_div_eq_of_coprime ha0
  rw [Int.nat_abs_one]
  exact Nat.coprime_one_leftₓ _

theorem inv_coe_nat_num {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.num = 1 :=
  inv_coe_int_num
    (by
      exact_mod_cast ha0 : 0 < (a : ℤ))

theorem inv_coe_int_denom {a : ℤ} (ha0 : 0 < a) : ((a : ℚ)⁻¹.denom : ℤ) = a := by
  rw [Rat.inv_def', Rat.coe_int_num, Rat.coe_int_denom, Nat.cast_oneₓ, ← Int.cast_oneₓ]
  apply denom_div_eq_of_coprime ha0
  rw [Int.nat_abs_one]
  exact Nat.coprime_one_leftₓ _

theorem inv_coe_nat_denom {a : ℕ} (ha0 : 0 < a) : (a : ℚ)⁻¹.denom = a := by
  rw [← Int.coe_nat_eq_coe_nat_iff, ← Int.cast_coe_nat a, inv_coe_int_denom]
  rwa [← Nat.cast_zeroₓ, Nat.cast_lt]

protected theorem forall {p : ℚ → Prop} : (∀ r, p r) ↔ ∀ a b : ℤ, p (a / b) :=
  ⟨fun h _ _ => h _, fun h q =>
    show q = q.num / q.denom by
          simp [← Rat.div_num_denom].symm ▸
      h q.1 q.2⟩

protected theorem exists {p : ℚ → Prop} : (∃ r, p r) ↔ ∃ a b : ℤ, p (a / b) :=
  ⟨fun ⟨r, hr⟩ =>
    ⟨r.num, r.denom, by
      rwa [← mk_eq_div, num_denom]⟩,
    fun ⟨a, b, h⟩ => ⟨_, h⟩⟩

/-!
### Denominator as `ℕ+`
-/


section PnatDenom

/-- Denominator as `ℕ+`. -/
def pnatDenom (x : ℚ) : ℕ+ :=
  ⟨x.denom, x.Pos⟩

@[simp]
theorem coe_pnat_denom (x : ℚ) : (x.pnatDenom : ℕ) = x.denom :=
  rfl

@[simp]
theorem mk_pnat_pnat_denom_eq (x : ℚ) : mkPnat x.num x.pnatDenom = x := by
  rw [pnat_denom, mk_pnat_eq, num_denom]

theorem pnat_denom_eq_iff_denom_eq {x : ℚ} {n : ℕ+} : x.pnatDenom = n ↔ x.denom = ↑n :=
  Subtype.ext_iff

end PnatDenom

end Rat

