/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Neil Strickland
-/
import Mathbin.Data.Nat.Basic

/-!
# The positive natural numbers

This file defines the type `ℕ+` or `pnat`, the subtype of natural numbers that are positive.
-/


/-- `ℕ+` is the type of positive natural numbers. It is defined as a subtype,
  and the VM representation of `ℕ+` is the same as `ℕ` because the proof
  is not stored. -/
def Pnat :=
  { n : ℕ // 0 < n }

-- mathport name: «exprℕ+»
notation "ℕ+" => Pnat

instance coePnatNat : Coe ℕ+ ℕ :=
  ⟨Subtype.val⟩

instance : HasRepr ℕ+ :=
  ⟨fun n => reprₓ n.1⟩

/-- Predecessor of a `ℕ+`, as a `ℕ`. -/
def Pnat.natPred (i : ℕ+) : ℕ :=
  i - 1

@[simp]
theorem Pnat.one_add_nat_pred (n : ℕ+) : 1 + n.natPred = n := by
  rw [Pnat.natPred, add_tsub_cancel_iff_le.mpr <| show 1 ≤ (n : ℕ) from n.2]

@[simp]
theorem Pnat.nat_pred_add_one (n : ℕ+) : n.natPred + 1 = n :=
  (add_commₓ _ _).trans n.one_add_nat_pred

@[simp]
theorem Pnat.nat_pred_eq_pred {n : ℕ} (h : 0 < n) : Pnat.natPred (⟨n, h⟩ : ℕ+) = n.pred :=
  rfl

namespace Nat

/-- Convert a natural number to a positive natural number. The
  positivity assumption is inferred by `dec_trivial`. -/
def toPnat (n : ℕ)
    (h : 0 < n := by
      run_tac
        tactic.exact_dec_trivial) :
    ℕ+ :=
  ⟨n, h⟩

/-- Write a successor as an element of `ℕ+`. -/
def succPnat (n : ℕ) : ℕ+ :=
  ⟨succ n, succ_posₓ n⟩

@[simp]
theorem succ_pnat_coe (n : ℕ) : (succPnat n : ℕ) = succ n :=
  rfl

theorem succ_pnat_inj {n m : ℕ} : succPnat n = succPnat m → n = m := fun h => by
  let h' := congr_arg (coe : ℕ+ → ℕ) h
  exact Nat.succ.injₓ h'

/-- Convert a natural number to a pnat. `n+1` is mapped to itself,
  and `0` becomes `1`. -/
def toPnat' (n : ℕ) : ℕ+ :=
  succPnat (pred n)

@[simp]
theorem to_pnat'_coe : ∀ n : ℕ, (toPnat' n : ℕ) = ite (0 < n) n 1
  | 0 => rfl
  | m + 1 => by
    rw [if_pos (succ_pos m)]
    rfl

end Nat

namespace Pnat

open Nat

/-- We now define a long list of structures on ℕ+ induced by
 similar structures on ℕ. Most of these behave in a completely
 obvious way, but there are a few things to be said about
 subtraction, division and powers.
-/
instance : DecidableEq ℕ+ := fun a b : ℕ+ => by
  infer_instance

instance : LinearOrderₓ ℕ+ :=
  Subtype.linearOrder _

@[simp]
theorem mk_le_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) ≤ ⟨k, hk⟩ ↔ n ≤ k :=
  Iff.rfl

@[simp]
theorem mk_lt_mk (n k : ℕ) (hn : 0 < n) (hk : 0 < k) : (⟨n, hn⟩ : ℕ+) < ⟨k, hk⟩ ↔ n < k :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe (n k : ℕ+) : (n : ℕ) ≤ k ↔ n ≤ k :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_lt_coe (n k : ℕ+) : (n : ℕ) < k ↔ n < k :=
  Iff.rfl

@[simp]
theorem pos (n : ℕ+) : 0 < (n : ℕ) :=
  n.2

-- see note [fact non_instances]
theorem fact_pos (n : ℕ+) : Fact (0 < ↑n) :=
  ⟨n.Pos⟩

theorem eq {m n : ℕ+} : (m : ℕ) = n → m = n :=
  Subtype.eq

@[simp]
theorem coe_inj {m n : ℕ+} : (m : ℕ) = n ↔ m = n :=
  SetCoe.ext_iff

theorem coe_injective : Function.Injective (coe : ℕ+ → ℕ) :=
  Subtype.coe_injective

@[simp]
theorem mk_coe (n h) : ((⟨n, h⟩ : ℕ+) : ℕ) = n :=
  rfl

instance : Add ℕ+ :=
  ⟨fun a b => ⟨(a + b : ℕ), add_pos a.Pos b.Pos⟩⟩

instance : AddCommSemigroupₓ ℕ+ :=
  coe_injective.AddCommSemigroup coe fun _ _ => rfl

@[simp]
theorem add_coe (m n : ℕ+) : ((m + n : ℕ+) : ℕ) = m + n :=
  rfl

/-- `pnat.coe` promoted to an `add_hom`, that is, a morphism which preserves addition. -/
def coeAddHom : AddHom ℕ+ ℕ where
  toFun := coe
  map_add' := add_coe

instance : AddLeftCancelSemigroup ℕ+ :=
  coe_injective.AddLeftCancelSemigroup coe fun _ _ => rfl

instance : AddRightCancelSemigroup ℕ+ :=
  coe_injective.AddRightCancelSemigroup coe fun _ _ => rfl

/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps]
def succOrderIso : ℕ ≃o ℕ+ where
  toFun := fun n => ⟨_, succ_posₓ n⟩
  invFun := fun n => pred (n : ℕ)
  left_inv := pred_succ
  right_inv := fun ⟨x, hx⟩ => by
    simpa using succ_pred_eq_of_pos hx
  map_rel_iff' := @succ_le_succ_iff

instance (priority := 10) : CovariantClass ℕ+ ℕ+ (· + ·) (· ≤ ·) :=
  ⟨by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨c, hc⟩
    simp [Pnat.coe_le_coe]⟩

@[simp]
theorem ne_zero (n : ℕ+) : (n : ℕ) ≠ 0 :=
  n.2.ne'

theorem to_pnat'_coe {n : ℕ} : 0 < n → (n.toPnat' : ℕ) = n :=
  succ_pred_eq_of_pos

@[simp]
theorem coe_to_pnat' (n : ℕ+) : (n : ℕ).toPnat' = n :=
  eq (to_pnat'_coe n.Pos)

instance : Mul ℕ+ :=
  ⟨fun m n => ⟨m.1 * n.1, mul_pos m.2 n.2⟩⟩

instance : One ℕ+ :=
  ⟨succPnat 0⟩

instance : Pow ℕ+ ℕ :=
  ⟨fun x n => ⟨x ^ n, pow_pos x.2 n⟩⟩

instance : CommMonoidₓ ℕ+ :=
  coe_injective.CommMonoid coe rfl (fun _ _ => rfl) fun _ _ => rfl

theorem lt_add_one_iff : ∀ {a b : ℕ+}, a < b + 1 ↔ a ≤ b := fun a b => Nat.lt_add_one_iff

theorem add_one_le_iff : ∀ {a b : ℕ+}, a + 1 ≤ b ↔ a < b := fun a b => Nat.add_one_le_iff

@[simp]
theorem one_le (n : ℕ+) : (1 : ℕ+) ≤ n :=
  n.2

@[simp]
theorem not_lt_one (n : ℕ+) : ¬n < 1 :=
  not_lt_of_le n.one_le

instance : OrderBot ℕ+ where
  bot := 1
  bot_le := fun a => a.property

@[simp]
theorem bot_eq_one : (⊥ : ℕ+) = 1 :=
  rfl

instance : Inhabited ℕ+ :=
  ⟨1⟩

-- Some lemmas that rewrite `pnat.mk n h`, for `n` an explicit numeral, into explicit numerals.
@[simp]
theorem mk_one {h} : (⟨1, h⟩ : ℕ+) = (1 : ℕ+) :=
  rfl

@[simp]
theorem mk_bit0 (n) {h} : (⟨bit0 n, h⟩ : ℕ+) = (bit0 ⟨n, pos_of_bit0_pos h⟩ : ℕ+) :=
  rfl

@[simp]
theorem mk_bit1 (n) {h} {k} : (⟨bit1 n, h⟩ : ℕ+) = (bit1 ⟨n, k⟩ : ℕ+) :=
  rfl

-- Some lemmas that rewrite inequalities between explicit numerals in `ℕ+`
-- into the corresponding inequalities in `ℕ`.
-- TODO: perhaps this should not be attempted by `simp`,
-- and instead we should expect `norm_num` to take care of these directly?
-- TODO: these lemmas are perhaps incomplete:
-- * 1 is not represented as a bit0 or bit1
-- * strict inequalities?
@[simp]
theorem bit0_le_bit0 (n m : ℕ+) : bit0 n ≤ bit0 m ↔ bit0 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl

@[simp]
theorem bit0_le_bit1 (n m : ℕ+) : bit0 n ≤ bit1 m ↔ bit0 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl

@[simp]
theorem bit1_le_bit0 (n m : ℕ+) : bit1 n ≤ bit0 m ↔ bit1 (n : ℕ) ≤ bit0 (m : ℕ) :=
  Iff.rfl

@[simp]
theorem bit1_le_bit1 (n m : ℕ+) : bit1 n ≤ bit1 m ↔ bit1 (n : ℕ) ≤ bit1 (m : ℕ) :=
  Iff.rfl

@[simp]
theorem one_coe : ((1 : ℕ+) : ℕ) = 1 :=
  rfl

@[simp]
theorem mul_coe (m n : ℕ+) : ((m * n : ℕ+) : ℕ) = m * n :=
  rfl

/-- `pnat.coe` promoted to a `monoid_hom`. -/
def coeMonoidHom : ℕ+ →* ℕ where
  toFun := coe
  map_one' := one_coe
  map_mul' := mul_coe

@[simp]
theorem coe_coe_monoid_hom : (coeMonoidHom : ℕ+ → ℕ) = coe :=
  rfl

@[simp]
theorem coe_eq_one_iff {m : ℕ+} : (m : ℕ) = 1 ↔ m = 1 := by
  constructor <;>
    intro h <;>
      try
          apply Pnat.eq <;>
        rw [h] <;> simp

@[simp]
theorem le_one_iff {n : ℕ+} : n ≤ 1 ↔ n = 1 := by
  rcases n with ⟨_ | n, hn⟩
  · exact absurd hn (lt_irreflₓ _)
    
  · simp [Pnat.coe_le_coe, ← Subtype.ext_iff, ← Nat.succ_le_succ_iff, ← Nat.succ_inj']
    

theorem lt_add_left (n m : ℕ+) : n < m + n := by
  rcases m with ⟨_ | m, hm⟩
  · exact absurd hm (lt_irreflₓ _)
    
  · simp [Pnat.coe_lt_coe]
    

theorem lt_add_right (n m : ℕ+) : n < n + m :=
  (lt_add_left n m).trans_le (add_commₓ _ _).le

@[simp]
theorem coe_bit0 (a : ℕ+) : ((bit0 a : ℕ+) : ℕ) = bit0 (a : ℕ) :=
  rfl

@[simp]
theorem coe_bit1 (a : ℕ+) : ((bit1 a : ℕ+) : ℕ) = bit1 (a : ℕ) :=
  rfl

@[simp]
theorem pow_coe (m : ℕ+) (n : ℕ) : ((m ^ n : ℕ+) : ℕ) = (m : ℕ) ^ n :=
  rfl

instance : OrderedCancelCommMonoid ℕ+ :=
  { Pnat.commMonoid, Pnat.linearOrder with
    mul_le_mul_left := by
      intros
      apply Nat.mul_le_mul_leftₓ
      assumption,
    le_of_mul_le_mul_left := by
      intro a b c h
      apply Nat.le_of_mul_le_mul_leftₓ h a.property,
    mul_left_cancel := fun a b c h => by
      replace h := congr_arg (coe : ℕ+ → ℕ) h
      exact Eq ((Nat.mul_right_inj a.pos).mp h) }

instance : Distribₓ ℕ+ :=
  coe_injective.Distrib coe (fun _ _ => rfl) fun _ _ => rfl

/-- Subtraction a - b is defined in the obvious way when
  a > b, and by a - b = 1 if a ≤ b.
-/
instance : Sub ℕ+ :=
  ⟨fun a b => toPnat' (a - b : ℕ)⟩

theorem sub_coe (a b : ℕ+) : ((a - b : ℕ+) : ℕ) = ite (b < a) (a - b : ℕ) 1 := by
  change (to_pnat' _ : ℕ) = ite _ _ _
  split_ifs with h
  · exact to_pnat'_coe (tsub_pos_of_lt h)
    
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gtₓ h : (a : ℕ) ≤ b)]
    rfl
    

theorem add_sub_of_lt {a b : ℕ+} : a < b → a + (b - a) = b := fun h =>
  Eq <| by
    rw [add_coe, sub_coe, if_pos h]
    exact add_tsub_cancel_of_le h.le

instance : HasWellFounded ℕ+ :=
  ⟨(· < ·), measure_wf coe⟩

/-- Strong induction on `ℕ+`. -/
def strongInductionOn {p : ℕ+ → Sort _} : ∀ (n : ℕ+) (h : ∀ k, (∀ m, m < k → p m) → p k), p n
  | n => fun IH => IH _ fun a h => strong_induction_on a IH

/-- If `n : ℕ+` is different from `1`, then it is the successor of some `k : ℕ+`. -/
theorem exists_eq_succ_of_ne_one : ∀ {n : ℕ+} (h1 : n ≠ 1), ∃ k : ℕ+, n = k + 1
  | ⟨1, _⟩, h1 => False.elim <| h1 rfl
  | ⟨n + 2, _⟩, _ =>
    ⟨⟨n + 1, by
        simp ⟩,
      rfl⟩

/-- Strong induction on `ℕ+`, with `n = 1` treated separately. -/
def caseStrongInductionOn {p : ℕ+ → Sort _} (a : ℕ+) (hz : p 1) (hi : ∀ n, (∀ m, m ≤ n → p m) → p (n + 1)) : p a := by
  apply strong_induction_on a
  rintro ⟨k, kprop⟩ hk
  cases' k with k
  · exact (lt_irreflₓ 0 kprop).elim
    
  cases' k with k
  · exact hz
    
  exact hi ⟨k.succ, Nat.succ_posₓ _⟩ fun m hm => hk _ (lt_succ_iff.2 hm)

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_eliminator]
def recOn (n : ℕ+) {p : ℕ+ → Sort _} (p1 : p 1) (hp : ∀ n, p n → p (n + 1)) : p n := by
  rcases n with ⟨n, h⟩
  induction' n with n IH
  · exact
      absurd h
        (by
          decide)
    
  · cases' n with n
    · exact p1
      
    · exact hp _ (IH n.succ_pos)
      
    

@[simp]
theorem rec_on_one {p} (p1 hp) : @Pnat.recOn 1 p p1 hp = p1 :=
  rfl

@[simp]
theorem rec_on_succ (n : ℕ+) {p : ℕ+ → Sort _} (p1 hp) : @Pnat.recOn (n + 1) p p1 hp = hp n (@Pnat.recOn n p p1 hp) :=
  by
  cases' n with n h
  cases n <;>
    [exact
      absurd h
        (by
          decide),
    rfl]

/-- We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def modDivAux : ℕ+ → ℕ → ℕ → ℕ+ × ℕ
  | k, 0, q => ⟨k, q.pred⟩
  | k, r + 1, q => ⟨⟨r + 1, Nat.succ_posₓ r⟩, q⟩

theorem mod_div_aux_spec :
    ∀ (k : ℕ+) (r q : ℕ) (h : ¬(r = 0 ∧ q = 0)), ((modDivAux k r q).1 : ℕ) + k * (modDivAux k r q).2 = r + k * q
  | k, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, h => by
    change (k : ℕ) + (k : ℕ) * (q + 1).pred = 0 + (k : ℕ) * (q + 1)
    rw [Nat.pred_succ, Nat.mul_succ, zero_addₓ, add_commₓ]
  | k, r + 1, q, h => rfl

/-- `mod_div m k = (m % k, m / k)`.
  We define `m % k` and `m / k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` and
  `m / k = n - 1`.  This ensures that `m % k` is always positive
  and `m = (m % k) + k * (m / k)` in all cases.  Later we
  define a function `div_exact` which gives the usual `m / k`
  in the case where `k` divides `m`.
-/
def modDiv (m k : ℕ+) : ℕ+ × ℕ :=
  modDivAux k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ))

/-- We define `m % k` in the same way as for `ℕ`
  except that when `m = n * k` we take `m % k = k` This ensures that `m % k` is always positive.
-/
def mod (m k : ℕ+) : ℕ+ :=
  (modDiv m k).1

/-- We define `m / k` in the same way as for `ℕ` except that when `m = n * k` we take
  `m / k = n - 1`. This ensures that `m = (m % k) + k * (m / k)` in all cases. Later we
  define a function `div_exact` which gives the usual `m / k` in the case where `k` divides `m`.
-/
def div (m k : ℕ+) : ℕ :=
  (modDiv m k).2

theorem mod_add_div (m k : ℕ+) : (mod m k + k * div m k : ℕ) = m := by
  let h₀ := Nat.mod_add_divₓ (m : ℕ) (k : ℕ)
  have : ¬((m : ℕ) % (k : ℕ) = 0 ∧ (m : ℕ) / (k : ℕ) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr, hq, mul_zero, zero_addₓ] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := mod_div_aux_spec k ((m : ℕ) % (k : ℕ)) ((m : ℕ) / (k : ℕ)) this
  exact this.trans h₀

theorem div_add_mod (m k : ℕ+) : (k * div m k + mod m k : ℕ) = m :=
  (add_commₓ _ _).trans (mod_add_div _ _)

theorem mod_add_div' (m k : ℕ+) : (mod m k + div m k * k : ℕ) = m := by
  rw [mul_comm]
  exact mod_add_div _ _

theorem div_add_mod' (m k : ℕ+) : (div m k * k + mod m k : ℕ) = m := by
  rw [mul_comm]
  exact div_add_mod _ _

theorem mod_coe (m k : ℕ+) : (mod m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) (k : ℕ) ((m : ℕ) % (k : ℕ)) := by
  dsimp' [← mod, ← mod_div]
  cases (m : ℕ) % (k : ℕ)
  · rw [if_pos rfl]
    rfl
    
  · rw [if_neg n.succ_ne_zero]
    rfl
    

theorem div_coe (m k : ℕ+) : (div m k : ℕ) = ite ((m : ℕ) % (k : ℕ) = 0) ((m : ℕ) / (k : ℕ)).pred ((m : ℕ) / (k : ℕ)) :=
  by
  dsimp' [← div, ← mod_div]
  cases (m : ℕ) % (k : ℕ)
  · rw [if_pos rfl]
    rfl
    
  · rw [if_neg n.succ_ne_zero]
    rfl
    

theorem mod_le (m k : ℕ+) : mod m k ≤ m ∧ mod m k ≤ k := by
  change (mod m k : ℕ) ≤ (m : ℕ) ∧ (mod m k : ℕ) ≤ (k : ℕ)
  rw [mod_coe]
  split_ifs
  · have hm : (m : ℕ) > 0 := m.pos
    rw [← Nat.mod_add_divₓ (m : ℕ) (k : ℕ), h, zero_addₓ] at hm⊢
    by_cases' h' : (m : ℕ) / (k : ℕ) = 0
    · rw [h', mul_zero] at hm
      exact (lt_irreflₓ _ hm).elim
      
    · let h' := Nat.mul_le_mul_leftₓ (k : ℕ) (Nat.succ_le_of_ltₓ (Nat.pos_of_ne_zeroₓ h'))
      rw [mul_oneₓ] at h'
      exact ⟨h', le_reflₓ (k : ℕ)⟩
      
    
  · exact ⟨Nat.mod_leₓ (m : ℕ) (k : ℕ), (Nat.mod_ltₓ (m : ℕ) k.pos).le⟩
    

theorem dvd_iff {k m : ℕ+} : k ∣ m ↔ (k : ℕ) ∣ (m : ℕ) := by
  constructor <;> intro h
  rcases h with ⟨_, rfl⟩
  apply dvd_mul_right
  rcases h with ⟨a, h⟩
  cases a
  · contrapose h
    apply ne_zero
    
  use a.succ
  apply Nat.succ_posₓ
  rw [← coe_inj, h, mul_coe, mk_coe]

theorem dvd_iff' {k m : ℕ+} : k ∣ m ↔ mod m k = k := by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zeroₓ]
  constructor
  · intro h
    apply Eq
    rw [mod_coe, if_pos h]
    
  · intro h
    by_cases' h' : (m : ℕ) % (k : ℕ) = 0
    · exact h'
      
    · replace h : (mod m k : ℕ) = (k : ℕ) := congr_arg _ h
      rw [mod_coe, if_neg h'] at h
      exact ((Nat.mod_ltₓ (m : ℕ) k.pos).Ne h).elim
      
    

theorem le_of_dvd {m n : ℕ+} : m ∣ n → m ≤ n := by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left

/-- If `h : k | m`, then `k * (div_exact m k) = m`. Note that this is not equal to `m / k`. -/
def divExact (m k : ℕ+) : ℕ+ :=
  ⟨(div m k).succ, Nat.succ_posₓ _⟩

theorem mul_div_exact {m k : ℕ+} (h : k ∣ m) : k * divExact m k = m := by
  apply Eq
  rw [mul_coe]
  change (k : ℕ) * (div m k).succ = m
  rw [← div_add_mod m k, dvd_iff'.mp h, Nat.mul_succ]

theorem dvd_antisymm {m n : ℕ+} : m ∣ n → n ∣ m → m = n := fun hmn hnm => (le_of_dvd hmn).antisymm (le_of_dvd hnm)

theorem dvd_one_iff (n : ℕ+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩

theorem pos_of_div_pos {n : ℕ+} {a : ℕ} (h : a ∣ n) : 0 < a := by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact Pnat.ne_zero n (eq_zero_of_zero_dvd h)

end Pnat

section CanLift

instance Nat.canLiftPnat : CanLift ℕ ℕ+ :=
  ⟨coe, fun n => 0 < n, fun n hn => ⟨Nat.toPnat' n, Pnat.to_pnat'_coe hn⟩⟩

instance Int.canLiftPnat : CanLift ℤ ℕ+ :=
  ⟨coe, fun n => 0 < n, fun n hn =>
    ⟨Nat.toPnat' (Int.natAbs n), by
      rw [coe_coe, Nat.to_pnat'_coe, if_pos (Int.nat_abs_pos_of_ne_zero hn.ne'), Int.nat_abs_of_nonneg hn.le]⟩⟩

end CanLift

