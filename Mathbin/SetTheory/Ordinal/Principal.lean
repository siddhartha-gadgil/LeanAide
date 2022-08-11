/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathbin.SetTheory.Ordinal.FixedPoint

/-!
### Principal ordinals

We define principal or indecomposable ordinals, and we prove the standard properties about them.

### Main definitions and results
* `principal`: A principal or indecomposable ordinal under some binary operation. We include 0 and
  any other typically excluded edge cases for simplicity.
* `unbounded_principal`: Principal ordinals are unbounded.
* `principal_add_iff_zero_or_omega_opow`: The main characterization theorem for additive principal
  ordinals.
* `principal_mul_iff_le_two_or_omega_opow_opow`: The main characterization theorem for
  multiplicative principal ordinals.

### Todo
* Prove that exponential principal ordinals are 0, 1, 2, ω, or epsilon numbers, i.e. fixed points
  of `λ x, ω ^ x`.
-/


universe u

noncomputable section

open Order

namespace Ordinal

-- mathport name: «expr ^ »
local infixr:0 "^" => @pow Ordinal Ordinal Ordinal.hasPow

/-! ### Principal ordinals -/


/-- An ordinal `o` is said to be principal or indecomposable under an operation when the set of
ordinals less than it is closed under that operation. In standard mathematical usage, this term is
almost exclusively used for additive and multiplicative principal ordinals.

For simplicity, we break usual convention and regard 0 as principal. -/
def Principal (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Prop :=
  ∀ ⦃a b⦄, a < o → b < o → op a b < o

theorem principal_iff_principal_swap {op : Ordinal → Ordinal → Ordinal} {o : Ordinal} :
    Principal op o ↔ Principal (Function.swap op) o := by
  constructor <;> exact fun h a b ha hb => h hb ha

theorem principal_zero {op : Ordinal → Ordinal → Ordinal} : Principal op 0 := fun a _ h =>
  (Ordinal.not_lt_zero a h).elim

@[simp]
theorem principal_one_iff {op : Ordinal → Ordinal → Ordinal} : Principal op 1 ↔ op 0 0 = 0 := by
  refine' ⟨fun h => _, fun h a b ha hb => _⟩
  · rwa [← lt_one_iff_zero]
    exact h zero_lt_one zero_lt_one
    
  · rwa [lt_one_iff_zero, ha, hb] at *
    

theorem Principal.iterate_lt {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal} (hao : a < o) (ho : Principal op o)
    (n : ℕ) : (op a^[n]) a < o := by
  induction' n with n hn
  · rwa [Function.iterate_zero]
    
  · rw [Function.iterate_succ']
    exact ho hao hn
    

theorem op_eq_self_of_principal {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal.{u}} (hao : a < o)
    (H : IsNormal (op a)) (ho : Principal op o) (ho' : IsLimit o) : op a o = o := by
  refine' le_antisymmₓ _ (H.self_le _)
  rw [← IsNormal.bsup_eq.{u, u} H ho', bsup_le_iff]
  exact fun b hbo => (ho hao hbo).le

theorem nfp_le_of_principal {op : Ordinal → Ordinal → Ordinal} {a o : Ordinal} (hao : a < o) (ho : Principal op o) :
    nfp (op a) a ≤ o :=
  nfp_le fun n => (ho.iterate_lt hao n).le

/-! ### Principal ordinals are unbounded -/


/-- The least strict upper bound of `op` applied to all pairs of ordinals less than `o`. This is
essentially a two-argument version of `ordinal.blsub`. -/
def blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) : Ordinal :=
  lsub fun x : o.out.α × o.out.α => op (typein (· < ·) x.1) (typein (· < ·) x.2)

theorem lt_blsub₂ (op : Ordinal → Ordinal → Ordinal) {o : Ordinal} {a b : Ordinal} (ha : a < o) (hb : b < o) :
    op a b < blsub₂ op o := by
  convert
    lt_lsub _
      (Prod.mk
        (enum (· < ·) a
          (by
            rwa [type_lt]))
        (enum (· < ·) b
          (by
            rwa [type_lt])))
  simp only [← typein_enum]

theorem principal_nfp_blsub₂ (op : Ordinal → Ordinal → Ordinal) (o : Ordinal) :
    Principal op (nfp (blsub₂.{u, u} op) o) := fun a b ha hb => by
  rw [lt_nfp] at *
  cases' ha with m hm
  cases' hb with n hn
  cases' le_totalₓ ((blsub₂.{u, u} op^[m]) o) ((blsub₂.{u, u} op^[n]) o) with h h
  · use n + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ op (hm.trans_le h) hn
    
  · use m + 1
    rw [Function.iterate_succ']
    exact lt_blsub₂ op hm (hn.trans_le h)
    

theorem unbounded_principal (op : Ordinal → Ordinal → Ordinal) : Set.Unbounded (· < ·) { o | Principal op o } :=
  fun o => ⟨_, principal_nfp_blsub₂ op o, (le_nfp _ o).not_lt⟩

/-! #### Additive principal ordinals -/


theorem principal_add_one : Principal (· + ·) 1 :=
  principal_one_iff.2 <| zero_addₓ 0

theorem principal_add_of_le_one {o : Ordinal} (ho : o ≤ 1) : Principal (· + ·) o := by
  rcases le_one_iff.1 ho with (rfl | rfl)
  · exact principal_zero
    
  · exact principal_add_one
    

theorem principal_add_is_limit {o : Ordinal} (ho₁ : 1 < o) (ho : Principal (· + ·) o) : o.IsLimit := by
  refine' ⟨fun ho₀ => _, fun a hao => _⟩
  · rw [ho₀] at ho₁
    exact not_lt_of_gtₓ Ordinal.zero_lt_one ho₁
    
  · cases' eq_or_ne a 0 with ha ha
    · rw [ha, succ_zero]
      exact ho₁
      
    · refine' lt_of_le_of_ltₓ _ (ho hao hao)
      rwa [← add_one_eq_succ, add_le_add_iff_left, one_le_iff_ne_zero]
      
    

theorem principal_add_iff_add_left_eq_self {o : Ordinal} : Principal (· + ·) o ↔ ∀, ∀ a < o, ∀, a + o = o := by
  refine' ⟨fun ho a hao => _, fun h a b hao hbo => _⟩
  · cases' lt_or_leₓ 1 o with ho₁ ho₁
    · exact op_eq_self_of_principal hao (add_is_normal a) ho (principal_add_is_limit ho₁ ho)
      
    · rcases le_one_iff.1 ho₁ with (rfl | rfl)
      · exact (Ordinal.not_lt_zero a hao).elim
        
      · rw [lt_one_iff_zero] at hao
        rw [hao, zero_addₓ]
        
      
    
  · rw [← h a hao]
    exact (add_is_normal a).StrictMono hbo
    

theorem exists_lt_add_of_not_principal_add {a} (ha : ¬Principal (· + ·) a) :
    ∃ (b c : _)(hb : b < a)(hc : c < a), b + c = a := by
  unfold principal  at ha
  push_neg  at ha
  rcases ha with ⟨b, c, hb, hc, H⟩
  refine' ⟨b, _, hb, lt_of_le_of_neₓ (sub_le_self a b) fun hab => _, Ordinal.add_sub_cancel_of_le hb.le⟩
  rw [← sub_le, hab] at H
  exact H.not_lt hc

theorem principal_add_iff_add_lt_ne_self {a} : Principal (· + ·) a ↔ ∀ ⦃b c⦄, b < a → c < a → b + c ≠ a :=
  ⟨fun ha b c hb hc => (ha hb hc).Ne, fun H => by
    by_contra' ha
    rcases exists_lt_add_of_not_principal_add ha with ⟨b, c, hb, hc, rfl⟩
    exact (H hb hc).irrefl⟩

theorem add_omega {a : Ordinal} (h : a < omega) : a + omega = omega := by
  rcases lt_omega.1 h with ⟨n, rfl⟩
  clear h
  induction' n with n IH
  · rw [Nat.cast_zeroₓ, zero_addₓ]
    
  · rwa [Nat.cast_succₓ, add_assocₓ, one_add_of_omega_le (le_reflₓ _)]
    

theorem principal_add_omega : Principal (· + ·) omega :=
  principal_add_iff_add_left_eq_self.2 fun a => add_omega

theorem add_omega_opow {a b : Ordinal} (h : a < (omega^b)) : a + (omega^b) = (omega^b) := by
  refine' le_antisymmₓ _ (le_add_left _ _)
  revert h
  refine' limit_rec_on b (fun h => _) (fun b _ h => _) fun b l IH h => _
  · rw [opow_zero, ← succ_zero, lt_succ_iff, Ordinal.le_zero] at h
    rw [h, zero_addₓ]
    
  · rw [opow_succ] at h
    rcases(lt_mul_of_limit omega_is_limit).1 h with ⟨x, xo, ax⟩
    refine' le_transₓ (add_le_add_right (le_of_ltₓ ax) _) _
    rw [opow_succ, ← mul_addₓ, add_omega xo]
    
  · rcases(lt_opow_of_limit omega_ne_zero l).1 h with ⟨x, xb, ax⟩
    exact
      (((add_is_normal a).trans (opow_is_normal one_lt_omega)).limit_le l).2 fun y yb =>
        (add_le_add_left (opow_le_opow_right omega_pos (le_max_rightₓ _ _)) _).trans
          (le_transₓ (IH _ (max_ltₓ xb yb) (ax.trans_le <| opow_le_opow_right omega_pos (le_max_leftₓ _ _)))
            (opow_le_opow_right omega_pos <| le_of_ltₓ <| max_ltₓ xb yb))
    

theorem principal_add_omega_opow (o : Ordinal) : Principal (· + ·) (omega^o) :=
  principal_add_iff_add_left_eq_self.2 fun a => add_omega_opow

/-- The main characterization theorem for additive principal ordinals. -/
theorem principal_add_iff_zero_or_omega_opow {o : Ordinal} : Principal (· + ·) o ↔ o = 0 ∨ ∃ a, o = (omega^a) := by
  rcases eq_or_ne o 0 with (rfl | ho)
  · simp only [← principal_zero, ← Or.inl]
    
  · rw [principal_add_iff_add_left_eq_self]
    simp only [← ho, ← false_orₓ]
    refine'
      ⟨fun H =>
        ⟨_, ((lt_or_eq_of_leₓ (opow_log_le_self _ (Ordinal.pos_iff_ne_zero.2 ho))).resolve_left fun h => _).symm⟩,
        fun ⟨b, e⟩ => e.symm ▸ fun a => add_omega_opow⟩
    have := H _ h
    have := lt_opow_succ_log_self one_lt_omega o
    rw [opow_succ, lt_mul_of_limit omega_is_limit] at this
    rcases this with ⟨a, ao, h'⟩
    rcases lt_omega.1 ao with ⟨n, rfl⟩
    clear ao
    revert h'
    apply not_lt_of_le
    suffices e : (omega^log omega o) * ↑n + o = o
    · simpa only [← e] using le_add_right ((omega^log omega o) * ↑n) o
      
    induction' n with n IH
    · simp only [← Nat.cast_zeroₓ, ← mul_zero, ← zero_addₓ]
      
    simp only [← Nat.cast_succₓ, ← mul_add_one, ← add_assocₓ, ← this, ← IH]
    

theorem opow_principal_add_of_principal_add {a} (ha : Principal (· + ·) a) (b : Ordinal) : Principal (· + ·) (a^b) := by
  rcases principal_add_iff_zero_or_omega_opow.1 ha with (rfl | ⟨c, rfl⟩)
  · rcases eq_or_ne b 0 with (rfl | hb)
    · rw [opow_zero]
      exact principal_add_one
      
    · rwa [zero_opow hb]
      
    
  · rw [← opow_mul]
    exact principal_add_omega_opow _
    

theorem add_absorp {a b c : Ordinal} (h₁ : a < (omega^b)) (h₂ : (omega^b) ≤ c) : a + c = c := by
  rw [← Ordinal.add_sub_cancel_of_le h₂, ← add_assocₓ, add_omega_opow h₁]

theorem mul_principal_add_is_principal_add (a : Ordinal.{u}) {b : Ordinal.{u}} (hb₁ : b ≠ 1)
    (hb : Principal (· + ·) b) : Principal (· + ·) (a * b) := by
  rcases eq_zero_or_pos a with (rfl | ha)
  · rw [zero_mul]
    exact principal_zero
    
  · rcases eq_zero_or_pos b with (rfl | hb₁')
    · rw [mul_zero]
      exact principal_zero
      
    · rw [← succ_le_iff, succ_zero] at hb₁'
      intro c d hc hd
      rw [lt_mul_of_limit (principal_add_is_limit (lt_of_le_of_neₓ hb₁' hb₁.symm) hb)] at *
      · rcases hc with ⟨x, hx, hx'⟩
        rcases hd with ⟨y, hy, hy'⟩
        use x + y, hb hx hy
        rw [mul_addₓ]
        exact Left.add_lt_add hx' hy'
        
      assumption'
      
    

/-! #### Multiplicative principal ordinals -/


theorem principal_mul_one : Principal (· * ·) 1 := by
  rw [principal_one_iff]
  exact zero_mul _

theorem principal_mul_two : Principal (· * ·) 2 := fun a b ha hb => by
  have h₂ : succ (1 : Ordinal) = 2 := rfl
  rw [← h₂, lt_succ_iff] at *
  convert mul_le_mul' ha hb
  exact (mul_oneₓ 1).symm

theorem principal_mul_of_le_two {o : Ordinal} (ho : o ≤ 2) : Principal (· * ·) o := by
  rcases lt_or_eq_of_leₓ ho with (ho | rfl)
  · have h₂ : succ (1 : Ordinal) = 2 := rfl
    rw [← h₂, lt_succ_iff] at ho
    rcases lt_or_eq_of_leₓ ho with (ho | rfl)
    · rw [lt_one_iff_zero.1 ho]
      exact principal_zero
      
    · exact principal_mul_one
      
    
  · exact principal_mul_two
    

theorem principal_add_of_principal_mul {o : Ordinal} (ho : Principal (· * ·) o) (ho₂ : o ≠ 2) : Principal (· + ·) o :=
  by
  cases' lt_or_gt_of_neₓ ho₂ with ho₁ ho₂
  · change o < succ 1 at ho₁
    rw [lt_succ_iff] at ho₁
    exact principal_add_of_le_one ho₁
    
  · refine' fun a b hao hbo => lt_of_le_of_ltₓ _ (ho (max_ltₓ hao hbo) ho₂)
    rw [mul_two]
    exact add_le_add (le_max_leftₓ a b) (le_max_rightₓ a b)
    

theorem principal_mul_is_limit {o : Ordinal.{u}} (ho₂ : 2 < o) (ho : Principal (· * ·) o) : o.IsLimit :=
  principal_add_is_limit ((lt_succ 1).trans ho₂) (principal_add_of_principal_mul ho (ne_of_gtₓ ho₂))

theorem principal_mul_iff_mul_left_eq {o : Ordinal} : Principal (· * ·) o ↔ ∀ a, 0 < a → a < o → a * o = o := by
  refine' ⟨fun h a ha₀ hao => _, fun h a b hao hbo => _⟩
  · cases' le_or_gtₓ o 2 with ho ho
    · convert one_mulₓ o
      apply le_antisymmₓ
      · have : a < succ 1 := hao.trans_le ho
        rwa [lt_succ_iff] at this
        
      · rwa [← succ_le_iff, succ_zero] at ha₀
        
      
    · exact op_eq_self_of_principal hao (mul_is_normal ha₀) h (principal_mul_is_limit ho h)
      
    
  · rcases eq_or_ne a 0 with (rfl | ha)
    · rwa [zero_mul]
      
    rw [← Ordinal.pos_iff_ne_zero] at ha
    rw [← h a ha hao]
    exact (mul_is_normal ha).StrictMono hbo
    

theorem principal_mul_omega : Principal (· * ·) omega := fun a b ha hb =>
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    rw [← nat_cast_mul]
    apply nat_lt_omega

theorem mul_omega {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : a * omega = omega :=
  principal_mul_iff_mul_left_eq.1 principal_mul_omega a a0 ha

theorem mul_lt_omega_opow {a b c : Ordinal} (c0 : 0 < c) (ha : a < (omega^c)) (hb : b < omega) : a * b < (omega^c) := by
  rcases zero_or_succ_or_limit c with (rfl | ⟨c, rfl⟩ | l)
  · exact (lt_irreflₓ _).elim c0
    
  · rw [opow_succ] at ha
    rcases((mul_is_normal <| opow_pos _ omega_pos).limit_lt omega_is_limit).1 ha with ⟨n, hn, an⟩
    apply (mul_le_mul_right' (le_of_ltₓ an) _).trans_lt
    rw [opow_succ, mul_assoc, mul_lt_mul_iff_left (opow_pos _ omega_pos)]
    exact principal_mul_omega hn hb
    
  · rcases((opow_is_normal one_lt_omega).limit_lt l).1 ha with ⟨x, hx, ax⟩
    refine' (mul_le_mul' (le_of_ltₓ ax) (le_of_ltₓ hb)).trans_lt _
    rw [← opow_succ, opow_lt_opow_iff_right one_lt_omega]
    exact l.2 _ hx
    

theorem mul_omega_opow_opow {a b : Ordinal} (a0 : 0 < a) (h : a < (omega^omega^b)) :
    a * (omega^omega^b) = (omega^omega^b) := by
  by_cases' b0 : b = 0
  · rw [b0, opow_zero, opow_one] at h⊢
    exact mul_omega a0 h
    
  refine'
    le_antisymmₓ _
      (by
        simpa only [← one_mulₓ] using mul_le_mul_right' (one_le_iff_pos.2 a0) (omega^omega^b))
  rcases(lt_opow_of_limit omega_ne_zero (opow_is_limit_left omega_is_limit b0)).1 h with ⟨x, xb, ax⟩
  apply (mul_le_mul_right' (le_of_ltₓ ax) _).trans
  rw [← opow_add, add_omega_opow xb]

theorem principal_mul_omega_opow_opow (o : Ordinal) : Principal (· * ·) (omega^omega^o) :=
  principal_mul_iff_mul_left_eq.2 fun a => mul_omega_opow_opow

theorem principal_add_of_principal_mul_opow {o b : Ordinal} (hb : 1 < b) (ho : Principal (· * ·) (b^o)) :
    Principal (· + ·) o := fun x y hx hy => by
  have := ho ((opow_lt_opow_iff_right hb).2 hx) ((opow_lt_opow_iff_right hb).2 hy)
  rwa [← opow_add, opow_lt_opow_iff_right hb] at this

/-- The main characterization theorem for multiplicative principal ordinals. -/
theorem principal_mul_iff_le_two_or_omega_opow_opow {o : Ordinal} :
    Principal (· * ·) o ↔ o ≤ 2 ∨ ∃ a, o = (omega^omega^a) := by
  refine' ⟨fun ho => _, _⟩
  · cases' le_or_ltₓ o 2 with ho₂ ho₂
    · exact Or.inl ho₂
      
    rcases principal_add_iff_zero_or_omega_opow.1 (principal_add_of_principal_mul ho ho₂.ne') with (rfl | ⟨a, rfl⟩)
    · exact (Ordinal.not_lt_zero 2 ho₂).elim
      
    rcases principal_add_iff_zero_or_omega_opow.1 (principal_add_of_principal_mul_opow one_lt_omega ho) with
      (rfl | ⟨b, rfl⟩)
    · rw [opow_zero] at ho₂
      exact ((lt_succ 1).not_le ho₂.le).elim
      
    exact Or.inr ⟨b, rfl⟩
    
  · rintro (ho₂ | ⟨a, rfl⟩)
    · exact principal_mul_of_le_two ho₂
      
    · exact principal_mul_omega_opow_opow a
      
    

theorem mul_omega_dvd {a : Ordinal} (a0 : 0 < a) (ha : a < omega) : ∀ {b}, omega ∣ b → a * b = b
  | _, ⟨b, rfl⟩ => by
    rw [← mul_assoc, mul_omega a0 ha]

theorem mul_eq_opow_log_succ {a b : Ordinal.{u}} (ha : 0 < a) (hb : Principal (· * ·) b) (hb₂ : 2 < b) :
    a * b = (b^succ (log b a)) := by
  apply le_antisymmₓ
  · have hbl := principal_mul_is_limit hb₂ hb
    rw [← IsNormal.bsup_eq.{u, u} (mul_is_normal ha) hbl, bsup_le_iff]
    intro c hcb
    have hb₁ : 1 < b := (lt_succ 1).trans hb₂
    have hbo₀ : (b^b.log a) ≠ 0 := Ordinal.pos_iff_ne_zero.1 (opow_pos _ (zero_lt_one.trans hb₁))
    apply le_transₓ (mul_le_mul_right' (le_of_ltₓ (lt_mul_succ_div a hbo₀)) c)
    rw [mul_assoc, opow_succ]
    refine' mul_le_mul_left' (le_of_ltₓ (hb (hbl.2 _ _) hcb)) _
    rw [div_lt hbo₀, ← opow_succ]
    exact lt_opow_succ_log_self hb₁ _
    
  · rw [opow_succ]
    exact mul_le_mul_right' (opow_log_le_self b ha) b
    

/-! #### Exponential principal ordinals -/


theorem principal_opow_omega : Principal (·^·) omega := fun a b ha hb =>
  match a, b, lt_omega.1 ha, lt_omega.1 hb with
  | _, _, ⟨m, rfl⟩, ⟨n, rfl⟩ => by
    simp_rw [← nat_cast_opow]
    apply nat_lt_omega

theorem opow_omega {a : Ordinal} (a1 : 1 < a) (h : a < omega) : (a^omega) = omega :=
  le_antisymmₓ
    ((opow_le_of_limit (one_le_iff_ne_zero.1 <| le_of_ltₓ a1) omega_is_limit).2 fun b hb =>
      (principal_opow_omega h hb).le)
    (right_le_opow _ a1)

end Ordinal

