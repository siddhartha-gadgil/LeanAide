/-
Copyright (c) 2019 Seul Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seul Baek
-/
import Mathbin.Tactic.Omega.Clause

/-
Correctness lemmas for equality elimination.
See 5.5 of <http://www.decision-procedures.org/> for details.
-/
open List.Func

namespace Omega

def symdiv (i j : Int) : Int :=
  if 2 * (i % j) < j then i / j else i / j + 1

def symmod (i j : Int) : Int :=
  if 2 * (i % j) < j then i % j else i % j - j

attribute [local semireducible] Int.Nonneg

theorem symmod_add_one_self {i : Int} : 0 < i → symmod i (i + 1) = -1 := by
  intro h1
  unfold symmod
  rw [Int.mod_eq_of_lt (le_of_ltₓ h1) (lt_add_one _), if_neg]
  simp only [← add_commₓ, ← add_neg_cancel_left, ← neg_add_rev, ← sub_eq_add_neg]
  have h2 : 2 * i = (1 + 1) * i := rfl
  simpa only [← h2, ← add_mulₓ, ← one_mulₓ, ← add_lt_add_iff_left, ← not_ltₓ] using h1

theorem mul_symdiv_eq {i j : Int} : j * symdiv i j = i - symmod i j := by
  unfold symdiv
  unfold symmod
  by_cases' h1 : 2 * (i % j) < j
  · repeat'
      rw [if_pos h1]
    rw [Int.mod_def, sub_sub_cancel]
    
  · repeat'
      rw [if_neg h1]
    rw [Int.mod_def, sub_sub, sub_sub_cancel, mul_addₓ, mul_oneₓ]
    

theorem symmod_eq {i j : Int} : symmod i j = i - j * symdiv i j := by
  rw [mul_symdiv_eq, sub_sub_cancel]

/-- (sgm v b as n) is the new value assigned to the nth variable
after a single step of equality elimination using valuation v,
term ⟨b, as⟩, and variable index n. If v satisfies the initial
constraint set, then (v ⟨n ↦ sgm v b as n⟩) satisfies the new
constraint set after equality elimination. -/
def sgm (v : Nat → Int) (b : Int) (as : List Int) (n : Nat) :=
  let a_n : Int := get n as
  let m : Int := a_n + 1
  (symmod b m + Coeffs.val v (as.map fun x => symmod x m)) / m

open List.Func

def rhs : Nat → Int → List Int → Term
  | n, b, as =>
    let m := get n as + 1
    ⟨symmod b m, (as.map fun x => symmod x m) {n ↦ -m}⟩

theorem rhs_correct_aux {v : Nat → Int} {m : Int} {as : List Int} :
    ∀ {k}, ∃ d, m * d + Coeffs.valBetween v (as.map fun x : ℤ => symmod x m) 0 k = Coeffs.valBetween v as 0 k
  | 0 => by
    exists (0 : Int)
    simp only [← add_zeroₓ, ← mul_zero, ← coeffs.val_between]
  | k + 1 => by
    simp only [← zero_addₓ, ← coeffs.val_between, ← List.map]
    cases' @rhs_correct_aux k with d h1
    rw [← h1]
    by_cases' hk : k < as.length
    · rw [get_map hk, symmod_eq, sub_mul]
      exists d + symdiv (get k as) m * v k
      ring
      
    · rw [not_ltₓ] at hk
      repeat'
        rw [get_eq_default_of_le]
      exists d
      rw [add_assocₓ]
      exact hk
      simp only [← hk, ← List.length_mapₓ]
      

open Omega

theorem rhs_correct {v : Nat → Int} {b : Int} {as : List Int} (n : Nat) :
    0 < get n as → 0 = Term.val v (b, as) → v n = Term.val (v ⟨n ↦ sgm v b as n⟩) (rhs n b as) := by
  intro h0 h1
  let a_n := get n as
  let m := a_n + 1
  have h3 : m ≠ 0 := by
    apply ne_of_gtₓ
    apply lt_transₓ h0
    simp [← a_n, ← m]
  have h2 : m * sgm v b as n = symmod b m + coeffs.val v (as.map fun x => symmod x m) := by
    simp only [← sgm, ← mul_comm m]
    rw [Int.div_mul_cancel]
    have h4 :
      ∃ c, m * c + (symmod b (get n as + 1) + coeffs.val v (as.map fun x : ℤ => symmod x m)) = term.val v (b, as) := by
      have h5 : ∃ d, m * d + coeffs.val v (as.map fun x => symmod x m) = coeffs.val v as := by
        simp only [← coeffs.val, ← List.length_mapₓ]
        apply rhs_correct_aux
      cases' h5 with d h5
      rw [symmod_eq]
      exists symdiv b m + d
      unfold term.val
      rw [← h5]
      simp only [← term.val, ← mul_addₓ, ← add_mulₓ, ← m, ← a_n]
      ring
    cases' h4 with c h4
    rw [dvd_add_iff_right (dvd_mul_right m c), h4, ← h1]
    apply dvd_zero
  apply
    calc
      v n = -(m * sgm v b as n) + symmod b m + coeffs.val_except n v (as.map fun x => symmod x m) := by
        rw [h2, ← coeffs.val_except_add_eq n]
        have hn : n < as.length := by
          by_contra hc
          rw [not_ltₓ] at hc
          rw [get_eq_default_of_le n hc] at h0
          cases h0
        rw [get_map hn]
        simp only [← a_n, ← m]
        rw [add_commₓ, symmod_add_one_self h0]
        ring
      _ = term.val (v ⟨n ↦ sgm v b as n⟩) (rhs n b as) := by
        unfold rhs
        unfold term.val
        rw [← coeffs.val_except_add_eq n, get_set, update_eq]
        have h2 : ∀ a b c : Int, a + b + c = b + (c + a) := by
          intros
          ring
        rw [h2 (-_)]
        apply fun_mono_2 rfl
        apply fun_mono_2
        · rw [coeffs.val_except_update_set]
          
        · simp only [← m, ← a_n]
          ring
          
      

def symSym (m b : Int) : Int :=
  symdiv b m + symmod b m

def coeffsReduce : Nat → Int → List Int → Term
  | n, b, as =>
    let a := get n as
    let m := a + 1
    (symSym m b, as.map (symSym m) {n ↦ -a})

theorem coeffs_reduce_correct {v : Nat → Int} {b : Int} {as : List Int} {n : Nat} :
    0 < get n as → 0 = Term.val v (b, as) → 0 = Term.val (v ⟨n ↦ sgm v b as n⟩) (coeffsReduce n b as) := by
  intro h1 h2
  let a_n := get n as
  let m := a_n + 1
  have h3 : m ≠ 0 := by
    apply ne_of_gtₓ
    apply lt_transₓ h1
    simp only [← m, ← lt_add_iff_pos_right]
  have h4 : 0 = term.val (v ⟨n ↦ sgm v b as n⟩) (coeffs_reduce n b as) * m :=
    calc
      0 = term.val v (b, as) := h2
      _ = b + coeffs.val_except n v as + a_n * (rhs n b as).val (v ⟨n ↦ sgm v b as n⟩) := by
        unfold term.val
        rw [← coeffs.val_except_add_eq n, rhs_correct n h1 h2]
        simp only [← a_n, ← add_assocₓ]
      _ =
          -(m * a_n * sgm v b as n) + (b + a_n * symmod b m) +
            (coeffs.val_except n v as + a_n * coeffs.val_except n v (as.map fun x => symmod x m)) :=
        by
        simp only [← term.val, ← rhs, ← mul_addₓ, ← m, ← a_n, ← add_assocₓ, ← add_right_injₓ, ← add_commₓ, ←
          add_left_commₓ]
        rw [← coeffs.val_except_add_eq n, get_set, update_eq, mul_addₓ]
        apply fun_mono_2
        · rw [coeffs.val_except_eq_val_except update_eq_of_ne (get_set_eq_of_ne _)]
          
        ring
      _ =
          -(m * a_n * sgm v b as n) + (b + a_n * symmod b m) +
            coeffs.val_except n v (as.map fun a_i => a_i + a_n * symmod a_i m) :=
        by
        apply fun_mono_2 rfl
        simp only [← coeffs.val_except, ← mul_addₓ]
        repeat'
          rw [← coeffs.val_between_map_mul]
        rw [add_add_add_commₓ]
        have h5 :
          add as (List.map (Mul.mul a_n) (List.map (fun x : ℤ => symmod x (get n as + 1)) as)) =
            List.map (fun a_i : ℤ => a_i + a_n * symmod a_i m) as :=
          by
          rw [List.map_mapₓ, ← map_add_map]
          apply fun_mono_2
          · have h5 : (fun x : Int => x) = id := by
              rw [Function.funext_iffₓ]
              intro x
              rfl
            rw [h5, List.map_id]
            
          · apply fun_mono_2 _ rfl
            rw [Function.funext_iffₓ]
            intro x
            simp only [← m]
            
        simp only [← List.length_mapₓ]
        repeat'
          rw [← coeffs.val_between_add, h5]
      _ = -(m * a_n * sgm v b as n) + m * sym_sym m b + coeffs.val_except n v (as.map fun a_i => m * sym_sym m a_i) :=
        by
        repeat'
          rw [add_assocₓ]
        apply fun_mono_2
        rfl
        rw [← add_assocₓ]
        have h4 : ∀ x : ℤ, x + a_n * symmod x m = m * sym_sym m x := by
          intro x
          have h5 : a_n = m - 1 := by
            simp only [← m]
            rw [add_sub_cancel]
          rw [h5, sub_mul, one_mulₓ, add_sub, add_commₓ, add_sub_assoc, ← mul_symdiv_eq]
          simp only [← sym_sym, ← mul_addₓ, ← add_commₓ]
        apply fun_mono_2 (h4 _)
        apply coeffs.val_except_eq_val_except <;> intro x h5
        rfl
        apply congr_arg
        apply fun_mono_2 _ rfl
        rw [Function.funext_iffₓ]
        apply h4
      _ = (-(a_n * sgm v b as n) + sym_sym m b + coeffs.val_except n v (as.map (sym_sym m))) * m := by
        simp only [← add_mulₓ _ _ m]
        apply fun_mono_2
        ring
        simp only [← coeffs.val_except, ← add_mulₓ _ _ m]
        apply fun_mono_2
        · rw [mul_comm _ m, ← coeffs.val_between_map_mul, List.map_mapₓ]
          
        simp only [← List.length_mapₓ, ← mul_comm _ m]
        rw [← coeffs.val_between_map_mul, List.map_mapₓ]
      _ = (sym_sym m b + (coeffs.val_except n v (as.map (sym_sym m)) + -a_n * sgm v b as n)) * m := by
        ring
      _ = term.val (v ⟨n ↦ sgm v b as n⟩) (coeffs_reduce n b as) * m := by
        simp only [← coeffs_reduce, ← term.val, ← m, ← a_n]
        rw [← coeffs.val_except_add_eq n, coeffs.val_except_update_set, get_set, update_eq]
      
  rw [← Int.mul_div_cancel (term.val _ _) h3, ← h4, Int.zero_div]

-- Requires : t1.coeffs[m] = 1
def cancel (m : Nat) (t1 t2 : Term) : Term :=
  Term.add (t1.mul (-get m t2.snd)) t2

def subst (n : Nat) (t1 t2 : Term) : Term :=
  Term.add (t1.mul (get n t2.snd)) (t2.fst, t2.snd {n ↦ 0})

theorem subst_correct {v : Nat → Int} {b : Int} {as : List Int} {t : Term} {n : Nat} :
    0 < get n as → 0 = Term.val v (b, as) → Term.val v t = Term.val (v ⟨n ↦ sgm v b as n⟩) (subst n (rhs n b as) t) :=
  by
  intro h1 h2
  simp only [← subst, ← term.val, ← term.val_add, ← term.val_mul]
  rw [← rhs_correct _ h1 h2]
  cases' t with b' as'
  simp only [← term.val]
  have h3 : coeffs.val (v ⟨n ↦ sgm v b as n⟩) (as' {n ↦ 0}) = coeffs.val_except n v as' := by
    rw [← coeffs.val_except_add_eq n, get_set, zero_mul, add_zeroₓ, coeffs.val_except_update_set]
  rw [h3, ← coeffs.val_except_add_eq n]
  ring

/-- The type of equality elimination rules. -/
inductive Ee : Type
  | drop : ee
  | nondiv : Int → ee
  | factor : Int → ee
  | neg : ee
  | reduce : Nat → ee
  | cancel : Nat → ee
  deriving has_reflect, Inhabited

namespace Ee

def repr : Ee → Stringₓ
  | drop => "↓"
  | nondiv i => i.repr ++ "∤"
  | factor i => "/" ++ i.repr
  | neg => "-"
  | reduce n => "≻" ++ n.repr
  | cancel n => "+" ++ n.repr

instance hasRepr : HasRepr Ee :=
  ⟨repr⟩

unsafe instance has_to_format : has_to_format Ee :=
  ⟨fun x => x.repr⟩

end Ee

/-- Apply a given sequence of equality elimination steps to a clause. -/
def eqElim : List Ee → Clause → Clause
  | [], ([], les) => ([], les)
  | [], (_ :: _, les) => ([], [])
  | _ :: _, ([], les) => ([], [])
  | ee.drop :: es, (Eq :: eqs, les) => eq_elim es (eqs, les)
  | ee.neg :: es, (Eq :: eqs, les) => eq_elim es (Eq.neg :: eqs, les)
  | ee.nondiv i :: es, ((b, as) :: eqs, les) => if ¬i ∣ b ∧ ∀, ∀ x ∈ as, ∀, i ∣ x then ([], [⟨-1, []⟩]) else ([], [])
  | ee.factor i :: es, ((b, as) :: eqs, les) =>
    if i ∣ b ∧ ∀, ∀ x ∈ as, ∀, i ∣ x then eq_elim es (Term.div i (b, as) :: eqs, les) else ([], [])
  | ee.reduce n :: es, ((b, as) :: eqs, les) =>
    if 0 < get n as then
      let eq' := coeffsReduce n b as
      let r := rhs n b as
      let eqs' := eqs.map (subst n r)
      let les' := les.map (subst n r)
      eq_elim es (eq' :: eqs', les')
    else ([], [])
  | ee.cancel m :: es, (Eq :: eqs, les) => eq_elim es (eqs.map (cancel m Eq), les.map (cancel m Eq))

open Tactic

theorem sat_empty : Clause.Sat ([], []) :=
  ⟨fun _ => 0,
    ⟨by
      decide, by
      decide⟩⟩

theorem sat_eq_elim : ∀ {es : List Ee} {c : Clause}, c.Sat → (eqElim es c).Sat
  | [], ([], les), h => h
  | e :: _, ([], les), h => by
    cases e <;> simp only [← eq_elim] <;> apply sat_empty
  | [], (_ :: _, les), h => sat_empty
  | ee.drop :: es, (Eq :: eqs, les), h1 => by
    apply @sat_eq_elim es _ _
    rcases h1 with ⟨v, h1, h2⟩
    refine' ⟨v, List.forall_mem_of_forall_mem_consₓ h1, h2⟩
  | ee.neg :: es, (Eq :: eqs, les), h1 => by
    simp only [← eq_elim]
    apply sat_eq_elim
    cases' h1 with v h1
    exists v
    cases' h1 with hl hr
    apply And.intro _ hr
    rw [List.forall_mem_consₓ] at *
    apply And.intro _ hl.right
    rw [term.val_neg]
    rw [← hl.left]
    rfl
  | ee.nondiv i :: es, ((b, as) :: eqs, les), h1 => by
    unfold eq_elim
    by_cases' h2 : ¬i ∣ b ∧ ∀ x : ℤ, x ∈ as → i ∣ x
    · exfalso
      cases' h1 with v h1
      have h3 : 0 = b + coeffs.val v as := h1.left _ (Or.inl rfl)
      have h4 : i ∣ coeffs.val v as := coeffs.dvd_val h2.right
      have h5 : i ∣ b + coeffs.val v as := by
        rw [← h3]
        apply dvd_zero
      rw [← dvd_add_iff_left h4] at h5
      apply h2.left h5
      
    rw [if_neg h2]
    apply sat_empty
  | ee.factor i :: es, ((b, as) :: eqs, les), h1 => by
    simp only [← eq_elim]
    by_cases' h2 : i ∣ b ∧ ∀, ∀ x ∈ as, ∀, i ∣ x
    · rw [if_pos h2]
      apply sat_eq_elim
      cases' h1 with v h1
      exists v
      cases' h1 with h3 h4
      apply And.intro _ h4
      rw [List.forall_mem_consₓ] at *
      cases' h3 with h5 h6
      apply And.intro _ h6
      rw [term.val_div h2.left h2.right, ← h5, Int.zero_div]
      
    · rw [if_neg h2]
      apply sat_empty
      
  | ee.reduce n :: es, ((b, as) :: eqs, les), h1 => by
    simp only [← eq_elim]
    by_cases' h2 : 0 < get n as
    run_tac
      tactic.rotate 1
    · rw [if_neg h2]
      apply sat_empty
      
    rw [if_pos h2]
    apply sat_eq_elim
    cases' h1 with v h1
    exists v ⟨n ↦ sgm v b as n⟩
    cases' h1 with h1 h3
    rw [List.forall_mem_consₓ] at h1
    cases' h1 with h4 h5
    constructor
    · rw [List.forall_mem_consₓ]
      constructor
      · apply coeffs_reduce_correct h2 h4
        
      · intro x h6
        rw [List.mem_mapₓ] at h6
        cases' h6 with t h6
        cases' h6 with h6 h7
        rw [← h7, ← subst_correct h2 h4]
        apply h5 _ h6
        
      
    · intro x h6
      rw [List.mem_mapₓ] at h6
      cases' h6 with t h6
      cases' h6 with h6 h7
      rw [← h7, ← subst_correct h2 h4]
      apply h3 _ h6
      
  | ee.cancel m :: es, (Eq :: eqs, les), h1 => by
    unfold eq_elim
    apply sat_eq_elim
    cases' h1 with v h1
    exists v
    cases' h1 with h1 h2
    rw [List.forall_mem_consₓ] at h1
    cases' h1 with h1 h3
    constructor <;>
      intro t h4 <;>
        rw [List.mem_mapₓ] at h4 <;>
          rcases h4 with ⟨s, h4, h5⟩ <;>
            rw [← h5] <;> simp only [← term.val_add, ← term.val_mul, ← cancel] <;> rw [← h1, mul_zero, zero_addₓ]
    · apply h3 _ h4
      
    · apply h2 _ h4
      

/-- If the result of equality elimination is unsatisfiable, the original clause is unsatisfiable. -/
theorem unsat_of_unsat_eq_elim (ee : List Ee) (c : Clause) : (eqElim ee c).Unsat → c.Unsat := by
  intro h1 h2
  apply h1
  apply sat_eq_elim h2

end Omega

