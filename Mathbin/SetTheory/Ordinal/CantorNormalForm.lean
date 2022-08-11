/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.SetTheory.Ordinal.Arithmetic

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`ordinal.CNF` in this manner, for any `b ≥ 2`.

# Todo

- Add API for the coefficients of the Cantor normal form.
- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/


noncomputable section

universe u

open Order

namespace Ordinal

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_eliminator]
noncomputable def cNFRec {b : Ordinal} (b0 : b ≠ 0) {C : Ordinal → Sort _} (H0 : C 0)
    (H : ∀ o, o ≠ 0 → C (o % b ^ log b o) → C o) : ∀ o, C o
  | o =>
    if o0 : o = 0 then by
      rwa [o0]
    else
      have := mod_opow_log_lt_self b0 o0
      H o o0 (CNF_rec (o % b ^ log b o))

@[simp]
theorem CNF_rec_zero {b} (b0) {C H0 H} : @cNFRec b b0 C H0 H 0 = H0 := by
  rw [CNF_rec, dif_pos rfl] <;> rfl

@[simp]
theorem CNF_rec_ne_zero {b} (b0) {C H0 H o} (o0) : @cNFRec b b0 C H0 H o = H o o0 (@cNFRec b b0 C H0 H _) := by
  rw [CNF_rec, dif_neg o0]

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = []`, `CNF b 0 = []`, and `CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
def cNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  if b0 : b = 0 then [] else cNFRec b0 [] (fun o o0 IH => (log b o, o / b ^ log b o) :: IH) o

@[simp]
theorem zero_CNF (o) : cNF 0 o = [] :=
  dif_pos rfl

@[simp]
theorem CNF_zero (b) : cNF b 0 = [] :=
  if b0 : b = 0 then dif_pos b0 else (dif_neg b0).trans <| CNF_rec_zero _

/-- Recursive definition for the Cantor normal form. -/
theorem CNF_ne_zero {b o : Ordinal} (b0 : b ≠ 0) (o0 : o ≠ 0) :
    cNF b o = (log b o, o / b ^ log b o) :: cNF b (o % b ^ log b o) := by
  unfold CNF <;> rw [dif_neg b0, dif_neg b0, CNF_rec_ne_zero b0 o0]

@[simp]
theorem one_CNF {o : Ordinal} (o0 : o ≠ 0) : cNF 1 o = [(0, o)] := by
  rw [CNF_ne_zero Ordinal.one_ne_zero o0, log_of_not_one_lt_left (irrefl _), opow_zero, mod_one, CNF_zero, div_one]

/-- Evaluating the Cantor normal form of an ordinal returns the ordinal. -/
theorem CNF_foldr {b : Ordinal} (b0 : b ≠ 0) (o) : (cNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o :=
  cNFRec b0
    (by
      rw [CNF_zero] <;> rfl)
    (fun o o0 IH => by
      rw [CNF_ne_zero b0 o0, List.foldr_cons, IH, div_add_mod])
    o

/-- This theorem exists to factor out commonalities between the proofs of `ordinal.CNF_pairwise` and
`ordinal.CNF_fst_le_log`. -/
private theorem CNF_pairwise_aux (b o : Ordinal.{u}) :
    (∀ p : Ordinal × Ordinal, p ∈ cNF b o → p.1 ≤ log b o) ∧ (cNF b o).Pairwise fun p q => q.1 < p.1 := by
  by_cases' b0 : b = 0
  · simp only [← b0, ← zero_CNF, ← List.Pairwiseₓ.nil, ← and_trueₓ]
    exact fun _ => False.elim
    
  cases' lt_or_eq_of_leₓ (one_le_iff_ne_zero.2 b0) with b1 b1
  · refine' CNF_rec b0 _ _ o
    · simp only [← CNF_zero, ← List.Pairwiseₓ.nil, ← and_trueₓ]
      exact fun _ => False.elim
      
    intro o o0 IH
    cases' IH with IH₁ IH₂
    simp only [← CNF_ne_zero b0 o0, ← List.forall_mem_consₓ, ← List.pairwise_cons, ← IH₂, ← and_trueₓ]
    refine' ⟨⟨le_rfl, fun p m => _⟩, fun p m => _⟩
    · exact (IH₁ p m).trans (log_mono_right _ <| le_of_ltₓ <| mod_opow_log_lt_self b0 o0)
      
    · refine' (IH₁ p m).trans_lt ((lt_opow_iff_log_lt b1 _).1 _)
      · rw [Ordinal.pos_iff_ne_zero]
        intro e
        rw [e] at m
        simpa only [← CNF_zero] using m
        
      · exact mod_lt _ (opow_ne_zero _ b0)
        
      
    
  · by_cases' o0 : o = 0
    · simp only [← o0, ← CNF_zero, ← List.Pairwiseₓ.nil, ← and_trueₓ]
      exact fun _ => False.elim
      
    rw [← b1, one_CNF o0]
    simp only [← List.mem_singletonₓ, ← log_one_left, ← forall_eq, ← le_reflₓ, ← true_andₓ, ← List.pairwise_singleton]
    

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_pairwise (b o : Ordinal.{u}) : (cNF b o).Pairwise fun p q : Ordinal × Ordinal => q.1 < p.1 :=
  (CNF_pairwise_aux _ _).2

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `log b o`. -/
theorem CNF_fst_le_log {b o : Ordinal.{u}} : ∀ {p : Ordinal × Ordinal}, p ∈ cNF b o → p.1 ≤ log b o :=
  (CNF_pairwise_aux _ _).1

/-- Every exponent in the Cantor normal form `CNF b o` is less or equal to `o`. -/
theorem CNF_fst_le {b o : Ordinal.{u}} {p : Ordinal × Ordinal} (hp : p ∈ cNF b o) : p.1 ≤ o :=
  (CNF_fst_le_log hp).trans (log_le_self _ _)

/-- This theorem exists to factor out commonalities between the proofs of `ordinal.CNF_snd_lt` and
`ordinal.CNF_lt_snd`. -/
private theorem CNF_snd_lt_aux {b o : Ordinal.{u}} (b1 : 1 < b) :
    ∀ {p : Ordinal × Ordinal}, p ∈ cNF b o → p.2 < b ∧ 0 < p.2 := by
  have b0 := (zero_lt_one.trans b1).ne'
  refine'
    CNF_rec b0
      (fun _ => by
        rw [CNF_zero]
        exact False.elim)
      (fun o o0 IH => _) o
  simp only [← CNF_ne_zero b0 o0, ← List.mem_cons_iff, ← forall_eq_or_imp, ← iff_true_intro @IH, ← and_trueₓ]
  nth_rw 1[← @succ_le_iff]
  rw [div_lt (opow_ne_zero _ b0), ← opow_succ, le_div (opow_ne_zero _ b0), succ_zero, mul_oneₓ]
  refine' ⟨lt_opow_succ_log_self b1 _, opow_log_le_self _ _⟩
  rwa [Ordinal.pos_iff_ne_zero]

/-- Every coefficient in the Cantor normal form `CNF b o` is less than `b`. -/
theorem CNF_snd_lt {b o : Ordinal.{u}} (b1 : 1 < b) {p : Ordinal × Ordinal} (hp : p ∈ cNF b o) : p.2 < b :=
  (CNF_snd_lt_aux b1 hp).1

/-- Every coefficient in a Cantor normal form is positive. -/
theorem CNF_lt_snd {b o : Ordinal.{u}} (b1 : 1 < b) {p : Ordinal × Ordinal} (hp : p ∈ cNF b o) : 0 < p.2 :=
  (CNF_snd_lt_aux b1 hp).2

/-- The exponents of the Cantor normal form are decreasing. -/
theorem CNF_sorted (b o : Ordinal) : ((cNF b o).map Prod.fst).Sorted (· > ·) := by
  rw [List.Sorted, List.pairwise_map]
  exact CNF_pairwise b o

end Ordinal

