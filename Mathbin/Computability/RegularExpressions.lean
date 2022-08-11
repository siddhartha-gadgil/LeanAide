/-
Copyright (c) 2020 Fox Thomson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fox Thomson
-/
import Mathbin.Tactic.Rcases
import Mathbin.Computability.Language

/-!
# Regular Expressions

This file contains the formal definition for regular expressions and basic lemmas. Note these are
regular expressions in terms of formal language theory. Note this is different to regex's used in
computer science such as the POSIX standard.

## TODO

* Show that this regular expressions and DFA/NFA's are equivalent.
* `attribute [pattern] has_mul.mul` has been added into this file, it could be moved.
-/


open List Set

universe u

variable {α β γ : Type _} [dec : DecidableEq α]

/-- This is the definition of regular expressions. The names used here is to mirror the definition
of a Kleene algebra (https://en.wikipedia.org/wiki/Kleene_algebra).
* `0` (`zero`) matches nothing
* `1` (`epsilon`) matches only the empty string
* `char a` matches only the string 'a'
* `star P` matches any finite concatenation of strings which match `P`
* `P + Q` (`plus P Q`) matches anything which match `P` or `Q`
* `P * Q` (`comp P Q`) matches `x ++ y` if `x` matches `P` and `y` matches `Q`
-/
inductive RegularExpression (α : Type u) : Type u
  | zero : RegularExpression
  | epsilon : RegularExpression
  | Charₓ : α → RegularExpression
  | plus : RegularExpression → RegularExpression → RegularExpression
  | comp : RegularExpression → RegularExpression → RegularExpression
  | star : RegularExpression → RegularExpression

namespace RegularExpression

variable {a b : α}

instance : Inhabited (RegularExpression α) :=
  ⟨zero⟩

instance : Add (RegularExpression α) :=
  ⟨plus⟩

instance : Mul (RegularExpression α) :=
  ⟨comp⟩

instance : One (RegularExpression α) :=
  ⟨epsilon⟩

instance : Zero (RegularExpression α) :=
  ⟨zero⟩

instance : Pow (RegularExpression α) ℕ :=
  ⟨fun n r => npowRec r n⟩

attribute [matchPattern] Mul.mul

@[simp]
theorem zero_def : (zero : RegularExpression α) = 0 :=
  rfl

@[simp]
theorem one_def : (epsilon : RegularExpression α) = 1 :=
  rfl

@[simp]
theorem plus_def (P Q : RegularExpression α) : plus P Q = P + Q :=
  rfl

@[simp]
theorem comp_def (P Q : RegularExpression α) : comp P Q = P * Q :=
  rfl

/-- `matches P` provides a language which contains all strings that `P` matches -/
@[simp]
def Matches : RegularExpression α → Language α
  | 0 => 0
  | 1 => 1
  | Charₓ a => {[a]}
  | P + Q => P.Matches + Q.Matches
  | P * Q => P.Matches * Q.Matches
  | star P => P.Matches.star

@[simp]
theorem matches_zero : (0 : RegularExpression α).Matches = 0 :=
  rfl

@[simp]
theorem matches_epsilon : (1 : RegularExpression α).Matches = 1 :=
  rfl

@[simp]
theorem matches_char (a : α) : (char a).Matches = {[a]} :=
  rfl

@[simp]
theorem matches_add (P Q : RegularExpression α) : (P + Q).Matches = P.Matches + Q.Matches :=
  rfl

@[simp]
theorem matches_mul (P Q : RegularExpression α) : (P * Q).Matches = P.Matches * Q.Matches :=
  rfl

@[simp]
theorem matches_pow (P : RegularExpression α) : ∀ n : ℕ, (P ^ n).Matches = P.Matches ^ n
  | 0 => matches_epsilon
  | n + 1 => (matches_mul _ _).trans <| Eq.trans (congr_arg _ (matches_pow n)) (pow_succₓ _ _).symm

@[simp]
theorem matches_star (P : RegularExpression α) : P.star.Matches = P.Matches.star :=
  rfl

/-- `match_epsilon P` is true if and only if `P` matches the empty string -/
def matchEpsilon : RegularExpression α → Bool
  | 0 => false
  | 1 => true
  | Charₓ _ => false
  | P + Q => P.matchEpsilon || Q.matchEpsilon
  | P * Q => P.matchEpsilon && Q.matchEpsilon
  | star P => true

include dec

/-- `P.deriv a` matches `x` if `P` matches `a :: x`, the Brzozowski derivative of `P` with respect
  to `a` -/
def deriv : RegularExpression α → α → RegularExpression α
  | 0, _ => 0
  | 1, _ => 0
  | Charₓ a₁, a₂ => if a₁ = a₂ then 1 else 0
  | P + Q, a => deriv P a + deriv Q a
  | P * Q, a => if P.matchEpsilon then deriv P a * Q + deriv Q a else deriv P a * Q
  | star P, a => deriv P a * star P

@[simp]
theorem deriv_zero (a : α) : deriv 0 a = 0 :=
  rfl

@[simp]
theorem deriv_one (a : α) : deriv 1 a = 0 :=
  rfl

@[simp]
theorem deriv_char_self (a : α) : deriv (char a) a = 1 :=
  if_pos rfl

@[simp]
theorem deriv_char_of_ne (h : a ≠ b) : deriv (char a) b = 0 :=
  if_neg h

@[simp]
theorem deriv_add (P Q : RegularExpression α) (a : α) : deriv (P + Q) a = deriv P a + deriv Q a :=
  rfl

@[simp]
theorem deriv_star (P : RegularExpression α) (a : α) : deriv P.star a = deriv P a * star P :=
  rfl

/-- `P.rmatch x` is true if and only if `P` matches `x`. This is a computable definition equivalent
  to `matches`. -/
def rmatch : RegularExpression α → List α → Bool
  | P, [] => matchEpsilon P
  | P, a :: as => rmatch (P.deriv a) as

@[simp]
theorem zero_rmatch (x : List α) : rmatch 0 x = ff := by
  induction x <;> simp [← rmatch, ← match_epsilon, *]

theorem one_rmatch_iff (x : List α) : rmatch 1 x ↔ x = [] := by
  induction x <;> simp [← rmatch, ← match_epsilon, *]

theorem char_rmatch_iff (a : α) (x : List α) : rmatch (char a) x ↔ x = [a] := by
  cases' x with _ x
  decide
  cases x
  rw [rmatch, deriv]
  split_ifs <;> tauto
  rw [rmatch, deriv]
  split_ifs
  rw [one_rmatch_iff]
  tauto
  rw [zero_rmatch]
  tauto

theorem add_rmatch_iff (P Q : RegularExpression α) (x : List α) : (P + Q).rmatch x ↔ P.rmatch x ∨ Q.rmatch x := by
  induction' x with _ _ ih generalizing P Q
  · simp only [← rmatch, ← match_epsilon, ← bor_coe_iff]
    
  · repeat'
      rw [rmatch]
    rw [deriv]
    exact ih _ _
    

theorem mul_rmatch_iff (P Q : RegularExpression α) (x : List α) :
    (P * Q).rmatch x ↔ ∃ t u : List α, x = t ++ u ∧ P.rmatch t ∧ Q.rmatch u := by
  induction' x with a x ih generalizing P Q
  · rw [rmatch, match_epsilon]
    constructor
    · intro h
      refine' ⟨[], [], rfl, _⟩
      rw [rmatch, rmatch]
      rwa [band_coe_iff] at h
      
    · rintro ⟨t, u, h₁, h₂⟩
      cases' List.append_eq_nil.1 h₁.symm with ht hu
      subst ht
      subst hu
      repeat'
        rw [rmatch] at h₂
      simp [← h₂]
      
    
  · rw [rmatch, deriv]
    split_ifs with hepsilon
    · rw [add_rmatch_iff, ih]
      constructor
      · rintro (⟨t, u, _⟩ | h)
        · exact
            ⟨a :: t, u, by
              tauto⟩
          
        · exact ⟨[], a :: x, rfl, hepsilon, h⟩
          
        
      · rintro ⟨t, u, h, hP, hQ⟩
        cases' t with b t
        · right
          rw [List.nil_append] at h
          rw [← h] at hQ
          exact hQ
          
        · left
          simp only [← List.cons_append] at h
          refine' ⟨t, u, h.2, _, hQ⟩
          rw [rmatch] at hP
          convert hP
          exact h.1
          
        
      
    · rw [ih]
      constructor <;> rintro ⟨t, u, h, hP, hQ⟩
      · exact
          ⟨a :: t, u, by
            tauto⟩
        
      · cases' t with b t
        · contradiction
          
        · simp only [← List.cons_append] at h
          refine' ⟨t, u, h.2, _, hQ⟩
          rw [rmatch] at hP
          convert hP
          exact h.1
          
        
      
    

theorem star_rmatch_iff (P : RegularExpression α) :
    ∀ x : List α, (star P).rmatch x ↔ ∃ S : List (List α), x = S.join ∧ ∀, ∀ t ∈ S, ∀, t ≠ [] ∧ P.rmatch t
  | x => by
    have A : ∀ m n : ℕ, n < m + n + 1 := by
      intro m n
      convert add_lt_add_of_le_of_lt (add_le_add (zero_le m) (le_reflₓ n)) zero_lt_one
      simp
    have IH := fun t (h : List.length t < List.length x) => star_rmatch_iff t
    clear star_rmatch_iff
    constructor
    · cases' x with a x
      · intro
        fconstructor
        exact []
        tauto
        
      · rw [rmatch, deriv, mul_rmatch_iff]
        rintro ⟨t, u, hs, ht, hu⟩
        have hwf : u.length < (List.cons a x).length := by
          rw [hs, List.length_cons, List.length_append]
          apply A
        rw [IH _ hwf] at hu
        rcases hu with ⟨S', hsum, helem⟩
        use (a :: t) :: S'
        constructor
        · simp [← hs, ← hsum]
          
        · intro t' ht'
          cases' ht' with ht' ht'
          · rw [ht']
            exact
              ⟨by
                decide, ht⟩
            
          · exact helem _ ht'
            
          
        
      
    · rintro ⟨S, hsum, helem⟩
      cases' x with a x
      · decide
        
      · rw [rmatch, deriv, mul_rmatch_iff]
        cases' S with t' U
        · exact
            ⟨[], [], by
              tauto⟩
          
        · cases' t' with b t
          · simp only [← forall_eq_or_imp, ← List.mem_cons_iff] at helem
            simp only [← eq_self_iff_true, ← not_true, ← Ne.def, ← false_andₓ] at helem
            cases helem
            
          simp only [← List.join, ← List.cons_append] at hsum
          refine' ⟨t, U.join, hsum.2, _, _⟩
          · specialize
              helem (b :: t)
                (by
                  simp )
            rw [rmatch] at helem
            convert helem.2
            exact hsum.1
            
          · have hwf : U.join.length < (List.cons a x).length := by
              rw [hsum.1, hsum.2]
              simp only [← List.length_append, ← List.length_join, ← List.length]
              apply A
            rw [IH _ hwf]
            refine' ⟨U, rfl, fun t h => helem t _⟩
            right
            assumption
            
          
        
      

@[simp]
theorem rmatch_iff_matches (P : RegularExpression α) : ∀ x : List α, P.rmatch x ↔ x ∈ P.Matches := by
  intro x
  induction P generalizing x
  all_goals
    try
      rw [zero_def]
    try
      rw [one_def]
    try
      rw [plus_def]
    try
      rw [comp_def]
    rw [matches]
  case zero =>
    rw [zero_rmatch]
    tauto
  case epsilon =>
    rw [one_rmatch_iff]
    rfl
  case char =>
    rw [char_rmatch_iff]
    rfl
  case plus _ _ ih₁ ih₂ =>
    rw [add_rmatch_iff, ih₁, ih₂]
    rfl
  case comp P Q ih₁ ih₂ =>
    simp only [← mul_rmatch_iff, ← comp_def, ← Language.mul_def, ← exists_and_distrib_left, ← Set.mem_image2, ←
      Set.image_prod]
    constructor
    · rintro ⟨x, y, hsum, hmatch₁, hmatch₂⟩
      rw [ih₁] at hmatch₁
      rw [ih₂] at hmatch₂
      exact ⟨x, hmatch₁, y, hmatch₂, hsum.symm⟩
      
    · rintro ⟨x, hmatch₁, y, hmatch₂, hsum⟩
      rw [← ih₁] at hmatch₁
      rw [← ih₂] at hmatch₂
      exact ⟨x, y, hsum.symm, hmatch₁, hmatch₂⟩
      
  case star _ ih =>
    rw [star_rmatch_iff, Language.star_def_nonempty]
    constructor
    all_goals
      rintro ⟨S, hx, hS⟩
      refine' ⟨S, hx, _⟩
      intro y
      specialize hS y
    · rw [← ih y]
      tauto
      
    · rw [ih y]
      tauto
      

instance (P : RegularExpression α) : DecidablePred P.Matches := by
  intro x
  change Decidable (x ∈ P.matches)
  rw [← rmatch_iff_matches]
  exact Eq.decidable _ _

omit dec

/-- Map the alphabet of a regular expression. -/
@[simp]
def map (f : α → β) : RegularExpression α → RegularExpression β
  | 0 => 0
  | 1 => 1
  | Charₓ a => char (f a)
  | R + S => map R + map S
  | R * S => map R * map S
  | star R => star (map R)

@[simp]
protected theorem map_pow (f : α → β) (P : RegularExpression α) : ∀ n : ℕ, map f (P ^ n) = map f P ^ n
  | 0 => rfl
  | n + 1 => (congr_arg ((· * ·) (map f P)) (map_pow n) : _)

@[simp]
theorem map_id : ∀ P : RegularExpression α, P.map id = P
  | 0 => rfl
  | 1 => rfl
  | Charₓ a => rfl
  | R + S => by
    simp_rw [map, map_id]
  | R * S => by
    simp_rw [map, map_id]
  | star R => by
    simp_rw [map, map_id]

@[simp]
theorem map_map (g : β → γ) (f : α → β) : ∀ P : RegularExpression α, (P.map f).map g = P.map (g ∘ f)
  | 0 => rfl
  | 1 => rfl
  | Charₓ a => rfl
  | R + S => by
    simp_rw [map, map_map]
  | R * S => by
    simp_rw [map, map_map]
  | star R => by
    simp_rw [map, map_map]

/-- The language of the map is the map of the language. -/
@[simp]
theorem matches_map (f : α → β) : ∀ P : RegularExpression α, (P.map f).Matches = Language.map f P.Matches
  | 0 => (map_zero _).symm
  | 1 => (map_one _).symm
  | Charₓ a => by
    rw [eq_comm]
    exact image_singleton
  | R + S => by
    simp only [← matches_map, ← map, ← matches_add, ← map_add]
  | R * S => by
    simp only [← matches_map, ← map, ← matches_mul, ← map_mul]
  | star R => by
    simp_rw [map, matches, matches_map]
    rw [Language.star_eq_supr_pow, Language.star_eq_supr_pow]
    simp_rw [← map_pow]
    exact image_Union.symm

end RegularExpression

