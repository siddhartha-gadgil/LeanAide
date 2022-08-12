/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Multiset.Bind
import Mathbin.Data.Multiset.Powerset

/-!
# The antidiagonal on a multiset.

The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
such that `t₁ + t₂ = s`. These pairs are counted with multiplicities.
-/


namespace Multiset

open List

variable {α β : Type _}

/-- The antidiagonal of a multiset `s` consists of all pairs `(t₁, t₂)`
    such that `t₁ + t₂ = s`. These pairs are counted with multiplicities. -/
def antidiagonal (s : Multiset α) : Multiset (Multiset α × Multiset α) :=
  Quot.liftOn s (fun l => (revzipₓ (powersetAux l) : Multiset (Multiset α × Multiset α))) fun l₁ l₂ h =>
    Quot.sound (revzip_powerset_aux_perm h)

theorem antidiagonal_coe (l : List α) : @antidiagonal α l = revzipₓ (powersetAux l) :=
  rfl

@[simp]
theorem antidiagonal_coe' (l : List α) : @antidiagonal α l = revzipₓ (powersetAux' l) :=
  Quot.sound revzip_powerset_aux_perm_aux'

/-- A pair `(t₁, t₂)` of multisets is contained in `antidiagonal s`
    if and only if `t₁ + t₂ = s`. -/
@[simp]
theorem mem_antidiagonal {s : Multiset α} {x : Multiset α × Multiset α} : x ∈ antidiagonal s ↔ x.1 + x.2 = s :=
  (Quotientₓ.induction_on s) fun l => by
    simp [← antidiagonal_coe]
    refine' ⟨fun h => revzip_powerset_aux h, fun h => _⟩
    have := Classical.decEq α
    simp [← revzip_powerset_aux_lemma l revzip_powerset_aux, ← h.symm]
    cases' x with x₁ x₂
    dsimp' only
    exact
      ⟨x₁, le_add_right _ _, by
        rw [add_tsub_cancel_left x₁ x₂]⟩

@[simp]
theorem antidiagonal_map_fst (s : Multiset α) : (antidiagonal s).map Prod.fst = powerset s :=
  (Quotientₓ.induction_on s) fun l => by
    simp [← powerset_aux']

@[simp]
theorem antidiagonal_map_snd (s : Multiset α) : (antidiagonal s).map Prod.snd = powerset s :=
  (Quotientₓ.induction_on s) fun l => by
    simp [← powerset_aux']

@[simp]
theorem antidiagonal_zero : @antidiagonal α 0 = {(0, 0)} :=
  rfl

@[simp]
theorem antidiagonal_cons (a : α) (s) :
    antidiagonal (a ::ₘ s) =
      map (Prod.map id (cons a)) (antidiagonal s) + map (Prod.map (cons a) id) (antidiagonal s) :=
  (Quotientₓ.induction_on s) fun l => by
    simp only [← revzip, ← reverse_append, ← quot_mk_to_coe, ← coe_eq_coe, ← powerset_aux'_cons, ← cons_coe, ← coe_map,
      ← antidiagonal_coe', ← coe_add]
    rw [← zip_map, ← zip_map, zip_append, (_ : _ ++ _ = _)]
    · congr <;> simp
      
    · simp
      

@[simp]
theorem card_antidiagonal (s : Multiset α) : card (antidiagonal s) = 2 ^ card s := by
  have := card_powerset s <;> rwa [← antidiagonal_map_fst, card_map] at this

theorem prod_map_add [CommSemiringₓ β] {s : Multiset α} {f g : α → β} :
    prod (s.map fun a => f a + g a) = sum ((antidiagonal s).map fun p => (p.1.map f).Prod * (p.2.map g).Prod) := by
  refine' s.induction_on _ _
  · simp
    
  · intro a s ih
    have := @sum_map_mul_left α β _
    simp [← ih, ← add_mulₓ, ← mul_comm, ← mul_left_commₓ (f a), ← mul_left_commₓ (g a), ← mul_assoc, ←
      sum_map_mul_left.symm]
    cc
    

end Multiset

