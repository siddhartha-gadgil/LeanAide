/-
Copyright (c) 2022 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Floris van Doorn
-/
import Mathbin.Data.Pnat.Basic

/-!
# Explicit least witnesses to existentials on positive natural numbers

Implemented via calling out to `nat.find`.

-/


namespace Pnat

variable {p q : ℕ+ → Prop} [DecidablePred p] [DecidablePred q] (h : ∃ n, p n)

instance decidablePredExistsNat : DecidablePred fun n' : ℕ => ∃ (n : ℕ+)(hn : n' = n), p n := fun n' =>
  decidableOfIff' (∃ h : 0 < n', p ⟨n', h⟩) <|
    Subtype.exists.trans <| by
      simp_rw [Subtype.coe_mk, @exists_comm (_ < _) (_ = _), exists_prop, exists_eq_left']

include h

/-- The `pnat` version of `nat.find_x` -/
protected def findX : { n // p n ∧ ∀ m : ℕ+, m < n → ¬p m } := by
  have : ∃ (n' : ℕ)(n : ℕ+)(hn' : n' = n), p n := Exists.elim h fun n hn => ⟨n, n, rfl, hn⟩
  have n := Nat.findX this
  refine' ⟨⟨n, _⟩, _, fun m hm pm => _⟩
  · obtain ⟨n', hn', -⟩ := n.prop.1
    rw [hn']
    exact n'.prop
    
  · obtain ⟨n', hn', pn'⟩ := n.prop.1
    simpa [← hn', ← Subtype.coe_eta] using pn'
    
  · exact n.prop.2 m hm ⟨m, rfl, pm⟩
    

/-- If `p` is a (decidable) predicate on `ℕ+` and `hp : ∃ (n : ℕ+), p n` is a proof that
there exists some positive natural number satisfying `p`, then `pnat.find hp` is the
smallest positive natural number satisfying `p`. Note that `pnat.find` is protected,
meaning that you can't just write `find`, even if the `pnat` namespace is open.

The API for `pnat.find` is:

* `pnat.find_spec` is the proof that `pnat.find hp` satisfies `p`.
* `pnat.find_min` is the proof that if `m < pnat.find hp` then `m` does not satisfy `p`.
* `pnat.find_min'` is the proof that if `m` does satisfy `p` then `pnat.find hp ≤ m`.
-/
protected def find : ℕ+ :=
  Pnat.findX h

protected theorem find_spec : p (Pnat.find h) :=
  (Pnat.findX h).Prop.left

protected theorem find_min : ∀ {m : ℕ+}, m < Pnat.find h → ¬p m :=
  (Pnat.findX h).Prop.right

protected theorem find_min' {m : ℕ+} (hm : p m) : Pnat.find h ≤ m :=
  le_of_not_ltₓ fun l => Pnat.find_min h l hm

variable {n m : ℕ+}

theorem find_eq_iff : Pnat.find h = m ↔ p m ∧ ∀, ∀ n < m, ∀, ¬p n := by
  constructor
  · rintro rfl
    exact ⟨Pnat.find_spec h, fun _ => Pnat.find_min h⟩
    
  · rintro ⟨hm, hlt⟩
    exact le_antisymmₓ (Pnat.find_min' h hm) (not_ltₓ.1 <| imp_not_comm.1 (hlt _) <| Pnat.find_spec h)
    

@[simp]
theorem find_lt_iff (n : ℕ+) : Pnat.find h < n ↔ ∃ m < n, p m :=
  ⟨fun h2 => ⟨Pnat.find h, h2, Pnat.find_spec h⟩, fun ⟨m, hmn, hm⟩ => (Pnat.find_min' h hm).trans_lt hmn⟩

@[simp]
theorem find_le_iff (n : ℕ+) : Pnat.find h ≤ n ↔ ∃ m ≤ n, p m := by
  simp only [← exists_prop, lt_add_one_iff, ← find_lt_iff]

@[simp]
theorem le_find_iff (n : ℕ+) : n ≤ Pnat.find h ↔ ∀, ∀ m < n, ∀, ¬p m := by
  simp_rw [← not_ltₓ, find_lt_iff, not_exists]

@[simp]
theorem lt_find_iff (n : ℕ+) : n < Pnat.find h ↔ ∀, ∀ m ≤ n, ∀, ¬p m := by
  simp only [add_one_le_iff, ← le_find_iff, ← add_le_add_iff_right]

@[simp]
theorem find_eq_one : Pnat.find h = 1 ↔ p 1 := by
  simp [← find_eq_iff]

@[simp]
theorem one_le_find : 1 < Pnat.find h ↔ ¬p 1 :=
  not_iff_not.mp <| by
    simp

theorem find_mono (h : ∀ n, q n → p n) {hp : ∃ n, p n} {hq : ∃ n, q n} : Pnat.find hp ≤ Pnat.find hq :=
  Pnat.find_min' _ (h _ (Pnat.find_spec hq))

theorem find_le {h : ∃ n, p n} (hn : p n) : Pnat.find h ≤ n :=
  (Pnat.find_le_iff _ _).2 ⟨n, le_rfl, hn⟩

theorem find_comp_succ (h : ∃ n, p n) (h₂ : ∃ n, p (n + 1)) (h1 : ¬p 1) : Pnat.find h = Pnat.find h₂ + 1 := by
  refine' (find_eq_iff _).2 ⟨Pnat.find_spec h₂, fun n => Pnat.recOn n _ _⟩
  · simp [← h1]
    
  intro m IH hm
  simp only [← add_lt_add_iff_right, ← lt_find_iff] at hm
  exact hm _ le_rfl

end Pnat

