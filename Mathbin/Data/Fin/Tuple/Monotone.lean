/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import Mathbin.Data.Fin.VecNotation

/-!
# Monotone finite sequences

In this file we prove `simp` lemmas that allow to simplify propositions like `monotone ![a, b, c]`.
-/


open Set Finₓ Matrix Function

variable {α : Type _}

theorem lift_fun_vec_cons {n : ℕ} (r : α → α → Prop) [IsTrans α r] {f : Finₓ (n + 1) → α} {a : α} :
    ((· < ·)⇒r) (vecCons a f) (vecCons a f) ↔ r a (f 0) ∧ ((· < ·)⇒r) f f := by
  simp only [← lift_fun_iff_succ r, ← forall_fin_succ, ← cons_val_succ, ← cons_val_zero, succ_cast_succ, ←
    cast_succ_zero]

variable [Preorderₓ α] {n : ℕ} {f : Finₓ (n + 1) → α} {a : α}

@[simp]
theorem strict_mono_vec_cons : StrictMono (vecCons a f) ↔ a < f 0 ∧ StrictMono f :=
  lift_fun_vec_cons (· < ·)

@[simp]
theorem monotone_vec_cons : Monotone (vecCons a f) ↔ a ≤ f 0 ∧ Monotone f := by
  simpa only [← monotone_iff_forall_lt] using @lift_fun_vec_cons α n (· ≤ ·) _ f a

@[simp]
theorem strict_anti_vec_cons : StrictAnti (vecCons a f) ↔ f 0 < a ∧ StrictAnti f :=
  lift_fun_vec_cons (· > ·)

@[simp]
theorem antitone_vec_cons : Antitone (vecCons a f) ↔ f 0 ≤ a ∧ Antitone f :=
  @monotone_vec_cons αᵒᵈ _ _ _ _

theorem StrictMono.vec_cons (hf : StrictMono f) (ha : a < f 0) : StrictMono (vecCons a f) :=
  strict_mono_vec_cons.2 ⟨ha, hf⟩

theorem StrictAnti.vec_cons (hf : StrictAnti f) (ha : f 0 < a) : StrictAnti (vecCons a f) :=
  strict_anti_vec_cons.2 ⟨ha, hf⟩

theorem Monotone.vec_cons (hf : Monotone f) (ha : a ≤ f 0) : Monotone (vecCons a f) :=
  monotone_vec_cons.2 ⟨ha, hf⟩

theorem Antitone.vec_cons (hf : Antitone f) (ha : f 0 ≤ a) : Antitone (vecCons a f) :=
  antitone_vec_cons.2 ⟨ha, hf⟩

example : Monotone ![1, 2, 2, 3] := by
  simp [← Subsingleton.monotone]

