/-
Copyright (c) 2021 Ivan Sadofschi Costa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Sadofschi Costa
-/
import Mathbin.Data.Fin.Tuple.Default
import Mathbin.Data.Finsupp.Basic

/-!
# `cons` and `tail` for maps `fin n →₀ M`

We interpret maps `fin n →₀ M` as `n`-tuples of elements of `M`,
We define the following operations:
* `finsupp.tail` : the tail of a map `fin (n + 1) →₀ M`, i.e., its last `n` entries;
* `finsupp.cons` : adding an element at the beginning of an `n`-tuple, to get an `n + 1`-tuple;

In this context, we prove some usual properties of `tail` and `cons`, analogous to those of
`data.fin.tuple.basic`.
-/


noncomputable section

namespace Finsupp

variable {n : ℕ} (i : Finₓ n) {M : Type _} [Zero M] (y : M) (t : Finₓ (n + 1) →₀ M) (s : Finₓ n →₀ M)

/-- `tail` for maps `fin (n + 1) →₀ M`. See `fin.tail` for more details. -/
def tail (s : Finₓ (n + 1) →₀ M) : Finₓ n →₀ M :=
  Finsupp.equivFunOnFintype.invFun (Finₓ.tail s.toFun)

/-- `cons` for maps `fin n →₀ M`. See `fin.cons` for more details. -/
def cons (y : M) (s : Finₓ n →₀ M) : Finₓ (n + 1) →₀ M :=
  Finsupp.equivFunOnFintype.invFun (Finₓ.cons y s.toFun)

theorem tail_apply : tail t i = t i.succ := by
  simp only [← tail, ← equiv_fun_on_fintype_symm_apply_to_fun, ← Equivₓ.inv_fun_as_coe]
  rfl

@[simp]
theorem cons_zero : cons y s 0 = y := by
  simp [← cons, ← Finsupp.equivFunOnFintype]

@[simp]
theorem cons_succ : cons y s i.succ = s i := by
  simp only [← Finsupp.cons, ← Finₓ.cons, ← Finsupp.equivFunOnFintype, ← Finₓ.cases_succ, ← Finsupp.coe_mk]
  rfl

@[simp]
theorem tail_cons : tail (cons y s) = s := by
  simp only [← Finsupp.cons, ← Finₓ.cons, ← Finsupp.tail, ← Finₓ.tail]
  ext
  simp only [← equiv_fun_on_fintype_symm_apply_to_fun, ← Equivₓ.inv_fun_as_coe, ← Finsupp.coe_mk, ← Finₓ.cases_succ, ←
    equiv_fun_on_fintype]
  rfl

@[simp]
theorem cons_tail : cons (t 0) (tail t) = t := by
  ext
  by_cases' c_a : a = 0
  · rw [c_a, cons_zero]
    
  · rw [← Finₓ.succ_pred a c_a, cons_succ, ← tail_apply]
    

@[simp]
theorem cons_zero_zero : cons 0 (0 : Finₓ n →₀ M) = 0 := by
  ext
  by_cases' c : a = 0
  · simp [← c]
    
  · rw [← Finₓ.succ_pred a c, cons_succ]
    simp
    

variable {s} {y}

theorem cons_ne_zero_of_left (h : y ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  rw [← cons_zero y s, c, Finsupp.coe_zero, Pi.zero_apply]

theorem cons_ne_zero_of_right (h : s ≠ 0) : cons y s ≠ 0 := by
  contrapose! h with c
  ext
  simp [cons_succ a y s, ← c]

theorem cons_ne_zero_iff : cons y s ≠ 0 ↔ y ≠ 0 ∨ s ≠ 0 := by
  refine' ⟨fun h => _, fun h => h.casesOn cons_ne_zero_of_left cons_ne_zero_of_right⟩
  refine' imp_iff_not_or.1 fun h' c => h _
  rw [h', c, Finsupp.cons_zero_zero]

end Finsupp

