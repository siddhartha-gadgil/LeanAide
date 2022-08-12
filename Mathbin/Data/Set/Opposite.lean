/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import Mathbin.Data.Opposite
import Mathbin.Data.Set.Basic

/-!
# The opposite of a set

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/


variable {α : Type _}

open Opposite

namespace Set

/-- The opposite of a set `s` is the set obtained by taking the opposite of each member of `s`. -/
protected def Op (s : Set α) : Set αᵒᵖ :=
  unop ⁻¹' s

/-- The unop of a set `s` is the set obtained by taking the unop of each member of `s`. -/
protected def Unop (s : Set αᵒᵖ) : Set α :=
  op ⁻¹' s

@[simp]
theorem mem_op {s : Set α} {a : αᵒᵖ} : a ∈ s.op ↔ unop a ∈ s :=
  Iff.rfl

@[simp]
theorem op_mem_op {s : Set α} {a : α} : op a ∈ s.op ↔ a ∈ s := by
  rw [mem_op, unop_op]

@[simp]
theorem mem_unop {s : Set αᵒᵖ} {a : α} : a ∈ s.unop ↔ op a ∈ s :=
  Iff.rfl

@[simp]
theorem unop_mem_unop {s : Set αᵒᵖ} {a : αᵒᵖ} : unop a ∈ s.unop ↔ a ∈ s := by
  rw [mem_unop, op_unop]

@[simp]
theorem op_unop (s : Set α) : s.op.unop = s :=
  ext
    (by
      simp only [← mem_unop, ← op_mem_op, ← iff_selfₓ, ← implies_true_iff])

@[simp]
theorem unop_op (s : Set αᵒᵖ) : s.unop.op = s :=
  ext
    (by
      simp only [← mem_op, ← unop_mem_unop, ← iff_selfₓ, ← implies_true_iff])

/-- Taking opposites as an equivalence of powersets. -/
@[simps]
def opEquiv : Set α ≃ Set αᵒᵖ :=
  ⟨Set.Op, Set.Unop, op_unop, unop_op⟩

@[simp]
theorem singleton_op (x : α) : ({x} : Set α).op = {op x} :=
  ext fun y => by
    simpa only [← mem_op, ← mem_singleton_iff] using unop_eq_iff_eq_op

@[simp]
theorem singleton_unop (x : αᵒᵖ) : ({x} : Set αᵒᵖ).unop = {unop x} :=
  ext fun y => by
    simpa only [← mem_unop, ← mem_singleton_iff] using op_eq_iff_eq_unop

@[simp]
theorem singleton_op_unop (x : α) : ({op x} : Set αᵒᵖ).unop = {x} := by
  simp only [← singleton_unop, ← Opposite.unop_op]

@[simp]
theorem singleton_unop_op (x : αᵒᵖ) : ({unop x} : Set α).op = {x} := by
  simp only [← singleton_op, ← Opposite.op_unop]

end Set

