/-
Copyright (c) 2015 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Mario Carneiro
-/
import Mathbin.Data.List.BigOperators

/-!
# Lists in product and sigma types

This file proves basic properties of `list.product` and `list.sigma`, which are list constructions
living in `prod` and `sigma` types respectively. Their definitions can be found in
[`data.list.defs`](./defs). Beware, this is not about `list.prod`, the multiplicative product.
-/


variable {α β : Type _}

namespace List

/-! ### product -/


@[simp]
theorem nil_product (l : List β) : product (@nil α) l = [] :=
  rfl

@[simp]
theorem product_cons (a : α) (l₁ : List α) (l₂ : List β) :
    product (a :: l₁) l₂ = map (fun b => (a, b)) l₂ ++ product l₁ l₂ :=
  rfl

@[simp]
theorem product_nil : ∀ l : List α, product l (@nil β) = []
  | [] => rfl
  | a :: l => by
    rw [product_cons, product_nil] <;> rfl

@[simp]
theorem mem_product {l₁ : List α} {l₂ : List β} {a : α} {b : β} : (a, b) ∈ product l₁ l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ := by
  simp only [← product, ← mem_bind, ← mem_map, ← Prod.ext_iff, ← exists_prop, ← And.left_comm, ←
    exists_and_distrib_left, ← exists_eq_left, ← exists_eq_right]

theorem length_product (l₁ : List α) (l₂ : List β) : length (product l₁ l₂) = length l₁ * length l₂ := by
  induction' l₁ with x l₁ IH <;> [exact (zero_mul _).symm,
    simp only [← length, ← product_cons, ← length_append, ← IH, ← right_distrib, ← one_mulₓ, ← length_map, ← add_commₓ]]

/-! ### sigma -/


variable {σ : α → Type _}

@[simp]
theorem nil_sigma (l : ∀ a, List (σ a)) : (@nil α).Sigma l = [] :=
  rfl

@[simp]
theorem sigma_cons (a : α) (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    (a :: l₁).Sigma l₂ = map (Sigma.mk a) (l₂ a) ++ l₁.Sigma l₂ :=
  rfl

@[simp]
theorem sigma_nil : ∀ l : List α, (l.Sigma fun a => @nil (σ a)) = []
  | [] => rfl
  | a :: l => by
    rw [sigma_cons, sigma_nil] <;> rfl

@[simp]
theorem mem_sigma {l₁ : List α} {l₂ : ∀ a, List (σ a)} {a : α} {b : σ a} :
    Sigma.mk a b ∈ l₁.Sigma l₂ ↔ a ∈ l₁ ∧ b ∈ l₂ a := by
  simp only [← List.sigma, ← mem_bind, ← mem_map, ← exists_prop, ← exists_and_distrib_left, ← And.left_comm, ←
    exists_eq_left, ← heq_iff_eq, ← exists_eq_right]

theorem length_sigma (l₁ : List α) (l₂ : ∀ a, List (σ a)) :
    length (l₁.Sigma l₂) = (l₁.map fun a => length (l₂ a)).Sum := by
  induction' l₁ with x l₁ IH <;> [rfl, simp only [← map, ← sigma_cons, ← length_append, ← length_map, ← IH, ← sum_cons]]

end List

