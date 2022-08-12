/-
Copyright (c) 2020 Yury Kudryashov, Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Anne Baanen
-/
import Mathbin.Data.Fintype.Card
import Mathbin.Data.Fintype.Fin
import Mathbin.Logic.Equiv.Fin

/-!
# Big operators and `fin`

Some results about products and sums over the type `fin`.

The most important results are the induction formulas `fin.prod_univ_cast_succ`
and `fin.prod_univ_succ`, and the formula `fin.prod_const` for the product of a
constant function. These results have variants for sums instead of products.

-/


open BigOperators

open Finset

variable {α : Type _} {β : Type _}

namespace Finset

@[to_additive]
theorem prod_range [CommMonoidₓ β] {n : ℕ} (f : ℕ → β) : (∏ i in Finset.range n, f i) = ∏ i : Finₓ n, f i :=
  prod_bij' (fun k w => ⟨k, mem_range.mp w⟩) (fun a ha => mem_univ _) (fun a ha => congr_arg _ (Finₓ.coe_mk _).symm)
    (fun a m => a) (fun a m => mem_range.mpr a.Prop) (fun a ha => Finₓ.coe_mk _) fun a ha => Finₓ.eta _ _

end Finset

namespace Finₓ

@[to_additive]
theorem prod_univ_def [CommMonoidₓ β] {n : ℕ} (f : Finₓ n → β) : (∏ i, f i) = ((List.finRange n).map f).Prod := by
  simp [← univ_def, ← Finset.finRange]

@[to_additive]
theorem prod_of_fn [CommMonoidₓ β] {n : ℕ} (f : Finₓ n → β) : (List.ofFnₓ f).Prod = ∏ i, f i := by
  rw [List.of_fn_eq_map, prod_univ_def]

/-- A product of a function `f : fin 0 → β` is `1` because `fin 0` is empty -/
@[to_additive "A sum of a function `f : fin 0 → β` is `0` because `fin 0` is empty"]
theorem prod_univ_zero [CommMonoidₓ β] (f : Finₓ 0 → β) : (∏ i, f i) = 1 :=
  rfl

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f x`, for some `x : fin (n + 1)` times the remaining product -/
/- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f x`, for some `x : fin (n + 1)` plus the remaining product -/
@[to_additive]
theorem prod_univ_succ_above [CommMonoidₓ β] {n : ℕ} (f : Finₓ (n + 1) → β) (x : Finₓ (n + 1)) :
    (∏ i, f i) = f x * ∏ i : Finₓ n, f (x.succAbove i) := by
  rw [univ_succ_above, prod_cons, Finset.prod_map, RelEmbedding.coe_fn_to_embedding]

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f 0` plus the remaining product -/
/- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f 0` plus the remaining product -/
@[to_additive]
theorem prod_univ_succ [CommMonoidₓ β] {n : ℕ} (f : Finₓ (n + 1) → β) : (∏ i, f i) = f 0 * ∏ i : Finₓ n, f i.succ :=
  prod_univ_succ_above f 0

/-- A product of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the product of `f (fin.last n)` plus the remaining product -/
/- A sum of a function `f : fin (n + 1) → β` over all `fin (n + 1)`
is the sum of `f (fin.last n)` plus the remaining sum -/
@[to_additive]
theorem prod_univ_cast_succ [CommMonoidₓ β] {n : ℕ} (f : Finₓ (n + 1) → β) :
    (∏ i, f i) = (∏ i : Finₓ n, f i.cast_succ) * f (last n) := by
  simpa [← mul_comm] using prod_univ_succ_above f (last n)

@[to_additive]
theorem prod_cons [CommMonoidₓ β] {n : ℕ} (x : β) (f : Finₓ n → β) :
    (∏ i : Finₓ n.succ, (cons x f : Finₓ n.succ → β) i) = x * ∏ i : Finₓ n, f i := by
  simp_rw [prod_univ_succ, cons_zero, cons_succ]

@[to_additive sum_univ_one]
theorem prod_univ_one [CommMonoidₓ β] (f : Finₓ 1 → β) : (∏ i, f i) = f 0 := by
  simp

@[simp, to_additive]
theorem prod_univ_two [CommMonoidₓ β] (f : Finₓ 2 → β) : (∏ i, f i) = f 0 * f 1 := by
  simp [← prod_univ_succ]

theorem sum_pow_mul_eq_add_pow {n : ℕ} {R : Type _} [CommSemiringₓ R] (a b : R) :
    (∑ s : Finset (Finₓ n), a ^ s.card * b ^ (n - s.card)) = (a + b) ^ n := by
  simpa using Fintype.sum_pow_mul_eq_add_pow (Finₓ n) a b

theorem prod_const [CommMonoidₓ α] (n : ℕ) (x : α) : (∏ i : Finₓ n, x) = x ^ n := by
  simp

theorem sum_const [AddCommMonoidₓ α] (n : ℕ) (x : α) : (∑ i : Finₓ n, x) = n • x := by
  simp

@[to_additive]
theorem prod_Ioi_zero {M : Type _} [CommMonoidₓ M] {n : ℕ} {v : Finₓ n.succ → M} :
    (∏ i in ioi 0, v i) = ∏ j : Finₓ n, v j.succ := by
  rw [Ioi_zero_eq_map, Finset.prod_map, RelEmbedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
theorem prod_Ioi_succ {M : Type _} [CommMonoidₓ M] {n : ℕ} (i : Finₓ n) (v : Finₓ n.succ → M) :
    (∏ j in ioi i.succ, v j) = ∏ j in ioi i, v j.succ := by
  rw [Ioi_succ, Finset.prod_map, RelEmbedding.coe_fn_to_embedding, coe_succ_embedding]

@[to_additive]
theorem prod_congr' {M : Type _} [CommMonoidₓ M] {a b : ℕ} (f : Finₓ b → M) (h : a = b) :
    (∏ i : Finₓ a, f (cast h i)) = ∏ i : Finₓ b, f i := by
  subst h
  congr
  ext
  congr
  ext
  rw [coe_cast]

@[to_additive]
theorem prod_univ_add {M : Type _} [CommMonoidₓ M] {a b : ℕ} (f : Finₓ (a + b) → M) :
    (∏ i : Finₓ (a + b), f i) = (∏ i : Finₓ a, f (castAdd b i)) * ∏ i : Finₓ b, f (natAdd a i) := by
  rw [Fintype.prod_equiv fin_sum_fin_equiv.symm f fun i => f (fin_sum_fin_equiv.to_fun i)]
  swap
  · intro x
    simp only [← Equivₓ.to_fun_as_coe, ← Equivₓ.apply_symm_apply]
    
  apply prod_on_sum

@[to_additive]
theorem prod_trunc {M : Type _} [CommMonoidₓ M] {a b : ℕ} (f : Finₓ (a + b) → M)
    (hf : ∀ j : Finₓ b, f (natAdd a j) = 1) :
    (∏ i : Finₓ (a + b), f i) = ∏ i : Finₓ a, f (castLe (Nat.Le.intro rfl) i) := by
  simpa only [← prod_univ_add, ← Fintype.prod_eq_one _ hf, ← mul_oneₓ]

section PartialProd

variable [Monoidₓ α] {n : ℕ}

/-- For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_prod f` is `(1, a₁, a₁a₂, ..., a₁...aₙ)` in `αⁿ⁺¹`. -/
@[to_additive "For `f = (a₁, ..., aₙ)` in `αⁿ`, `partial_sum f` is\n`(0, a₁, a₁ + a₂, ..., a₁ + ... + aₙ)` in `αⁿ⁺¹`."]
def partialProd (f : Finₓ n → α) (i : Finₓ (n + 1)) : α :=
  ((List.ofFnₓ f).take i).Prod

@[simp, to_additive]
theorem partial_prod_zero (f : Finₓ n → α) : partialProd f 0 = 1 := by
  simp [← partial_prod]

@[to_additive]
theorem partial_prod_succ (f : Finₓ n → α) (j : Finₓ n) : partialProd f j.succ = partialProd f j.cast_succ * f j := by
  simp [← partial_prod, ← List.take_succ, ← List.ofFnNthValₓ, ← dif_pos j.is_lt, Option.coe_def]

@[to_additive]
theorem partial_prod_succ' (f : Finₓ (n + 1) → α) (j : Finₓ (n + 1)) :
    partialProd f j.succ = f 0 * partialProd (Finₓ.tail f) j := by
  simpa [← partial_prod]

end PartialProd

end Finₓ

namespace List

section CommMonoidₓ

variable [CommMonoidₓ α]

@[to_additive]
theorem prod_take_of_fn {n : ℕ} (f : Finₓ n → α) (i : ℕ) :
    ((ofFnₓ f).take i).Prod = ∏ j in Finset.univ.filter fun j : Finₓ n => j.val < i, f j := by
  have A : ∀ j : Finₓ n, ¬(j : ℕ) < 0 := fun j => not_lt_bot
  induction' i with i IH
  · simp [← A]
    
  by_cases' h : i < n
  · have : i < length (of_fn f) := by
      rwa [length_of_fn f]
    rw [prod_take_succ _ _ this]
    have A :
      ((Finset.univ : Finset (Finₓ n)).filter fun j => j.val < i + 1) =
        ((Finset.univ : Finset (Finₓ n)).filter fun j => j.val < i) ∪ {(⟨i, h⟩ : Finₓ n)} :=
      by
      ext j
      simp [← Nat.lt_succ_iff_lt_or_eq, ← Finₓ.ext_iff, -add_commₓ]
    have B : _root_.disjoint (Finset.filter (fun j : Finₓ n => j.val < i) Finset.univ) (singleton (⟨i, h⟩ : Finₓ n)) :=
      by
      simp
    rw [A, Finset.prod_union B, IH]
    simp
    
  · have A : (of_fn f).take i = (of_fn f).take i.succ := by
      rw [← length_of_fn f] at h
      have : length (of_fn f) ≤ i := not_lt.mp h
      rw [take_all_of_le this, take_all_of_le (le_transₓ this (Nat.le_succₓ _))]
    have B : ∀ j : Finₓ n, ((j : ℕ) < i.succ) = ((j : ℕ) < i) := by
      intro j
      have : (j : ℕ) < i := lt_of_lt_of_leₓ j.2 (not_lt.mp h)
      simp [← this, ← lt_transₓ this (Nat.lt_succ_selfₓ _)]
    simp [A, ← B, ← IH]
    

@[to_additive]
theorem prod_of_fn {n : ℕ} {f : Finₓ n → α} : (ofFnₓ f).Prod = ∏ i, f i := by
  convert prod_take_of_fn f n
  · rw [take_all_of_le (le_of_eqₓ (length_of_fn f))]
    
  · have : ∀ j : Finₓ n, (j : ℕ) < n := fun j => j.is_lt
    simp [← this]
    

end CommMonoidₓ

theorem alternating_sum_eq_finset_sum {G : Type _} [AddCommGroupₓ G] :
    ∀ L : List G, alternatingSum L = ∑ i : Finₓ L.length, (-1 : ℤ) ^ (i : ℕ) • L.nthLe i i.is_lt
  | [] => by
    rw [alternating_sum, Finset.sum_eq_zero]
    rintro ⟨i, ⟨⟩⟩
  | g :: [] => by
    simp
  | g :: h :: L =>
    calc
      g + -h + L.alternatingSum = g + -h + ∑ i : Finₓ L.length, (-1 : ℤ) ^ (i : ℕ) • L.nthLe i i.2 :=
        congr_arg _ (alternating_sum_eq_finset_sum _)
      _ = ∑ i : Finₓ (L.length + 2), (-1 : ℤ) ^ (i : ℕ) • List.nthLe (g :: h :: L) i _ := by
        rw [Finₓ.sum_univ_succ, Finₓ.sum_univ_succ, add_assocₓ]
        unfold_coes
        simp [← Nat.succ_eq_add_one, ← pow_addₓ]
        rfl
      

@[to_additive]
theorem alternating_prod_eq_finset_prod {G : Type _} [CommGroupₓ G] :
    ∀ L : List G, alternatingProd L = ∏ i : Finₓ L.length, L.nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ)
  | [] => by
    rw [alternating_prod, Finset.prod_eq_one]
    rintro ⟨i, ⟨⟩⟩
  | g :: [] => by
    show g = ∏ i : Finₓ 1, [g].nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ)
    rw [Finₓ.prod_univ_succ]
    simp
  | g :: h :: L =>
    calc
      g * h⁻¹ * L.alternatingProd = g * h⁻¹ * ∏ i : Finₓ L.length, L.nthLe i i.2 ^ (-1 : ℤ) ^ (i : ℕ) :=
        congr_arg _ (alternating_prod_eq_finset_prod _)
      _ = ∏ i : Finₓ (L.length + 2), List.nthLe (g :: h :: L) i _ ^ (-1 : ℤ) ^ (i : ℕ) := by
        rw [Finₓ.prod_univ_succ, Finₓ.prod_univ_succ, mul_assoc]
        unfold_coes
        simp [← Nat.succ_eq_add_one, ← pow_addₓ]
        rfl
      

end List

