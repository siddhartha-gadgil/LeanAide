/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Field.Basic
import Mathbin.Data.Finset.Pi
import Mathbin.Data.Finset.Powerset

/-!
# Results about big operators with values in a (semi)ring

We prove results about big operators that involve some interaction between
multiplicative and additive structures on the values being combined.
-/


universe u v w

open BigOperators

variable {α : Type u} {β : Type v} {γ : Type w}

namespace Finset

variable {s s₁ s₂ : Finset α} {a : α} {b : β} {f g : α → β}

section CommMonoidₓ

variable [CommMonoidₓ β]

open Classical

theorem prod_pow_eq_pow_sum {x : β} {f : α → ℕ} : ∀ {s : Finset α}, (∏ i in s, x ^ f i) = x ^ ∑ x in s, f x := by
  apply Finset.induction
  · simp
    
  · intro a s has H
    rw [Finset.prod_insert has, Finset.sum_insert has, pow_addₓ, H]
    

end CommMonoidₓ

section Semiringₓ

variable [NonUnitalNonAssocSemiringₓ β]

theorem sum_mul : (∑ x in s, f x) * b = ∑ x in s, f x * b :=
  AddMonoidHom.map_sum (AddMonoidHom.mulRight b) _ s

theorem mul_sum : (b * ∑ x in s, f x) = ∑ x in s, b * f x :=
  AddMonoidHom.map_sum (AddMonoidHom.mulLeft b) _ s

theorem sum_mul_sum {ι₁ : Type _} {ι₂ : Type _} (s₁ : Finset ι₁) (s₂ : Finset ι₂) (f₁ : ι₁ → β) (f₂ : ι₂ → β) :
    ((∑ x₁ in s₁, f₁ x₁) * ∑ x₂ in s₂, f₂ x₂) = ∑ p in s₁.product s₂, f₁ p.1 * f₂ p.2 := by
  rw [sum_product, sum_mul, sum_congr rfl]
  intros
  rw [mul_sum]

end Semiringₓ

section Semiringₓ

variable [NonAssocSemiringₓ β]

theorem sum_mul_boole [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∑ x in s, f x * ite (a = x) 1 0) = ite (a ∈ s) (f a) 0 := by
  simp

theorem sum_boole_mul [DecidableEq α] (s : Finset α) (f : α → β) (a : α) :
    (∑ x in s, ite (a = x) 1 0 * f x) = ite (a ∈ s) (f a) 0 := by
  simp

end Semiringₓ

theorem sum_div [DivisionRing β] {s : Finset α} {f : α → β} {b : β} : (∑ x in s, f x) / b = ∑ x in s, f x / b := by
  simp only [← div_eq_mul_inv, ← sum_mul]

section CommSemiringₓ

variable [CommSemiringₓ β]

/-- The product over a sum can be written as a sum over the product of sets, `finset.pi`.
  `finset.prod_univ_sum` is an alternative statement when the product is over `univ`. -/
theorem prod_sum {δ : α → Type _} [DecidableEq α] [∀ a, DecidableEq (δ a)] {s : Finset α} {t : ∀ a, Finset (δ a)}
    {f : ∀ a, δ a → β} : (∏ a in s, ∑ b in t a, f a b) = ∑ p in s.pi t, ∏ x in s.attach, f x.1 (p x.1 x.2) := by
  induction' s using Finset.induction with a s ha ih
  · rw [pi_empty, sum_singleton]
    rfl
    
  · have h₁ :
      ∀,
        ∀ x ∈ t a,
          ∀, ∀, ∀ y ∈ t a, ∀, ∀ h : x ≠ y, Disjoint (image (pi.cons s a x) (pi s t)) (image (pi.cons s a y) (pi s t)) :=
      by
      intro x hx y hy h
      simp only [← disjoint_iff_ne, ← mem_image]
      rintro _ ⟨p₂, hp, eq₂⟩ _ ⟨p₃, hp₃, eq₃⟩ eq
      have : pi.cons s a x p₂ a (mem_insert_self _ _) = pi.cons s a y p₃ a (mem_insert_self _ _) := by
        rw [eq₂, eq₃, Eq]
      rw [pi.cons_same, pi.cons_same] at this
      exact h this
    rw [prod_insert ha, pi_insert ha, ih, sum_mul, sum_bUnion h₁]
    refine' sum_congr rfl fun b _ => _
    have h₂ : ∀, ∀ p₁ ∈ pi s t, ∀, ∀, ∀ p₂ ∈ pi s t, ∀, pi.cons s a b p₁ = pi.cons s a b p₂ → p₁ = p₂ :=
      fun p₁ h₁ p₂ h₂ eq => pi_cons_injective ha Eq
    rw [sum_image h₂, mul_sum]
    refine' sum_congr rfl fun g _ => _
    rw [attach_insert, prod_insert, prod_image]
    · simp only [← pi.cons_same]
      congr with ⟨v, hv⟩
      congr
      exact
        (pi.cons_ne
            (by
              rintro rfl <;> exact ha hv)).symm
      
    · exact fun _ _ _ _ => Subtype.eq ∘ Subtype.mk.injₓ
      
    · simp only [← mem_image]
      rintro ⟨⟨_, hm⟩, _, rfl⟩
      exact ha hm
      
    

open Classical

/-- The product of `f a + g a` over all of `s` is the sum
  over the powerset of `s` of the product of `f` over a subset `t` times
  the product of `g` over the complement of `t`  -/
theorem prod_add (f g : α → β) (s : Finset α) :
    (∏ a in s, f a + g a) = ∑ t in s.Powerset, (∏ a in t, f a) * ∏ a in s \ t, g a :=
  calc
    (∏ a in s, f a + g a) = ∏ a in s, ∑ p in ({True, False} : Finset Prop), if p then f a else g a := by
      simp
    _ =
        ∑ p in (s.pi fun _ => {True, False} : Finset (∀, ∀ a ∈ s, ∀, Prop)),
          ∏ a in s.attach, if p a.1 a.2 then f a.1 else g a.1 :=
      prod_sum
    _ = ∑ t in s.Powerset, (∏ a in t, f a) * ∏ a in s \ t, g a := by
      refine' Eq.symm (sum_bij (fun t _ a _ => a ∈ t) _ _ _ _)
      · simp [← subset_iff] <;> tauto
        
      · intro t ht
        erw [prod_ite (fun a : { a // a ∈ s } => f a.1) fun a : { a // a ∈ s } => g a.1]
        refine'
            congr_arg2ₓ _
              (prod_bij (fun (a : α) (ha : a ∈ t) => ⟨a, mem_powerset.1 ht ha⟩) _ _ _ fun b hb =>
                ⟨b, by
                  cases b <;>
                    simpa only [← true_andₓ, ← exists_prop, ← mem_filter, ← and_trueₓ, ← mem_attach, ← eq_self_iff_true,
                      ← Subtype.coe_mk] using hb⟩)
              (prod_bij
                (fun (a : α) (ha : a ∈ s \ t) =>
                  ⟨a, by
                    simp_all ⟩)
                _ _ _ fun b hb =>
                ⟨b, by
                  cases b <;>
                    · simp only [← true_andₓ, ← mem_filter, ← mem_attach, ← Subtype.coe_mk] at hb
                      simpa only [← true_andₓ, ← exists_prop, ← and_trueₓ, ← mem_sdiff, ← eq_self_iff_true, ←
                        Subtype.coe_mk, ← b_property]
                      ⟩) <;>
          intros <;> simp_all <;> simp_all
        
      · intro a₁ a₂ h₁ h₂ H
        ext x
        simp only [← Function.funext_iffₓ, ← subset_iff, ← mem_powerset, ← eq_iff_iff] at h₁ h₂ H
        exact ⟨fun hx => (H x (h₁ hx)).1 hx, fun hx => (H x (h₂ hx)).2 hx⟩
        
      · intro f hf
        exact
          ⟨s.filter fun a : α => ∃ h : a ∈ s, f a h, by
            simp , by
            funext <;> intros <;> simp [*]⟩
        
    

/-- `∏ i, (f i + g i) = (∏ i, f i) + ∑ i, g i * (∏ j < i, f j + g j) * (∏ j > i, f j)`. -/
theorem prod_add_ordered {ι R : Type _} [CommSemiringₓ R] [LinearOrderₓ ι] (s : Finset ι) (f g : ι → R) :
    (∏ i in s, f i + g i) =
      (∏ i in s, f i) + ∑ i in s, (g i * ∏ j in s.filter (· < i), f j + g j) * ∏ j in s.filter fun j => i < j, f j :=
  by
  refine'
    Finset.induction_on_max s
      (by
        simp )
      _
  clear s
  intro a s ha ihs
  have ha' : a ∉ s := fun ha' => (ha a ha').False
  rw [prod_insert ha', prod_insert ha', sum_insert ha', filter_insert, if_neg (lt_irreflₓ a), filter_true_of_mem ha,
    ihs, add_mulₓ, mul_addₓ, mul_addₓ, add_assocₓ]
  congr 1
  rw [add_commₓ]
  congr 1
  · rw [filter_false_of_mem, prod_empty, mul_oneₓ]
    exact (forall_mem_insert _ _ _).2 ⟨lt_irreflₓ a, fun i hi => (ha i hi).not_lt⟩
    
  · rw [mul_sum]
    refine' sum_congr rfl fun i hi => _
    rw [filter_insert, if_neg (ha i hi).not_lt, filter_insert, if_pos (ha i hi), prod_insert, mul_left_commₓ]
    exact mt (fun ha => (mem_filter.1 ha).1) ha'
    

/-- `∏ i, (f i - g i) = (∏ i, f i) - ∑ i, g i * (∏ j < i, f j - g j) * (∏ j > i, f j)`. -/
theorem prod_sub_ordered {ι R : Type _} [CommRingₓ R] [LinearOrderₓ ι] (s : Finset ι) (f g : ι → R) :
    (∏ i in s, f i - g i) =
      (∏ i in s, f i) - ∑ i in s, (g i * ∏ j in s.filter (· < i), f j - g j) * ∏ j in s.filter fun j => i < j, f j :=
  by
  simp only [← sub_eq_add_neg]
  convert prod_add_ordered s f fun i => -g i
  simp

/-- `∏ i, (1 - f i) = 1 - ∑ i, f i * (∏ j < i, 1 - f j)`. This formula is useful in construction of
a partition of unity from a collection of “bump” functions.  -/
theorem prod_one_sub_ordered {ι R : Type _} [CommRingₓ R] [LinearOrderₓ ι] (s : Finset ι) (f : ι → R) :
    (∏ i in s, 1 - f i) = 1 - ∑ i in s, f i * ∏ j in s.filter (· < i), 1 - f j := by
  rw [prod_sub_ordered]
  simp

/-- Summing `a^s.card * b^(n-s.card)` over all finite subsets `s` of a `finset`
gives `(a + b)^s.card`.-/
theorem sum_pow_mul_eq_add_pow {α R : Type _} [CommSemiringₓ R] (a b : R) (s : Finset α) :
    (∑ t in s.Powerset, a ^ t.card * b ^ (s.card - t.card)) = (a + b) ^ s.card := by
  rw [← prod_const, prod_add]
  refine' Finset.sum_congr rfl fun t ht => _
  rw [prod_const, prod_const, ← card_sdiff (mem_powerset.1 ht)]

theorem dvd_sum {b : β} {s : Finset α} {f : α → β} (h : ∀, ∀ x ∈ s, ∀, b ∣ f x) : b ∣ ∑ x in s, f x :=
  Multiset.dvd_sum fun y hy => by
    rcases Multiset.mem_map.1 hy with ⟨x, hx, rfl⟩ <;> exact h x hx

@[norm_cast]
theorem prod_nat_cast (s : Finset α) (f : α → ℕ) : ↑(∏ x in s, f x : ℕ) = ∏ x in s, (f x : β) :=
  (Nat.castRingHom β).map_prod f s

end CommSemiringₓ

section CommRingₓ

variable {R : Type _} [CommRingₓ R]

theorem prod_range_cast_nat_sub (n k : ℕ) : (∏ i in range k, (n - i : R)) = (∏ i in range k, n - i : ℕ) := by
  rw [prod_nat_cast]
  cases' le_or_ltₓ k n with hkn hnk
  · exact prod_congr rfl fun i hi => (Nat.cast_sub <| (mem_range.1 hi).le.trans hkn).symm
    
  · rw [← mem_range] at hnk
    rw [prod_eq_zero hnk, prod_eq_zero hnk] <;> simp
    

end CommRingₓ

/-- A product over all subsets of `s ∪ {x}` is obtained by multiplying the product over all subsets
of `s`, and over all subsets of `s` to which one adds `x`. -/
@[to_additive
      "A sum over all subsets of `s ∪ {x}` is obtained by summing the sum over all subsets\nof `s`, and over all subsets of `s` to which one adds `x`."]
theorem prod_powerset_insert [DecidableEq α] [CommMonoidₓ β] {s : Finset α} {x : α} (h : x ∉ s) (f : Finset α → β) :
    (∏ a in (insert x s).Powerset, f a) = (∏ a in s.Powerset, f a) * ∏ t in s.Powerset, f (insert x t) := by
  rw [powerset_insert, Finset.prod_union, Finset.prod_image]
  · intro t₁ h₁ t₂ h₂ heq
    rw [← Finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₁ h), ←
      Finset.erase_insert (not_mem_of_mem_powerset_of_not_mem h₂ h), HEq]
    
  · rw [Finset.disjoint_iff_ne]
    intro t₁ h₁ t₂ h₂
    rcases Finset.mem_image.1 h₂ with ⟨t₃, h₃, H₃₂⟩
    rw [← H₃₂]
    exact ne_insert_of_not_mem _ _ (not_mem_of_mem_powerset_of_not_mem h₁ h)
    

/-- A product over `powerset s` is equal to the double product over sets of subsets of `s` with
`card s = k`, for `k = 1, ..., card s`. -/
@[to_additive
      "A sum over `powerset s` is equal to the double sum over sets of subsets of `s` with\n`card s = k`, for `k = 1, ..., card s`"]
theorem prod_powerset [CommMonoidₓ β] (s : Finset α) (f : Finset α → β) :
    (∏ t in powerset s, f t) = ∏ j in range (card s + 1), ∏ t in powersetLen j s, f t := by
  classical
  rw [powerset_card_bUnion, prod_bUnion]
  intro i hi j hj hij
  rw [Function.onFun, powerset_len_eq_filter, powerset_len_eq_filter, disjoint_filter]
  intro x hx hc hnc
  apply hij
  rwa [← hc]

theorem sum_range_succ_mul_sum_range_succ [NonUnitalNonAssocSemiringₓ β] (n k : ℕ) (f g : ℕ → β) :
    ((∑ i in range (n + 1), f i) * ∑ i in range (k + 1), g i) =
      (((∑ i in range n, f i) * ∑ i in range k, g i) + f n * ∑ i in range k, g i) + (∑ i in range n, f i) * g k +
        f n * g k :=
  by
  simp only [← add_mulₓ, ← mul_addₓ, ← add_assocₓ, ← sum_range_succ]

end Finset

