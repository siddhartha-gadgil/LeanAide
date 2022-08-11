/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathbin.Algebra.BigOperators.Basic

/-!
# Products (respectively, sums) over a finset or a multiset.

The regular `finset.prod` and `multiset.prod` require `[comm_monoid α]`.
Often, there are collections `s : finset α` where `[monoid α]` and we know,
in a dependent fashion, that for all the terms `∀ (x ∈ s) (y ∈ s), commute x y`.
This allows to still have a well-defined product over `s`.

## Main definitions

- `finset.noncomm_prod`, requiring a proof of commutativity of held terms
- `multiset.noncomm_prod`, requiring a proof of commutativity of held terms

## Implementation details

While `list.prod` is defined via `list.foldl`, `noncomm_prod` is defined via
`multiset.foldr` for neater proofs and definitions. By the commutativity assumption,
the two must be equal.

-/


variable {α β γ : Type _} (f : α → β → β) (op : α → α → α)

namespace Multiset

/-- Fold of a `s : multiset α` with `f : α → β → β`, given a proof that `left_commutative f`
on all elements `x ∈ s`. -/
def noncommFoldr (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀ (b), f x (f y b) = f y (f x b)) (b : β) : β :=
  s.attach.foldr (f ∘ Subtype.val) (fun ⟨x, hx⟩ ⟨y, hy⟩ => comm x hx y hy) b

@[simp]
theorem noncomm_foldr_coe (l : List α)
    (comm : ∀, ∀ x ∈ (l : Multiset α), ∀, ∀ y ∈ (l : Multiset α), ∀ (b), f x (f y b) = f y (f x b)) (b : β) :
    noncommFoldr f (l : Multiset α) comm b = l.foldr f b := by
  simp only [← noncomm_foldr, ← coe_foldr, ← coe_attach, ← List.attach]
  rw [← List.foldr_map]
  simp [← List.map_pmap, ← List.pmap_eq_map]

@[simp]
theorem noncomm_foldr_empty (h : ∀, ∀ x ∈ (0 : Multiset α), ∀, ∀ y ∈ (0 : Multiset α), ∀ (b), f x (f y b) = f y (f x b))
    (b : β) : noncommFoldr f (0 : Multiset α) h b = b :=
  rfl

theorem noncomm_foldr_cons (s : Multiset α) (a : α)
    (h : ∀, ∀ x ∈ a ::ₘ s, ∀, ∀ y ∈ a ::ₘ s, ∀ (b), f x (f y b) = f y (f x b))
    (h' : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀ (b), f x (f y b) = f y (f x b)) (b : β) :
    noncommFoldr f (a ::ₘ s) h b = f a (noncommFoldr f s h' b) := by
  induction s using Quotientₓ.induction_on
  simp

theorem noncomm_foldr_eq_foldr (s : Multiset α) (h : LeftCommutative f) (b : β) :
    noncommFoldr f s (fun x _ y _ => h x y) b = foldr f h b s := by
  induction s using Quotientₓ.induction_on
  simp

variable [assoc : IsAssociative α op]

include assoc

/-- Fold of a `s : multiset α` with an associative `op : α → α → α`, given a proofs that `op`
is commutative on all elements `x ∈ s`. -/
def noncommFold (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, op x y = op y x) (a : α) : α :=
  noncommFoldr op s
    (fun x hx y hy b => by
      rw [← assoc.assoc, comm _ hx _ hy, assoc.assoc])
    a

@[simp]
theorem noncomm_fold_coe (l : List α) (comm : ∀, ∀ x ∈ (l : Multiset α), ∀, ∀ y ∈ (l : Multiset α), ∀, op x y = op y x)
    (a : α) : noncommFold op (l : Multiset α) comm a = l.foldr op a := by
  simp [← noncomm_fold]

@[simp]
theorem noncomm_fold_empty (h : ∀, ∀ x ∈ (0 : Multiset α), ∀, ∀ y ∈ (0 : Multiset α), ∀, op x y = op y x) (a : α) :
    noncommFold op (0 : Multiset α) h a = a :=
  rfl

theorem noncomm_fold_cons (s : Multiset α) (a : α) (h : ∀, ∀ x ∈ a ::ₘ s, ∀, ∀ y ∈ a ::ₘ s, ∀, op x y = op y x)
    (h' : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, op x y = op y x) (x : α) :
    noncommFold op (a ::ₘ s) h x = op a (noncommFold op s h' x) := by
  induction s using Quotientₓ.induction_on
  simp

theorem noncomm_fold_eq_fold (s : Multiset α) [IsCommutative α op] (a : α) :
    noncommFold op s (fun x _ y _ => IsCommutative.comm x y) a = fold op a s := by
  induction s using Quotientₓ.induction_on
  simp

omit assoc

variable [Monoidₓ α] [Monoidₓ β]

/-- Product of a `s : multiset α` with `[monoid α]`, given a proof that `*` commutes
on all elements `x ∈ s`. -/
@[to_additive
      "Sum of a `s : multiset α` with `[add_monoid α]`, given a proof that `+` commutes\non all elements `x ∈ s`."]
def noncommProd (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute x y) : α :=
  s.noncommFold (· * ·) comm 1

@[simp, to_additive]
theorem noncomm_prod_coe (l : List α) (comm : ∀, ∀ x ∈ (l : Multiset α), ∀, ∀ y ∈ (l : Multiset α), ∀, Commute x y) :
    noncommProd (l : Multiset α) comm = l.Prod := by
  rw [noncomm_prod]
  simp only [← noncomm_fold_coe]
  induction' l with hd tl hl
  · simp
    
  · rw [List.prod_cons, List.foldr, hl]
    intro x hx y hy
    exact comm x (List.mem_cons_of_memₓ _ hx) y (List.mem_cons_of_memₓ _ hy)
    

@[simp, to_additive]
theorem noncomm_prod_empty (h : ∀, ∀ x ∈ (0 : Multiset α), ∀, ∀ y ∈ (0 : Multiset α), ∀, Commute x y) :
    noncommProd (0 : Multiset α) h = 1 :=
  rfl

@[simp, to_additive]
theorem noncomm_prod_cons (s : Multiset α) (a : α) (comm : ∀, ∀ x ∈ a ::ₘ s, ∀, ∀ y ∈ a ::ₘ s, ∀, Commute x y) :
    noncommProd (a ::ₘ s) comm =
      a * noncommProd s fun x hx y hy => comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy) :=
  by
  induction s using Quotientₓ.induction_on
  simp

@[to_additive]
theorem noncomm_prod_cons' (s : Multiset α) (a : α) (comm : ∀, ∀ x ∈ a ::ₘ s, ∀, ∀ y ∈ a ::ₘ s, ∀, Commute x y) :
    noncommProd (a ::ₘ s) comm =
      (noncommProd s fun x hx y hy => comm _ (mem_cons_of_mem hx) _ (mem_cons_of_mem hy)) * a :=
  by
  induction' s using Quotientₓ.induction_on with s
  simp only [← quot_mk_to_coe, ← cons_coe, ← noncomm_prod_coe, ← List.prod_cons]
  induction' s with hd tl IH
  · simp
    
  · rw [List.prod_cons, mul_assoc, ← IH, ← mul_assoc, ← mul_assoc]
    · congr 1
      apply comm <;> simp
      
    · intro x hx y hy
      simp only [← quot_mk_to_coe, ← List.mem_cons_iff, ← mem_coe, ← cons_coe] at hx hy
      apply comm
      · cases hx <;> simp [← hx]
        
      · cases hy <;> simp [← hy]
        
      
    

@[protected, to_additive]
theorem nocomm_prod_map_aux (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute x y) {F : Type _}
    [MonoidHomClass F α β] (f : F) : ∀, ∀ x ∈ s.map f, ∀, ∀ y ∈ s.map f, ∀, Commute x y := by
  simp only [← Multiset.mem_map]
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (comm _ hx _ hy).map f

@[to_additive]
theorem noncomm_prod_map (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute x y) {F : Type _}
    [MonoidHomClass F α β] (f : F) : f (s.noncommProd comm) = (s.map f).noncommProd (nocomm_prod_map_aux s comm f) := by
  induction s using Quotientₓ.induction_on
  simpa using map_list_prod f _

@[to_additive noncomm_sum_eq_card_nsmul]
theorem noncomm_prod_eq_pow_card (s : Multiset α) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute x y) (m : α)
    (h : ∀, ∀ x ∈ s, ∀, x = m) : s.noncommProd comm = m ^ s.card := by
  induction s using Quotientₓ.induction_on
  simp only [← quot_mk_to_coe, ← noncomm_prod_coe, ← coe_card, ← mem_coe] at *
  exact List.prod_eq_pow_card _ m h

@[to_additive]
theorem noncomm_prod_eq_prod {α : Type _} [CommMonoidₓ α] (s : Multiset α) :
    (noncommProd s fun _ _ _ _ => Commute.all _ _) = prod s := by
  induction s using Quotientₓ.induction_on
  simp

@[to_additive noncomm_sum_add_commute]
theorem noncomm_prod_commute (s : Multiset α) (comm : ∀ x : α, x ∈ s → ∀ y : α, y ∈ s → Commute x y) (y : α)
    (h : ∀ x : α, x ∈ s → Commute y x) : Commute y (s.noncommProd comm) := by
  induction s using Quotientₓ.induction_on
  simp only [← quot_mk_to_coe, ← noncomm_prod_coe]
  exact Commute.list_prod_right _ _ h

end Multiset

namespace Finset

variable [Monoidₓ β] [Monoidₓ γ]

/-- Product of a `s : finset α` mapped with `f : α → β` with `[monoid β]`,
given a proof that `*` commutes on all elements `f x` for `x ∈ s`. -/
@[to_additive
      "Sum of a `s : finset α` mapped with `f : α → β` with `[add_monoid β]`,\ngiven a proof that `+` commutes on all elements `f x` for `x ∈ s`."]
def noncommProd (s : Finset α) (f : α → β) (comm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute (f x) (f y)) : β :=
  (s.1.map f).noncommProd
    (by
      simpa [← Multiset.mem_map, Finset.mem_def] using comm)

@[congr, to_additive]
theorem noncomm_prod_congr {s₁ s₂ : Finset α} {f g : α → β} (h₁ : s₁ = s₂) (h₂ : ∀, ∀ x ∈ s₂, ∀, f x = g x)
    (comm : ∀, ∀ x ∈ s₁, ∀, ∀ y ∈ s₁, ∀, Commute (f x) (f y)) :
    noncommProd s₁ f comm =
      noncommProd s₂ g fun x hx y hy => h₂ x hx ▸ h₂ y hy ▸ comm x (h₁.symm ▸ hx) y (h₁.symm ▸ hy) :=
  by
  simp_rw [noncomm_prod, Multiset.map_congr (congr_arg _ h₁) h₂]

@[simp, to_additive]
theorem noncomm_prod_to_finset [DecidableEq α] (l : List α) (f : α → β)
    (comm : ∀, ∀ x ∈ l.toFinset, ∀, ∀ y ∈ l.toFinset, ∀, Commute (f x) (f y)) (hl : l.Nodup) :
    noncommProd l.toFinset f comm = (l.map f).Prod := by
  rw [← List.dedup_eq_self] at hl
  simp [← noncomm_prod, ← hl]

@[simp, to_additive]
theorem noncomm_prod_empty (f : α → β) (h : ∀, ∀ x ∈ (∅ : Finset α), ∀, ∀ y ∈ (∅ : Finset α), ∀, Commute (f x) (f y)) :
    noncommProd (∅ : Finset α) f h = 1 :=
  rfl

@[simp, to_additive]
theorem noncomm_prod_insert_of_not_mem [DecidableEq α] (s : Finset α) (a : α) (f : α → β)
    (comm : ∀, ∀ x ∈ insert a s, ∀, ∀ y ∈ insert a s, ∀, Commute (f x) (f y)) (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      f a * noncommProd s f fun x hx y hy => comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy) :=
  by
  simp [← insert_val_of_not_mem ha, ← noncomm_prod]

@[to_additive]
theorem noncomm_prod_insert_of_not_mem' [DecidableEq α] (s : Finset α) (a : α) (f : α → β)
    (comm : ∀, ∀ x ∈ insert a s, ∀, ∀ y ∈ insert a s, ∀, Commute (f x) (f y)) (ha : a ∉ s) :
    noncommProd (insert a s) f comm =
      (noncommProd s f fun x hx y hy => comm _ (mem_insert_of_mem hx) _ (mem_insert_of_mem hy)) * f a :=
  by
  simp [← noncomm_prod, ← insert_val_of_not_mem ha, ← Multiset.noncomm_prod_cons']

@[simp, to_additive]
theorem noncomm_prod_singleton (a : α) (f : α → β) :
    (noncommProd ({a} : Finset α) f fun x hx y hy => by
        rw [mem_singleton.mp hx, mem_singleton.mp hy]) =
      f a :=
  by
  simp [← noncomm_prod, ← Multiset.singleton_eq_cons]

@[to_additive]
theorem noncomm_prod_map (s : Finset α) (f : α → β) (comm : ∀ x : α, x ∈ s → ∀ y : α, y ∈ s → Commute (f x) (f y))
    {F : Type _} [MonoidHomClass F β γ] (g : F) :
    g (s.noncommProd f comm) = s.noncommProd (fun i => g (f i)) fun x hx y hy => (comm x hx y hy).map g := by
  simp [← noncomm_prod, ← Multiset.noncomm_prod_map]

@[to_additive noncomm_sum_eq_card_nsmul]
theorem noncomm_prod_eq_pow_card (s : Finset α) (f : α → β)
    (comm : ∀ x : α, x ∈ s → ∀ y : α, y ∈ s → Commute (f x) (f y)) (m : β) (h : ∀ x : α, x ∈ s → f x = m) :
    s.noncommProd f comm = m ^ s.card := by
  rw [noncomm_prod, Multiset.noncomm_prod_eq_pow_card _ _ m]
  simp only [← Finset.card_def, ← Multiset.card_map]
  simpa using h

@[to_additive noncomm_sum_add_commute]
theorem noncomm_prod_commute (s : Finset α) (f : α → β) (comm : ∀ x : α, x ∈ s → ∀ y : α, y ∈ s → Commute (f x) (f y))
    (y : β) (h : ∀ x : α, x ∈ s → Commute y (f x)) : Commute y (s.noncommProd f comm) := by
  apply Multiset.noncomm_prod_commute
  intro y
  rw [Multiset.mem_map]
  rintro ⟨x, ⟨hx, rfl⟩⟩
  exact h x hx

@[to_additive]
theorem noncomm_prod_eq_prod {β : Type _} [CommMonoidₓ β] (s : Finset α) (f : α → β) :
    (noncommProd s f fun _ _ _ _ => Commute.all _ _) = s.Prod f := by
  classical
  induction' s using Finset.induction_on with a s ha IH
  · simp
    
  · simp [← ha, ← IH]
    

-- The non-commutative version of `finset.prod_union`
@[to_additive "The non-commutative version of `finset.sum_union`"]
theorem noncomm_prod_union_of_disjoint [DecidableEq α] {s t : Finset α} (h : Disjoint s t) (f : α → β)
    (comm : ∀, ∀ x ∈ s ∪ t, ∀, ∀ y ∈ s ∪ t, ∀, Commute (f x) (f y))
    (scomm : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute (f x) (f y) := fun _ hx _ hy =>
      comm _ (mem_union_left _ hx) _ (mem_union_left _ hy))
    (tcomm : ∀, ∀ x ∈ t, ∀, ∀ y ∈ t, ∀, Commute (f x) (f y) := fun _ hx _ hy =>
      comm _ (mem_union_right _ hx) _ (mem_union_right _ hy)) :
    noncommProd (s ∪ t) f comm = noncommProd s f scomm * noncommProd t f tcomm := by
  obtain ⟨sl, sl', rfl⟩ := exists_list_nodup_eq s
  obtain ⟨tl, tl', rfl⟩ := exists_list_nodup_eq t
  rw [List.disjoint_to_finset_iff_disjoint] at h
  simp [← sl', ← tl', ← noncomm_prod_to_finset, List.prod_append, List.to_finset_append, ← sl'.append tl' h]

@[protected, to_additive]
theorem noncomm_prod_mul_distrib_aux {s : Finset α} {f : α → β} {g : α → β}
    (comm_ff : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute (f x) (f y))
    (comm_gg : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute (g x) (g y))
    (comm_gf : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, x ≠ y → Commute (g x) (f y)) :
    ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute ((f * g) x) ((f * g) y) := by
  intro x hx y hy
  by_cases' h : x = y
  · subst h
    
  apply Commute.mul_left <;> apply Commute.mul_right
  · exact comm_ff x hx y hy
    
  · exact (comm_gf y hy x hx (Ne.symm h)).symm
    
  · exact comm_gf x hx y hy h
    
  · exact comm_gg x hx y hy
    

/-- The non-commutative version of `finset.prod_mul_distrib` -/
@[to_additive "The non-commutative version of `finset.sum_add_distrib`"]
theorem noncomm_prod_mul_distrib {s : Finset α} (f : α → β) (g : α → β)
    (comm_ff : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute (f x) (f y))
    (comm_gg : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, Commute (g x) (g y))
    (comm_gf : ∀, ∀ x ∈ s, ∀, ∀ y ∈ s, ∀, x ≠ y → Commute (g x) (f y)) :
    noncommProd s (f * g) (noncomm_prod_mul_distrib_aux comm_ff comm_gg comm_gf) =
      noncommProd s f comm_ff * noncommProd s g comm_gg :=
  by
  classical
  induction' s using Finset.induction_on with x s hnmem ih
  · simp
    
  · simp only [← Finset.noncomm_prod_insert_of_not_mem _ _ _ _ hnmem]
    specialize
      ih (fun x hx y hy => comm_ff x (mem_insert_of_mem hx) y (mem_insert_of_mem hy))
        (fun x hx y hy => comm_gg x (mem_insert_of_mem hx) y (mem_insert_of_mem hy)) fun x hx y hy hne =>
        comm_gf x (mem_insert_of_mem hx) y (mem_insert_of_mem hy) hne
    rw [ih, Pi.mul_apply]
    simp only [← mul_assoc]
    congr 1
    simp only [mul_assoc]
    congr 1
    apply noncomm_prod_commute
    intro y hy
    have : x ≠ y := by
      rintro rfl
      contradiction
    exact comm_gf x (mem_insert_self x s) y (mem_insert_of_mem hy) this
    

section FinitePi

variable {ι : Type _} [Fintype ι] [DecidableEq ι] {M : ι → Type _} [∀ i, Monoidₓ (M i)]

variable (x : ∀ i, M i)

@[to_additive]
theorem noncomm_prod_mul_single :
    (univ.noncommProd (fun i => Pi.mulSingle i (x i)) fun i _ j _ => Pi.mul_single_apply_commute x i j) = x := by
  ext i
  apply (univ.noncomm_prod_map (fun i => MonoidHom.single M i (x i)) _ (Pi.evalMonoidHom M i)).trans
  rw [← insert_erase (mem_univ i), noncomm_prod_insert_of_not_mem' _ _ _ _ (not_mem_erase _ _),
    noncomm_prod_eq_pow_card, one_pow]
  · simp
    
  · intro i h
    simp at h
    simp [← h]
    

@[to_additive]
theorem _root_.monoid_hom.pi_ext {f g : (∀ i, M i) →* γ} (h : ∀ i x, f (Pi.mulSingle i x) = g (Pi.mulSingle i x)) :
    f = g := by
  ext x
  rw [← noncomm_prod_mul_single x, univ.noncomm_prod_map, univ.noncomm_prod_map]
  congr 1 with i
  exact h i (x i)

end FinitePi

end Finset

