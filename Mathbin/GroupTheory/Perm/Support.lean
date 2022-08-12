/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Aaron Anderson, Yakov Pechersky
-/
import Mathbin.Data.Finset.Card
import Mathbin.Data.Fintype.Basic
import Mathbin.GroupTheory.Perm.Basic

/-!
# Support of a permutation

## Main definitions

In the following, `f g : equiv.perm α`.

* `equiv.perm.disjoint`: two permutations `f` and `g` are `disjoint` if every element is fixed
  either by `f`, or by `g`.
  Equivalently, `f` and `g` are `disjoint` iff their `support` are disjoint.
* `equiv.perm.is_swap`: `f = swap x y` for `x ≠ y`.
* `equiv.perm.support`: the elements `x : α` that are not fixed by `f`.

-/


open Equivₓ Finset

namespace Equivₓ.Perm

variable {α : Type _}

section Disjoint

/-- Two permutations `f` and `g` are `disjoint` if their supports are disjoint, i.e.,
every element is fixed either by `f`, or by `g`. -/
def Disjoint (f g : Perm α) :=
  ∀ x, f x = x ∨ g x = x

variable {f g h : Perm α}

@[symm]
theorem Disjoint.symm : Disjoint f g → Disjoint g f := by
  simp only [← Disjoint, ← Or.comm, ← imp_self]

theorem Disjoint.symmetric : Symmetric (@Disjoint α) := fun _ _ => Disjoint.symm

theorem disjoint_comm : Disjoint f g ↔ Disjoint g f :=
  ⟨Disjoint.symm, Disjoint.symm⟩

theorem Disjoint.commute (h : Disjoint f g) : Commute f g :=
  Equivₓ.ext fun x =>
    (h x).elim
      (fun hf =>
        (h (g x)).elim
          (fun hg => by
            simp [← mul_apply, ← hf, ← hg])
          fun hg => by
          simp [← mul_apply, ← hf, ← g.injective hg])
      fun hg =>
      (h (f x)).elim
        (fun hf => by
          simp [← mul_apply, ← f.injective hf, ← hg])
        fun hf => by
        simp [← mul_apply, ← hf, ← hg]

@[simp]
theorem disjoint_one_left (f : Perm α) : Disjoint 1 f := fun _ => Or.inl rfl

@[simp]
theorem disjoint_one_right (f : Perm α) : Disjoint f 1 := fun _ => Or.inr rfl

theorem disjoint_iff_eq_or_eq : Disjoint f g ↔ ∀ x : α, f x = x ∨ g x = x :=
  Iff.rfl

@[simp]
theorem disjoint_refl_iff : Disjoint f f ↔ f = 1 := by
  refine' ⟨fun h => _, fun h => h.symm ▸ disjoint_one_left 1⟩
  ext x
  cases' h x with hx hx <;> simp [← hx]

theorem Disjoint.inv_left (h : Disjoint f g) : Disjoint f⁻¹ g := by
  intro x
  rw [inv_eq_iff_eq, eq_comm]
  exact h x

theorem Disjoint.inv_right (h : Disjoint f g) : Disjoint f g⁻¹ :=
  h.symm.inv_left.symm

@[simp]
theorem disjoint_inv_left_iff : Disjoint f⁻¹ g ↔ Disjoint f g := by
  refine' ⟨fun h => _, disjoint.inv_left⟩
  convert h.inv_left
  exact (inv_invₓ _).symm

@[simp]
theorem disjoint_inv_right_iff : Disjoint f g⁻¹ ↔ Disjoint f g := by
  rw [disjoint_comm, disjoint_inv_left_iff, disjoint_comm]

theorem Disjoint.mul_left (H1 : Disjoint f h) (H2 : Disjoint g h) : Disjoint (f * g) h := fun x => by
  cases H1 x <;> cases H2 x <;> simp [*]

theorem Disjoint.mul_right (H1 : Disjoint f g) (H2 : Disjoint f h) : Disjoint f (g * h) := by
  rw [disjoint_comm]
  exact H1.symm.mul_left H2.symm

theorem disjoint_prod_right (l : List (Perm α)) (h : ∀, ∀ g ∈ l, ∀, Disjoint f g) : Disjoint f l.Prod := by
  induction' l with g l ih
  · exact disjoint_one_right _
    
  · rw [List.prod_cons]
    exact (h _ (List.mem_cons_selfₓ _ _)).mul_right (ih fun g hg => h g (List.mem_cons_of_memₓ _ hg))
    

theorem disjoint_prod_perm {l₁ l₂ : List (Perm α)} (hl : l₁.Pairwise Disjoint) (hp : l₁ ~ l₂) : l₁.Prod = l₂.Prod :=
  hp.prod_eq' <| hl.imp fun f g => Disjoint.commute

theorem nodup_of_pairwise_disjoint {l : List (Perm α)} (h1 : (1 : Perm α) ∉ l) (h2 : l.Pairwise Disjoint) : l.Nodup :=
  by
  refine' List.Pairwiseₓ.imp_of_mem _ h2
  rintro σ - h_mem - h_disjoint rfl
  suffices σ = 1 by
    rw [this] at h_mem
    exact h1 h_mem
  exact ext fun a => (or_selfₓ _).mp (h_disjoint a)

theorem pow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℕ, (f ^ n) x = x
  | 0 => rfl
  | n + 1 => by
    rw [pow_succ'ₓ, mul_apply, hfx, pow_apply_eq_self_of_apply_eq_self]

theorem zpow_apply_eq_self_of_apply_eq_self {x : α} (hfx : f x = x) : ∀ n : ℤ, (f ^ n) x = x
  | (n : ℕ) => pow_apply_eq_self_of_apply_eq_self hfx n
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, inv_eq_iff_eq, pow_apply_eq_self_of_apply_eq_self hfx]

theorem pow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) : ∀ n : ℕ, (f ^ n) x = x ∨ (f ^ n) x = f x
  | 0 => Or.inl rfl
  | n + 1 =>
    (pow_apply_eq_of_apply_apply_eq_self n).elim
      (fun h =>
        Or.inr
          (by
            rw [pow_succₓ, mul_apply, h]))
      fun h =>
      Or.inl
        (by
          rw [pow_succₓ, mul_apply, h, hffx])

theorem zpow_apply_eq_of_apply_apply_eq_self {x : α} (hffx : f (f x) = x) : ∀ i : ℤ, (f ^ i) x = x ∨ (f ^ i) x = f x
  | (n : ℕ) => pow_apply_eq_of_apply_apply_eq_self hffx n
  | -[1+ n] => by
    rw [zpow_neg_succ_of_nat, inv_eq_iff_eq, ← f.injective.eq_iff, ← mul_apply, ← pow_succₓ, eq_comm, inv_eq_iff_eq, ←
      mul_apply, ← pow_succ'ₓ, @eq_comm _ x, Or.comm]
    exact pow_apply_eq_of_apply_apply_eq_self hffx _

theorem Disjoint.mul_apply_eq_iff {σ τ : Perm α} (hστ : Disjoint σ τ) {a : α} : (σ * τ) a = a ↔ σ a = a ∧ τ a = a := by
  refine'
    ⟨fun h => _, fun h => by
      rw [mul_apply, h.2, h.1]⟩
  cases' hστ a with hσ hτ
  · exact ⟨hσ, σ.injective (h.trans hσ.symm)⟩
    
  · exact ⟨(congr_arg σ hτ).symm.trans h, hτ⟩
    

theorem Disjoint.mul_eq_one_iff {σ τ : Perm α} (hστ : Disjoint σ τ) : σ * τ = 1 ↔ σ = 1 ∧ τ = 1 := by
  simp_rw [ext_iff, one_apply, hστ.mul_apply_eq_iff, forall_and_distrib]

theorem Disjoint.zpow_disjoint_zpow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℤ) : Disjoint (σ ^ m) (τ ^ n) := fun x =>
  Or.imp (fun h => zpow_apply_eq_self_of_apply_eq_self h m) (fun h => zpow_apply_eq_self_of_apply_eq_self h n) (hστ x)

theorem Disjoint.pow_disjoint_pow {σ τ : Perm α} (hστ : Disjoint σ τ) (m n : ℕ) : Disjoint (σ ^ m) (τ ^ n) :=
  hστ.zpow_disjoint_zpow m n

end Disjoint

section IsSwap

variable [DecidableEq α]

/-- `f.is_swap` indicates that the permutation `f` is a transposition of two elements. -/
def IsSwap (f : Perm α) : Prop :=
  ∃ x y, x ≠ y ∧ f = swap x y

theorem IsSwap.of_subtype_is_swap {p : α → Prop} [DecidablePred p] {f : Perm (Subtype p)} (h : f.IsSwap) :
    (ofSubtype f).IsSwap :=
  let ⟨⟨x, hx⟩, ⟨y, hy⟩, hxy⟩ := h
  ⟨x, y, by
    simp only [← Ne.def] at hxy
    exact hxy.1,
    Equivₓ.ext fun z => by
      rw [hxy.2, of_subtype]
      simp only [← swap_apply_def, ← coe_fn_mk, ← swap_inv, ← Subtype.mk_eq_mk, ← MonoidHom.coe_mk]
      split_ifs <;>
        first |
          rw [Subtype.coe_mk]|
          cc⟩

theorem ne_and_ne_of_swap_mul_apply_ne_self {f : Perm α} {x y : α} (hy : (swap x (f x) * f) y ≠ y) : f y ≠ y ∧ y ≠ x :=
  by
  simp only [← swap_apply_def, ← mul_apply, ← f.injective.eq_iff] at *
  by_cases' h : f y = x
  · constructor <;> intro <;> simp_all only [← if_true, ← eq_self_iff_true, ← not_true, ← Ne.def]
    
  · split_ifs  at hy <;> cc
    

end IsSwap

section Support

section Set

variable (p q : Perm α)

theorem set_support_inv_eq : { x | p⁻¹ x ≠ x } = { x | p x ≠ x } := by
  ext x
  simp only [← Set.mem_set_of_eq, ← Ne.def]
  rw [inv_def, symm_apply_eq, eq_comm]

theorem set_support_apply_mem {p : Perm α} {a : α} : p a ∈ { x | p x ≠ x } ↔ a ∈ { x | p x ≠ x } := by
  simp

theorem set_support_zpow_subset (n : ℤ) : { x | (p ^ n) x ≠ x } ⊆ { x | p x ≠ x } := by
  intro x
  simp only [← Set.mem_set_of_eq, ← Ne.def]
  intro hx H
  simpa [← zpow_apply_eq_self_of_apply_eq_self H] using hx

theorem set_support_mul_subset : { x | (p * q) x ≠ x } ⊆ { x | p x ≠ x } ∪ { x | q x ≠ x } := by
  intro x
  simp only [← perm.coe_mul, ← Function.comp_app, ← Ne.def, ← Set.mem_union_eq, ← Set.mem_set_of_eq]
  by_cases' hq : q x = x <;> simp [← hq]

end Set

variable [DecidableEq α] [Fintype α] {f g : Perm α}

/-- The `finset` of nonfixed points of a permutation. -/
def support (f : Perm α) : Finset α :=
  univ.filter fun x => f x ≠ x

@[simp]
theorem mem_support {x : α} : x ∈ f.support ↔ f x ≠ x := by
  rw [support, mem_filter, and_iff_right (mem_univ x)]

theorem not_mem_support {x : α} : x ∉ f.support ↔ f x = x := by
  simp

theorem coe_support_eq_set_support (f : Perm α) : (f.support : Set α) = { x | f x ≠ x } := by
  ext
  simp

@[simp]
theorem support_eq_empty_iff {σ : Perm α} : σ.support = ∅ ↔ σ = 1 := by
  simp_rw [Finset.ext_iff, mem_support, Finset.not_mem_empty, iff_falseₓ, not_not, Equivₓ.Perm.ext_iff, one_apply]

@[simp]
theorem support_one : (1 : Perm α).support = ∅ := by
  rw [support_eq_empty_iff]

@[simp]
theorem support_refl : support (Equivₓ.refl α) = ∅ :=
  support_one

theorem support_congr (h : f.support ⊆ g.support) (h' : ∀, ∀ x ∈ g.support, ∀, f x = g x) : f = g := by
  ext x
  by_cases' hx : x ∈ g.support
  · exact h' x hx
    
  · rw [not_mem_support.mp hx, ← not_mem_support]
    exact fun H => hx (h H)
    

theorem support_mul_le (f g : Perm α) : (f * g).support ≤ f.support⊔g.support := fun x => by
  rw [sup_eq_union, mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_distrib, not_imp_not]
  rintro ⟨hf, hg⟩
  rw [hg, hf]

theorem exists_mem_support_of_mem_support_prod {l : List (Perm α)} {x : α} (hx : x ∈ l.Prod.support) :
    ∃ f : Perm α, f ∈ l ∧ x ∈ f.support := by
  contrapose! hx
  simp_rw [mem_support, not_not] at hx⊢
  induction' l with f l ih generalizing hx
  · rfl
    
  · rw [List.prod_cons, mul_apply, ih fun g hg => hx g (Or.inr hg), hx f (Or.inl rfl)]
    

theorem support_pow_le (σ : Perm α) (n : ℕ) : (σ ^ n).support ≤ σ.support := fun x h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (pow_apply_eq_self_of_apply_eq_self h2 n)

@[simp]
theorem support_inv (σ : Perm α) : support σ⁻¹ = σ.support := by
  simp_rw [Finset.ext_iff, mem_support, not_iff_not, inv_eq_iff_eq.trans eq_comm, iff_selfₓ, imp_true_iff]

@[simp]
theorem apply_mem_support {x : α} : f x ∈ f.support ↔ x ∈ f.support := by
  rw [mem_support, mem_support, Ne.def, Ne.def, not_iff_not, apply_eq_iff_eq]

@[simp]
theorem pow_apply_mem_support {n : ℕ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  induction' n with n ih
  · rfl
    
  rw [pow_succₓ, perm.mul_apply, apply_mem_support, ih]

@[simp]
theorem zpow_apply_mem_support {n : ℤ} {x : α} : (f ^ n) x ∈ f.support ↔ x ∈ f.support := by
  cases n
  · rw [Int.of_nat_eq_coe, zpow_coe_nat, pow_apply_mem_support]
    
  · rw [zpow_neg_succ_of_nat, ← support_inv, ← inv_pow, pow_apply_mem_support]
    

theorem pow_eq_on_of_mem_support (h : ∀, ∀ x ∈ f.support ∩ g.support, ∀, f x = g x) (k : ℕ) :
    ∀, ∀ x ∈ f.support ∩ g.support, ∀, (f ^ k) x = (g ^ k) x := by
  induction' k with k hk
  · simp
    
  · intro x hx
    rw [pow_succ'ₓ, mul_apply, pow_succ'ₓ, mul_apply, h _ hx, hk]
    rwa [mem_inter, apply_mem_support, ← h _ hx, apply_mem_support, ← mem_inter]
    

theorem disjoint_iff_disjoint_support : Disjoint f g ↔ Disjoint f.support g.support := by
  simp [← disjoint_iff_eq_or_eq, ← disjoint_iff, ← Finset.ext_iff, ← not_and_distrib]

theorem Disjoint.disjoint_support (h : Disjoint f g) : Disjoint f.support g.support :=
  disjoint_iff_disjoint_support.1 h

theorem Disjoint.support_mul (h : Disjoint f g) : (f * g).support = f.support ∪ g.support := by
  refine' le_antisymmₓ (support_mul_le _ _) fun a => _
  rw [mem_union, mem_support, mem_support, mem_support, mul_apply, ← not_and_distrib, not_imp_not]
  exact
    (h a).elim (fun hf h => ⟨hf, f.apply_eq_iff_eq.mp (h.trans hf.symm)⟩) fun hg h =>
      ⟨(congr_arg f hg).symm.trans h, hg⟩

theorem support_prod_of_pairwise_disjoint (l : List (Perm α)) (h : l.Pairwise Disjoint) :
    l.Prod.support = (l.map support).foldr (·⊔·) ⊥ := by
  induction' l with hd tl hl
  · simp
    
  · rw [List.pairwise_cons] at h
    have : Disjoint hd tl.prod := disjoint_prod_right _ h.left
    simp [← this.support_mul, ← hl h.right]
    

theorem support_prod_le (l : List (Perm α)) : l.Prod.support ≤ (l.map support).foldr (·⊔·) ⊥ := by
  induction' l with hd tl hl
  · simp
    
  · rw [List.prod_cons, List.map_cons, List.foldr_cons]
    refine' (support_mul_le hd tl.prod).trans _
    exact sup_le_sup le_rfl hl
    

theorem support_zpow_le (σ : Perm α) (n : ℤ) : (σ ^ n).support ≤ σ.support := fun x h1 =>
  mem_support.mpr fun h2 => mem_support.mp h1 (zpow_apply_eq_self_of_apply_eq_self h2 n)

-- ./././Mathport/Syntax/Translate/Tactic/Basic.lean:51:50: missing argument
@[simp]
theorem support_swap {x y : α} (h : x ≠ y) : support (swap x y) = {x, y} := by
  ext z
  by_cases' hx : z = x
  any_goals {
  }
  by_cases' hy : z = y <;>
    · simp [← swap_apply_of_ne_of_ne, ← hx, ← hy] <;> cc
      

theorem support_swap_iff (x y : α) : support (swap x y) = {x, y} ↔ x ≠ y := by
  refine' ⟨fun h H => _, support_swap⟩
  subst H
  simp only [← swap_self, ← support_refl, ← pair_eq_singleton] at h
  have : x ∈ ∅ := by
    rw [h]
    exact mem_singleton.mpr rfl
  simpa

theorem support_swap_mul_swap {x y z : α} (h : List.Nodupₓ [x, y, z]) : support (swap x y * swap y z) = {x, y, z} := by
  simp only [← List.not_mem_nilₓ, ← and_trueₓ, ← List.mem_cons_iff, ← not_false_iff, ← List.nodup_cons, ←
    List.mem_singletonₓ, ← and_selfₓ, ← List.nodup_nil] at h
  push_neg  at h
  apply le_antisymmₓ
  · convert support_mul_le _ _
    rw [support_swap h.left.left, support_swap h.right]
    ext
    simp [← Or.comm, ← Or.left_comm]
    
  · intro
    simp only [← mem_insert, ← mem_singleton]
    rintro (rfl | rfl | rfl | _) <;>
      simp [← swap_apply_of_ne_of_ne, ← h.left.left, ← h.left.left.symm, ← h.left.right, ← h.left.right.symm, ←
        h.right.symm]
    

theorem support_swap_mul_ge_support_diff (f : Perm α) (x y : α) : f.support \ {x, y} ≤ (swap x y * f).support := by
  intro
  simp only [← and_imp, ← perm.coe_mul, ← Function.comp_app, ← Ne.def, ← mem_support, ← mem_insert, ← mem_sdiff, ←
    mem_singleton]
  push_neg
  rintro ha ⟨hx, hy⟩ H
  rw [swap_apply_eq_iff, swap_apply_of_ne_of_ne hx hy] at H
  exact ha H

theorem support_swap_mul_eq (f : Perm α) (x : α) (h : f (f x) ≠ x) : (swap x (f x) * f).support = f.support \ {x} := by
  by_cases' hx : f x = x
  · simp [← hx, ← sdiff_singleton_eq_erase, ← not_mem_support.mpr hx, ← erase_eq_of_not_mem]
    
  ext z
  by_cases' hzx : z = x
  · simp [← hzx]
    
  by_cases' hzf : z = f x
  · simp [← hzf, ← hx, ← h, ← swap_apply_of_ne_of_ne]
    
  by_cases' hzfx : f z = x
  · simp [← Ne.symm hzx, ← hzx, ← Ne.symm hzf, ← hzfx]
    
  · simp [← Ne.symm hzx, ← hzx, ← Ne.symm hzf, ← hzfx, ← f.injective.ne hzx, ← swap_apply_of_ne_of_ne]
    

theorem mem_support_swap_mul_imp_mem_support_ne {x y : α} (hy : y ∈ support (swap x (f x) * f)) :
    y ∈ support f ∧ y ≠ x := by
  simp only [← mem_support, ← swap_apply_def, ← mul_apply, ← f.injective.eq_iff] at *
  by_cases' h : f y = x
  · constructor <;> intro <;> simp_all only [← if_true, ← eq_self_iff_true, ← not_true, ← Ne.def]
    
  · split_ifs  at hy <;> cc
    

theorem Disjoint.mem_imp (h : Disjoint f g) {x : α} (hx : x ∈ f.support) : x ∉ g.support := fun H =>
  h.disjoint_support (mem_inter_of_mem hx H)

theorem eq_on_support_mem_disjoint {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    ∀, ∀ x ∈ f.support, ∀, f x = l.Prod x := by
  induction' l with hd tl IH
  · simpa using h
    
  · intro x hx
    rw [List.pairwise_cons] at hl
    rw [List.mem_cons_iff] at h
    rcases h with (rfl | h)
    · rw [List.prod_cons, mul_apply, not_mem_support.mp ((disjoint_prod_right tl hl.left).mem_imp hx)]
      
    · rw [List.prod_cons, mul_apply, ← IH h hl.right _ hx, eq_comm, ← not_mem_support]
      refine' (hl.left _ h).symm.mem_imp _
      simpa using hx
      
    

theorem Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.support ≤ f.support) (hg : y.support ≤ g.support) :
    Disjoint x y := by
  rw [disjoint_iff_disjoint_support] at h⊢
  intro a ha
  exact h (mem_inter_of_mem (hf (mem_of_mem_inter_left ha)) (hg (mem_of_mem_inter_right ha)))

theorem support_le_prod_of_mem {l : List (Perm α)} (h : f ∈ l) (hl : l.Pairwise Disjoint) :
    f.support ≤ l.Prod.support := by
  intro x hx
  rwa [mem_support, ← eq_on_support_mem_disjoint h hl _ hx, ← mem_support]

section ExtendDomain

variable {β : Type _} [DecidableEq β] [Fintype β] {p : β → Prop} [DecidablePred p]

@[simp]
theorem support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    support (g.extendDomain f) = g.support.map f.asEmbedding := by
  ext b
  simp only [← exists_prop, ← Function.Embedding.coe_fn_mk, ← to_embedding_apply, ← mem_map, ← Ne.def, ←
    Function.Embedding.trans_apply, ← mem_support]
  by_cases' pb : p b
  · rw [extend_domain_apply_subtype _ _ pb]
    constructor
    · rintro h
      refine'
        ⟨f.symm ⟨b, pb⟩, _, by
          simp ⟩
      contrapose! h
      simp [← h]
      
    · rintro ⟨a, ha, hb⟩
      contrapose! ha
      obtain rfl : a = f.symm ⟨b, pb⟩ := by
        rw [eq_symm_apply]
        exact Subtype.coe_injective hb
      rw [eq_symm_apply]
      exact Subtype.coe_injective ha
      
    
  · rw [extend_domain_apply_not_subtype _ _ pb]
    simp only [← not_exists, ← false_iffₓ, ← not_and, ← eq_self_iff_true, ← not_true]
    rintro a ha rfl
    exact pb (Subtype.prop _)
    

theorem card_support_extend_domain (f : α ≃ Subtype p) {g : Perm α} :
    (g.extendDomain f).support.card = g.support.card := by
  simp

end ExtendDomain

section Card

@[simp]
theorem card_support_eq_zero {f : Perm α} : f.support.card = 0 ↔ f = 1 := by
  rw [Finset.card_eq_zero, support_eq_empty_iff]

theorem one_lt_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 1 < f.support.card := by
  simp_rw [one_lt_card_iff, mem_support, ← not_or_distrib]
  contrapose! h
  ext a
  specialize h (f a) a
  rwa [apply_eq_iff_eq, or_selfₓ, or_selfₓ] at h

theorem card_support_ne_one (f : Perm α) : f.support.card ≠ 1 := by
  by_cases' h : f = 1
  · exact ne_of_eq_of_ne (card_support_eq_zero.mpr h) zero_ne_one
    
  · exact ne_of_gtₓ (one_lt_card_support_of_ne_one h)
    

@[simp]
theorem card_support_le_one {f : Perm α} : f.support.card ≤ 1 ↔ f = 1 := by
  rw [le_iff_lt_or_eqₓ, Nat.lt_succ_iffₓ, Nat.le_zero_iffₓ, card_support_eq_zero, or_iff_not_imp_right,
    imp_iff_right f.card_support_ne_one]

theorem two_le_card_support_of_ne_one {f : Perm α} (h : f ≠ 1) : 2 ≤ f.support.card :=
  one_lt_card_support_of_ne_one h

theorem card_support_swap_mul {f : Perm α} {x : α} (hx : f x ≠ x) : (swap x (f x) * f).support.card < f.support.card :=
  Finset.card_lt_card
    ⟨fun z hz => (mem_support_swap_mul_imp_mem_support_ne hz).left, fun h =>
      absurd (h (mem_support.2 hx))
        (mt mem_support.1
          (by
            simp ))⟩

theorem card_support_swap {x y : α} (hxy : x ≠ y) : (swap x y).support.card = 2 :=
  show
    (swap x y).support.card =
      Finset.card
        ⟨x ::ₘ y ::ₘ 0, by
          simp [← hxy]⟩
    from
    congr_arg card <| by
      simp [← support_swap hxy, *, ← Finset.ext_iff]

@[simp]
theorem card_support_eq_two {f : Perm α} : f.support.card = 2 ↔ IsSwap f := by
  constructor <;> intro h
  · obtain ⟨x, t, hmem, hins, ht⟩ := card_eq_succ.1 h
    obtain ⟨y, rfl⟩ := card_eq_one.1 ht
    rw [mem_singleton] at hmem
    refine' ⟨x, y, hmem, _⟩
    ext a
    have key : ∀ b, f b ≠ b ↔ _ := fun b => by
      rw [← mem_support, ← hins, mem_insert, mem_singleton]
    by_cases' ha : f a = a
    · have ha' := not_or_distrib.mp (mt (key a).mpr (not_not.mpr ha))
      rw [ha, swap_apply_of_ne_of_ne ha'.1 ha'.2]
      
    · have ha' := (key (f a)).mp (mt f.apply_eq_iff_eq.mp ha)
      obtain rfl | rfl := (key a).mp ha
      · rw [Or.resolve_left ha' ha, swap_apply_left]
        
      · rw [Or.resolve_right ha' ha, swap_apply_right]
        
      
    
  · obtain ⟨x, y, hxy, rfl⟩ := h
    exact card_support_swap hxy
    

theorem Disjoint.card_support_mul (h : Disjoint f g) : (f * g).support.card = f.support.card + g.support.card := by
  rw [← Finset.card_disjoint_union]
  · congr
    ext
    simp [← h.support_mul]
    
  · simpa using h.disjoint_support
    

theorem card_support_prod_list_of_pairwise_disjoint {l : List (Perm α)} (h : l.Pairwise Disjoint) :
    l.Prod.support.card = (l.map (Finset.card ∘ support)).Sum := by
  induction' l with a t ih
  · exact card_support_eq_zero.mpr rfl
    
  · obtain ⟨ha, ht⟩ := List.pairwise_cons.1 h
    rw [List.prod_cons, List.map_cons, List.sum_cons, ← ih ht]
    exact (disjoint_prod_right _ ha).card_support_mul
    

end Card

end Support

end Equivₓ.Perm

