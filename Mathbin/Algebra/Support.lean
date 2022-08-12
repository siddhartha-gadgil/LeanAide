/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Order.ConditionallyCompleteLattice
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Group.Pi
import Mathbin.Algebra.Module.Pi

/-!
# Support of a function

In this file we define `function.support f = {x | f x ≠ 0}` and prove its basic properties.
We also define `function.mul_support f = {x | f x ≠ 1}`.
-/


open Set

open BigOperators

namespace Function

variable {α β A B M N P R S G M₀ G₀ : Type _} {ι : Sort _}

section One

variable [One M] [One N] [One P]

/-- `support` of a function is the set of points `x` such that `f x ≠ 0`. -/
def Support [Zero A] (f : α → A) : Set α :=
  { x | f x ≠ 0 }

/-- `mul_support` of a function is the set of points `x` such that `f x ≠ 1`. -/
@[to_additive]
def MulSupport (f : α → M) : Set α :=
  { x | f x ≠ 1 }

@[to_additive]
theorem mul_support_eq_preimage (f : α → M) : MulSupport f = f ⁻¹' {1}ᶜ :=
  rfl

@[to_additive]
theorem nmem_mul_support {f : α → M} {x : α} : x ∉ MulSupport f ↔ f x = 1 :=
  not_not

@[to_additive]
theorem compl_mul_support {f : α → M} : MulSupport fᶜ = { x | f x = 1 } :=
  ext fun x => nmem_mul_support

@[simp, to_additive]
theorem mem_mul_support {f : α → M} {x : α} : x ∈ MulSupport f ↔ f x ≠ 1 :=
  Iff.rfl

@[simp, to_additive]
theorem mul_support_subset_iff {f : α → M} {s : Set α} : MulSupport f ⊆ s ↔ ∀ x, f x ≠ 1 → x ∈ s :=
  Iff.rfl

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » s)
@[to_additive]
theorem mul_support_subset_iff' {f : α → M} {s : Set α} : MulSupport f ⊆ s ↔ ∀ (x) (_ : x ∉ s), f x = 1 :=
  forall_congrₓ fun x => not_imp_comm

@[to_additive]
theorem mul_support_disjoint_iff {f : α → M} {s : Set α} : Disjoint (MulSupport f) s ↔ EqOn f 1 s := by
  simp_rw [← subset_compl_iff_disjoint_right, mul_support_subset_iff', not_mem_compl_iff, eq_on, Pi.one_apply]

@[to_additive]
theorem disjoint_mul_support_iff {f : α → M} {s : Set α} : Disjoint s (MulSupport f) ↔ EqOn f 1 s := by
  rw [Disjoint.comm, mul_support_disjoint_iff]

@[simp, to_additive]
theorem mul_support_eq_empty_iff {f : α → M} : MulSupport f = ∅ ↔ f = 1 := by
  simp_rw [← subset_empty_iff, mul_support_subset_iff', funext_iff]
  simp

@[simp, to_additive]
theorem mul_support_nonempty_iff {f : α → M} : (MulSupport f).Nonempty ↔ f ≠ 1 := by
  rw [← ne_empty_iff_nonempty, Ne.def, mul_support_eq_empty_iff]

@[to_additive]
theorem range_subset_insert_image_mul_support (f : α → M) : Range f ⊆ insert 1 (f '' MulSupport f) := by
  intro y hy
  rcases eq_or_ne y 1 with (rfl | h2y)
  · exact mem_insert _ _
    
  · obtain ⟨x, rfl⟩ := hy
    refine' mem_insert_of_mem _ ⟨x, h2y, rfl⟩
    

@[simp, to_additive]
theorem mul_support_one' : MulSupport (1 : α → M) = ∅ :=
  mul_support_eq_empty_iff.2 rfl

@[simp, to_additive]
theorem mul_support_one : (MulSupport fun x : α => (1 : M)) = ∅ :=
  mul_support_one'

@[to_additive]
theorem mul_support_const {c : M} (hc : c ≠ 1) : (MulSupport fun x : α => c) = Set.Univ := by
  ext x
  simp [← hc]

@[to_additive]
theorem mul_support_binop_subset (op : M → N → P) (op1 : op 1 1 = 1) (f : α → M) (g : α → N) :
    (MulSupport fun x => op (f x) (g x)) ⊆ MulSupport f ∪ MulSupport g := fun x hx =>
  Classical.by_cases
    (fun hf : f x = 1 =>
      Or.inr fun hg =>
        hx <| by
          simp only [← hf, ← hg, ← op1])
    Or.inl

@[to_additive]
theorem mul_support_sup [SemilatticeSup M] (f g : α → M) :
    (MulSupport fun x => f x⊔g x) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (·⊔·) sup_idem f g

@[to_additive]
theorem mul_support_inf [SemilatticeInf M] (f g : α → M) :
    (MulSupport fun x => f x⊓g x) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (·⊓·) inf_idem f g

@[to_additive]
theorem mul_support_max [LinearOrderₓ M] (f g : α → M) :
    (MulSupport fun x => max (f x) (g x)) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_sup f g

@[to_additive]
theorem mul_support_min [LinearOrderₓ M] (f g : α → M) :
    (MulSupport fun x => min (f x) (g x)) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_inf f g

@[to_additive]
theorem mul_support_supr [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (MulSupport fun x => ⨆ i, f i x) ⊆ ⋃ i, MulSupport (f i) := by
  rw [mul_support_subset_iff']
  simp only [← mem_Union, ← not_exists, ← nmem_mul_support]
  intro x hx
  simp only [← hx, ← csupr_const]

@[to_additive]
theorem mul_support_infi [ConditionallyCompleteLattice M] [Nonempty ι] (f : ι → α → M) :
    (MulSupport fun x => ⨅ i, f i x) ⊆ ⋃ i, MulSupport (f i) :=
  @mul_support_supr _ Mᵒᵈ ι ⟨(1 : M)⟩ _ _ f

@[to_additive]
theorem mul_support_comp_subset {g : M → N} (hg : g 1 = 1) (f : α → M) : MulSupport (g ∘ f) ⊆ MulSupport f := fun x =>
  mt fun h => by
    simp only [← (· ∘ ·), *]

@[to_additive]
theorem mul_support_subset_comp {g : M → N} (hg : ∀ {x}, g x = 1 → x = 1) (f : α → M) :
    MulSupport f ⊆ MulSupport (g ∘ f) := fun x => mt hg

@[to_additive]
theorem mul_support_comp_eq (g : M → N) (hg : ∀ {x}, g x = 1 ↔ x = 1) (f : α → M) : MulSupport (g ∘ f) = MulSupport f :=
  Set.ext fun x => not_congr hg

@[to_additive]
theorem mul_support_comp_eq_preimage (g : β → M) (f : α → β) : MulSupport (g ∘ f) = f ⁻¹' MulSupport g :=
  rfl

@[to_additive support_prod_mk]
theorem mul_support_prod_mk (f : α → M) (g : α → N) : (MulSupport fun x => (f x, g x)) = MulSupport f ∪ MulSupport g :=
  Set.ext fun x => by
    simp only [← mul_support, ← not_and_distrib, ← mem_union_eq, ← mem_set_of_eq, ← Prod.mk_eq_one, ← Ne.def]

@[to_additive support_prod_mk']
theorem mul_support_prod_mk' (f : α → M × N) :
    MulSupport f = (MulSupport fun x => (f x).1) ∪ MulSupport fun x => (f x).2 := by
  simp only [mul_support_prod_mk, ← Prod.mk.eta]

@[to_additive]
theorem mul_support_along_fiber_subset (f : α × β → M) (a : α) :
    (MulSupport fun b => f (a, b)) ⊆ (MulSupport f).Image Prod.snd := by
  tidy

@[simp, to_additive]
theorem mul_support_along_fiber_finite_of_finite (f : α × β → M) (a : α) (h : (MulSupport f).Finite) :
    (MulSupport fun b => f (a, b)).Finite :=
  (h.Image Prod.snd).Subset (mul_support_along_fiber_subset f a)

end One

@[to_additive]
theorem mul_support_mul [MulOneClassₓ M] (f g : α → M) :
    (MulSupport fun x => f x * g x) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (· * ·) (one_mulₓ _) f g

@[to_additive]
theorem mul_support_pow [Monoidₓ M] (f : α → M) (n : ℕ) : (MulSupport fun x => f x ^ n) ⊆ MulSupport f := by
  induction' n with n hfn
  · simpa only [← pow_zeroₓ, ← mul_support_one] using empty_subset _
    
  · simpa only [← pow_succₓ] using subset_trans (mul_support_mul f _) (union_subset (subset.refl _) hfn)
    

section DivisionMonoid

variable [DivisionMonoid G] (f g : α → G)

@[simp, to_additive]
theorem mul_support_inv : (MulSupport fun x => (f x)⁻¹) = MulSupport f :=
  ext fun _ => inv_ne_one

@[simp, to_additive]
theorem mul_support_inv' : MulSupport f⁻¹ = MulSupport f :=
  mul_support_inv f

@[to_additive]
theorem mul_support_mul_inv : (MulSupport fun x => f x * (g x)⁻¹) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (fun a b => a * b⁻¹)
    (by
      simp )
    f g

@[to_additive]
theorem mul_support_div : (MulSupport fun x => f x / g x) ⊆ MulSupport f ∪ MulSupport g :=
  mul_support_binop_subset (· / ·) one_div_one f g

end DivisionMonoid

@[simp]
theorem support_mul [MulZeroClassₓ R] [NoZeroDivisors R] (f g : α → R) :
    (Support fun x => f x * g x) = Support f ∩ Support g :=
  Set.ext fun x => by
    simp only [← mem_support, ← mul_ne_zero_iff, ← mem_inter_eq, ← not_or_distrib]

@[simp]
theorem support_mul_subset_left [MulZeroClassₓ R] (f g : α → R) : (Support fun x => f x * g x) ⊆ Support f :=
  fun x hfg hf =>
  hfg <| by
    simp only [← hf, ← zero_mul]

@[simp]
theorem support_mul_subset_right [MulZeroClassₓ R] (f g : α → R) : (Support fun x => f x * g x) ⊆ Support g :=
  fun x hfg hg =>
  hfg <| by
    simp only [← hg, ← mul_zero]

theorem support_smul_subset_right [AddMonoidₓ A] [Monoidₓ B] [DistribMulAction B A] (b : B) (f : α → A) :
    Support (b • f) ⊆ Support f := fun x hbf hf =>
  hbf <| by
    rw [Pi.smul_apply, hf, smul_zero]

theorem support_smul_subset_left [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (f : α → R) (g : α → M) :
    Support (f • g) ⊆ Support f := fun x hfg hf =>
  hfg <| by
    rw [Pi.smul_apply', hf, zero_smul]

theorem support_smul [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [NoZeroSmulDivisors R M] (f : α → R) (g : α → M) :
    Support (f • g) = Support f ∩ Support g :=
  ext fun x => smul_ne_zero

theorem support_const_smul_of_ne_zero [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [NoZeroSmulDivisors R M] (c : R)
    (g : α → M) (hc : c ≠ 0) : Support (c • g) = Support g :=
  ext fun x => by
    simp only [← hc, ← mem_support, ← Pi.smul_apply, ← Ne.def, ← smul_eq_zero, ← false_orₓ]

@[simp]
theorem support_inv [GroupWithZeroₓ G₀] (f : α → G₀) : (Support fun x => (f x)⁻¹) = Support f :=
  Set.ext fun x => not_congr inv_eq_zero

@[simp]
theorem support_div [GroupWithZeroₓ G₀] (f g : α → G₀) : (Support fun x => f x / g x) = Support f ∩ Support g := by
  simp [← div_eq_mul_inv]

@[to_additive]
theorem mul_support_prod [CommMonoidₓ M] (s : Finset α) (f : α → β → M) :
    (MulSupport fun x => ∏ i in s, f i x) ⊆ ⋃ i ∈ s, MulSupport (f i) := by
  rw [mul_support_subset_iff']
  simp only [← mem_Union, ← not_exists, ← nmem_mul_support]
  exact fun x => Finset.prod_eq_one

theorem support_prod_subset [CommMonoidWithZero A] (s : Finset α) (f : α → β → A) :
    (Support fun x => ∏ i in s, f i x) ⊆ ⋂ i ∈ s, Support (f i) := fun x hx =>
  mem_Inter₂.2 fun i hi H => hx <| Finset.prod_eq_zero hi H

theorem support_prod [CommMonoidWithZero A] [NoZeroDivisors A] [Nontrivial A] (s : Finset α) (f : α → β → A) :
    (Support fun x => ∏ i in s, f i x) = ⋂ i ∈ s, Support (f i) :=
  Set.ext fun x => by
    simp only [← support, ← Ne.def, ← Finset.prod_eq_zero_iff, ← mem_set_of_eq, ← Set.mem_Inter, ← not_exists]

theorem mul_support_one_add [One R] [AddLeftCancelMonoid R] (f : α → R) : (MulSupport fun x => 1 + f x) = Support f :=
  Set.ext fun x => not_congr add_right_eq_selfₓ

theorem mul_support_one_add' [One R] [AddLeftCancelMonoid R] (f : α → R) : MulSupport (1 + f) = Support f :=
  mul_support_one_add f

theorem mul_support_add_one [One R] [AddRightCancelMonoid R] (f : α → R) : (MulSupport fun x => f x + 1) = Support f :=
  Set.ext fun x => not_congr add_left_eq_self

theorem mul_support_add_one' [One R] [AddRightCancelMonoid R] (f : α → R) : MulSupport (f + 1) = Support f :=
  mul_support_add_one f

theorem mul_support_one_sub' [One R] [AddGroupₓ R] (f : α → R) : MulSupport (1 - f) = Support f := by
  rw [sub_eq_add_neg, mul_support_one_add', support_neg']

theorem mul_support_one_sub [One R] [AddGroupₓ R] (f : α → R) : (MulSupport fun x => 1 - f x) = Support f :=
  mul_support_one_sub' f

end Function

namespace Set

open Function

variable {α β M : Type _} [One M] {f : α → M}

@[to_additive]
theorem image_inter_mul_support_eq {s : Set β} {g : β → α} : g '' s ∩ MulSupport f = g '' (s ∩ MulSupport (f ∘ g)) := by
  rw [mul_support_comp_eq_preimage f g, image_inter_preimage]

end Set

namespace Pi

variable {A : Type _} {B : Type _} [DecidableEq A] [Zero B] {a : A} {b : B}

theorem support_single_zero : Function.Support (Pi.single a (0 : B)) = ∅ := by
  simp

@[simp]
theorem support_single_of_ne (h : b ≠ 0) : Function.Support (Pi.single a b) = {a} := by
  ext
  simp only [← mem_singleton_iff, ← Ne.def, ← Function.mem_support]
  constructor
  · contrapose!
    exact fun h' => single_eq_of_ne h' b
    
  · rintro rfl
    rw [single_eq_same]
    exact h
    

theorem support_single [DecidableEq B] : Function.Support (Pi.single a b) = if b = 0 then ∅ else {a} := by
  split_ifs with h <;> simp [← h]

theorem support_single_subset : Function.Support (Pi.single a b) ⊆ {a} := by
  classical
  rw [support_single]
  split_ifs <;> simp

theorem support_single_disjoint {b' : B} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : A} :
    Disjoint (Function.Support (single i b)) (Function.Support (single j b')) ↔ i ≠ j := by
  rw [support_single_of_ne hb, support_single_of_ne hb', disjoint_singleton]

end Pi

