/-
Copyright (c) 2020 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou
-/
import Mathbin.Algebra.Support

/-!
# Indicator function

- `indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `0` otherwise.
- `mul_indicator (s : set α) (f : α → β) (a : α)` is `f a` if `a ∈ s` and is `1` otherwise.


## Implementation note

In mathematics, an indicator function or a characteristic function is a function
used to indicate membership of an element in a set `s`,
having the value `1` for all elements of `s` and the value `0` otherwise.
But since it is usually used to restrict a function to a certain set `s`,
we let the indicator function take the value `f x` for some function `f`, instead of `1`.
If the usual indicator function is needed, just set `f` to be the constant function `λx, 1`.

The indicator function is implemented non-computably, to avoid having to pass around `decidable`
arguments. This is in contrast with the design of `pi.single` or `set.piecewise`.

## Tags
indicator, characteristic
-/


open BigOperators

open Function

variable {α β ι M N : Type _}

namespace Set

section One

variable [One M] [One N] {s t : Set α} {f g : α → M} {a : α}

/-- `indicator s f a` is `f a` if `a ∈ s`, `0` otherwise.  -/
noncomputable def indicatorₓ {M} [Zero M] (s : Set α) (f : α → M) : α → M
  | x =>
    have := Classical.decPred (· ∈ s)
    if x ∈ s then f x else 0

/-- `mul_indicator s f a` is `f a` if `a ∈ s`, `1` otherwise.  -/
@[to_additive]
noncomputable def mulIndicator (s : Set α) (f : α → M) : α → M
  | x =>
    have := Classical.decPred (· ∈ s)
    if x ∈ s then f x else 1

@[simp, to_additive]
theorem piecewise_eq_mul_indicator [DecidablePred (· ∈ s)] : s.piecewise f 1 = s.mulIndicator f :=
  funext fun x => @if_congr _ _ _ _ (id _) _ _ _ _ Iff.rfl rfl rfl

@[to_additive]
theorem mul_indicator_apply (s : Set α) (f : α → M) (a : α) [Decidable (a ∈ s)] :
    mulIndicator s f a = if a ∈ s then f a else 1 := by
  convert rfl

@[simp, to_additive]
theorem mul_indicator_of_mem (h : a ∈ s) (f : α → M) : mulIndicator s f a = f a := by
  let this := Classical.dec (a ∈ s)
  exact if_pos h

@[simp, to_additive]
theorem mul_indicator_of_not_mem (h : a ∉ s) (f : α → M) : mulIndicator s f a = 1 := by
  let this := Classical.dec (a ∈ s)
  exact if_neg h

@[to_additive]
theorem mul_indicator_eq_one_or_self (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a = 1 ∨ mulIndicator s f a = f a := by
  by_cases' h : a ∈ s
  · exact Or.inr (mul_indicator_of_mem h f)
    
  · exact Or.inl (mul_indicator_of_not_mem h f)
    

@[simp, to_additive]
theorem mul_indicator_apply_eq_self : s.mulIndicator f a = f a ↔ a ∉ s → f a = 1 := by
  let this := Classical.dec (a ∈ s) <;>
    exact
      ite_eq_left_iff.trans
        (by
          rw [@eq_comm _ (f a)])

@[simp, to_additive]
theorem mul_indicator_eq_self : s.mulIndicator f = f ↔ MulSupport f ⊆ s := by
  simp only [← funext_iff, ← subset_def, ← mem_mul_support, ← mul_indicator_apply_eq_self, ← not_imp_comm]

@[to_additive]
theorem mul_indicator_eq_self_of_superset (h1 : s.mulIndicator f = f) (h2 : s ⊆ t) : t.mulIndicator f = f := by
  rw [mul_indicator_eq_self] at h1⊢
  exact subset.trans h1 h2

@[simp, to_additive]
theorem mul_indicator_apply_eq_one : mulIndicator s f a = 1 ↔ a ∈ s → f a = 1 := by
  let this := Classical.dec (a ∈ s) <;> exact ite_eq_right_iff

@[simp, to_additive]
theorem mul_indicator_eq_one : (mulIndicator s f = fun x => 1) ↔ Disjoint (MulSupport f) s := by
  simp only [← funext_iff, ← mul_indicator_apply_eq_one, ← Set.disjoint_left, ← mem_mul_support, ← not_imp_not]

@[simp, to_additive]
theorem mul_indicator_eq_one' : mulIndicator s f = 1 ↔ Disjoint (MulSupport f) s :=
  mul_indicator_eq_one

@[to_additive]
theorem mul_indicator_apply_ne_one {a : α} : s.mulIndicator f a ≠ 1 ↔ a ∈ s ∩ MulSupport f := by
  simp only [← Ne.def, ← mul_indicator_apply_eq_one, ← not_imp, ← mem_inter_eq, ← mem_mul_support]

@[simp, to_additive]
theorem mul_support_mul_indicator : Function.MulSupport (s.mulIndicator f) = s ∩ Function.MulSupport f :=
  ext fun x => by
    simp [← Function.mem_mul_support, ← mul_indicator_apply_eq_one]

/-- If a multiplicative indicator function is not equal to `1` at a point, then that point is in the
set. -/
@[to_additive "If an additive indicator function is not equal to `0` at a point, then that point is\nin the set."]
theorem mem_of_mul_indicator_ne_one (h : mulIndicator s f a ≠ 1) : a ∈ s :=
  not_imp_comm.1 (fun hn => mul_indicator_of_not_mem hn f) h

@[to_additive]
theorem eq_on_mul_indicator : EqOn (mulIndicator s f) f s := fun x hx => mul_indicator_of_mem hx f

@[to_additive]
theorem mul_support_mul_indicator_subset : MulSupport (s.mulIndicator f) ⊆ s := fun x hx =>
  hx.imp_symm fun h => mul_indicator_of_not_mem h f

@[simp, to_additive]
theorem mul_indicator_mul_support : mulIndicator (MulSupport f) f = f :=
  mul_indicator_eq_self.2 Subset.rfl

@[simp, to_additive]
theorem mul_indicator_range_comp {ι : Sort _} (f : ι → α) (g : α → M) : mulIndicator (Range f) g ∘ f = g ∘ f := by
  let this := Classical.decPred (· ∈ range f) <;> exact piecewise_range_comp _ _ _

@[to_additive]
theorem mul_indicator_congr (h : EqOn f g s) : mulIndicator s f = mulIndicator s g :=
  funext fun x => by
    simp only [← mul_indicator]
    split_ifs
    · exact h h_1
      
    rfl

@[simp, to_additive]
theorem mul_indicator_univ (f : α → M) : mulIndicator (Univ : Set α) f = f :=
  mul_indicator_eq_self.2 <| subset_univ _

@[simp, to_additive]
theorem mul_indicator_empty (f : α → M) : mulIndicator (∅ : Set α) f = fun a => 1 :=
  mul_indicator_eq_one.2 <| disjoint_empty _

@[to_additive]
theorem mul_indicator_empty' (f : α → M) : mulIndicator (∅ : Set α) f = 1 :=
  mul_indicator_empty f

variable (M)

@[simp, to_additive]
theorem mul_indicator_one (s : Set α) : (mulIndicator s fun x => (1 : M)) = fun x => (1 : M) :=
  mul_indicator_eq_one.2 <| by
    simp only [← mul_support_one, ← empty_disjoint]

@[simp, to_additive]
theorem mul_indicator_one' {s : Set α} : s.mulIndicator (1 : α → M) = 1 :=
  mul_indicator_one M s

variable {M}

@[to_additive]
theorem mul_indicator_mul_indicator (s t : Set α) (f : α → M) :
    mulIndicator s (mulIndicator t f) = mulIndicator (s ∩ t) f :=
  funext fun x => by
    simp only [← mul_indicator]
    split_ifs
    repeat'
      simp_all (config := { contextual := true })

@[simp, to_additive]
theorem mul_indicator_inter_mul_support (s : Set α) (f : α → M) :
    mulIndicator (s ∩ MulSupport f) f = mulIndicator s f := by
  rw [← mul_indicator_mul_indicator, mul_indicator_mul_support]

@[to_additive]
theorem comp_mul_indicator (h : M → β) (f : α → M) {s : Set α} {x : α} [DecidablePred (· ∈ s)] :
    h (s.mulIndicator f x) = s.piecewise (h ∘ f) (const α (h 1)) x := by
  let this := Classical.decPred (· ∈ s) <;> convert s.apply_piecewise f (const α 1) fun _ => h

@[to_additive]
theorem mul_indicator_comp_right {s : Set α} (f : β → α) {g : α → M} {x : β} :
    mulIndicator (f ⁻¹' s) (g ∘ f) x = mulIndicator s g (f x) := by
  simp only [← mul_indicator]
  split_ifs <;> rfl

@[to_additive]
theorem mul_indicator_image {s : Set α} {f : β → M} {g : α → β} (hg : Injective g) {x : α} :
    mulIndicator (g '' s) f (g x) = mulIndicator s (f ∘ g) x := by
  rw [← mul_indicator_comp_right, preimage_image_eq _ hg]

@[to_additive]
theorem mul_indicator_comp_of_one {g : M → N} (hg : g 1 = 1) : mulIndicator s (g ∘ f) = g ∘ mulIndicator s f := by
  funext
  simp only [← mul_indicator]
  split_ifs <;> simp [*]

@[to_additive]
theorem comp_mul_indicator_const (c : M) (f : M → N) (hf : f 1 = 1) :
    (fun x => f (s.mulIndicator (fun x => c) x)) = s.mulIndicator fun x => f c :=
  (mul_indicator_comp_of_one hf).symm

@[to_additive]
theorem mul_indicator_preimage (s : Set α) (f : α → M) (B : Set M) :
    mulIndicator s f ⁻¹' B = s.ite (f ⁻¹' B) (1 ⁻¹' B) := by
  let this := Classical.decPred (· ∈ s) <;> exact piecewise_preimage s f 1 B

@[to_additive]
theorem mul_indicator_preimage_of_not_mem (s : Set α) (f : α → M) {t : Set M} (ht : (1 : M) ∉ t) :
    mulIndicator s f ⁻¹' t = f ⁻¹' t ∩ s := by
  simp [← mul_indicator_preimage, ← Pi.one_def, ← Set.preimage_const_of_not_mem ht]

@[to_additive]
theorem mem_range_mul_indicator {r : M} {s : Set α} {f : α → M} :
    r ∈ Range (mulIndicator s f) ↔ r = 1 ∧ s ≠ univ ∨ r ∈ f '' s := by
  simp [← mul_indicator, ← ite_eq_iff, ← exists_or_distrib, ← eq_univ_iff_forall, ← and_comm, ← or_comm, ←
    @eq_comm _ r 1]

@[to_additive]
theorem mul_indicator_rel_mul_indicator {r : M → M → Prop} (h1 : r 1 1) (ha : a ∈ s → r (f a) (g a)) :
    r (mulIndicator s f a) (mulIndicator s g a) := by
  simp only [← mul_indicator]
  split_ifs with has has
  exacts[ha has, h1]

end One

section Monoidₓ

variable [MulOneClassₓ M] {s t : Set α} {f g : α → M} {a : α}

@[to_additive]
theorem mul_indicator_union_mul_inter_apply (f : α → M) (s t : Set α) (a : α) :
    mulIndicator (s ∪ t) f a * mulIndicator (s ∩ t) f a = mulIndicator s f a * mulIndicator t f a := by
  by_cases' hs : a ∈ s <;> by_cases' ht : a ∈ t <;> simp [*]

@[to_additive]
theorem mul_indicator_union_mul_inter (f : α → M) (s t : Set α) :
    mulIndicator (s ∪ t) f * mulIndicator (s ∩ t) f = mulIndicator s f * mulIndicator t f :=
  funext <| mul_indicator_union_mul_inter_apply f s t

@[to_additive]
theorem mul_indicator_union_of_not_mem_inter (h : a ∉ s ∩ t) (f : α → M) :
    mulIndicator (s ∪ t) f a = mulIndicator s f a * mulIndicator t f a := by
  rw [← mul_indicator_union_mul_inter_apply f s t, mul_indicator_of_not_mem h, mul_oneₓ]

@[to_additive]
theorem mul_indicator_union_of_disjoint (h : Disjoint s t) (f : α → M) :
    mulIndicator (s ∪ t) f = fun a => mulIndicator s f a * mulIndicator t f a :=
  funext fun a => mul_indicator_union_of_not_mem_inter (fun ha => h ha) _

@[to_additive]
theorem mul_indicator_mul (s : Set α) (f g : α → M) :
    (mulIndicator s fun a => f a * g a) = fun a => mulIndicator s f a * mulIndicator s g a := by
  funext
  simp only [← mul_indicator]
  split_ifs
  · rfl
    
  rw [mul_oneₓ]

@[to_additive]
theorem mul_indicator_mul' (s : Set α) (f g : α → M) : mulIndicator s (f * g) = mulIndicator s f * mulIndicator s g :=
  mul_indicator_mul s f g

@[simp, to_additive]
theorem mul_indicator_compl_mul_self_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator (sᶜ) f a * mulIndicator s f a = f a :=
  Classical.by_cases
    (fun ha : a ∈ s => by
      simp [← ha])
    fun ha => by
    simp [← ha]

@[simp, to_additive]
theorem mul_indicator_compl_mul_self (s : Set α) (f : α → M) : mulIndicator (sᶜ) f * mulIndicator s f = f :=
  funext <| mul_indicator_compl_mul_self_apply s f

@[simp, to_additive]
theorem mul_indicator_self_mul_compl_apply (s : Set α) (f : α → M) (a : α) :
    mulIndicator s f a * mulIndicator (sᶜ) f a = f a :=
  Classical.by_cases
    (fun ha : a ∈ s => by
      simp [← ha])
    fun ha => by
    simp [← ha]

@[simp, to_additive]
theorem mul_indicator_self_mul_compl (s : Set α) (f : α → M) : mulIndicator s f * mulIndicator (sᶜ) f = f :=
  funext <| mul_indicator_self_mul_compl_apply s f

@[to_additive]
theorem mul_indicator_mul_eq_left {f g : α → M} (h : Disjoint (MulSupport f) (MulSupport g)) :
    (MulSupport f).mulIndicator (f * g) = f := by
  refine' (mul_indicator_congr fun x hx => _).trans mul_indicator_mul_support
  have : g x = 1 := nmem_mul_support.1 (disjoint_left.1 h hx)
  rw [Pi.mul_apply, this, mul_oneₓ]

@[to_additive]
theorem mul_indicator_mul_eq_right {f g : α → M} (h : Disjoint (MulSupport f) (MulSupport g)) :
    (MulSupport g).mulIndicator (f * g) = g := by
  refine' (mul_indicator_congr fun x hx => _).trans mul_indicator_mul_support
  have : f x = 1 := nmem_mul_support.1 (disjoint_right.1 h hx)
  rw [Pi.mul_apply, this, one_mulₓ]

@[to_additive]
theorem mul_indicator_mul_compl_eq_piecewise [DecidablePred (· ∈ s)] (f g : α → M) :
    s.mulIndicator f * sᶜ.mulIndicator g = s.piecewise f g := by
  ext x
  by_cases' h : x ∈ s
  · rw [piecewise_eq_of_mem _ _ _ h, Pi.mul_apply, Set.mul_indicator_of_mem h,
      Set.mul_indicator_of_not_mem (Set.not_mem_compl_iff.2 h), mul_oneₓ]
    
  · rw [piecewise_eq_of_not_mem _ _ _ h, Pi.mul_apply, Set.mul_indicator_of_not_mem h,
      Set.mul_indicator_of_mem (Set.mem_compl h), one_mulₓ]
    

/-- `set.mul_indicator` as a `monoid_hom`. -/
@[to_additive "`set.indicator` as an `add_monoid_hom`."]
noncomputable def mulIndicatorHom {α} (M) [MulOneClassₓ M] (s : Set α) : (α → M) →* α → M where
  toFun := mulIndicator s
  map_one' := mul_indicator_one M s
  map_mul' := mul_indicator_mul s

end Monoidₓ

section DistribMulAction

variable {A : Type _} [AddMonoidₓ A] [Monoidₓ M] [DistribMulAction M A]

theorem indicator_smul_apply (s : Set α) (r : α → M) (f : α → A) (x : α) :
    indicatorₓ s (fun x => r x • f x) x = r x • indicatorₓ s f x := by
  dunfold indicator
  split_ifs
  exacts[rfl, (smul_zero (r x)).symm]

theorem indicator_smul (s : Set α) (r : α → M) (f : α → A) :
    (indicatorₓ s fun x : α => r x • f x) = fun x : α => r x • indicatorₓ s f x :=
  funext <| indicator_smul_apply s r f

theorem indicator_const_smul_apply (s : Set α) (r : M) (f : α → A) (x : α) :
    indicatorₓ s (fun x => r • f x) x = r • indicatorₓ s f x :=
  indicator_smul_apply s (fun x => r) f x

theorem indicator_const_smul (s : Set α) (r : M) (f : α → A) :
    (indicatorₓ s fun x : α => r • f x) = fun x : α => r • indicatorₓ s f x :=
  funext <| indicator_const_smul_apply s r f

end DistribMulAction

section Groupₓ

variable {G : Type _} [Groupₓ G] {s t : Set α} {f g : α → G} {a : α}

@[to_additive]
theorem mul_indicator_inv' (s : Set α) (f : α → G) : mulIndicator s f⁻¹ = (mulIndicator s f)⁻¹ :=
  (mulIndicatorHom G s).map_inv f

@[to_additive]
theorem mul_indicator_inv (s : Set α) (f : α → G) :
    (mulIndicator s fun a => (f a)⁻¹) = fun a => (mulIndicator s f a)⁻¹ :=
  mul_indicator_inv' s f

@[to_additive]
theorem mul_indicator_div (s : Set α) (f g : α → G) :
    (mulIndicator s fun a => f a / g a) = fun a => mulIndicator s f a / mulIndicator s g a :=
  (mulIndicatorHom G s).map_div f g

@[to_additive]
theorem mul_indicator_div' (s : Set α) (f g : α → G) : mulIndicator s (f / g) = mulIndicator s f / mulIndicator s g :=
  mul_indicator_div s f g

@[to_additive indicator_compl']
theorem mul_indicator_compl (s : Set α) (f : α → G) : mulIndicator (sᶜ) f = f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <| s.mul_indicator_compl_mul_self f

theorem indicator_compl {G} [AddGroupₓ G] (s : Set α) (f : α → G) : indicatorₓ (sᶜ) f = f - indicatorₓ s f := by
  rw [sub_eq_add_neg, indicator_compl']

@[to_additive indicator_diff']
theorem mul_indicator_diff (h : s ⊆ t) (f : α → G) : mulIndicator (t \ s) f = mulIndicator t f * (mulIndicator s f)⁻¹ :=
  eq_mul_inv_of_mul_eq <| by
    rw [Pi.mul_def, ← mul_indicator_union_of_disjoint disjoint_diff.symm f, diff_union_self,
      union_eq_self_of_subset_right h]

theorem indicator_diff {G : Type _} [AddGroupₓ G] {s t : Set α} (h : s ⊆ t) (f : α → G) :
    indicatorₓ (t \ s) f = indicatorₓ t f - indicatorₓ s f := by
  rw [indicator_diff' h, sub_eq_add_neg]

end Groupₓ

section CommMonoidₓ

variable [CommMonoidₓ M]

/-- Consider a product of `g i (f i)` over a `finset`.  Suppose `g` is a
function such as `pow`, which maps a second argument of `1` to
`1`. Then if `f` is replaced by the corresponding multiplicative indicator
function, the `finset` may be replaced by a possibly larger `finset`
without changing the value of the sum. -/
@[to_additive]
theorem prod_mul_indicator_subset_of_eq_one [One N] (f : α → N) (g : α → N → M) {s t : Finset α} (h : s ⊆ t)
    (hg : ∀ a, g a 1 = 1) : (∏ i in s, g i (f i)) = ∏ i in t, g i (mulIndicator (↑s) f i) := by
  rw [← Finset.prod_subset h _]
  · apply Finset.prod_congr rfl
    intro i hi
    congr
    symm
    exact mul_indicator_of_mem hi _
    
  · refine' fun i hi hn => _
    convert hg i
    exact mul_indicator_of_not_mem hn _
    

/-- Consider a sum of `g i (f i)` over a `finset`. Suppose `g` is a
function such as multiplication, which maps a second argument of 0 to
0.  (A typical use case would be a weighted sum of `f i * h i` or `f i
• h i`, where `f` gives the weights that are multiplied by some other
function `h`.)  Then if `f` is replaced by the corresponding indicator
function, the `finset` may be replaced by a possibly larger `finset`
without changing the value of the sum. -/
add_decl_doc Set.sum_indicator_subset_of_eq_zero

/-- Taking the product of an indicator function over a possibly larger `finset` is the same as
taking the original function over the original `finset`. -/
@[to_additive
      "Summing an indicator function over a possibly larger `finset` is the same as summing\nthe original function over the original `finset`."]
theorem prod_mul_indicator_subset (f : α → M) {s t : Finset α} (h : s ⊆ t) :
    (∏ i in s, f i) = ∏ i in t, mulIndicator (↑s) f i :=
  prod_mul_indicator_subset_of_eq_one _ (fun a b => b) h fun _ => rfl

@[to_additive]
theorem _root_.finset.prod_mul_indicator_eq_prod_filter (s : Finset ι) (f : ι → α → M) (t : ι → Set α) (g : ι → α)
    [DecidablePred fun i => g i ∈ t i] :
    (∏ i in s, mulIndicator (t i) (f i) (g i)) = ∏ i in s.filter fun i => g i ∈ t i, f i (g i) := by
  refine' (Finset.prod_filter_mul_prod_filter_not s (fun i => g i ∈ t i) _).symm.trans _
  refine' Eq.trans _ (mul_oneₓ _)
  exact
    congr_arg2ₓ (· * ·) ((Finset.prod_congr rfl) fun x hx => mul_indicator_of_mem (Finset.mem_filter.1 hx).2 _)
      (Finset.prod_eq_one fun x hx => mul_indicator_of_not_mem (Finset.mem_filter.1 hx).2 _)

@[to_additive]
theorem mul_indicator_finset_prod (I : Finset ι) (s : Set α) (f : ι → α → M) :
    mulIndicator s (∏ i in I, f i) = ∏ i in I, mulIndicator s (f i) :=
  (mulIndicatorHom M s).map_prod _ _

@[to_additive]
theorem mul_indicator_finset_bUnion {ι} (I : Finset ι) (s : ι → Set α) {f : α → M} :
    (∀, ∀ i ∈ I, ∀, ∀ j ∈ I, ∀, i ≠ j → Disjoint (s i) (s j)) →
      mulIndicator (⋃ i ∈ I, s i) f = fun a => ∏ i in I, mulIndicator (s i) f a :=
  by
  classical
  refine' Finset.induction_on I _ _
  · intro h
    funext
    simp
    
  intro a I haI ih hI
  funext
  rw [Finset.prod_insert haI, Finset.set_bUnion_insert, mul_indicator_union_of_not_mem_inter, ih _]
  · intro i hi j hj hij
    exact hI i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
    
  simp only [← not_exists, ← exists_prop, ← mem_Union, ← mem_inter_eq, ← not_and]
  intro hx a' ha'
  refine' disjoint_left.1 (hI a (Finset.mem_insert_self _ _) a' (Finset.mem_insert_of_mem ha') _) hx
  exact (ne_of_mem_of_not_mem ha' haI).symm

@[to_additive]
theorem mul_indicator_finset_bUnion_apply {ι} (I : Finset ι) (s : ι → Set α) {f : α → M}
    (h : ∀, ∀ i ∈ I, ∀, ∀ j ∈ I, ∀, i ≠ j → Disjoint (s i) (s j)) (x : α) :
    mulIndicator (⋃ i ∈ I, s i) f x = ∏ i in I, mulIndicator (s i) f x := by
  rw [Set.mul_indicator_finset_bUnion I s h]

end CommMonoidₓ

section MulZeroClassₓ

variable [MulZeroClassₓ M] {s t : Set α} {f g : α → M} {a : α}

theorem indicator_mul (s : Set α) (f g : α → M) :
    (indicatorₓ s fun a => f a * g a) = fun a => indicatorₓ s f a * indicatorₓ s g a := by
  funext
  simp only [← indicator]
  split_ifs
  · rfl
    
  rw [mul_zero]

theorem indicator_mul_left (s : Set α) (f g : α → M) : indicatorₓ s (fun a => f a * g a) a = indicatorₓ s f a * g a :=
  by
  simp only [← indicator]
  split_ifs
  · rfl
    
  rw [zero_mul]

theorem indicator_mul_right (s : Set α) (f g : α → M) : indicatorₓ s (fun a => f a * g a) a = f a * indicatorₓ s g a :=
  by
  simp only [← indicator]
  split_ifs
  · rfl
    
  rw [mul_zero]

theorem inter_indicator_mul {t1 t2 : Set α} (f g : α → M) (x : α) :
    (t1 ∩ t2).indicator (fun x => f x * g x) x = t1.indicator f x * t2.indicator g x := by
  rw [← Set.indicator_indicator]
  simp [← indicator]

end MulZeroClassₓ

section MulZeroOneClassₓ

variable [MulZeroOneClassₓ M]

theorem inter_indicator_one {s t : Set α} : (s ∩ t).indicator (1 : _ → M) = s.indicator 1 * t.indicator 1 :=
  funext fun _ => by
    simpa only [inter_indicator_mul, ← Pi.mul_apply, ← Pi.one_apply, ← one_mulₓ]

theorem indicator_prod_one {s : Set α} {t : Set β} {x : α} {y : β} :
    (s ×ˢ t : Set _).indicator (1 : _ → M) (x, y) = s.indicator 1 x * t.indicator 1 y := by
  let this := Classical.decPred (· ∈ s)
  let this := Classical.decPred (· ∈ t)
  simp [← indicator_apply, ite_and]

variable (M) [Nontrivial M]

theorem indicator_eq_zero_iff_not_mem {U : Set α} {x : α} : indicatorₓ U 1 x = (0 : M) ↔ x ∉ U := by
  classical
  simp [← indicator_apply, ← imp_false]

theorem indicator_eq_one_iff_mem {U : Set α} {x : α} : indicatorₓ U 1 x = (1 : M) ↔ x ∈ U := by
  classical
  simp [← indicator_apply, ← imp_false]

theorem indicator_one_inj {U V : Set α} (h : indicatorₓ U (1 : α → M) = indicatorₓ V 1) : U = V := by
  ext
  simp_rw [← indicator_eq_one_iff_mem M, h]

end MulZeroOneClassₓ

section Order

variable [One M] {s t : Set α} {f g : α → M} {a : α} {y : M}

section

variable [LE M]

@[to_additive]
theorem mul_indicator_apply_le' (hfg : a ∈ s → f a ≤ y) (hg : a ∉ s → 1 ≤ y) : mulIndicator s f a ≤ y := by
  by_cases' ha : a ∈ s
  · simpa [← ha] using hfg ha
    
  · simpa [← ha] using hg ha
    

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ∉ » s)
@[to_additive]
theorem mul_indicator_le' (hfg : ∀, ∀ a ∈ s, ∀, f a ≤ g a) (hg : ∀ (a) (_ : a ∉ s), 1 ≤ g a) : mulIndicator s f ≤ g :=
  fun a => mul_indicator_apply_le' (hfg _) (hg _)

@[to_additive]
theorem le_mul_indicator_apply {y} (hfg : a ∈ s → y ≤ g a) (hf : a ∉ s → y ≤ 1) : y ≤ mulIndicator s g a :=
  @mul_indicator_apply_le' α Mᵒᵈ ‹_› _ _ _ _ _ hfg hf

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ∉ » s)
@[to_additive]
theorem le_mul_indicator (hfg : ∀, ∀ a ∈ s, ∀, f a ≤ g a) (hf : ∀ (a) (_ : a ∉ s), f a ≤ 1) : f ≤ mulIndicator s g :=
  fun a => le_mul_indicator_apply (hfg _) (hf _)

end

variable [Preorderₓ M]

@[to_additive indicator_apply_nonneg]
theorem one_le_mul_indicator_apply (h : a ∈ s → 1 ≤ f a) : 1 ≤ mulIndicator s f a :=
  le_mul_indicator_apply h fun _ => le_rfl

@[to_additive indicator_nonneg]
theorem one_le_mul_indicator (h : ∀, ∀ a ∈ s, ∀, 1 ≤ f a) (a : α) : 1 ≤ mulIndicator s f a :=
  one_le_mul_indicator_apply (h a)

@[to_additive]
theorem mul_indicator_apply_le_one (h : a ∈ s → f a ≤ 1) : mulIndicator s f a ≤ 1 :=
  mul_indicator_apply_le' h fun _ => le_rfl

@[to_additive]
theorem mul_indicator_le_one (h : ∀, ∀ a ∈ s, ∀, f a ≤ 1) (a : α) : mulIndicator s f a ≤ 1 :=
  mul_indicator_apply_le_one (h a)

@[to_additive]
theorem mul_indicator_le_mul_indicator (h : f a ≤ g a) : mulIndicator s f a ≤ mulIndicator s g a :=
  mul_indicator_rel_mul_indicator le_rfl fun _ => h

attribute [mono] mul_indicator_le_mul_indicator indicator_le_indicator

@[to_additive]
theorem mul_indicator_le_mul_indicator_of_subset (h : s ⊆ t) (hf : ∀ a, 1 ≤ f a) (a : α) :
    mulIndicator s f a ≤ mulIndicator t f a :=
  mul_indicator_apply_le' (fun ha => le_mul_indicator_apply (fun _ => le_rfl) fun hat => (hat <| h ha).elim) fun ha =>
    one_le_mul_indicator_apply fun _ => hf _

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ∉ » s)
@[to_additive]
theorem mul_indicator_le_self' (hf : ∀ (x) (_ : x ∉ s), 1 ≤ f x) : mulIndicator s f ≤ f :=
  mul_indicator_le' (fun _ _ => le_rfl) hf

@[to_additive]
theorem mul_indicator_Union_apply {ι M} [CompleteLattice M] [One M] (h1 : (⊥ : M) = 1) (s : ι → Set α) (f : α → M)
    (x : α) : mulIndicator (⋃ i, s i) f x = ⨆ i, mulIndicator (s i) f x := by
  by_cases' hx : x ∈ ⋃ i, s i
  · rw [mul_indicator_of_mem hx]
    rw [mem_Union] at hx
    refine' le_antisymmₓ _ (supr_le fun i => mul_indicator_le_self' (fun x hx => h1 ▸ bot_le) x)
    rcases hx with ⟨i, hi⟩
    exact le_supr_of_le i (ge_of_eq <| mul_indicator_of_mem hi _)
    
  · rw [mul_indicator_of_not_mem hx]
    simp only [← mem_Union, ← not_exists] at hx
    simp [← hx, h1]
    

end Order

section CanonicallyOrderedMonoid

variable [CanonicallyOrderedMonoid M]

@[to_additive]
theorem mul_indicator_le_self (s : Set α) (f : α → M) : mulIndicator s f ≤ f :=
  mul_indicator_le_self' fun _ _ => one_le _

@[to_additive]
theorem mul_indicator_apply_le {a : α} {s : Set α} {f g : α → M} (hfg : a ∈ s → f a ≤ g a) : mulIndicator s f a ≤ g a :=
  (mul_indicator_apply_le' hfg) fun _ => one_le _

@[to_additive]
theorem mul_indicator_le {s : Set α} {f g : α → M} (hfg : ∀, ∀ a ∈ s, ∀, f a ≤ g a) : mulIndicator s f ≤ g :=
  (mul_indicator_le' hfg) fun _ _ => one_le _

end CanonicallyOrderedMonoid

theorem indicator_le_indicator_nonneg {β} [LinearOrderₓ β] [Zero β] (s : Set α) (f : α → β) :
    s.indicator f ≤ { x | 0 ≤ f x }.indicator f := by
  intro x
  classical
  simp_rw [indicator_apply]
  split_ifs
  · exact le_rfl
    
  · exact (not_le.mp h_1).le
    
  · exact h_1
    
  · exact le_rfl
    

theorem indicator_nonpos_le_indicator {β} [LinearOrderₓ β] [Zero β] (s : Set α) (f : α → β) :
    { x | f x ≤ 0 }.indicator f ≤ s.indicator f :=
  @indicator_le_indicator_nonneg α βᵒᵈ _ _ s f

end Set

@[to_additive]
theorem MonoidHom.map_mul_indicator {M N : Type _} [MulOneClassₓ M] [MulOneClassₓ N] (f : M →* N) (s : Set α)
    (g : α → M) (x : α) : f (s.mulIndicator g x) = s.mulIndicator (f ∘ g) x :=
  congr_fun (Set.mul_indicator_comp_of_one f.map_one).symm x

