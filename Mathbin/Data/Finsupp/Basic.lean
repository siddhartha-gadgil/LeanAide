/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Scott Morrison
-/
import Mathbin.Algebra.Hom.GroupAction
import Mathbin.Algebra.IndicatorFunction
import Mathbin.Data.Finset.Preimage

/-!
# Type of functions with finite support

For any type `α` and a type `M` with zero, we define the type `finsupp α M` (notation: `α →₀ M`)
of finitely supported functions from `α` to `M`, i.e. the functions which are zero everywhere
on `α` except on a finite set.

Functions with finite support are used (at least) in the following parts of the library:

* `monoid_algebra R M` and `add_monoid_algebra R M` are defined as `M →₀ R`;

* polynomials and multivariate polynomials are defined as `add_monoid_algebra`s, hence they use
  `finsupp` under the hood;

* the linear combination of a family of vectors `v i` with coefficients `f i` (as used, e.g., to
  define linearly independent family `linear_independent`) is defined as a map
  `finsupp.total : (ι → M) → (ι →₀ R) →ₗ[R] M`.

Some other constructions are naturally equivalent to `α →₀ M` with some `α` and `M` but are defined
in a different way in the library:

* `multiset α ≃+ α →₀ ℕ`;
* `free_abelian_group α ≃+ α →₀ ℤ`.

Most of the theory assumes that the range is a commutative additive monoid. This gives us the big
sum operator as a powerful way to construct `finsupp` elements.

Many constructions based on `α →₀ M` use `semireducible` type tags to avoid reusing unwanted type
instances. E.g., `monoid_algebra`, `add_monoid_algebra`, and types based on these two have
non-pointwise multiplication.

## Main declarations

* `finsupp`: The type of finitely supported functions from `α` to `β`.
* `finsupp.single`: The `finsupp` which is nonzero in exactly one point.
* `finsupp.update`: Changes one value of a `finsupp`.
* `finsupp.erase`: Replaces one value of a `finsupp` by `0`.
* `finsupp.on_finset`: The restriction of a function to a `finset` as a `finsupp`.
* `finsupp.map_range`: Composition of a `zero_hom` with a `finsupp`.
* `finsupp.emb_domain`: Maps the domain of a `finsupp` by an embedding.
* `finsupp.map_domain`: Maps the domain of a `finsupp` by a function and by summing.
* `finsupp.comap_domain`: Postcomposition of a `finsupp` with a function injective on the preimage
  of its support.
* `finsupp.zip_with`: Postcomposition of two `finsupp`s with a function `f` such that `f 0 0 = 0`.
* `finsupp.sum`: Sum of the values of a `finsupp`.
* `finsupp.prod`: Product of the nonzero values of a `finsupp`.

## Notations

This file adds `α →₀ M` as a global notation for `finsupp α M`.

We also use the following convention for `Type*` variables in this file

* `α`, `β`, `γ`: types with no additional structure that appear as the first argument to `finsupp`
  somewhere in the statement;

* `ι` : an auxiliary index type;

* `M`, `M'`, `N`, `P`: types with `has_zero` or `(add_)(comm_)monoid` structure; `M` is also used
  for a (semi)module over a (semi)ring.

* `G`, `H`: groups (commutative or not, multiplicative or additive);

* `R`, `S`: (semi)rings.

## Implementation notes

This file is a `noncomputable theory` and uses classical logic throughout.

## TODO

* This file is currently ~2.7K lines long, so it should be splitted into smaller chunks.
  One option would be to move all the sum and product stuff to `algebra.big_operators.finsupp` and
  move the definitions that depend on it to new files under `data.finsupp.`.

* Expand the list of definitions and important lemmas to the module docstring.

-/


noncomputable section

open Finset Function

open Classical BigOperators

variable {α β γ ι M M' N P G H R S : Type _}

/-- `finsupp α M`, denoted `α →₀ M`, is the type of functions `f : α → M` such that
  `f x = 0` for all but finitely many `x`. -/
structure Finsupp (α : Type _) (M : Type _) [Zero M] where
  Support : Finset α
  toFun : α → M
  mem_support_to_fun : ∀ a, a ∈ support ↔ to_fun a ≠ 0

-- mathport name: «expr →₀ »
infixr:25 " →₀ " => Finsupp

namespace Finsupp

/-! ### Basic declarations about `finsupp` -/


section Basic

variable [Zero M]

instance funLike : FunLike (α →₀ M) α fun _ => M :=
  ⟨toFun, by
    rintro ⟨s, f, hf⟩ ⟨t, g, hg⟩ (rfl : f = g)
    congr
    ext a
    exact (hf _).trans (hg _).symm⟩

/-- Helper instance for when there are too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →₀ M) fun _ => α → M :=
  FunLike.hasCoeToFun

@[ext]
theorem ext {f g : α →₀ M} (h : ∀ a, f a = g a) : f = g :=
  FunLike.ext _ _ h

/-- Deprecated. Use `fun_like.ext_iff` instead. -/
theorem ext_iff {f g : α →₀ M} : f = g ↔ ∀ a, f a = g a :=
  FunLike.ext_iff

/-- Deprecated. Use `fun_like.coe_fn_eq` instead. -/
theorem coe_fn_inj {f g : α →₀ M} : (f : α → M) = g ↔ f = g :=
  FunLike.coe_fn_eq

/-- Deprecated. Use `fun_like.coe_injective` instead. -/
theorem coe_fn_injective : @Function.Injective (α →₀ M) (α → M) coeFn :=
  FunLike.coe_injective

/-- Deprecated. Use `fun_like.congr_fun` instead. -/
theorem congr_fun {f g : α →₀ M} (h : f = g) (a : α) : f a = g a :=
  FunLike.congr_fun h _

@[simp]
theorem coe_mk (f : α → M) (s : Finset α) (h : ∀ a, a ∈ s ↔ f a ≠ 0) : ⇑(⟨s, f, h⟩ : α →₀ M) = f :=
  rfl

instance : Zero (α →₀ M) :=
  ⟨⟨∅, 0, fun _ => ⟨False.elim, fun H => H rfl⟩⟩⟩

@[simp]
theorem coe_zero : ⇑(0 : α →₀ M) = 0 :=
  rfl

theorem zero_apply {a : α} : (0 : α →₀ M) a = 0 :=
  rfl

@[simp]
theorem support_zero : (0 : α →₀ M).Support = ∅ :=
  rfl

instance : Inhabited (α →₀ M) :=
  ⟨0⟩

@[simp]
theorem mem_support_iff {f : α →₀ M} : ∀ {a : α}, a ∈ f.Support ↔ f a ≠ 0 :=
  f.mem_support_to_fun

@[simp, norm_cast]
theorem fun_support_eq (f : α →₀ M) : Function.Support f = f.Support :=
  Set.ext fun x => mem_support_iff.symm

theorem not_mem_support_iff {f : α →₀ M} {a} : a ∉ f.Support ↔ f a = 0 :=
  not_iff_comm.1 mem_support_iff.symm

@[simp, norm_cast]
theorem coe_eq_zero {f : α →₀ M} : (f : α → M) = 0 ↔ f = 0 := by
  rw [← coe_zero, coe_fn_inj]

theorem ext_iff' {f g : α →₀ M} : f = g ↔ f.Support = g.Support ∧ ∀, ∀ x ∈ f.Support, ∀, f x = g x :=
  ⟨fun h => h ▸ ⟨rfl, fun _ _ => rfl⟩, fun ⟨h₁, h₂⟩ =>
    ext fun a =>
      if h : a ∈ f.Support then h₂ a h
      else by
        have hf : f a = 0 := not_mem_support_iff.1 h
        have hg : g a = 0 := by
          rwa [h₁, not_mem_support_iff] at h
        rw [hf, hg]⟩

@[simp]
theorem support_eq_empty {f : α →₀ M} : f.Support = ∅ ↔ f = 0 := by
  exact_mod_cast @Function.support_eq_empty_iff _ _ _ f

theorem support_nonempty_iff {f : α →₀ M} : f.Support.Nonempty ↔ f ≠ 0 := by
  simp only [← Finsupp.support_eq_empty, ← Finset.nonempty_iff_ne_empty, ← Ne.def]

theorem nonzero_iff_exists {f : α →₀ M} : f ≠ 0 ↔ ∃ a : α, f a ≠ 0 := by
  simp [Finsupp.support_eq_empty, ← Finset.eq_empty_iff_forall_not_mem]

theorem card_support_eq_zero {f : α →₀ M} : card f.Support = 0 ↔ f = 0 := by
  simp

instance [DecidableEq α] [DecidableEq M] : DecidableEq (α →₀ M) := fun f g =>
  decidableOfIff (f.Support = g.Support ∧ ∀, ∀ a ∈ f.Support, ∀, f a = g a) ext_iff'.symm

theorem finite_support (f : α →₀ M) : Set.Finite (Function.Support f) :=
  f.fun_support_eq.symm ▸ f.Support.finite_to_set

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (a «expr ∉ » s)
theorem support_subset_iff {s : Set α} {f : α →₀ M} : ↑f.Support ⊆ s ↔ ∀ (a) (_ : a ∉ s), f a = 0 := by
  simp only [← Set.subset_def, ← mem_coe, ← mem_support_iff] <;> exact forall_congrₓ fun a => not_imp_comm

/-- Given `fintype α`, `equiv_fun_on_fintype` is the `equiv` between `α →₀ β` and `α → β`.
  (All functions on a finite type are finitely supported.) -/
@[simps]
def equivFunOnFintype [Fintype α] : (α →₀ M) ≃ (α → M) :=
  ⟨fun f a => f a, fun f =>
    mk (Finset.univ.filter fun a => f a ≠ 0) f
      (by
        simp only [← true_andₓ, ← Finset.mem_univ, ← iff_selfₓ, ← Finset.mem_filter, ← Finset.filter_congr_decidable, ←
          forall_true_iff]),
    by
    intro f
    ext a
    rfl, by
    intro f
    ext a
    rfl⟩

@[simp]
theorem equiv_fun_on_fintype_symm_coe {α} [Fintype α] (f : α →₀ M) : equivFunOnFintype.symm f = f := by
  ext
  simp [← equiv_fun_on_fintype]

/-- If `α` has a unique term,
then the type of finitely supported functions `α →₀ β` is equivalent to `β`. -/
@[simps]
noncomputable def _root_.equiv.finsupp_unique {ι : Type _} [Unique ι] : (ι →₀ M) ≃ M :=
  Finsupp.equivFunOnFintype.trans (Equivₓ.funUnique ι M)

end Basic

/-! ### Declarations about `single` -/


section Single

variable [Zero M] {a a' : α} {b : M}

/-- `single a b` is the finitely supported function which has
  value `b` at `a` and zero otherwise. -/
def single (a : α) (b : M) : α →₀ M :=
  ⟨if b = 0 then ∅ else {a}, fun a' => if a = a' then b else 0, fun a' => by
    by_cases' hb : b = 0 <;> by_cases' a = a' <;> simp only [← hb, ← h, ← if_pos, ← if_false, ← mem_singleton]
    · exact ⟨False.elim, fun H => H rfl⟩
      
    · exact ⟨False.elim, fun H => H rfl⟩
      
    · exact ⟨fun _ => hb, fun _ => rfl⟩
      
    · exact ⟨fun H _ => h H.symm, fun H => (H rfl).elim⟩
      ⟩

theorem single_apply [Decidable (a = a')] : single a b a' = if a = a' then b else 0 := by
  convert rfl

theorem single_eq_indicator : ⇑(single a b) = Set.indicatorₓ {a} fun _ => b := by
  ext
  simp [← single_apply, ← Set.indicatorₓ, ← @eq_comm _ a]

@[simp]
theorem single_eq_same : (single a b : α →₀ M) a = b :=
  if_pos rfl

@[simp]
theorem single_eq_of_ne (h : a ≠ a') : (single a b : α →₀ M) a' = 0 :=
  if_neg h

theorem single_eq_update [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Function.update 0 a b := by
  rw [single_eq_indicator, ← Set.piecewise_eq_indicator, Set.piecewise_singleton]

theorem single_eq_pi_single [DecidableEq α] (a : α) (b : M) : ⇑(single a b) = Pi.single a b :=
  single_eq_update a b

@[simp]
theorem single_zero (a : α) : (single a 0 : α →₀ M) = 0 :=
  coe_fn_injective <| by
    simpa only [← single_eq_update, ← coe_zero] using Function.update_eq_self a (0 : α → M)

theorem single_of_single_apply (a a' : α) (b : M) : single a ((single a' b) a) = single a' (single a' b) a := by
  rw [single_apply, single_apply]
  ext
  split_ifs
  · rw [h]
    
  · rw [zero_apply, single_apply, if_t_t]
    

theorem support_single_ne_zero (a : α) (hb : b ≠ 0) : (single a b).Support = {a} :=
  if_neg hb

theorem support_single_subset : (single a b).Support ⊆ {a} :=
  show ite _ _ _ ⊆ _ by
    split_ifs <;> [exact empty_subset _, exact subset.refl _]

theorem single_apply_mem (x) : single a b x ∈ ({0, b} : Set M) := by
  rcases em (a = x) with (rfl | hx) <;> [simp , simp [← single_eq_of_ne hx]]

theorem range_single_subset : Set.Range (single a b) ⊆ {0, b} :=
  Set.range_subset_iff.2 single_apply_mem

/-- `finsupp.single a b` is injective in `b`. For the statement that it is injective in `a`, see
`finsupp.single_left_injective` -/
theorem single_injective (a : α) : Function.Injective (single a : M → α →₀ M) := fun b₁ b₂ eq => by
  have : (single a b₁ : α →₀ M) a = (single a b₂ : α →₀ M) a := by
    rw [Eq]
  rwa [single_eq_same, single_eq_same] at this

theorem single_apply_eq_zero {a x : α} {b : M} : single a b x = 0 ↔ x = a → b = 0 := by
  simp [← single_eq_indicator]

theorem single_apply_ne_zero {a x : α} {b : M} : single a b x ≠ 0 ↔ x = a ∧ b ≠ 0 := by
  simp [← single_apply_eq_zero]

theorem mem_support_single (a a' : α) (b : M) : a ∈ (single a' b).Support ↔ a = a' ∧ b ≠ 0 := by
  simp [← single_apply_eq_zero, ← not_or_distrib]

theorem eq_single_iff {f : α →₀ M} {a b} : f = single a b ↔ f.Support ⊆ {a} ∧ f a = b := by
  refine' ⟨fun h => h.symm ▸ ⟨support_single_subset, single_eq_same⟩, _⟩
  rintro ⟨h, rfl⟩
  ext x
  by_cases' hx : a = x <;> simp only [← hx, ← single_eq_same, ← single_eq_of_ne, ← Ne.def, ← not_false_iff]
  exact not_mem_support_iff.1 (mt (fun hx => (mem_singleton.1 (h hx)).symm) hx)

theorem single_eq_single_iff (a₁ a₂ : α) (b₁ b₂ : M) :
    single a₁ b₁ = single a₂ b₂ ↔ a₁ = a₂ ∧ b₁ = b₂ ∨ b₁ = 0 ∧ b₂ = 0 := by
  constructor
  · intro eq
    by_cases' a₁ = a₂
    · refine' Or.inl ⟨h, _⟩
      rwa [h, (single_injective a₂).eq_iff] at eq
      
    · rw [ext_iff] at eq
      have h₁ := Eq a₁
      have h₂ := Eq a₂
      simp only [← single_eq_same, ← single_eq_of_ne h, ← single_eq_of_ne (Ne.symm h)] at h₁ h₂
      exact Or.inr ⟨h₁, h₂.symm⟩
      
    
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
      
    · rw [single_zero, single_zero]
      
    

/-- `finsupp.single a b` is injective in `a`. For the statement that it is injective in `b`, see
`finsupp.single_injective` -/
theorem single_left_injective (h : b ≠ 0) : Function.Injective fun a : α => single a b := fun a a' H =>
  (((single_eq_single_iff _ _ _ _).mp H).resolve_right fun hb => h hb.1).left

theorem single_left_inj (h : b ≠ 0) : single a b = single a' b ↔ a = a' :=
  (single_left_injective h).eq_iff

theorem support_single_ne_bot (i : α) (h : b ≠ 0) : (single i b).Support ≠ ⊥ := by
  simpa only [← support_single_ne_zero _ h] using singleton_ne_empty _

theorem support_single_disjoint [DecidableEq α] {b' : M} (hb : b ≠ 0) (hb' : b' ≠ 0) {i j : α} :
    Disjoint (single i b).Support (single j b').Support ↔ i ≠ j := by
  rw [support_single_ne_zero _ hb, support_single_ne_zero _ hb', disjoint_singleton]

@[simp]
theorem single_eq_zero : single a b = 0 ↔ b = 0 := by
  simp [← ext_iff, ← single_eq_indicator]

theorem single_swap (a₁ a₂ : α) (b : M) : single a₁ b a₂ = single a₂ b a₁ := by
  simp only [← single_apply] <;> ac_rfl

instance [Nonempty α] [Nontrivial M] : Nontrivial (α →₀ M) := by
  inhabit α
  rcases exists_ne (0 : M) with ⟨x, hx⟩
  exact nontrivial_of_ne (single default x) 0 (mt single_eq_zero.1 hx)

theorem unique_single [Unique α] (x : α →₀ M) : x = single default (x default) :=
  ext <| Unique.forall_iff.2 single_eq_same.symm

@[ext]
theorem unique_ext [Unique α] {f g : α →₀ M} (h : f default = g default) : f = g :=
  ext fun a => by
    rwa [Unique.eq_default a]

theorem unique_ext_iff [Unique α] {f g : α →₀ M} : f = g ↔ f default = g default :=
  ⟨fun h => h ▸ rfl, unique_ext⟩

@[simp]
theorem unique_single_eq_iff [Unique α] {b' : M} : single a b = single a' b' ↔ b = b' := by
  rw [unique_ext_iff, Unique.eq_default a, Unique.eq_default a', single_eq_same, single_eq_same]

theorem support_eq_singleton {f : α →₀ M} {a : α} : f.Support = {a} ↔ f a ≠ 0 ∧ f = single a (f a) :=
  ⟨fun h => ⟨mem_support_iff.1 <| h.symm ▸ Finset.mem_singleton_self a, eq_single_iff.2 ⟨subset_of_eq h, rfl⟩⟩, fun h =>
    h.2.symm ▸ support_single_ne_zero _ h.1⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ≠ » 0)
theorem support_eq_singleton' {f : α →₀ M} {a : α} : f.Support = {a} ↔ ∃ (b : _)(_ : b ≠ 0), f = single a b :=
  ⟨fun h =>
    let h := support_eq_singleton.1 h
    ⟨_, h.1, h.2⟩,
    fun ⟨b, hb, hf⟩ => hf.symm ▸ support_single_ne_zero _ hb⟩

theorem card_support_eq_one {f : α →₀ M} : card f.Support = 1 ↔ ∃ a, f a ≠ 0 ∧ f = single a (f a) := by
  simp only [← card_eq_one, ← support_eq_singleton]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (b «expr ≠ » 0)
theorem card_support_eq_one' {f : α →₀ M} : card f.Support = 1 ↔ ∃ (a : _)(b : _)(_ : b ≠ 0), f = single a b := by
  simp only [← card_eq_one, ← support_eq_singleton']

theorem support_subset_singleton {f : α →₀ M} {a : α} : f.Support ⊆ {a} ↔ f = single a (f a) :=
  ⟨fun h => eq_single_iff.mpr ⟨h, rfl⟩, fun h => (eq_single_iff.mp h).left⟩

theorem support_subset_singleton' {f : α →₀ M} {a : α} : f.Support ⊆ {a} ↔ ∃ b, f = single a b :=
  ⟨fun h => ⟨f a, support_subset_singleton.mp h⟩, fun ⟨b, hb⟩ => by
    rw [hb, support_subset_singleton, single_eq_same]⟩

theorem card_support_le_one [Nonempty α] {f : α →₀ M} : card f.Support ≤ 1 ↔ ∃ a, f = single a (f a) := by
  simp only [← card_le_one_iff_subset_singleton, ← support_subset_singleton]

theorem card_support_le_one' [Nonempty α] {f : α →₀ M} : card f.Support ≤ 1 ↔ ∃ a b, f = single a b := by
  simp only [← card_le_one_iff_subset_singleton, ← support_subset_singleton']

@[simp]
theorem equiv_fun_on_fintype_single [DecidableEq α] [Fintype α] (x : α) (m : M) :
    (@Finsupp.equivFunOnFintype α M _ _) (Finsupp.single x m) = Pi.single x m := by
  ext
  simp [← Finsupp.single_eq_pi_single, ← Finsupp.equivFunOnFintype]

@[simp]
theorem equiv_fun_on_fintype_symm_single [DecidableEq α] [Fintype α] (x : α) (m : M) :
    (@Finsupp.equivFunOnFintype α M _ _).symm (Pi.single x m) = Finsupp.single x m := by
  ext
  simp [← Finsupp.single_eq_pi_single, ← Finsupp.equivFunOnFintype]

end Single

/-! ### Declarations about `update` -/


section Update

variable [Zero M] (f : α →₀ M) (a : α) (b : M) (i : α)

/-- Replace the value of a `α →₀ M` at a given point `a : α` by a given value `b : M`.
If `b = 0`, this amounts to removing `a` from the `finsupp.support`.
Otherwise, if `a` was not in the `finsupp.support`, it is added to it.

This is the finitely-supported version of `function.update`. -/
def update : α →₀ M :=
  ⟨if b = 0 then f.Support.erase a else insert a f.Support, Function.update f a b, fun i => by
    simp only [← Function.update_apply, ← Ne.def]
    split_ifs with hb ha ha hb <;> simp [← ha, ← hb]⟩

@[simp]
theorem coe_update [DecidableEq α] : (f.update a b : α → M) = Function.update f a b := by
  convert rfl

@[simp]
theorem update_self : f.update a (f a) = f := by
  ext
  simp

theorem support_update [DecidableEq α] :
    support (f.update a b) = if b = 0 then f.Support.erase a else insert a f.Support := by
  convert rfl

@[simp]
theorem support_update_zero [DecidableEq α] : support (f.update a 0) = f.Support.erase a := by
  convert if_pos rfl

variable {b}

theorem support_update_ne_zero [DecidableEq α] (h : b ≠ 0) : support (f.update a b) = insert a f.Support := by
  convert if_neg h

end Update

/-! ### Declarations about `on_finset` -/


section OnFinset

variable [Zero M]

/-- `on_finset s f hf` is the finsupp function representing `f` restricted to the finset `s`.
  The function needs to be `0` outside of `s`. Use this when the set needs to be filtered anyways,
  otherwise a better set representation is often available. -/
def onFinset (s : Finset α) (f : α → M) (hf : ∀ a, f a ≠ 0 → a ∈ s) : α →₀ M :=
  ⟨s.filter fun a => f a ≠ 0, f, by
    simpa⟩

@[simp]
theorem on_finset_apply {s : Finset α} {f : α → M} {hf a} : (onFinset s f hf : α →₀ M) a = f a :=
  rfl

@[simp]
theorem support_on_finset_subset {s : Finset α} {f : α → M} {hf} : (onFinset s f hf).Support ⊆ s :=
  filter_subset _ _

@[simp]
theorem mem_support_on_finset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) {a : α} :
    a ∈ (Finsupp.onFinset s f hf).Support ↔ f a ≠ 0 := by
  rw [Finsupp.mem_support_iff, Finsupp.on_finset_apply]

theorem support_on_finset {s : Finset α} {f : α → M} (hf : ∀ a : α, f a ≠ 0 → a ∈ s) :
    (Finsupp.onFinset s f hf).Support = s.filter fun a => f a ≠ 0 :=
  rfl

end OnFinset

section OfSupportFinite

variable [Zero M]

/-- The natural `finsupp` induced by the function `f` given that it has finite support. -/
noncomputable def ofSupportFinite (f : α → M) (hf : (Function.Support f).Finite) : α →₀ M where
  Support := hf.toFinset
  toFun := f
  mem_support_to_fun := fun _ => hf.mem_to_finset

theorem of_support_finite_coe {f : α → M} {hf : (Function.Support f).Finite} : (ofSupportFinite f hf : α → M) = f :=
  rfl

instance : CanLift (α → M) (α →₀ M) where
  coe := coeFn
  cond := fun f => (Function.Support f).Finite
  prf := fun f hf => ⟨ofSupportFinite f hf, rfl⟩

end OfSupportFinite

/-! ### Declarations about `map_range` -/


section MapRange

variable [Zero M] [Zero N] [Zero P]

/-- The composition of `f : M → N` and `g : α →₀ M` is
`map_range f hf g : α →₀ N`, well-defined when `f 0 = 0`.

This preserves the structure on `f`, and exists in various bundled forms for when `f` is itself
bundled:

* `finsupp.map_range.equiv`
* `finsupp.map_range.zero_hom`
* `finsupp.map_range.add_monoid_hom`
* `finsupp.map_range.add_equiv`
* `finsupp.map_range.linear_map`
* `finsupp.map_range.linear_equiv`
-/
def mapRange (f : M → N) (hf : f 0 = 0) (g : α →₀ M) : α →₀ N :=
  (onFinset g.Support (f ∘ g)) fun a => by
    rw [mem_support_iff, not_imp_not] <;> exact fun H => (congr_arg f H).trans hf

@[simp]
theorem map_range_apply {f : M → N} {hf : f 0 = 0} {g : α →₀ M} {a : α} : mapRange f hf g a = f (g a) :=
  rfl

@[simp]
theorem map_range_zero {f : M → N} {hf : f 0 = 0} : mapRange f hf (0 : α →₀ M) = 0 :=
  ext fun a => by
    simp only [← hf, ← zero_apply, ← map_range_apply]

@[simp]
theorem map_range_id (g : α →₀ M) : mapRange id rfl g = g :=
  ext fun _ => rfl

theorem map_range_comp (f : N → P) (hf : f 0 = 0) (f₂ : M → N) (hf₂ : f₂ 0 = 0) (h : (f ∘ f₂) 0 = 0) (g : α →₀ M) :
    mapRange (f ∘ f₂) h g = mapRange f hf (mapRange f₂ hf₂ g) :=
  ext fun _ => rfl

theorem support_map_range {f : M → N} {hf : f 0 = 0} {g : α →₀ M} : (mapRange f hf g).Support ⊆ g.Support :=
  support_on_finset_subset

@[simp]
theorem map_range_single {f : M → N} {hf : f 0 = 0} {a : α} {b : M} : mapRange f hf (single a b) = single a (f b) :=
  ext fun a' =>
    show f (ite _ _ _) = ite _ _ _ by
      split_ifs <;> [rfl, exact hf]

theorem support_map_range_of_injective {e : M → N} (he0 : e 0 = 0) (f : ι →₀ M) (he : Function.Injective e) :
    (Finsupp.mapRange e he0 f).Support = f.Support := by
  ext
  simp only [← Finsupp.mem_support_iff, ← Ne.def, ← Finsupp.map_range_apply]
  exact he.ne_iff' he0

end MapRange

/-! ### Declarations about `emb_domain` -/


section EmbDomain

variable [Zero M] [Zero N]

/-- Given `f : α ↪ β` and `v : α →₀ M`, `emb_domain f v : β →₀ M`
is the finitely supported function whose value at `f a : β` is `v a`.
For a `b : β` outside the range of `f`, it is zero. -/
def embDomain (f : α ↪ β) (v : α →₀ M) : β →₀ M := by
  refine'
    ⟨v.support.map f, fun a₂ => if h : a₂ ∈ v.support.map f then v (v.support.choose (fun a₁ => f a₁ = a₂) _) else 0, _⟩
  · rcases Finset.mem_map.1 h with ⟨a, ha, rfl⟩
    exact ExistsUnique.intro a ⟨ha, rfl⟩ fun b ⟨_, hb⟩ => f.injective hb
    
  · intro a₂
    split_ifs
    · simp only [← h, ← true_iffₓ, ← Ne.def]
      rw [← not_mem_support_iff, not_not]
      apply Finset.choose_mem
      
    · simp only [← h, ← Ne.def, ← ne_self_iff_false]
      
    

@[simp]
theorem support_emb_domain (f : α ↪ β) (v : α →₀ M) : (embDomain f v).Support = v.Support.map f :=
  rfl

@[simp]
theorem emb_domain_zero (f : α ↪ β) : (embDomain f 0 : β →₀ M) = 0 :=
  rfl

@[simp]
theorem emb_domain_apply (f : α ↪ β) (v : α →₀ M) (a : α) : embDomain f v (f a) = v a := by
  change dite _ _ _ = _
  split_ifs <;> rw [Finset.mem_map' f] at h
  · refine' congr_arg (v : α → M) (f.inj' _)
    exact Finset.choose_property (fun a₁ => f a₁ = f a) _ _
    
  · exact (not_mem_support_iff.1 h).symm
    

theorem emb_domain_notin_range (f : α ↪ β) (v : α →₀ M) (a : β) (h : a ∉ Set.Range f) : embDomain f v a = 0 := by
  refine' dif_neg (mt (fun h => _) h)
  rcases Finset.mem_map.1 h with ⟨a, h, rfl⟩
  exact Set.mem_range_self a

theorem emb_domain_injective (f : α ↪ β) : Function.Injective (embDomain f : (α →₀ M) → β →₀ M) := fun l₁ l₂ h =>
  ext fun a => by
    simpa only [← emb_domain_apply] using ext_iff.1 h (f a)

@[simp]
theorem emb_domain_inj {f : α ↪ β} {l₁ l₂ : α →₀ M} : embDomain f l₁ = embDomain f l₂ ↔ l₁ = l₂ :=
  (emb_domain_injective f).eq_iff

@[simp]
theorem emb_domain_eq_zero {f : α ↪ β} {l : α →₀ M} : embDomain f l = 0 ↔ l = 0 :=
  (emb_domain_injective f).eq_iff' <| emb_domain_zero f

theorem emb_domain_map_range (f : α ↪ β) (g : M → N) (p : α →₀ M) (hg : g 0 = 0) :
    embDomain f (mapRange g hg p) = mapRange g hg (embDomain f p) := by
  ext a
  by_cases' a ∈ Set.Range f
  · rcases h with ⟨a', rfl⟩
    rw [map_range_apply, emb_domain_apply, emb_domain_apply, map_range_apply]
    
  · rw [map_range_apply, emb_domain_notin_range, emb_domain_notin_range, ← hg] <;> assumption
    

theorem single_of_emb_domain_single (l : α →₀ M) (f : α ↪ β) (a : β) (b : M) (hb : b ≠ 0)
    (h : l.embDomain f = single a b) : ∃ x, l = single x b ∧ f x = a := by
  have h_map_support : Finset.map f l.support = {a} := by
    rw [← support_emb_domain, h, support_single_ne_zero _ hb] <;> rfl
  have ha : a ∈ Finset.map f l.support := by
    simp only [← h_map_support, ← Finset.mem_singleton]
  rcases Finset.mem_map.1 ha with ⟨c, hc₁, hc₂⟩
  use c
  constructor
  · ext d
    rw [← emb_domain_apply f l, h]
    by_cases' h_cases : c = d
    · simp only [← Eq.symm h_cases, ← hc₂, ← single_eq_same]
      
    · rw [single_apply, single_apply, if_neg, if_neg h_cases]
      by_contra hfd
      exact h_cases (f.injective (hc₂.trans hfd))
      
    
  · exact hc₂
    

@[simp]
theorem emb_domain_single (f : α ↪ β) (a : α) (m : M) : embDomain f (single a m) = single (f a) m := by
  ext b
  by_cases' h : b ∈ Set.Range f
  · rcases h with ⟨a', rfl⟩
    simp [← single_apply]
    
  · simp only [← emb_domain_notin_range, ← h, ← single_apply, ← not_false_iff]
    rw [if_neg]
    rintro rfl
    simpa using h
    

end EmbDomain

/-! ### Declarations about `zip_with` -/


section ZipWith

variable [Zero M] [Zero N] [Zero P]

/-- `zip_with f hf g₁ g₂` is the finitely supported function satisfying
  `zip_with f hf g₁ g₂ a = f (g₁ a) (g₂ a)`, and it is well-defined when `f 0 0 = 0`. -/
def zipWith (f : M → N → P) (hf : f 0 0 = 0) (g₁ : α →₀ M) (g₂ : α →₀ N) : α →₀ P :=
  (onFinset (g₁.Support ∪ g₂.Support) fun a => f (g₁ a) (g₂ a)) fun a H => by
    simp only [← mem_union, ← mem_support_iff, ← Ne]
    rw [← not_and_distrib]
    rintro ⟨h₁, h₂⟩
    rw [h₁, h₂] at H
    exact H hf

@[simp]
theorem zip_with_apply {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} {a : α} :
    zipWith f hf g₁ g₂ a = f (g₁ a) (g₂ a) :=
  rfl

theorem support_zip_with [D : DecidableEq α] {f : M → N → P} {hf : f 0 0 = 0} {g₁ : α →₀ M} {g₂ : α →₀ N} :
    (zipWith f hf g₁ g₂).Support ⊆ g₁.Support ∪ g₂.Support := by
  rw [Subsingleton.elimₓ D] <;> exact support_on_finset_subset

end ZipWith

/-! ### Declarations about `erase` -/


section Erase

variable [Zero M]

/-- `erase a f` is the finitely supported function equal to `f` except at `a` where it is equal to
  `0`. -/
def erase (a : α) (f : α →₀ M) : α →₀ M :=
  ⟨f.Support.erase a, fun a' => if a' = a then 0 else f a', fun a' => by
    rw [mem_erase, mem_support_iff] <;>
      split_ifs <;> [exact ⟨fun H _ => H.1 h, fun H => (H rfl).elim⟩, exact and_iff_right h]⟩

@[simp]
theorem support_erase [DecidableEq α] {a : α} {f : α →₀ M} : (f.erase a).Support = f.Support.erase a := by
  convert rfl

@[simp]
theorem erase_same {a : α} {f : α →₀ M} : (f.erase a) a = 0 :=
  if_pos rfl

@[simp]
theorem erase_ne {a a' : α} {f : α →₀ M} (h : a' ≠ a) : (f.erase a) a' = f a' :=
  if_neg h

@[simp]
theorem erase_single {a : α} {b : M} : erase a (single a b) = 0 := by
  ext s
  by_cases' hs : s = a
  · rw [hs, erase_same]
    rfl
    
  · rw [erase_ne hs]
    exact single_eq_of_ne (Ne.symm hs)
    

theorem erase_single_ne {a a' : α} {b : M} (h : a ≠ a') : erase a (single a' b) = single a' b := by
  ext s
  by_cases' hs : s = a
  · rw [hs, erase_same, single_eq_of_ne h.symm]
    
  · rw [erase_ne hs]
    

@[simp]
theorem erase_of_not_mem_support {f : α →₀ M} {a} (haf : a ∉ f.Support) : erase a f = f := by
  ext b
  by_cases' hab : b = a
  · rwa [hab, erase_same, eq_comm, ← not_mem_support_iff]
    
  · rw [erase_ne hab]
    

@[simp]
theorem erase_zero (a : α) : erase a (0 : α →₀ M) = 0 := by
  rw [← support_eq_empty, support_erase, support_zero, erase_empty]

end Erase

/-! ### Declarations about `graph` -/


section Graph

variable [Zero M]

/-- The graph of a finitely supported function over its support, i.e. the finset of input and output
pairs with non-zero outputs. -/
def graph (f : α →₀ M) : Finset (α × M) :=
  f.Support.map ⟨fun a => Prod.mk a (f a), fun x y h => (Prod.mk.inj h).1⟩

theorem mk_mem_graph_iff {a : α} {m : M} {f : α →₀ M} : (a, m) ∈ f.graph ↔ f a = m ∧ m ≠ 0 := by
  simp_rw [graph, mem_map, mem_support_iff]
  constructor
  · rintro ⟨b, ha, rfl, -⟩
    exact ⟨rfl, ha⟩
    
  · rintro ⟨rfl, ha⟩
    exact ⟨a, ha, rfl⟩
    

@[simp]
theorem mem_graph_iff {c : α × M} {f : α →₀ M} : c ∈ f.graph ↔ f c.1 = c.2 ∧ c.2 ≠ 0 := by
  cases c
  exact mk_mem_graph_iff

theorem mk_mem_graph (f : α →₀ M) {a : α} (ha : a ∈ f.Support) : (a, f a) ∈ f.graph :=
  mk_mem_graph_iff.2 ⟨rfl, mem_support_iff.1 ha⟩

theorem apply_eq_of_mem_graph {a : α} {m : M} {f : α →₀ M} (h : (a, m) ∈ f.graph) : f a = m :=
  (mem_graph_iff.1 h).1

@[simp]
theorem not_mem_graph_snd_zero (a : α) (f : α →₀ M) : (a, (0 : M)) ∉ f.graph := fun h => (mem_graph_iff.1 h).2.irrefl

@[simp]
theorem image_fst_graph (f : α →₀ M) : f.graph.Image Prod.fst = f.Support := by
  simp only [← graph, ← map_eq_image, ← image_image, ← embedding.coe_fn_mk, ← (· ∘ ·), ← image_id']

theorem graph_injective (α M) [Zero M] : Injective (@graph α M _) := by
  intro f g h
  have hsup : f.support = g.support := by
    rw [← image_fst_graph, h, image_fst_graph]
  refine' ext_iff'.2 ⟨hsup, fun x hx => apply_eq_of_mem_graph <| h.symm ▸ _⟩
  exact mk_mem_graph _ (hsup ▸ hx)

@[simp]
theorem graph_inj {f g : α →₀ M} : f.graph = g.graph ↔ f = g :=
  (graph_injective α M).eq_iff

@[simp]
theorem graph_zero : graph (0 : α →₀ M) = ∅ := by
  simp [← graph]

@[simp]
theorem graph_eq_empty {f : α →₀ M} : f.graph = ∅ ↔ f = 0 :=
  (graph_injective α M).eq_iff' graph_zero

end Graph

/-!
### Declarations about `sum` and `prod`

In most of this section, the domain `β` is assumed to be an `add_monoid`.
-/


section SumProd

/-- `prod f g` is the product of `g a (f a)` over the support of `f`. -/
@[to_additive "`sum f g` is the sum of `g a (f a)` over the support of `f`. "]
def prod [Zero M] [CommMonoidₓ N] (f : α →₀ M) (g : α → M → N) : N :=
  ∏ a in f.Support, g a (f a)

variable [Zero M] [Zero M'] [CommMonoidₓ N]

@[to_additive]
theorem prod_of_support_subset (f : α →₀ M) {s : Finset α} (hs : f.Support ⊆ s) (g : α → M → N)
    (h : ∀, ∀ i ∈ s, ∀, g i 0 = 1) : f.Prod g = ∏ x in s, g x (f x) :=
  (Finset.prod_subset hs) fun x hxs hx => h x hxs ▸ congr_arg (g x) <| not_mem_support_iff.1 hx

@[to_additive]
theorem prod_fintype [Fintype α] (f : α →₀ M) (g : α → M → N) (h : ∀ i, g i 0 = 1) : f.Prod g = ∏ i, g i (f i) :=
  f.prod_of_support_subset (subset_univ _) g fun x _ => h x

@[simp, to_additive]
theorem prod_single_index {a : α} {b : M} {h : α → M → N} (h_zero : h a 0 = 1) : (single a b).Prod h = h a b :=
  calc
    (single a b).Prod h = ∏ x in {a}, h x (single a b x) :=
      (prod_of_support_subset _ support_single_subset h) fun x hx => (mem_singleton.1 hx).symm ▸ h_zero
    _ = h a b := by
      simp
    

@[to_additive]
theorem prod_map_range_index {f : M → M'} {hf : f 0 = 0} {g : α →₀ M} {h : α → M' → N} (h0 : ∀ a, h a 0 = 1) :
    (mapRange f hf g).Prod h = g.Prod fun a b => h a (f b) :=
  (Finset.prod_subset support_map_range) fun _ _ H => by
    rw [not_mem_support_iff.1 H, h0]

@[simp, to_additive]
theorem prod_zero_index {h : α → M → N} : (0 : α →₀ M).Prod h = 1 :=
  rfl

@[to_additive]
theorem prod_comm (f : α →₀ M) (g : β →₀ M') (h : α → M → β → M' → N) :
    (f.Prod fun x v => g.Prod fun x' v' => h x v x' v') = g.Prod fun x' v' => f.Prod fun x v => h x v x' v' :=
  Finset.prod_comm

@[simp, to_additive]
theorem prod_ite_eq [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.Prod fun x v => ite (a = x) (b x v) 1) = ite (a ∈ f.Support) (b a (f a)) 1 := by
  dsimp' [← Finsupp.prod]
  rw [f.support.prod_ite_eq]

@[simp]
theorem sum_ite_self_eq [DecidableEq α] {N : Type _} [AddCommMonoidₓ N] (f : α →₀ N) (a : α) :
    (f.Sum fun x v => ite (a = x) v 0) = f a := by
  convert f.sum_ite_eq a fun x => id
  simp [← ite_eq_right_iff.2 Eq.symm]

/-- A restatement of `prod_ite_eq` with the equality test reversed. -/
@[simp, to_additive "A restatement of `sum_ite_eq` with the equality test reversed."]
theorem prod_ite_eq' [DecidableEq α] (f : α →₀ M) (a : α) (b : α → M → N) :
    (f.Prod fun x v => ite (x = a) (b x v) 1) = ite (a ∈ f.Support) (b a (f a)) 1 := by
  dsimp' [← Finsupp.prod]
  rw [f.support.prod_ite_eq']

@[simp]
theorem sum_ite_self_eq' [DecidableEq α] {N : Type _} [AddCommMonoidₓ N] (f : α →₀ N) (a : α) :
    (f.Sum fun x v => ite (x = a) v 0) = f a := by
  convert f.sum_ite_eq' a fun x => id
  simp [← ite_eq_right_iff.2 Eq.symm]

@[simp]
theorem prod_pow [Fintype α] (f : α →₀ ℕ) (g : α → N) : (f.Prod fun a b => g a ^ b) = ∏ a, g a ^ f a :=
  (f.prod_fintype _) fun a => pow_zeroₓ _

/-- If `g` maps a second argument of 0 to 1, then multiplying it over the
result of `on_finset` is the same as multiplying it over the original
`finset`. -/
@[to_additive
      "If `g` maps a second argument of 0 to 0, summing it over the\nresult of `on_finset` is the same as summing it over the original\n`finset`."]
theorem on_finset_prod {s : Finset α} {f : α → M} {g : α → M → N} (hf : ∀ a, f a ≠ 0 → a ∈ s) (hg : ∀ a, g a 0 = 1) :
    (onFinset s f hf).Prod g = ∏ a in s, g a (f a) :=
  Finset.prod_subset support_on_finset_subset <| by
    simp (config := { contextual := true })[*]

/-- Taking a product over `f : α →₀ M` is the same as multiplying the value on a single element
`y ∈ f.support` by the product over `erase y f`. -/
@[to_additive
      " Taking a sum over over `f : α →₀ M` is the same as adding the value on a\nsingle element `y ∈ f.support` to the sum over `erase y f`. "]
theorem mul_prod_erase (f : α →₀ M) (y : α) (g : α → M → N) (hyf : y ∈ f.Support) :
    g y (f y) * (erase y f).Prod g = f.Prod g := by
  rw [Finsupp.prod, Finsupp.prod, ← Finset.mul_prod_erase _ _ hyf, Finsupp.support_erase, Finset.prod_congr rfl]
  intro h hx
  rw [Finsupp.erase_ne (ne_of_mem_erase hx)]

/-- Generalization of `finsupp.mul_prod_erase`: if `g` maps a second argument of 0 to 1,
then its product over `f : α →₀ M` is the same as multiplying the value on any element
`y : α` by the product over `erase y f`. -/
@[to_additive
      " Generalization of `finsupp.add_sum_erase`: if `g` maps a second argument of 0\nto 0, then its sum over `f : α →₀ M` is the same as adding the value on any element\n`y : α` to the sum over `erase y f`. "]
theorem mul_prod_erase' (f : α →₀ M) (y : α) (g : α → M → N) (hg : ∀ i : α, g i 0 = 1) :
    g y (f y) * (erase y f).Prod g = f.Prod g := by
  classical
  by_cases' hyf : y ∈ f.support
  · exact Finsupp.mul_prod_erase f y g hyf
    
  · rw [not_mem_support_iff.mp hyf, hg y, erase_of_not_mem_support hyf, one_mulₓ]
    

@[to_additive]
theorem _root_.submonoid_class.finsupp_prod_mem {S : Type _} [SetLike S N] [SubmonoidClass S N] (s : S) (f : α →₀ M)
    (g : α → M → N) (h : ∀ c, f c ≠ 0 → g c (f c) ∈ s) : f.Prod g ∈ s :=
  prod_mem fun i hi => h _ (Finsupp.mem_support_iff.mp hi)

@[to_additive]
theorem prod_congr {f : α →₀ M} {g1 g2 : α → M → N} (h : ∀, ∀ x ∈ f.Support, ∀, g1 x (f x) = g2 x (f x)) :
    f.Prod g1 = f.Prod g2 :=
  Finset.prod_congr rfl h

end SumProd

/-!
### Additive monoid structure on `α →₀ M`
-/


section AddZeroClassₓ

variable [AddZeroClassₓ M]

instance : Add (α →₀ M) :=
  ⟨zipWith (· + ·) (add_zeroₓ 0)⟩

@[simp]
theorem coe_add (f g : α →₀ M) : ⇑(f + g) = f + g :=
  rfl

theorem add_apply (g₁ g₂ : α →₀ M) (a : α) : (g₁ + g₂) a = g₁ a + g₂ a :=
  rfl

theorem support_add [DecidableEq α] {g₁ g₂ : α →₀ M} : (g₁ + g₂).Support ⊆ g₁.Support ∪ g₂.Support :=
  support_zip_with

theorem support_add_eq [DecidableEq α] {g₁ g₂ : α →₀ M} (h : Disjoint g₁.Support g₂.Support) :
    (g₁ + g₂).Support = g₁.Support ∪ g₂.Support :=
  (le_antisymmₓ support_zip_with) fun a ha =>
    (Finset.mem_union.1 ha).elim
      (fun ha => by
        have : a ∉ g₂.Support := disjoint_left.1 h ha
        simp only [← mem_support_iff, ← not_not] at * <;> simpa only [← add_apply, ← this, ← add_zeroₓ] )
      fun ha => by
      have : a ∉ g₁.Support := disjoint_right.1 h ha
      simp only [← mem_support_iff, ← not_not] at * <;> simpa only [← add_apply, ← this, ← zero_addₓ]

@[simp]
theorem single_add (a : α) (b₁ b₂ : M) : single a (b₁ + b₂) = single a b₁ + single a b₂ :=
  ext fun a' => by
    by_cases' h : a = a'
    · rw [h, add_apply, single_eq_same, single_eq_same, single_eq_same]
      
    · rw [add_apply, single_eq_of_ne h, single_eq_of_ne h, single_eq_of_ne h, zero_addₓ]
      

instance : AddZeroClassₓ (α →₀ M) :=
  FunLike.coe_injective.AddZeroClass _ coe_zero coe_add

/-- `finsupp.single` as an `add_monoid_hom`.

See `finsupp.lsingle` for the stronger version as a linear map.
-/
@[simps]
def singleAddHom (a : α) : M →+ α →₀ M :=
  ⟨single a, single_zero a, single_add a⟩

/-- Evaluation of a function `f : α →₀ M` at a point as an additive monoid homomorphism.

See `finsupp.lapply` for the stronger version as a linear map. -/
@[simps apply]
def applyAddHom (a : α) : (α →₀ M) →+ M :=
  ⟨fun g => g a, zero_apply, fun _ _ => add_apply _ _ _⟩

/-- Coercion from a `finsupp` to a function type is an `add_monoid_hom`. -/
@[simps]
noncomputable def coeFnAddHom : (α →₀ M) →+ α → M where
  toFun := coeFn
  map_zero' := coe_zero
  map_add' := coe_add

theorem update_eq_single_add_erase (f : α →₀ M) (a : α) (b : M) : f.update a b = single a b + f.erase a := by
  ext j
  rcases eq_or_ne a j with (rfl | h)
  · simp
    
  · simp [← Function.update_noteq h.symm, ← single_apply, ← h, ← erase_ne, ← h.symm]
    

theorem update_eq_erase_add_single (f : α →₀ M) (a : α) (b : M) : f.update a b = f.erase a + single a b := by
  ext j
  rcases eq_or_ne a j with (rfl | h)
  · simp
    
  · simp [← Function.update_noteq h.symm, ← single_apply, ← h, ← erase_ne, ← h.symm]
    

theorem single_add_erase (a : α) (f : α →₀ M) : single a (f a) + f.erase a = f := by
  rw [← update_eq_single_add_erase, update_self]

theorem erase_add_single (a : α) (f : α →₀ M) : f.erase a + single a (f a) = f := by
  rw [← update_eq_erase_add_single, update_self]

@[simp]
theorem erase_add (a : α) (f f' : α →₀ M) : erase a (f + f') = erase a f + erase a f' := by
  ext s
  by_cases' hs : s = a
  · rw [hs, add_apply, erase_same, erase_same, erase_same, add_zeroₓ]
    
  rw [add_apply, erase_ne hs, erase_ne hs, erase_ne hs, add_apply]

/-- `finsupp.erase` as an `add_monoid_hom`. -/
@[simps]
def eraseAddHom (a : α) : (α →₀ M) →+ α →₀ M where
  toFun := erase a
  map_zero' := erase_zero a
  map_add' := erase_add a

@[elab_as_eliminator]
protected theorem induction {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.Support → b ≠ 0 → p f → p (single a b + f)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.Support = s → p f from this _ _ rfl
  fun s =>
  (Finset.induction_on s fun f hf => by
      rwa [support_eq_empty.1 hf])
    fun a s has ih f hf => by
    suffices p (single a (f a) + f.erase a) by
      rwa [single_add_erase] at this
    apply ha
    · rw [support_erase, mem_erase]
      exact fun H => H.1 rfl
      
    · rw [← mem_support_iff, hf]
      exact mem_insert_self _ _
      
    · apply ih _ _
      rw [support_erase, hf, Finset.erase_insert has]
      

theorem induction₂ {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0)
    (ha : ∀ (a b) (f : α →₀ M), a ∉ f.Support → b ≠ 0 → p f → p (f + single a b)) : p f :=
  suffices ∀ (s) (f : α →₀ M), f.Support = s → p f from this _ _ rfl
  fun s =>
  (Finset.induction_on s fun f hf => by
      rwa [support_eq_empty.1 hf])
    fun a s has ih f hf => by
    suffices p (f.erase a + single a (f a)) by
      rwa [erase_add_single] at this
    apply ha
    · rw [support_erase, mem_erase]
      exact fun H => H.1 rfl
      
    · rw [← mem_support_iff, hf]
      exact mem_insert_self _ _
      
    · apply ih _ _
      rw [support_erase, hf, Finset.erase_insert has]
      

theorem induction_linear {p : (α →₀ M) → Prop} (f : α →₀ M) (h0 : p 0) (hadd : ∀ f g : α →₀ M, p f → p g → p (f + g))
    (hsingle : ∀ a b, p (single a b)) : p f :=
  induction₂ f h0 fun a b f _ _ w => hadd _ _ w (hsingle _ _)

@[simp]
theorem add_closure_set_of_eq_single : AddSubmonoid.closure { f : α →₀ M | ∃ a b, f = single a b } = ⊤ :=
  top_unique fun x hx =>
    (Finsupp.induction x (AddSubmonoid.zero_mem _)) fun a b f ha hb hf =>
      AddSubmonoid.add_mem _ (AddSubmonoid.subset_closure <| ⟨a, b, rfl⟩) hf

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal. -/
theorem add_hom_ext [AddZeroClassₓ N] ⦃f g : (α →₀ M) →+ N⦄ (H : ∀ x y, f (single x y) = g (single x y)) : f = g := by
  refine' AddMonoidHom.eq_of_eq_on_mdense add_closure_set_of_eq_single _
  rintro _ ⟨x, y, rfl⟩
  apply H

/-- If two additive homomorphisms from `α →₀ M` are equal on each `single a b`, then
they are equal.

We formulate this using equality of `add_monoid_hom`s so that `ext` tactic can apply a type-specific
extensionality lemma after this one.  E.g., if the fiber `M` is `ℕ` or `ℤ`, then it suffices to
verify `f (single a 1) = g (single a 1)`. -/
@[ext]
theorem add_hom_ext' [AddZeroClassₓ N] ⦃f g : (α →₀ M) →+ N⦄
    (H : ∀ x, f.comp (singleAddHom x) = g.comp (singleAddHom x)) : f = g :=
  add_hom_ext fun x => AddMonoidHom.congr_fun (H x)

theorem mul_hom_ext [MulOneClassₓ N] ⦃f g : Multiplicative (α →₀ M) →* N⦄
    (H : ∀ x y, f (Multiplicative.ofAdd <| single x y) = g (Multiplicative.ofAdd <| single x y)) : f = g :=
  MonoidHom.ext <| AddMonoidHom.congr_fun <| @add_hom_ext α M (Additive N) _ _ f.toAdditive'' g.toAdditive'' H

@[ext]
theorem mul_hom_ext' [MulOneClassₓ N] {f g : Multiplicative (α →₀ M) →* N}
    (H : ∀ x, f.comp (singleAddHom x).toMultiplicative = g.comp (singleAddHom x).toMultiplicative) : f = g :=
  mul_hom_ext fun x => MonoidHom.congr_fun (H x)

theorem map_range_add [AddZeroClassₓ N] {f : M → N} {hf : f 0 = 0} (hf' : ∀ x y, f (x + y) = f x + f y)
    (v₁ v₂ : α →₀ M) : mapRange f hf (v₁ + v₂) = mapRange f hf v₁ + mapRange f hf v₂ :=
  ext fun a => by
    simp only [← hf', ← add_apply, ← map_range_apply]

/-- Bundle `emb_domain f` as an additive map from `α →₀ M` to `β →₀ M`. -/
@[simps]
def embDomain.addMonoidHom (f : α ↪ β) : (α →₀ M) →+ β →₀ M where
  toFun := fun v => embDomain f v
  map_zero' := by
    simp
  map_add' := fun v w => by
    ext b
    by_cases' h : b ∈ Set.Range f
    · rcases h with ⟨a, rfl⟩
      simp
      
    · simp [← emb_domain_notin_range, ← h]
      

@[simp]
theorem emb_domain_add (f : α ↪ β) (v w : α →₀ M) : embDomain f (v + w) = embDomain f v + embDomain f w :=
  (embDomain.addMonoidHom f).map_add v w

end AddZeroClassₓ

section AddMonoidₓ

variable [AddMonoidₓ M]

/-- Note the general `finsupp.has_smul` instance doesn't apply as `ℕ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasNatScalar : HasSmul ℕ (α →₀ M) :=
  ⟨fun n v => v.map_range ((· • ·) n) (nsmul_zero _)⟩

instance : AddMonoidₓ (α →₀ M) :=
  FunLike.coe_injective.AddMonoid _ coe_zero coe_add fun _ _ => rfl

end AddMonoidₓ

end Finsupp

@[to_additive]
theorem map_finsupp_prod [Zero M] [CommMonoidₓ N] [CommMonoidₓ P] {H : Type _} [MonoidHomClass H N P] (h : H)
    (f : α →₀ M) (g : α → M → N) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  map_prod h _ _

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_finsupp_sum` instead."]
protected theorem MulEquiv.map_finsupp_prod [Zero M] [CommMonoidₓ N] [CommMonoidₓ P] (h : N ≃* P) (f : α →₀ M)
    (g : α → M → N) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  map_finsupp_prod h f g

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
@[to_additive "Deprecated, use `_root_.map_finsupp_sum` instead."]
protected theorem MonoidHom.map_finsupp_prod [Zero M] [CommMonoidₓ N] [CommMonoidₓ P] (h : N →* P) (f : α →₀ M)
    (g : α → M → N) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  map_finsupp_prod h f g

/-- Deprecated, use `_root_.map_finsupp_sum` instead. -/
protected theorem RingHom.map_finsupp_sum [Zero M] [Semiringₓ R] [Semiringₓ S] (h : R →+* S) (f : α →₀ M)
    (g : α → M → R) : h (f.Sum g) = f.Sum fun a b => h (g a b) :=
  map_finsupp_sum h f g

/-- Deprecated, use `_root_.map_finsupp_prod` instead. -/
protected theorem RingHom.map_finsupp_prod [Zero M] [CommSemiringₓ R] [CommSemiringₓ S] (h : R →+* S) (f : α →₀ M)
    (g : α → M → R) : h (f.Prod g) = f.Prod fun a b => h (g a b) :=
  map_finsupp_prod h f g

@[to_additive]
theorem MonoidHom.coe_finsupp_prod [Zero β] [Monoidₓ N] [CommMonoidₓ P] (f : α →₀ β) (g : α → β → N →* P) :
    ⇑(f.Prod g) = f.Prod fun i fi => g i fi :=
  MonoidHom.coe_finset_prod _ _

@[simp, to_additive]
theorem MonoidHom.finsupp_prod_apply [Zero β] [Monoidₓ N] [CommMonoidₓ P] (f : α →₀ β) (g : α → β → N →* P) (x : N) :
    f.Prod g x = f.Prod fun i fi => g i fi x :=
  MonoidHom.finset_prod_apply _ _ _

namespace Finsupp

instance [AddCommMonoidₓ M] : AddCommMonoidₓ (α →₀ M) :=
  FunLike.coe_injective.AddCommMonoid _ coe_zero coe_add fun _ _ => rfl

instance [AddGroupₓ G] : Neg (α →₀ G) :=
  ⟨mapRange Neg.neg neg_zero⟩

@[simp]
theorem coe_neg [AddGroupₓ G] (g : α →₀ G) : ⇑(-g) = -g :=
  rfl

theorem neg_apply [AddGroupₓ G] (g : α →₀ G) (a : α) : (-g) a = -g a :=
  rfl

instance [AddGroupₓ G] : Sub (α →₀ G) :=
  ⟨zipWith Sub.sub (sub_zero _)⟩

@[simp]
theorem coe_sub [AddGroupₓ G] (g₁ g₂ : α →₀ G) : ⇑(g₁ - g₂) = g₁ - g₂ :=
  rfl

theorem sub_apply [AddGroupₓ G] (g₁ g₂ : α →₀ G) (a : α) : (g₁ - g₂) a = g₁ a - g₂ a :=
  rfl

/-- Note the general `finsupp.has_smul` instance doesn't apply as `ℤ` is not distributive
unless `β i`'s addition is commutative. -/
instance hasIntScalar [AddGroupₓ G] : HasSmul ℤ (α →₀ G) :=
  ⟨fun n v => v.map_range ((· • ·) n) (zsmul_zero _)⟩

instance [AddGroupₓ G] : AddGroupₓ (α →₀ G) :=
  FunLike.coe_injective.AddGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

instance [AddCommGroupₓ G] : AddCommGroupₓ (α →₀ G) :=
  FunLike.coe_injective.AddCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => rfl) fun _ _ => rfl

theorem single_add_single_eq_single_add_single [AddCommMonoidₓ M] {k l m n : α} {u v : M} (hu : u ≠ 0) (hv : v ≠ 0) :
    single k u + single l v = single m u + single n v ↔
      k = m ∧ l = n ∨ u = v ∧ k = n ∧ l = m ∨ u + v = 0 ∧ k = l ∧ m = n :=
  by
  simp_rw [FunLike.ext_iff, coe_add, single_eq_pi_single, ← funext_iff]
  exact Pi.single_add_single_eq_single_add_single hu hv

theorem single_multiset_sum [AddCommMonoidₓ M] (s : Multiset M) (a : α) : single a s.Sum = (s.map (single a)).Sum :=
  (Multiset.induction_on s (single_zero _)) fun a s ih => by
    rw [Multiset.sum_cons, single_add, ih, Multiset.map_cons, Multiset.sum_cons]

theorem single_finset_sum [AddCommMonoidₓ M] (s : Finset ι) (f : ι → M) (a : α) :
    single a (∑ b in s, f b) = ∑ b in s, single a (f b) := by
  trans
  apply single_multiset_sum
  rw [Multiset.map_map]
  rfl

theorem single_sum [Zero M] [AddCommMonoidₓ N] (s : ι →₀ M) (f : ι → M → N) (a : α) :
    single a (s.Sum f) = s.Sum fun d c => single a (f d c) :=
  single_finset_sum _ _ _

@[to_additive]
theorem prod_neg_index [AddGroupₓ G] [CommMonoidₓ M] {g : α →₀ G} {h : α → G → M} (h0 : ∀ a, h a 0 = 1) :
    (-g).Prod h = g.Prod fun a b => h a (-b) :=
  prod_map_range_index h0

@[simp]
theorem support_neg [AddGroupₓ G] (f : α →₀ G) : support (-f) = support f :=
  Finset.Subset.antisymm support_map_range
    (calc
      support f = support (- -f) := congr_arg support (neg_negₓ _).symm
      _ ⊆ support (-f) := support_map_range
      )

theorem support_sub [DecidableEq α] [AddGroupₓ G] {f g : α →₀ G} : support (f - g) ⊆ support f ∪ support g := by
  rw [sub_eq_add_neg, ← support_neg g]
  exact support_add

theorem erase_eq_sub_single [AddGroupₓ G] (f : α →₀ G) (a : α) : f.erase a = f - single a (f a) := by
  ext a'
  rcases eq_or_ne a a' with (rfl | h)
  · simp
    
  · simp [← erase_ne h.symm, ← single_eq_of_ne h]
    

theorem update_eq_sub_add_single [AddGroupₓ G] (f : α →₀ G) (a : α) (b : G) :
    f.update a b = f - single a (f a) + single a b := by
  rw [update_eq_erase_add_single, erase_eq_sub_single]

theorem finset_sum_apply [AddCommMonoidₓ N] (S : Finset ι) (f : ι → α →₀ N) (a : α) :
    (∑ i in S, f i) a = ∑ i in S, f i a :=
  (applyAddHom a : (α →₀ N) →+ _).map_sum _ _

@[simp]
theorem sum_apply [Zero M] [AddCommMonoidₓ N] {f : α →₀ M} {g : α → M → β →₀ N} {a₂ : β} :
    (f.Sum g) a₂ = f.Sum fun a₁ b => g a₁ b a₂ :=
  finset_sum_apply _ _ _

theorem coe_finset_sum [AddCommMonoidₓ N] (S : Finset ι) (f : ι → α →₀ N) : ⇑(∑ i in S, f i) = ∑ i in S, f i :=
  (coeFnAddHom : (α →₀ N) →+ _).map_sum _ _

theorem coe_sum [Zero M] [AddCommMonoidₓ N] (f : α →₀ M) (g : α → M → β →₀ N) : ⇑(f.Sum g) = f.Sum fun a₁ b => g a₁ b :=
  coe_finset_sum _ _

theorem support_sum [DecidableEq β] [Zero M] [AddCommMonoidₓ N] {f : α →₀ M} {g : α → M → β →₀ N} :
    (f.Sum g).Support ⊆ f.Support.bUnion fun a => (g a (f a)).Support := by
  have : ∀ c, (f.Sum fun a b => g a b c) ≠ 0 → ∃ a, f a ≠ 0 ∧ ¬(g a (f a)) c = 0 := fun a₁ h =>
    let ⟨a, ha, Ne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    ⟨a, mem_support_iff.mp ha, Ne⟩
  simpa only [← Finset.subset_iff, ← mem_support_iff, ← Finset.mem_bUnion, ← sum_apply, ← exists_prop]

theorem support_finset_sum [DecidableEq β] [AddCommMonoidₓ M] {s : Finset α} {f : α → β →₀ M} :
    (Finset.sum s f).Support ⊆ s.bUnion fun x => (f x).Support := by
  rw [← Finset.sup_eq_bUnion]
  induction' s using Finset.cons_induction_on with a s ha ih
  · rfl
    
  · rw [Finset.sum_cons, Finset.sup_cons]
    exact support_add.trans (Finset.union_subset_union (Finset.Subset.refl _) ih)
    

@[simp]
theorem sum_zero [Zero M] [AddCommMonoidₓ N] {f : α →₀ M} : (f.Sum fun a b => (0 : N)) = 0 :=
  Finset.sum_const_zero

@[simp, to_additive]
theorem prod_mul [Zero M] [CommMonoidₓ N] {f : α →₀ M} {h₁ h₂ : α → M → N} :
    (f.Prod fun a b => h₁ a b * h₂ a b) = f.Prod h₁ * f.Prod h₂ :=
  Finset.prod_mul_distrib

@[simp, to_additive]
theorem prod_inv [Zero M] [CommGroupₓ G] {f : α →₀ M} {h : α → M → G} : (f.Prod fun a b => (h a b)⁻¹) = (f.Prod h)⁻¹ :=
  (map_prod (MonoidHom.id G)⁻¹ _ _).symm

@[simp]
theorem sum_sub [Zero M] [AddCommGroupₓ G] {f : α →₀ M} {h₁ h₂ : α → M → G} :
    (f.Sum fun a b => h₁ a b - h₂ a b) = f.Sum h₁ - f.Sum h₂ :=
  Finset.sum_sub_distrib

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism on the support.
This is a more general version of `finsupp.prod_add_index'`; the latter has simpler hypotheses. -/
@[to_additive
      "Taking the product under `h` is an additive homomorphism of finsupps,\nif `h` is an additive homomorphism on the support.\nThis is a more general version of `finsupp.sum_add_index'`; the latter has simpler hypotheses."]
theorem prod_add_index [AddZeroClassₓ M] [CommMonoidₓ N] {f g : α →₀ M} {h : α → M → N}
    (h_zero : ∀, ∀ a ∈ f.Support ∪ g.Support, ∀, h a 0 = 1)
    (h_add : ∀, ∀ a ∈ f.Support ∪ g.Support, ∀ (b₁ b₂), h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f + g).Prod h = f.Prod h * g.Prod h := by
  rw [Finsupp.prod_of_support_subset f (subset_union_left _ g.support) h h_zero,
    Finsupp.prod_of_support_subset g (subset_union_right f.support _) h h_zero, ← Finset.prod_mul_distrib,
    Finsupp.prod_of_support_subset (f + g) Finsupp.support_add h h_zero]
  exact
    Finset.prod_congr rfl fun x hx => by
      apply h_add x hx

/-- Taking the product under `h` is an additive-to-multiplicative homomorphism of finsupps,
if `h` is an additive-to-multiplicative homomorphism.
This is a more specialized version of `finsupp.prod_add_index` with simpler hypotheses. -/
@[to_additive
      "Taking the sum under `h` is an additive homomorphism of finsupps,\nif `h` is an additive homomorphism.\nThis is a more specific version of `finsupp.sum_add_index` with simpler hypotheses."]
theorem prod_add_index' [AddZeroClassₓ M] [CommMonoidₓ N] {f g : α →₀ M} {h : α → M → N} (h_zero : ∀ a, h a 0 = 1)
    (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) : (f + g).Prod h = f.Prod h * g.Prod h :=
  prod_add_index (fun a ha => h_zero a) fun a ha => h_add a

@[simp]
theorem sum_hom_add_index [AddZeroClassₓ M] [AddCommMonoidₓ N] {f g : α →₀ M} (h : α → M →+ N) :
    ((f + g).Sum fun x => h x) = (f.Sum fun x => h x) + g.Sum fun x => h x :=
  sum_add_index' (fun a => (h a).map_zero) fun a => (h a).map_add

@[simp]
theorem prod_hom_add_index [AddZeroClassₓ M] [CommMonoidₓ N] {f g : α →₀ M} (h : α → Multiplicative M →* N) :
    ((f + g).Prod fun a b => h a (Multiplicative.ofAdd b)) =
      (f.Prod fun a b => h a (Multiplicative.ofAdd b)) * g.Prod fun a b => h a (Multiplicative.ofAdd b) :=
  prod_add_index' (fun a => (h a).map_one) fun a => (h a).map_mul

/-- The canonical isomorphism between families of additive monoid homomorphisms `α → (M →+ N)`
and monoid homomorphisms `(α →₀ M) →+ N`. -/
def liftAddHom [AddZeroClassₓ M] [AddCommMonoidₓ N] : (α → M →+ N) ≃+ ((α →₀ M) →+ N) where
  toFun := fun F =>
    { toFun := fun f => f.Sum fun x => F x, map_zero' := Finset.sum_empty,
      map_add' := fun _ _ => sum_add_index' (fun x => (F x).map_zero) fun x => (F x).map_add }
  invFun := fun F x => F.comp <| singleAddHom x
  left_inv := fun F => by
    ext
    simp
  right_inv := fun F => by
    ext
    simp
  map_add' := fun F G => by
    ext
    simp

@[simp]
theorem lift_add_hom_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : α → M →+ N) (f : α →₀ M) :
    liftAddHom F f = f.Sum fun x => F x :=
  rfl

@[simp]
theorem lift_add_hom_symm_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : (α →₀ M) →+ N) (x : α) :
    liftAddHom.symm F x = F.comp (singleAddHom x) :=
  rfl

theorem lift_add_hom_symm_apply_apply [AddCommMonoidₓ M] [AddCommMonoidₓ N] (F : (α →₀ M) →+ N) (x : α) (y : M) :
    liftAddHom.symm F x y = F (single x y) :=
  rfl

@[simp]
theorem lift_add_hom_single_add_hom [AddCommMonoidₓ M] :
    liftAddHom (singleAddHom : α → M →+ α →₀ M) = AddMonoidHom.id _ :=
  liftAddHom.toEquiv.apply_eq_iff_eq_symm_apply.2 rfl

@[simp]
theorem sum_single [AddCommMonoidₓ M] (f : α →₀ M) : f.Sum single = f :=
  AddMonoidHom.congr_fun lift_add_hom_single_add_hom f

@[simp]
theorem sum_univ_single [AddCommMonoidₓ M] [Fintype α] (i : α) (m : M) : (∑ j : α, (single i m) j) = m := by
  simp [← single]

@[simp]
theorem sum_univ_single' [AddCommMonoidₓ M] [Fintype α] (i : α) (m : M) : (∑ j : α, (single j m) i) = m := by
  simp [← single]

@[simp]
theorem lift_add_hom_apply_single [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : α → M →+ N) (a : α) (b : M) :
    liftAddHom f (single a b) = f a b :=
  sum_single_index (f a).map_zero

@[simp]
theorem lift_add_hom_comp_single [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : α → M →+ N) (a : α) :
    (liftAddHom f).comp (singleAddHom a) = f a :=
  AddMonoidHom.ext fun b => lift_add_hom_apply_single f a b

theorem comp_lift_add_hom [AddCommMonoidₓ M] [AddCommMonoidₓ N] [AddCommMonoidₓ P] (g : N →+ P) (f : α → M →+ N) :
    g.comp (liftAddHom f) = liftAddHom fun a => g.comp (f a) :=
  liftAddHom.symm_apply_eq.1 <|
    funext fun a => by
      rw [lift_add_hom_symm_apply, AddMonoidHom.comp_assoc, lift_add_hom_comp_single]

theorem sum_sub_index [AddCommGroupₓ β] [AddCommGroupₓ γ] {f g : α →₀ β} {h : α → β → γ}
    (h_sub : ∀ a b₁ b₂, h a (b₁ - b₂) = h a b₁ - h a b₂) : (f - g).Sum h = f.Sum h - g.Sum h :=
  (liftAddHom fun a => AddMonoidHom.ofMapSub (h a) (h_sub a)).map_sub f g

@[to_additive]
theorem prod_emb_domain [Zero M] [CommMonoidₓ N] {v : α →₀ M} {f : α ↪ β} {g : β → M → N} :
    (v.embDomain f).Prod g = v.Prod fun a b => g (f a) b := by
  rw [Prod, Prod, support_emb_domain, Finset.prod_map]
  simp_rw [emb_domain_apply]

@[to_additive]
theorem prod_finset_sum_index [AddCommMonoidₓ M] [CommMonoidₓ N] {s : Finset ι} {g : ι → α →₀ M} {h : α → M → N}
    (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (∏ i in s, (g i).Prod h) = (∑ i in s, g i).Prod h :=
  (Finset.induction_on s rfl) fun a s has ih => by
    rw [prod_insert has, ih, sum_insert has, prod_add_index' h_zero h_add]

@[to_additive]
theorem prod_sum_index [AddCommMonoidₓ M] [AddCommMonoidₓ N] [CommMonoidₓ P] {f : α →₀ M} {g : α → M → β →₀ N}
    {h : β → N → P} (h_zero : ∀ a, h a 0 = 1) (h_add : ∀ a b₁ b₂, h a (b₁ + b₂) = h a b₁ * h a b₂) :
    (f.Sum g).Prod h = f.Prod fun a b => (g a b).Prod h :=
  (prod_finset_sum_index h_zero h_add).symm

theorem multiset_sum_sum_index [AddCommMonoidₓ M] [AddCommMonoidₓ N] (f : Multiset (α →₀ M)) (h : α → M → N)
    (h₀ : ∀ a, h a 0 = 0) (h₁ : ∀ (a : α) (b₁ b₂ : M), h a (b₁ + b₂) = h a b₁ + h a b₂) :
    f.Sum.Sum h = (f.map fun g : α →₀ M => g.Sum h).Sum :=
  (Multiset.induction_on f rfl) fun a s ih => by
    rw [Multiset.sum_cons, Multiset.map_cons, Multiset.sum_cons, sum_add_index' h₀ h₁, ih]

theorem support_sum_eq_bUnion {α : Type _} {ι : Type _} {M : Type _} [AddCommMonoidₓ M] {g : ι → α →₀ M} (s : Finset ι)
    (h : ∀ i₁ i₂, i₁ ≠ i₂ → Disjoint (g i₁).Support (g i₂).Support) :
    (∑ i in s, g i).Support = s.bUnion fun i => (g i).Support := by
  apply Finset.induction_on s
  · simp
    
  · intro i s hi
    simp only [← hi, ← sum_insert, ← not_false_iff, ← bUnion_insert]
    intro hs
    rw [Finsupp.support_add_eq, hs]
    rw [hs]
    intro x hx
    simp only [← mem_bUnion, ← exists_prop, ← inf_eq_inter, ← Ne.def, ← mem_inter] at hx
    obtain ⟨hxi, j, hj, hxj⟩ := hx
    have hn : i ≠ j := fun H => hi (H.symm ▸ hj)
    apply h _ _ hn
    simp [← hxi, ← hxj]
    

theorem multiset_map_sum [Zero M] {f : α →₀ M} {m : β → γ} {h : α → M → Multiset β} :
    Multiset.map m (f.Sum h) = f.Sum fun a b => (h a b).map m :=
  (Multiset.mapAddMonoidHom m).map_sum _ f.Support

theorem multiset_sum_sum [Zero M] [AddCommMonoidₓ N] {f : α →₀ M} {h : α → M → Multiset N} :
    Multiset.sum (f.Sum h) = f.Sum fun a b => Multiset.sum (h a b) :=
  (Multiset.sumAddMonoidHom : Multiset N →+ N).map_sum _ f.Support

/-- For disjoint `f1` and `f2`, and function `g`, the product of the products of `g`
over `f1` and `f2` equals the product of `g` over `f1 + f2` -/
@[to_additive
      "For disjoint `f1` and `f2`, and function `g`, the sum of the sums of `g`\nover `f1` and `f2` equals the sum of `g` over `f1 + f2`"]
theorem prod_add_index_of_disjoint [AddCommMonoidₓ M] {f1 f2 : α →₀ M} (hd : Disjoint f1.Support f2.Support)
    {β : Type _} [CommMonoidₓ β] (g : α → M → β) : (f1 + f2).Prod g = f1.Prod g * f2.Prod g := by
  have : ∀ {f1 f2 : α →₀ M}, Disjoint f1.Support f2.Support → (∏ x in f1.Support, g x (f1 x + f2 x)) = f1.Prod g :=
    fun f1 f2 hd =>
    Finset.prod_congr rfl fun x hx => by
      simp only [← not_mem_support_iff.mp (disjoint_left.mp hd hx), ← add_zeroₓ]
  simp_rw [← this hd, ← this hd.symm, add_commₓ (f2 _), Finsupp.prod, support_add_eq hd, prod_union hd, add_apply]

section MapRange

section Equivₓ

variable [Zero M] [Zero N] [Zero P]

/-- `finsupp.map_range` as an equiv. -/
@[simps apply]
def mapRange.equiv (f : M ≃ N) (hf : f 0 = 0) (hf' : f.symm 0 = 0) : (α →₀ M) ≃ (α →₀ N) where
  toFun := (mapRange f hf : (α →₀ M) → α →₀ N)
  invFun := (mapRange f.symm hf' : (α →₀ N) → α →₀ M)
  left_inv := fun x => by
    rw [← map_range_comp _ _ _ _] <;> simp_rw [Equivₓ.symm_comp_self]
    · exact map_range_id _
      
    · rfl
      
  right_inv := fun x => by
    rw [← map_range_comp _ _ _ _] <;> simp_rw [Equivₓ.self_comp_symm]
    · exact map_range_id _
      
    · rfl
      

@[simp]
theorem mapRange.equiv_refl : mapRange.equiv (Equivₓ.refl M) rfl rfl = Equivₓ.refl (α →₀ M) :=
  Equivₓ.ext map_range_id

theorem mapRange.equiv_trans (f : M ≃ N) (hf : f 0 = 0) (hf') (f₂ : N ≃ P) (hf₂ : f₂ 0 = 0) (hf₂') :
    (mapRange.equiv (f.trans f₂)
        (by
          rw [Equivₓ.trans_apply, hf, hf₂])
        (by
          rw [Equivₓ.symm_trans_apply, hf₂', hf']) :
        (α →₀ _) ≃ _) =
      (mapRange.equiv f hf hf').trans (mapRange.equiv f₂ hf₂ hf₂') :=
  Equivₓ.ext <| map_range_comp _ _ _ _ _

@[simp]
theorem mapRange.equiv_symm (f : M ≃ N) (hf hf') :
    ((mapRange.equiv f hf hf').symm : (α →₀ _) ≃ _) = mapRange.equiv f.symm hf' hf :=
  Equivₓ.ext fun x => rfl

end Equivₓ

section ZeroHom

variable [Zero M] [Zero N] [Zero P]

/-- Composition with a fixed zero-preserving homomorphism is itself an zero-preserving homomorphism
on functions. -/
@[simps]
def mapRange.zeroHom (f : ZeroHom M N) : ZeroHom (α →₀ M) (α →₀ N) where
  toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
  map_zero' := map_range_zero

@[simp]
theorem mapRange.zero_hom_id : mapRange.zeroHom (ZeroHom.id M) = ZeroHom.id (α →₀ M) :=
  ZeroHom.ext map_range_id

theorem mapRange.zero_hom_comp (f : ZeroHom N P) (f₂ : ZeroHom M N) :
    (mapRange.zeroHom (f.comp f₂) : ZeroHom (α →₀ _) _) = (mapRange.zeroHom f).comp (mapRange.zeroHom f₂) :=
  ZeroHom.ext <| map_range_comp _ _ _ _ _

end ZeroHom

section AddMonoidHom

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [AddCommMonoidₓ P]

/-- Composition with a fixed additive homomorphism is itself an additive homomorphism on functions.
-/
@[simps]
def mapRange.addMonoidHom (f : M →+ N) : (α →₀ M) →+ α →₀ N where
  toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N)
  map_zero' := map_range_zero
  map_add' := fun a b => map_range_add f.map_add _ _

@[simp]
theorem mapRange.add_monoid_hom_id : mapRange.addMonoidHom (AddMonoidHom.id M) = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext map_range_id

theorem mapRange.add_monoid_hom_comp (f : N →+ P) (f₂ : M →+ N) :
    (mapRange.addMonoidHom (f.comp f₂) : (α →₀ _) →+ _) = (mapRange.addMonoidHom f).comp (mapRange.addMonoidHom f₂) :=
  AddMonoidHom.ext <| map_range_comp _ _ _ _ _

@[simp]
theorem mapRange.add_monoid_hom_to_zero_hom (f : M →+ N) :
    (mapRange.addMonoidHom f).toZeroHom = (mapRange.zeroHom f.toZeroHom : ZeroHom (α →₀ _) _) :=
  ZeroHom.ext fun _ => rfl

theorem map_range_multiset_sum (f : M →+ N) (m : Multiset (α →₀ M)) :
    mapRange f f.map_zero m.Sum = (m.map fun x => mapRange f f.map_zero x).Sum :=
  (mapRange.addMonoidHom f : (α →₀ _) →+ _).map_multiset_sum _

theorem map_range_finset_sum (f : M →+ N) (s : Finset ι) (g : ι → α →₀ M) :
    mapRange f f.map_zero (∑ x in s, g x) = ∑ x in s, mapRange f f.map_zero (g x) :=
  (mapRange.addMonoidHom f : (α →₀ _) →+ _).map_sum _ _

/-- `finsupp.map_range.add_monoid_hom` as an equiv. -/
@[simps apply]
def mapRange.addEquiv (f : M ≃+ N) : (α →₀ M) ≃+ (α →₀ N) :=
  { mapRange.addMonoidHom f.toAddMonoidHom with toFun := (mapRange f f.map_zero : (α →₀ M) → α →₀ N),
    invFun := (mapRange f.symm f.symm.map_zero : (α →₀ N) → α →₀ M),
    left_inv := fun x => by
      rw [← map_range_comp _ _ _ _] <;> simp_rw [AddEquiv.symm_comp_self]
      · exact map_range_id _
        
      · rfl
        ,
    right_inv := fun x => by
      rw [← map_range_comp _ _ _ _] <;> simp_rw [AddEquiv.self_comp_symm]
      · exact map_range_id _
        
      · rfl
         }

@[simp]
theorem mapRange.add_equiv_refl : mapRange.addEquiv (AddEquiv.refl M) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext map_range_id

theorem mapRange.add_equiv_trans (f : M ≃+ N) (f₂ : N ≃+ P) :
    (mapRange.addEquiv (f.trans f₂) : (α →₀ _) ≃+ _) = (mapRange.addEquiv f).trans (mapRange.addEquiv f₂) :=
  AddEquiv.ext <| map_range_comp _ _ _ _ _

@[simp]
theorem mapRange.add_equiv_symm (f : M ≃+ N) :
    ((mapRange.addEquiv f).symm : (α →₀ _) ≃+ _) = mapRange.addEquiv f.symm :=
  AddEquiv.ext fun x => rfl

@[simp]
theorem mapRange.add_equiv_to_add_monoid_hom (f : M ≃+ N) :
    (mapRange.addEquiv f : (α →₀ _) ≃+ _).toAddMonoidHom = (mapRange.addMonoidHom f.toAddMonoidHom : (α →₀ _) →+ _) :=
  AddMonoidHom.ext fun _ => rfl

@[simp]
theorem mapRange.add_equiv_to_equiv (f : M ≃+ N) :
    (mapRange.addEquiv f).toEquiv = (mapRange.equiv f.toEquiv f.map_zero f.symm.map_zero : (α →₀ _) ≃ _) :=
  Equivₓ.ext fun _ => rfl

end AddMonoidHom

end MapRange

/-! ### Declarations about `map_domain` -/


section MapDomain

variable [AddCommMonoidₓ M] {v v₁ v₂ : α →₀ M}

/-- Given `f : α → β` and `v : α →₀ M`, `map_domain f v : β →₀ M`
  is the finitely supported function whose value at `a : β` is the sum
  of `v x` over all `x` such that `f x = a`. -/
def mapDomain (f : α → β) (v : α →₀ M) : β →₀ M :=
  v.Sum fun a => single (f a)

theorem map_domain_apply {f : α → β} (hf : Function.Injective f) (x : α →₀ M) (a : α) : mapDomain f x (f a) = x a := by
  rw [map_domain, sum_apply, Sum, Finset.sum_eq_single a, single_eq_same]
  · intro b _ hba
    exact single_eq_of_ne (hf.ne hba)
    
  · intro h
    rw [not_mem_support_iff.1 h, single_zero, zero_apply]
    

theorem map_domain_notin_range {f : α → β} (x : α →₀ M) (a : β) (h : a ∉ Set.Range f) : mapDomain f x a = 0 := by
  rw [map_domain, sum_apply, Sum]
  exact Finset.sum_eq_zero fun a' h' => single_eq_of_ne fun eq => h <| Eq ▸ Set.mem_range_self _

@[simp]
theorem map_domain_id : mapDomain id v = v :=
  sum_single _

theorem map_domain_comp {f : α → β} {g : β → γ} : mapDomain (g ∘ f) v = mapDomain g (mapDomain f v) := by
  refine' ((sum_sum_index _ _).trans _).symm
  · intro
    exact single_zero _
    
  · intro
    exact single_add _
    
  refine' sum_congr fun _ _ => sum_single_index _
  · exact single_zero _
    

@[simp]
theorem map_domain_single {f : α → β} {a : α} {b : M} : mapDomain f (single a b) = single (f a) b :=
  sum_single_index <| single_zero _

@[simp]
theorem map_domain_zero {f : α → β} : mapDomain f (0 : α →₀ M) = (0 : β →₀ M) :=
  sum_zero_index

theorem map_domain_congr {f g : α → β} (h : ∀, ∀ x ∈ v.Support, ∀, f x = g x) : v.mapDomain f = v.mapDomain g :=
  (Finset.sum_congr rfl) fun _ H => by
    simp only [← h _ H]

theorem map_domain_add {f : α → β} : mapDomain f (v₁ + v₂) = mapDomain f v₁ + mapDomain f v₂ :=
  sum_add_index' (fun _ => single_zero _) fun _ => single_add _

@[simp]
theorem map_domain_equiv_apply {f : α ≃ β} (x : α →₀ M) (a : β) : mapDomain f x a = x (f.symm a) := by
  conv_lhs => rw [← f.apply_symm_apply a]
  exact map_domain_apply f.injective _ _

/-- `finsupp.map_domain` is an `add_monoid_hom`. -/
@[simps]
def mapDomain.addMonoidHom (f : α → β) : (α →₀ M) →+ β →₀ M where
  toFun := mapDomain f
  map_zero' := map_domain_zero
  map_add' := fun _ _ => map_domain_add

@[simp]
theorem mapDomain.add_monoid_hom_id : mapDomain.addMonoidHom id = AddMonoidHom.id (α →₀ M) :=
  AddMonoidHom.ext fun _ => map_domain_id

theorem mapDomain.add_monoid_hom_comp (f : β → γ) (g : α → β) :
    (mapDomain.addMonoidHom (f ∘ g) : (α →₀ M) →+ γ →₀ M) =
      (mapDomain.addMonoidHom f).comp (mapDomain.addMonoidHom g) :=
  AddMonoidHom.ext fun _ => map_domain_comp

theorem map_domain_finset_sum {f : α → β} {s : Finset ι} {v : ι → α →₀ M} :
    mapDomain f (∑ i in s, v i) = ∑ i in s, mapDomain f (v i) :=
  (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M).map_sum _ _

theorem map_domain_sum [Zero N] {f : α → β} {s : α →₀ N} {v : α → N → α →₀ M} :
    mapDomain f (s.Sum v) = s.Sum fun a b => mapDomain f (v a b) :=
  (mapDomain.addMonoidHom f : (α →₀ M) →+ β →₀ M).map_finsupp_sum _ _

theorem map_domain_support [DecidableEq β] {f : α → β} {s : α →₀ M} : (s.mapDomain f).Support ⊆ s.Support.Image f :=
  Finset.Subset.trans support_sum <|
    Finset.Subset.trans (Finset.bUnion_mono fun a ha => support_single_subset) <| by
      rw [Finset.bUnion_singleton] <;> exact subset.refl _

theorem map_domain_apply' (S : Set α) {f : α → β} (x : α →₀ M) (hS : (x.Support : Set α) ⊆ S) (hf : Set.InjOn f S)
    {a : α} (ha : a ∈ S) : mapDomain f x (f a) = x a := by
  rw [map_domain, sum_apply, Sum]
  simp_rw [single_apply]
  have : ∀ (b : α) (ha1 : b ∈ x.support), (if f b = f a then x b else 0) = if f b = f a then x a else 0 := by
    intro b hb
    refine' if_ctx_congr Iff.rfl (fun hh => _) fun _ => rfl
    rw [hf (hS hb) ha hh]
  conv in ite _ _ _ => rw [this _ H]
  by_cases' ha : a ∈ x.support
  · rw [← Finset.add_sum_erase _ _ ha, if_pos rfl]
    convert add_zeroₓ _
    have : ∀, ∀ i ∈ x.support.erase a, ∀, f i ≠ f a := by
      intro i hi
      exact Finset.ne_of_mem_erase hi ∘ hf (hS <| Finset.mem_of_mem_erase hi) (hS ha)
    conv in ite _ _ _ => rw [if_neg (this x H)]
    exact Finset.sum_const_zero
    
  · rw [mem_support_iff, not_not] at ha
    simp [← ha]
    

theorem map_domain_support_of_inj_on [DecidableEq β] {f : α → β} (s : α →₀ M) (hf : Set.InjOn f s.Support) :
    (mapDomain f s).Support = Finset.image f s.Support :=
  Finset.Subset.antisymm map_domain_support <| by
    intro x hx
    simp only [← mem_image, ← exists_prop, ← mem_support_iff, ← Ne.def] at hx
    rcases hx with ⟨hx_w, hx_h_left, rfl⟩
    simp only [← mem_support_iff, ← Ne.def]
    rw [map_domain_apply' (↑s.support : Set _) _ _ hf]
    · exact hx_h_left
      
    · simp only [← mem_coe, ← mem_support_iff, ← Ne.def]
      exact hx_h_left
      
    · exact subset.refl _
      

theorem map_domain_support_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f) (s : α →₀ M) :
    (mapDomain f s).Support = Finset.image f s.Support :=
  map_domain_support_of_inj_on s (hf.InjOn _)

@[to_additive]
theorem prod_map_domain_index [CommMonoidₓ N] {f : α → β} {s : α →₀ M} {h : β → M → N} (h_zero : ∀ b, h b 0 = 1)
    (h_add : ∀ b m₁ m₂, h b (m₁ + m₂) = h b m₁ * h b m₂) : (mapDomain f s).Prod h = s.Prod fun a m => h (f a) m :=
  (prod_sum_index h_zero h_add).trans <| prod_congr fun _ _ => prod_single_index (h_zero _)

/-- A version of `sum_map_domain_index` that takes a bundled `add_monoid_hom`,
rather than separate linearity hypotheses.
-/
-- Note that in `prod_map_domain_index`, `M` is still an additive monoid,
-- so there is no analogous version in terms of `monoid_hom`.
@[simp]
theorem sum_map_domain_index_add_monoid_hom [AddCommMonoidₓ N] {f : α → β} {s : α →₀ M} (h : β → M →+ N) :
    ((mapDomain f s).Sum fun b m => h b m) = s.Sum fun a m => h (f a) m :=
  @sum_map_domain_index _ _ _ _ _ _ _ _ (fun b m => h b m) (fun b => (h b).map_zero) fun b m₁ m₂ => (h b).map_add _ _

theorem emb_domain_eq_map_domain (f : α ↪ β) (v : α →₀ M) : embDomain f v = mapDomain f v := by
  ext a
  by_cases' a ∈ Set.Range f
  · rcases h with ⟨a, rfl⟩
    rw [map_domain_apply f.injective, emb_domain_apply]
    
  · rw [map_domain_notin_range, emb_domain_notin_range] <;> assumption
    

@[to_additive]
theorem prod_map_domain_index_inj [CommMonoidₓ N] {f : α → β} {s : α →₀ M} {h : β → M → N} (hf : Function.Injective f) :
    (s.mapDomain f).Prod h = s.Prod fun a b => h (f a) b := by
  rw [← Function.Embedding.coe_fn_mk f hf, ← emb_domain_eq_map_domain, prod_emb_domain]

theorem map_domain_injective {f : α → β} (hf : Function.Injective f) :
    Function.Injective (mapDomain f : (α →₀ M) → β →₀ M) := by
  intro v₁ v₂ eq
  ext a
  have : map_domain f v₁ (f a) = map_domain f v₂ (f a) := by
    rw [Eq]
  rwa [map_domain_apply hf, map_domain_apply hf] at this

/-- When `f` is an embedding we have an embedding `(α →₀ ℕ)  ↪ (β →₀ ℕ)` given by `map_domain`. -/
@[simps]
def mapDomainEmbedding {α β : Type _} (f : α ↪ β) : (α →₀ ℕ) ↪ β →₀ ℕ :=
  ⟨Finsupp.mapDomain f, Finsupp.map_domain_injective f.Injective⟩

theorem mapDomain.add_monoid_hom_comp_map_range [AddCommMonoidₓ N] (f : α → β) (g : M →+ N) :
    (mapDomain.addMonoidHom f).comp (mapRange.addMonoidHom g) =
      (mapRange.addMonoidHom g).comp (mapDomain.addMonoidHom f) :=
  by
  ext
  simp

/-- When `g` preserves addition, `map_range` and `map_domain` commute. -/
theorem map_domain_map_range [AddCommMonoidₓ N] (f : α → β) (v : α →₀ M) (g : M → N) (h0 : g 0 = 0)
    (hadd : ∀ x y, g (x + y) = g x + g y) : mapDomain f (mapRange g h0 v) = mapRange g h0 (mapDomain f v) :=
  let g' : M →+ N := { toFun := g, map_zero' := h0, map_add' := hadd }
  AddMonoidHom.congr_fun (mapDomain.add_monoid_hom_comp_map_range f g') v

theorem sum_update_add [AddCommMonoidₓ α] [AddCommMonoidₓ β] (f : ι →₀ α) (i : ι) (a : α) (g : ι → α → β)
    (hg : ∀ i, g i 0 = 0) (hgg : ∀ (j : ι) (a₁ a₂ : α), g j (a₁ + a₂) = g j a₁ + g j a₂) :
    (f.update i a).Sum g + g i (f i) = f.Sum g + g i a := by
  rw [update_eq_erase_add_single, sum_add_index' hg hgg]
  conv_rhs => rw [← Finsupp.update_self f i]
  rw [update_eq_erase_add_single, sum_add_index' hg hgg, add_assocₓ, add_assocₓ]
  congr 1
  rw [add_commₓ, sum_single_index (hg _), sum_single_index (hg _)]

theorem map_domain_inj_on (S : Set α) {f : α → β} (hf : Set.InjOn f S) :
    Set.InjOn (mapDomain f : (α →₀ M) → β →₀ M) { w | (w.Support : Set α) ⊆ S } := by
  intro v₁ hv₁ v₂ hv₂ eq
  ext a
  by_cases' h : a ∈ v₁.support ∪ v₂.support
  · rw [← map_domain_apply' S _ hv₁ hf _, ← map_domain_apply' S _ hv₂ hf _, Eq] <;>
      · apply Set.union_subset hv₁ hv₂
        exact_mod_cast h
        
    
  · simp only [← Decidable.not_or_iff_and_not, ← mem_union, ← not_not, ← mem_support_iff] at h
    simp [← h]
    

end MapDomain

/-! ### Declarations about `comap_domain` -/


section ComapDomain

/-- Given `f : α → β`, `l : β →₀ M` and a proof `hf` that `f` is injective on
the preimage of `l.support`, `comap_domain f l hf` is the finitely supported function
from `α` to `M` given by composing `l` with `f`. -/
@[simps Support]
def comapDomain [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.Support)) : α →₀ M where
  Support := l.Support.Preimage f hf
  toFun := fun a => l (f a)
  mem_support_to_fun := by
    intro a
    simp only [← finset.mem_def.symm, ← Finset.mem_preimage]
    exact l.mem_support_to_fun (f a)

@[simp]
theorem comap_domain_apply [Zero M] (f : α → β) (l : β →₀ M) (hf : Set.InjOn f (f ⁻¹' ↑l.Support)) (a : α) :
    comapDomain f l hf a = l (f a) :=
  rfl

theorem sum_comap_domain [Zero M] [AddCommMonoidₓ N] (f : α → β) (l : β →₀ M) (g : β → M → N)
    (hf : Set.BijOn f (f ⁻¹' ↑l.Support) ↑l.Support) : (comapDomain f l hf.InjOn).Sum (g ∘ f) = l.Sum g := by
  simp only [← Sum, ← comap_domain_apply, ← (· ∘ ·)]
  simp [← comap_domain, ← Finset.sum_preimage_of_bij f _ _ fun x => g x (l x)]

theorem eq_zero_of_comap_domain_eq_zero [AddCommMonoidₓ M] (f : α → β) (l : β →₀ M)
    (hf : Set.BijOn f (f ⁻¹' ↑l.Support) ↑l.Support) : comapDomain f l hf.InjOn = 0 → l = 0 := by
  rw [← support_eq_empty, ← support_eq_empty, comap_domain]
  simp only [← Finset.ext_iff, ← Finset.not_mem_empty, ← iff_falseₓ, ← mem_preimage]
  intro h a ha
  cases' hf.2.2 ha with b hb
  exact h b (hb.2.symm ▸ ha)

section FInjective

section Zero

variable [Zero M]

/-- Note the `hif` argument is needed for this to work in `rw`. -/
@[simp]
theorem comap_domain_zero (f : α → β) (hif : Set.InjOn f (f ⁻¹' ↑(0 : β →₀ M).Support) := Set.inj_on_empty _) :
    comapDomain f (0 : β →₀ M) hif = (0 : α →₀ M) := by
  ext
  rfl

@[simp]
theorem comap_domain_single (f : α → β) (a : α) (m : M) (hif : Set.InjOn f (f ⁻¹' (single (f a) m).Support)) :
    comapDomain f (Finsupp.single (f a) m) hif = Finsupp.single a m := by
  rcases eq_or_ne m 0 with (rfl | hm)
  · simp only [← single_zero, ← comap_domain_zero]
    
  · rw [eq_single_iff, comap_domain_apply, comap_domain_support, ← Finset.coe_subset, coe_preimage,
      support_single_ne_zero _ hm, coe_singleton, coe_singleton, single_eq_same]
    rw [support_single_ne_zero _ hm, coe_singleton] at hif
    exact ⟨fun x hx => hif hx rfl hx, rfl⟩
    

end Zero

section AddZeroClassₓ

variable [AddZeroClassₓ M] {f : α → β}

theorem comap_domain_add (v₁ v₂ : β →₀ M) (hv₁ : Set.InjOn f (f ⁻¹' ↑v₁.Support))
    (hv₂ : Set.InjOn f (f ⁻¹' ↑v₂.Support)) (hv₁₂ : Set.InjOn f (f ⁻¹' ↑(v₁ + v₂).Support)) :
    comapDomain f (v₁ + v₂) hv₁₂ = comapDomain f v₁ hv₁ + comapDomain f v₂ hv₂ := by
  ext
  simp only [← comap_domain_apply, ← coe_add, ← Pi.add_apply]

/-- A version of `finsupp.comap_domain_add` that's easier to use. -/
theorem comap_domain_add_of_injective (hf : Function.Injective f) (v₁ v₂ : β →₀ M) :
    comapDomain f (v₁ + v₂) (hf.InjOn _) = comapDomain f v₁ (hf.InjOn _) + comapDomain f v₂ (hf.InjOn _) :=
  comap_domain_add _ _ _ _ _

/-- `finsupp.comap_domain` is an `add_monoid_hom`. -/
@[simps]
def comapDomain.addMonoidHom (hf : Function.Injective f) : (β →₀ M) →+ α →₀ M where
  toFun := fun x => comapDomain f x (hf.InjOn _)
  map_zero' := comap_domain_zero f
  map_add' := comap_domain_add_of_injective hf

end AddZeroClassₓ

variable [AddCommMonoidₓ M] (f : α → β)

theorem map_domain_comap_domain (hf : Function.Injective f) (l : β →₀ M) (hl : ↑l.Support ⊆ Set.Range f) :
    mapDomain f (comapDomain f l (hf.InjOn _)) = l := by
  ext a
  by_cases' h_cases : a ∈ Set.Range f
  · rcases Set.mem_range.1 h_cases with ⟨b, hb⟩
    rw [hb.symm, map_domain_apply hf, comap_domain_apply]
    
  · rw [map_domain_notin_range _ _ h_cases]
    by_contra h_contr
    apply h_cases (hl <| Finset.mem_coe.2 <| mem_support_iff.2 fun h => h_contr h.symm)
    

end FInjective

end ComapDomain

section Option

/-- Restrict a finitely supported function on `option α` to a finitely supported function on `α`. -/
def some [Zero M] (f : Option α →₀ M) : α →₀ M :=
  f.comapDomain Option.some fun _ => by
    simp

@[simp]
theorem some_apply [Zero M] (f : Option α →₀ M) (a : α) : f.some a = f (Option.some a) :=
  rfl

@[simp]
theorem some_zero [Zero M] : (0 : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_add [AddCommMonoidₓ M] (f g : Option α →₀ M) : (f + g).some = f.some + g.some := by
  ext
  simp

@[simp]
theorem some_single_none [Zero M] (m : M) : (single none m : Option α →₀ M).some = 0 := by
  ext
  simp

@[simp]
theorem some_single_some [Zero M] (a : α) (m : M) : (single (Option.some a) m : Option α →₀ M).some = single a m := by
  ext b
  simp [← single_apply]

@[to_additive]
theorem prod_option_index [AddCommMonoidₓ M] [CommMonoidₓ N] (f : Option α →₀ M) (b : Option α → M → N)
    (h_zero : ∀ o, b o 0 = 1) (h_add : ∀ o m₁ m₂, b o (m₁ + m₂) = b o m₁ * b o m₂) :
    f.Prod b = b none (f none) * f.some.Prod fun a => b (Option.some a) := by
  apply induction_linear f
  · simp [← h_zero]
    
  · intro f₁ f₂ h₁ h₂
    rw [Finsupp.prod_add_index, h₁, h₂, some_add, Finsupp.prod_add_index]
    simp only [← h_add, ← Pi.add_apply, ← Finsupp.coe_add]
    rw [mul_mul_mul_commₓ]
    all_goals
      simp [← h_zero, ← h_add]
    
  · rintro (_ | a) m <;> simp [← h_zero, ← h_add]
    

theorem sum_option_index_smul [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] (f : Option α →₀ R) (b : Option α → M) :
    (f.Sum fun o r => r • b o) = f none • b none + f.some.Sum fun a r => r • b (Option.some a) :=
  f.sum_option_index _ (fun _ => zero_smul _ _) fun _ _ _ => add_smul _ _ _

end Option

/-! ### Declarations about `equiv_congr_left` -/


section EquivCongrLeft

variable [Zero M]

/-- Given `f : α ≃ β`, we can map `l : α →₀ M` to  `equiv_map_domain f l : β →₀ M` (computably)
by mapping the support forwards and the function backwards. -/
def equivMapDomain (f : α ≃ β) (l : α →₀ M) : β →₀ M where
  Support := l.Support.map f.toEmbedding
  toFun := fun a => l (f.symm a)
  mem_support_to_fun := fun a => by
    simp only [← Finset.mem_map_equiv, ← mem_support_to_fun] <;> rfl

@[simp]
theorem equiv_map_domain_apply (f : α ≃ β) (l : α →₀ M) (b : β) : equivMapDomain f l b = l (f.symm b) :=
  rfl

theorem equiv_map_domain_symm_apply (f : α ≃ β) (l : β →₀ M) (a : α) : equivMapDomain f.symm l a = l (f a) :=
  rfl

@[simp]
theorem equiv_map_domain_refl (l : α →₀ M) : equivMapDomain (Equivₓ.refl _) l = l := by
  ext x <;> rfl

theorem equiv_map_domain_refl' : equivMapDomain (Equivₓ.refl _) = @id (α →₀ M) := by
  ext x <;> rfl

theorem equiv_map_domain_trans (f : α ≃ β) (g : β ≃ γ) (l : α →₀ M) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by
  ext x <;> rfl

theorem equiv_map_domain_trans' (f : α ≃ β) (g : β ≃ γ) :
    @equivMapDomain _ _ M _ (f.trans g) = equivMapDomain g ∘ equivMapDomain f := by
  ext x <;> rfl

@[simp]
theorem equiv_map_domain_single (f : α ≃ β) (a : α) (b : M) : equivMapDomain f (single a b) = single (f a) b := by
  ext x <;> simp only [← single_apply, ← Equivₓ.apply_eq_iff_eq_symm_apply, ← equiv_map_domain_apply] <;> congr

@[simp]
theorem equiv_map_domain_zero {f : α ≃ β} : equivMapDomain f (0 : α →₀ M) = (0 : β →₀ M) := by
  ext x <;> simp only [← equiv_map_domain_apply, ← coe_zero, ← Pi.zero_apply]

theorem equiv_map_domain_eq_map_domain {M} [AddCommMonoidₓ M] (f : α ≃ β) (l : α →₀ M) :
    equivMapDomain f l = mapDomain f l := by
  ext x <;> simp [← map_domain_equiv_apply]

/-- Given `f : α ≃ β`, the finitely supported function spaces are also in bijection:
`(α →₀ M) ≃ (β →₀ M)`.

This is the finitely-supported version of `equiv.Pi_congr_left`. -/
def equivCongrLeft (f : α ≃ β) : (α →₀ M) ≃ (β →₀ M) := by
  refine' ⟨equiv_map_domain f, equiv_map_domain f.symm, fun f => _, fun f => _⟩ <;>
    ext x <;>
      simp only [← equiv_map_domain_apply, ← Equivₓ.symm_symm, ← Equivₓ.symm_apply_apply, ← Equivₓ.apply_symm_apply]

@[simp]
theorem equiv_congr_left_apply (f : α ≃ β) (l : α →₀ M) : equivCongrLeft f l = equivMapDomain f l :=
  rfl

@[simp]
theorem equiv_congr_left_symm (f : α ≃ β) : (@equivCongrLeft _ _ M _ f).symm = equivCongrLeft f.symm :=
  rfl

end EquivCongrLeft

/-! ### Declarations about `filter` -/


section Filter

section Zero

variable [Zero M] (p : α → Prop) (f : α →₀ M)

/-- `filter p f` is the function which is `f a` if `p a` is true and 0 otherwise. -/
def filter (p : α → Prop) (f : α →₀ M) : α →₀ M where
  toFun := fun a => if p a then f a else 0
  Support := f.Support.filter fun a => p a
  mem_support_to_fun := fun a => by
    split_ifs <;>
      · simp only [← h, ← mem_filter, ← mem_support_iff]
        tauto
        

theorem filter_apply (a : α) [D : Decidable (p a)] : f.filter p a = if p a then f a else 0 := by
  rw [Subsingleton.elimₓ D] <;> rfl

theorem filter_eq_indicator : ⇑(f.filter p) = Set.indicatorₓ { x | p x } f :=
  rfl

theorem filter_eq_zero_iff : f.filter p = 0 ↔ ∀ x, p x → f x = 0 := by
  simp only [← FunLike.ext_iff, ← filter_eq_indicator, ← zero_apply, ← Set.indicator_apply_eq_zero, ← Set.mem_set_of_eq]

theorem filter_eq_self_iff : f.filter p = f ↔ ∀ x, f x ≠ 0 → p x := by
  simp only [← FunLike.ext_iff, ← filter_eq_indicator, ← Set.indicator_apply_eq_self, ← Set.mem_set_of_eq, ←
    not_imp_comm]

@[simp]
theorem filter_apply_pos {a : α} (h : p a) : f.filter p a = f a :=
  if_pos h

@[simp]
theorem filter_apply_neg {a : α} (h : ¬p a) : f.filter p a = 0 :=
  if_neg h

@[simp]
theorem support_filter [D : DecidablePred p] : (f.filter p).Support = f.Support.filter p := by
  rw [Subsingleton.elimₓ D] <;> rfl

theorem filter_zero : (0 : α →₀ M).filter p = 0 := by
  rw [← support_eq_empty, support_filter, support_zero, Finset.filter_empty]

@[simp]
theorem filter_single_of_pos {a : α} {b : M} (h : p a) : (single a b).filter p = single a b :=
  (filter_eq_self_iff _ _).2 fun x hx => (single_apply_ne_zero.1 hx).1.symm ▸ h

@[simp]
theorem filter_single_of_neg {a : α} {b : M} (h : ¬p a) : (single a b).filter p = 0 :=
  (filter_eq_zero_iff _ _).2 fun x hpx => single_apply_eq_zero.2 fun hxa => absurd hpx (hxa.symm ▸ h)

@[to_additive]
theorem prod_filter_index [CommMonoidₓ N] (g : α → M → N) :
    (f.filter p).Prod g = ∏ x in (f.filter p).Support, g x (f x) := by
  refine' Finset.prod_congr rfl fun x hx => _
  rw [support_filter, Finset.mem_filter] at hx
  rw [filter_apply_pos _ _ hx.2]

@[simp, to_additive]
theorem prod_filter_mul_prod_filter_not [CommMonoidₓ N] (g : α → M → N) :
    (f.filter p).Prod g * (f.filter fun a => ¬p a).Prod g = f.Prod g := by
  simp_rw [prod_filter_index, support_filter, prod_filter_mul_prod_filter_not, Finsupp.prod]

@[simp, to_additive]
theorem prod_div_prod_filter [CommGroupₓ G] (g : α → M → G) :
    f.Prod g / (f.filter p).Prod g = (f.filter fun a => ¬p a).Prod g :=
  div_eq_of_eq_mul' (prod_filter_mul_prod_filter_not _ _ _).symm

end Zero

theorem filter_pos_add_filter_neg [AddZeroClassₓ M] (f : α →₀ M) (p : α → Prop) :
    (f.filter p + f.filter fun a => ¬p a) = f :=
  coe_fn_injective <| Set.indicator_self_add_compl { x | p x } f

end Filter

/-! ### Declarations about `frange` -/


section Frange

variable [Zero M]

/-- `frange f` is the image of `f` on the support of `f`. -/
def frange (f : α →₀ M) : Finset M :=
  Finset.image f f.Support

theorem mem_frange {f : α →₀ M} {y : M} : y ∈ f.frange ↔ y ≠ 0 ∧ ∃ x, f x = y :=
  Finset.mem_image.trans
    ⟨fun ⟨x, hx1, hx2⟩ => ⟨hx2 ▸ mem_support_iff.1 hx1, x, hx2⟩, fun ⟨hy, x, hx⟩ =>
      ⟨x, mem_support_iff.2 (hx.symm ▸ hy), hx⟩⟩

theorem zero_not_mem_frange {f : α →₀ M} : (0 : M) ∉ f.frange := fun H => (mem_frange.1 H).1 rfl

theorem frange_single {x : α} {y : M} : frange (single x y) ⊆ {y} := fun r hr =>
  let ⟨t, ht1, ht2⟩ := mem_frange.1 hr
  ht2 ▸ by
    rw [single_apply] at ht2⊢ <;> split_ifs  at ht2⊢ <;> [exact Finset.mem_singleton_self _, cc]

end Frange

/-! ### Declarations about `subtype_domain` -/


section SubtypeDomain

section Zero

variable [Zero M] {p : α → Prop}

/-- `subtype_domain p f` is the restriction of the finitely supported function
  `f` to the subtype `p`. -/
def subtypeDomain (p : α → Prop) (f : α →₀ M) : Subtype p →₀ M :=
  ⟨f.Support.Subtype p, f ∘ coe, fun a => by
    simp only [← mem_subtype, ← mem_support_iff]⟩

@[simp]
theorem support_subtype_domain [D : DecidablePred p] {f : α →₀ M} : (subtypeDomain p f).Support = f.Support.Subtype p :=
  by
  rw [Subsingleton.elimₓ D] <;> rfl

@[simp]
theorem subtype_domain_apply {a : Subtype p} {v : α →₀ M} : (subtypeDomain p v) a = v a.val :=
  rfl

@[simp]
theorem subtype_domain_zero : subtypeDomain p (0 : α →₀ M) = 0 :=
  rfl

theorem subtype_domain_eq_zero_iff' {f : α →₀ M} : f.subtypeDomain p = 0 ↔ ∀ x, p x → f x = 0 := by
  simp_rw [← support_eq_empty, support_subtype_domain, subtype_eq_empty, not_mem_support_iff]

theorem subtype_domain_eq_zero_iff {f : α →₀ M} (hf : ∀, ∀ x ∈ f.Support, ∀, p x) : f.subtypeDomain p = 0 ↔ f = 0 :=
  subtype_domain_eq_zero_iff'.trans
    ⟨fun H => ext fun x => if hx : p x then H x hx else not_mem_support_iff.1 <| mt (hf x) hx, fun H x _ => by
      simp [← H]⟩

@[to_additive]
theorem prod_subtype_domain_index [CommMonoidₓ N] {v : α →₀ M} {h : α → M → N} (hp : ∀, ∀ x ∈ v.Support, ∀, p x) :
    ((v.subtypeDomain p).Prod fun a b => h a b) = v.Prod h :=
  prod_bij (fun p _ => p.val) (fun _ => mem_subtype.1) (fun _ _ => rfl) (fun _ _ _ _ => Subtype.eq) fun b hb =>
    ⟨⟨b, hp b hb⟩, mem_subtype.2 hb, rfl⟩

end Zero

section AddZeroClassₓ

variable [AddZeroClassₓ M] {p : α → Prop} {v v' : α →₀ M}

@[simp]
theorem subtype_domain_add {v v' : α →₀ M} : (v + v').subtypeDomain p = v.subtypeDomain p + v'.subtypeDomain p :=
  ext fun _ => rfl

/-- `subtype_domain` but as an `add_monoid_hom`. -/
def subtypeDomainAddMonoidHom : (α →₀ M) →+ Subtype p →₀ M where
  toFun := subtypeDomain p
  map_zero' := subtype_domain_zero
  map_add' := fun _ _ => subtype_domain_add

/-- `finsupp.filter` as an `add_monoid_hom`. -/
def filterAddHom (p : α → Prop) : (α →₀ M) →+ α →₀ M where
  toFun := filter p
  map_zero' := filter_zero p
  map_add' := fun f g => coe_fn_injective <| Set.indicator_add { x | p x } f g

@[simp]
theorem filter_add {v v' : α →₀ M} : (v + v').filter p = v.filter p + v'.filter p :=
  (filterAddHom p).map_add v v'

end AddZeroClassₓ

section CommMonoidₓ

variable [AddCommMonoidₓ M] {p : α → Prop}

theorem subtype_domain_sum {s : Finset ι} {h : ι → α →₀ M} :
    (∑ c in s, h c).subtypeDomain p = ∑ c in s, (h c).subtypeDomain p :=
  (subtypeDomainAddMonoidHom : _ →+ Subtype p →₀ M).map_sum _ s

theorem subtype_domain_finsupp_sum [Zero N] {s : β →₀ N} {h : β → N → α →₀ M} :
    (s.Sum h).subtypeDomain p = s.Sum fun c d => (h c d).subtypeDomain p :=
  subtype_domain_sum

theorem filter_sum (s : Finset ι) (f : ι → α →₀ M) : (∑ a in s, f a).filter p = ∑ a in s, filter p (f a) :=
  (filterAddHom p : (α →₀ M) →+ _).map_sum f s

theorem filter_eq_sum (p : α → Prop) [D : DecidablePred p] (f : α →₀ M) :
    f.filter p = ∑ i in f.Support.filter p, single i (f i) :=
  (f.filter p).sum_single.symm.trans <|
    (Finset.sum_congr
        (by
          rw [Subsingleton.elimₓ D] <;> rfl))
      fun x hx => by
      rw [filter_apply_pos _ _ (mem_filter.1 hx).2]

end CommMonoidₓ

section Groupₓ

variable [AddGroupₓ G] {p : α → Prop} {v v' : α →₀ G}

@[simp]
theorem subtype_domain_neg : (-v).subtypeDomain p = -v.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
theorem subtype_domain_sub : (v - v').subtypeDomain p = v.subtypeDomain p - v'.subtypeDomain p :=
  ext fun _ => rfl

@[simp]
theorem single_neg (a : α) (b : G) : single a (-b) = -single a b :=
  (singleAddHom a : G →+ _).map_neg b

@[simp]
theorem single_sub (a : α) (b₁ b₂ : G) : single a (b₁ - b₂) = single a b₁ - single a b₂ :=
  (singleAddHom a : G →+ _).map_sub b₁ b₂

@[simp]
theorem erase_neg (a : α) (f : α →₀ G) : erase a (-f) = -erase a f :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_neg f

@[simp]
theorem erase_sub (a : α) (f₁ f₂ : α →₀ G) : erase a (f₁ - f₂) = erase a f₁ - erase a f₂ :=
  (eraseAddHom a : (_ →₀ G) →+ _).map_sub f₁ f₂

@[simp]
theorem filter_neg (p : α → Prop) (f : α →₀ G) : filter p (-f) = -filter p f :=
  (filterAddHom p : (_ →₀ G) →+ _).map_neg f

@[simp]
theorem filter_sub (p : α → Prop) (f₁ f₂ : α →₀ G) : filter p (f₁ - f₂) = filter p f₁ - filter p f₂ :=
  (filterAddHom p : (_ →₀ G) →+ _).map_sub f₁ f₂

end Groupₓ

end SubtypeDomain

theorem mem_support_multiset_sum [AddCommMonoidₓ M] {s : Multiset (α →₀ M)} (a : α) :
    a ∈ s.Sum.Support → ∃ f ∈ s, a ∈ (f : α →₀ M).Support :=
  Multiset.induction_on s False.elim
    (by
      intro f s ih ha
      by_cases' a ∈ f.support
      · exact ⟨f, Multiset.mem_cons_self _ _, h⟩
        
      · simp only [← Multiset.sum_cons, ← mem_support_iff, ← add_apply, ← not_mem_support_iff.1 h, ← zero_addₓ] at ha
        rcases ih (mem_support_iff.2 ha) with ⟨f', h₀, h₁⟩
        exact ⟨f', Multiset.mem_cons_of_mem h₀, h₁⟩
        )

theorem mem_support_finset_sum [AddCommMonoidₓ M] {s : Finset ι} {h : ι → α →₀ M} (a : α)
    (ha : a ∈ (∑ c in s, h c).Support) : ∃ c ∈ s, a ∈ (h c).Support :=
  let ⟨f, hf, hfa⟩ := mem_support_multiset_sum a ha
  let ⟨c, hc, Eq⟩ := Multiset.mem_map.1 hf
  ⟨c, hc, Eq.symm ▸ hfa⟩

/-! ### Declarations about `curry` and `uncurry` -/


section CurryUncurry

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N]

/-- Given a finitely supported function `f` from a product type `α × β` to `γ`,
`curry f` is the "curried" finitely supported function from `α` to the type of
finitely supported functions from `β` to `γ`. -/
protected def curry (f : α × β →₀ M) : α →₀ β →₀ M :=
  f.Sum fun p c => single p.1 (single p.2 c)

@[simp]
theorem curry_apply (f : α × β →₀ M) (x : α) (y : β) : f.curry x y = f (x, y) := by
  have : ∀ b : α × β, single b.fst (single b.snd (f b)) x y = if b = (x, y) then f b else 0 := by
    rintro ⟨b₁, b₂⟩
    simp [← single_apply, ← ite_apply, ← Prod.ext_iff, ← ite_and]
    split_ifs <;> simp [← single_apply, *]
  rw [Finsupp.curry, sum_apply, sum_apply, Finsupp.sum, Finset.sum_eq_single, this, if_pos rfl]
  · intro b hb b_ne
    rw [this b, if_neg b_ne]
    
  · intro hxy
    rw [this (x, y), if_pos rfl, not_mem_support_iff.mp hxy]
    

theorem sum_curry_index (f : α × β →₀ M) (g : α → β → M → N) (hg₀ : ∀ a b, g a b 0 = 0)
    (hg₁ : ∀ a b c₀ c₁, g a b (c₀ + c₁) = g a b c₀ + g a b c₁) :
    (f.curry.Sum fun a f => f.Sum (g a)) = f.Sum fun p c => g p.1 p.2 c := by
  rw [Finsupp.curry]
  trans
  · exact
      sum_sum_index (fun a => sum_zero_index) fun a b₀ b₁ =>
        sum_add_index' (fun a => hg₀ _ _) fun c d₀ d₁ => hg₁ _ _ _ _
    
  congr
  funext p c
  trans
  · exact sum_single_index sum_zero_index
    
  exact sum_single_index (hg₀ _ _)

/-- Given a finitely supported function `f` from `α` to the type of
finitely supported functions from `β` to `M`,
`uncurry f` is the "uncurried" finitely supported function from `α × β` to `M`. -/
protected def uncurry (f : α →₀ β →₀ M) : α × β →₀ M :=
  f.Sum fun a g => g.Sum fun b c => single (a, b) c

/-- `finsupp_prod_equiv` defines the `equiv` between `((α × β) →₀ M)` and `(α →₀ (β →₀ M))` given by
currying and uncurrying. -/
def finsuppProdEquiv : (α × β →₀ M) ≃ (α →₀ β →₀ M) := by
  refine' ⟨Finsupp.curry, Finsupp.uncurry, fun f => _, fun f => _⟩ <;>
    simp only [← Finsupp.curry, ← Finsupp.uncurry, ← sum_sum_index, ← sum_zero_index, ← sum_add_index, ←
      sum_single_index, ← single_zero, ← single_add, ← eq_self_iff_true, ← forall_true_iff, ← forall_3_true_iff, ←
      Prod.mk.eta, ← (single_sum _ _ _).symm, ← sum_single]

theorem filter_curry (f : α × β →₀ M) (p : α → Prop) : (f.filter fun a : α × β => p a.1).curry = f.curry.filter p := by
  rw [Finsupp.curry, Finsupp.curry, Finsupp.sum, Finsupp.sum, filter_sum, support_filter, sum_filter]
  refine' Finset.sum_congr rfl _
  rintro ⟨a₁, a₂⟩ ha
  dsimp' only
  split_ifs
  · rw [filter_apply_pos, filter_single_of_pos] <;> exact h
    
  · rwa [filter_single_of_neg]
    

theorem support_curry [DecidableEq α] (f : α × β →₀ M) : f.curry.Support ⊆ f.Support.Image Prod.fst := by
  rw [← Finset.bUnion_singleton]
  refine' Finset.Subset.trans support_sum _
  refine' Finset.bUnion_mono fun a _ => support_single_subset

end CurryUncurry

section Sum

/-- `finsupp.sum_elim f g` maps `inl x` to `f x` and `inr y` to `g y`. -/
def sumElim {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) : Sum α β →₀ γ :=
  onFinset (f.Support.map ⟨_, Sum.inl_injective⟩ ∪ g.Support.map ⟨_, Sum.inr_injective⟩) (Sum.elim f g) fun ab h => by
    cases' ab with a b <;> simp only [← Sum.elim_inl, ← Sum.elim_inr] at h <;> simpa

@[simp]
theorem coe_sum_elim {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) : ⇑(sumElim f g) = Sum.elim f g :=
  rfl

theorem sum_elim_apply {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : Sum α β) :
    sumElim f g x = Sum.elim f g x :=
  rfl

theorem sum_elim_inl {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : α) : sumElim f g (Sum.inl x) = f x :=
  rfl

theorem sum_elim_inr {α β γ : Type _} [Zero γ] (f : α →₀ γ) (g : β →₀ γ) (x : β) : sumElim f g (Sum.inr x) = g x :=
  rfl

/-- The equivalence between `(α ⊕ β) →₀ γ` and `(α →₀ γ) × (β →₀ γ)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symmApply]
def sumFinsuppEquivProdFinsupp {α β γ : Type _} [Zero γ] : (Sum α β →₀ γ) ≃ (α →₀ γ) × (β →₀ γ) where
  toFun := fun f =>
    ⟨f.comapDomain Sum.inl (Sum.inl_injective.InjOn _), f.comapDomain Sum.inr (Sum.inr_injective.InjOn _)⟩
  invFun := fun fg => sumElim fg.1 fg.2
  left_inv := fun f => by
    ext ab
    cases' ab with a b <;> simp
  right_inv := fun fg => by
    ext <;> simp

theorem fst_sum_finsupp_equiv_prod_finsupp {α β γ : Type _} [Zero γ] (f : Sum α β →₀ γ) (x : α) :
    (sumFinsuppEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sum_finsupp_equiv_prod_finsupp {α β γ : Type _} [Zero γ] (f : Sum α β →₀ γ) (y : β) :
    (sumFinsuppEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl

theorem sum_finsupp_equiv_prod_finsupp_symm_inl {α β γ : Type _} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ)) (x : α) :
    (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sum_finsupp_equiv_prod_finsupp_symm_inr {α β γ : Type _} [Zero γ] (fg : (α →₀ γ) × (β →₀ γ)) (y : β) :
    (sumFinsuppEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

variable [AddMonoidₓ M]

/-- The additive equivalence between `(α ⊕ β) →₀ M` and `(α →₀ M) × (β →₀ M)`.

This is the `finsupp` version of `equiv.sum_arrow_equiv_prod_arrow`. -/
@[simps apply symmApply]
def sumFinsuppAddEquivProdFinsupp {α β : Type _} : (Sum α β →₀ M) ≃+ (α →₀ M) × (β →₀ M) :=
  { sumFinsuppEquivProdFinsupp with
    map_add' := by
      intros
      ext <;>
        simp only [← Equivₓ.to_fun_as_coe, ← Prod.fst_add, ← Prod.snd_add, ← add_apply, ←
          snd_sum_finsupp_equiv_prod_finsupp, ← fst_sum_finsupp_equiv_prod_finsupp] }

theorem fst_sum_finsupp_add_equiv_prod_finsupp {α β : Type _} (f : Sum α β →₀ M) (x : α) :
    (sumFinsuppAddEquivProdFinsupp f).1 x = f (Sum.inl x) :=
  rfl

theorem snd_sum_finsupp_add_equiv_prod_finsupp {α β : Type _} (f : Sum α β →₀ M) (y : β) :
    (sumFinsuppAddEquivProdFinsupp f).2 y = f (Sum.inr y) :=
  rfl

theorem sum_finsupp_add_equiv_prod_finsupp_symm_inl {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (x : α) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inl x) = fg.1 x :=
  rfl

theorem sum_finsupp_add_equiv_prod_finsupp_symm_inr {α β : Type _} (fg : (α →₀ M) × (β →₀ M)) (y : β) :
    (sumFinsuppAddEquivProdFinsupp.symm fg) (Sum.inr y) = fg.2 y :=
  rfl

end Sum

section

variable [Zero M] [MonoidWithZeroₓ R] [MulActionWithZero R M]

@[simp]
theorem single_smul (a b : α) (f : α → M) (r : R) : single a r b • f a = single a (r • f b) b := by
  by_cases' a = b <;> simp [← h]

end

section

variable [Monoidₓ G] [MulAction G α] [AddCommMonoidₓ M]

/-- Scalar multiplication acting on the domain.

This is not an instance as it would conflict with the action on the range.
See the `instance_diamonds` test for examples of such conflicts. -/
def comapHasSmul : HasSmul G (α →₀ M) where smul := fun g => mapDomain ((· • ·) g)

attribute [local instance] comap_has_smul

theorem comap_smul_def (g : G) (f : α →₀ M) : g • f = mapDomain ((· • ·) g) f :=
  rfl

@[simp]
theorem comap_smul_single (g : G) (a : α) (b : M) : g • single a b = single (g • a) b :=
  map_domain_single

/-- `finsupp.comap_has_smul` is multiplicative -/
def comapMulAction : MulAction G (α →₀ M) where
  one_smul := fun f => by
    rw [comap_smul_def, one_smul_eq_id, map_domain_id]
  mul_smul := fun g g' f => by
    rw [comap_smul_def, comap_smul_def, comap_smul_def, ← comp_smul_left, map_domain_comp]

attribute [local instance] comap_mul_action

/-- `finsupp.comap_has_smul` is distributive -/
def comapDistribMulAction : DistribMulAction G (α →₀ M) where
  smul_zero := fun g => by
    ext
    dsimp' [← (· • ·)]
    simp
  smul_add := fun g f f' => by
    ext
    dsimp' [← (· • ·)]
    simp [← map_domain_add]

end

section

variable [Groupₓ G] [MulAction G α] [AddCommMonoidₓ M]

attribute [local instance] comap_has_smul comap_mul_action comap_distrib_mul_action

/-- When `G` is a group, `finsupp.comap_has_smul` acts by precomposition with the action of `g⁻¹`.
-/
@[simp]
theorem comap_smul_apply (g : G) (f : α →₀ M) (a : α) : (g • f) a = f (g⁻¹ • a) := by
  conv_lhs => rw [← smul_inv_smul g a]
  exact map_domain_apply (MulAction.injective g) _ (g⁻¹ • a)

end

section

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : HasSmul R (α →₀ M) :=
  ⟨fun a v => v.map_range ((· • ·) a) (smul_zero _)⟩

/-!
Throughout this section, some `monoid` and `semiring` arguments are specified with `{}` instead of
`[]`. See note [implicit instance arguments].
-/


@[simp]
theorem coe_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (b : R) (v : α →₀ M) : ⇑(b • v) = b • v :=
  rfl

theorem smul_apply {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (b : R) (v : α →₀ M) (a : α) :
    (b • v) a = b • v a :=
  rfl

theorem _root_.is_smul_regular.finsupp {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {k : R}
    (hk : IsSmulRegular M k) : IsSmulRegular (α →₀ M) k := fun _ _ h => ext fun i => hk (congr_fun h i)

instance [Monoidₓ R] [Nonempty α] [AddMonoidₓ M] [DistribMulAction R M] [HasFaithfulSmul R M] :
    HasFaithfulSmul R (α →₀ M) where eq_of_smul_eq_smul := fun r₁ r₂ h =>
    let ⟨a⟩ := ‹Nonempty α›
    eq_of_smul_eq_smul fun m : M => by
      simpa using congr_fun (h (single a m)) a

variable (α M)

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] : DistribMulAction R (α →₀ M) where
  smul := (· • ·)
  smul_add := fun a x y => ext fun _ => smul_add _ _ _
  one_smul := fun x => ext fun _ => one_smul _ _
  mul_smul := fun r s x => ext fun _ => mul_smul _ _ _
  smul_zero := fun x => ext fun _ => smul_zero _

instance [Monoidₓ R] [Monoidₓ S] [AddMonoidₓ M] [DistribMulAction R M] [DistribMulAction S M] [HasSmul R S]
    [IsScalarTower R S M] : IsScalarTower R S (α →₀ M) where smul_assoc := fun r s a => ext fun _ => smul_assoc _ _ _

instance [Monoidₓ R] [Monoidₓ S] [AddMonoidₓ M] [DistribMulAction R M] [DistribMulAction S M] [SmulCommClass R S M] :
    SmulCommClass R S (α →₀ M) where smul_comm := fun r s a => ext fun _ => smul_comm _ _ _

instance [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] [DistribMulAction Rᵐᵒᵖ M] [IsCentralScalar R M] :
    IsCentralScalar R (α →₀ M) where op_smul_eq_smul := fun r a => ext fun _ => op_smul_eq_smul _ _

instance [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] : Module R (α →₀ M) :=
  { Finsupp.distribMulAction α M with smul := (· • ·), zero_smul := fun x => ext fun _ => zero_smul _ _,
    add_smul := fun a x y => ext fun _ => add_smul _ _ _ }

variable {α M} {R}

theorem support_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {b : R} {g : α →₀ M} :
    (b • g).Support ⊆ g.Support := fun a => by
  simp only [← smul_apply, ← mem_support_iff, ← Ne.def]
  exact mt fun h => h.symm ▸ smul_zero _

@[simp]
theorem support_smul_eq [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] [NoZeroSmulDivisors R M] {b : R} (hb : b ≠ 0)
    {g : α →₀ M} : (b • g).Support = g.Support :=
  Finset.ext fun a => by
    simp [← Finsupp.smul_apply, ← hb]

section

variable {p : α → Prop}

@[simp]
theorem filter_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] {b : R} {v : α →₀ M} :
    (b • v).filter p = b • v.filter p :=
  coe_fn_injective <| Set.indicator_const_smul { x | p x } b v

end

theorem map_domain_smul {_ : Monoidₓ R} [AddCommMonoidₓ M] [DistribMulAction R M] {f : α → β} (b : R) (v : α →₀ M) :
    mapDomain f (b • v) = b • mapDomain f v :=
  map_domain_map_range _ _ _ _ (smul_add b)

@[simp]
theorem smul_single {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] (c : R) (a : α) (b : M) :
    c • Finsupp.single a b = Finsupp.single a (c • b) :=
  map_range_single

@[simp]
theorem smul_single' {_ : Semiringₓ R} (c : R) (a : α) (b : R) : c • Finsupp.single a b = Finsupp.single a (c * b) :=
  smul_single _ _ _

theorem map_range_smul {_ : Monoidₓ R} [AddMonoidₓ M] [DistribMulAction R M] [AddMonoidₓ N] [DistribMulAction R N]
    {f : M → N} {hf : f 0 = 0} (c : R) (v : α →₀ M) (hsmul : ∀ x, f (c • x) = c • f x) :
    mapRange f hf (c • v) = c • mapRange f hf v := by
  erw [← map_range_comp]
  have : f ∘ (· • ·) c = (· • ·) c ∘ f := funext hsmul
  simp_rw [this]
  apply map_range_comp
  rw [Function.comp_applyₓ, smul_zero, hf]

theorem smul_single_one [Semiringₓ R] (a : α) (b : R) : b • single a 1 = single a b := by
  rw [smul_single, smul_eq_mul, mul_oneₓ]

theorem comap_domain_smul [AddMonoidₓ M] [Monoidₓ R] [DistribMulAction R M] {f : α → β} (r : R) (v : β →₀ M)
    (hfv : Set.InjOn f (f ⁻¹' ↑v.Support))
    (hfrv : Set.InjOn f (f ⁻¹' ↑(r • v).Support) :=
      hfv.mono <| Set.preimage_mono <| Finset.coe_subset.mpr support_smul) :
    comapDomain f (r • v) hfrv = r • comapDomain f v hfv := by
  ext
  rfl

/-- A version of `finsupp.comap_domain_smul` that's easier to use. -/
theorem comap_domain_smul_of_injective [AddMonoidₓ M] [Monoidₓ R] [DistribMulAction R M] {f : α → β}
    (hf : Function.Injective f) (r : R) (v : β →₀ M) :
    comapDomain f (r • v) (hf.InjOn _) = r • comapDomain f v (hf.InjOn _) :=
  comap_domain_smul _ _ _ _

end

theorem sum_smul_index [Semiringₓ R] [AddCommMonoidₓ M] {g : α →₀ R} {b : R} {h : α → R → M} (h0 : ∀ i, h i 0 = 0) :
    (b • g).Sum h = g.Sum fun i a => h i (b * a) :=
  Finsupp.sum_map_range_index h0

theorem sum_smul_index' [Monoidₓ R] [AddMonoidₓ M] [DistribMulAction R M] [AddCommMonoidₓ N] {g : α →₀ M} {b : R}
    {h : α → M → N} (h0 : ∀ i, h i 0 = 0) : (b • g).Sum h = g.Sum fun i c => h i (b • c) :=
  Finsupp.sum_map_range_index h0

/-- A version of `finsupp.sum_smul_index'` for bundled additive maps. -/
theorem sum_smul_index_add_monoid_hom [Monoidₓ R] [AddMonoidₓ M] [AddCommMonoidₓ N] [DistribMulAction R M] {g : α →₀ M}
    {b : R} {h : α → M →+ N} : ((b • g).Sum fun a => h a) = g.Sum fun i c => h i (b • c) :=
  sum_map_range_index fun i => (h i).map_zero

instance [Semiringₓ R] [AddCommMonoidₓ M] [Module R M] {ι : Type _} [NoZeroSmulDivisors R M] :
    NoZeroSmulDivisors R (ι →₀ M) :=
  ⟨fun c f h =>
    or_iff_not_imp_left.mpr fun hc => Finsupp.ext fun i => (smul_eq_zero.mp (Finsupp.ext_iff.mp h i)).resolve_left hc⟩

section DistribMulActionHom

variable [Semiringₓ R]

variable [AddCommMonoidₓ M] [AddCommMonoidₓ N] [DistribMulAction R M] [DistribMulAction R N]

/-- `finsupp.single` as a `distrib_mul_action_hom`.

See also `finsupp.lsingle` for the version as a linear map. -/
def DistribMulActionHom.single (a : α) : M →+[R] α →₀ M :=
  { singleAddHom a with
    map_smul' := fun k m => by
      simp only [← AddMonoidHom.to_fun_eq_coe, ← single_add_hom_apply, ← smul_single] }

theorem distrib_mul_action_hom_ext {f g : (α →₀ M) →+[R] N} (h : ∀ (a : α) (m : M), f (single a m) = g (single a m)) :
    f = g :=
  DistribMulActionHom.to_add_monoid_hom_injective <| add_hom_ext h

/-- See note [partially-applied ext lemmas]. -/
@[ext]
theorem distrib_mul_action_hom_ext' {f g : (α →₀ M) →+[R] N}
    (h : ∀ a : α, f.comp (DistribMulActionHom.single a) = g.comp (DistribMulActionHom.single a)) : f = g :=
  distrib_mul_action_hom_ext fun a => DistribMulActionHom.congr_fun (h a)

end DistribMulActionHom

section

variable [Zero R]

/-- The `finsupp` version of `pi.unique`. -/
instance uniqueOfRight [Subsingleton R] : Unique (α →₀ R) :=
  { Finsupp.inhabited with uniq := fun l => ext fun i => Subsingleton.elimₓ _ _ }

/-- The `finsupp` version of `pi.unique_of_is_empty`. -/
instance uniqueOfLeft [IsEmpty α] : Unique (α →₀ R) :=
  { Finsupp.inhabited with uniq := fun l => ext isEmptyElim }

end

/-- Given an `add_comm_monoid M` and `s : set α`, `restrict_support_equiv s M` is the `equiv`
between the subtype of finitely supported functions with support contained in `s` and
the type of finitely supported functions from `s`. -/
def restrictSupportEquiv (s : Set α) (M : Type _) [AddCommMonoidₓ M] : { f : α →₀ M // ↑f.Support ⊆ s } ≃ (s →₀ M) := by
  refine' ⟨fun f => subtype_domain (fun x => x ∈ s) f.1, fun f => ⟨f.mapDomain Subtype.val, _⟩, _, _⟩
  · refine' Set.Subset.trans (Finset.coe_subset.2 map_domain_support) _
    rw [Finset.coe_image, Set.image_subset_iff]
    exact fun x hx => x.2
    
  · rintro ⟨f, hf⟩
    apply Subtype.eq
    ext a
    dsimp' only
    refine' Classical.by_cases (fun h : a ∈ Set.Range (Subtype.val : s → α) => _) fun h => _
    · rcases h with ⟨x, rfl⟩
      rw [map_domain_apply Subtype.val_injective, subtype_domain_apply]
      
    · convert map_domain_notin_range _ _ h
      rw [← not_mem_support_iff]
      refine' mt _ h
      exact fun ha => ⟨⟨a, hf ha⟩, rfl⟩
      
    
  · intro f
    ext ⟨a, ha⟩
    dsimp' only
    rw [subtype_domain_apply, map_domain_apply Subtype.val_injective]
    

/-- Given `add_comm_monoid M` and `e : α ≃ β`, `dom_congr e` is the corresponding `equiv` between
`α →₀ M` and `β →₀ M`.

This is `finsupp.equiv_congr_left` as an `add_equiv`. -/
@[simps apply]
protected def domCongr [AddCommMonoidₓ M] (e : α ≃ β) : (α →₀ M) ≃+ (β →₀ M) where
  toFun := equivMapDomain e
  invFun := equivMapDomain e.symm
  left_inv := fun v => by
    simp only [equiv_map_domain_trans, ← Equivₓ.self_trans_symm]
    exact equiv_map_domain_refl _
  right_inv := by
    intro v
    simp only [equiv_map_domain_trans, ← Equivₓ.symm_trans_self]
    exact equiv_map_domain_refl _
  map_add' := fun a b => by
    simp only [← equiv_map_domain_eq_map_domain] <;> exact map_domain_add

@[simp]
theorem dom_congr_refl [AddCommMonoidₓ M] : Finsupp.domCongr (Equivₓ.refl α) = AddEquiv.refl (α →₀ M) :=
  AddEquiv.ext fun _ => equiv_map_domain_refl _

@[simp]
theorem dom_congr_symm [AddCommMonoidₓ M] (e : α ≃ β) :
    (Finsupp.domCongr e).symm = (Finsupp.domCongr e.symm : (β →₀ M) ≃+ (α →₀ M)) :=
  AddEquiv.ext fun _ => rfl

@[simp]
theorem dom_congr_trans [AddCommMonoidₓ M] (e : α ≃ β) (f : β ≃ γ) :
    (Finsupp.domCongr e).trans (Finsupp.domCongr f) = (Finsupp.domCongr (e.trans f) : (α →₀ M) ≃+ _) :=
  AddEquiv.ext fun _ => (equiv_map_domain_trans _ _ _).symm

end Finsupp

namespace Finsupp

/-! ### Declarations about sigma types -/


section Sigma

variable {αs : ι → Type _} [Zero M] (l : (Σi, αs i) →₀ M)

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `M` and
an index element `i : ι`, `split l i` is the `i`th component of `l`,
a finitely supported function from `as i` to `M`.

This is the `finsupp` version of `sigma.curry`.
-/
def split (i : ι) : αs i →₀ M :=
  l.comapDomain (Sigma.mk i) fun x1 x2 _ _ hx => heq_iff_eq.1 (Sigma.mk.inj hx).2

theorem split_apply (i : ι) (x : αs i) : split l i x = l ⟨i, x⟩ := by
  dunfold split
  rw [comap_domain_apply]

/-- Given `l`, a finitely supported function from the sigma type `Σ (i : ι), αs i` to `β`,
`split_support l` is the finset of indices in `ι` that appear in the support of `l`. -/
def splitSupport : Finset ι :=
  l.Support.Image Sigma.fst

theorem mem_split_support_iff_nonzero (i : ι) : i ∈ splitSupport l ↔ split l i ≠ 0 := by
  rw [split_support, mem_image, Ne.def, ← support_eq_empty, ← Ne.def, ← Finset.nonempty_iff_ne_empty, split,
    comap_domain, Finset.Nonempty]
  simp only [← exists_prop, ← Finset.mem_preimage, ← exists_and_distrib_right, ← exists_eq_right, ← mem_support_iff, ←
    Sigma.exists, ← Ne.def]

/-- Given `l`, a finitely supported function from the sigma type `Σ i, αs i` to `β` and
an `ι`-indexed family `g` of functions from `(αs i →₀ β)` to `γ`, `split_comp` defines a
finitely supported function from the index type `ι` to `γ` given by composing `g i` with
`split l i`. -/
def splitComp [Zero N] (g : ∀ i, (αs i →₀ M) → N) (hg : ∀ i x, x = 0 ↔ g i x = 0) : ι →₀ N where
  Support := splitSupport l
  toFun := fun i => g i (split l i)
  mem_support_to_fun := by
    intro i
    rw [mem_split_support_iff_nonzero, not_iff_not, hg]

theorem sigma_support : l.Support = l.splitSupport.Sigma fun i => (l.split i).Support := by
  simp only [← Finset.ext_iff, ← split_support, ← split, ← comap_domain, ← mem_image, ← mem_preimage, ← Sigma.forall, ←
      mem_sigma] <;>
    tauto

theorem sigma_sum [AddCommMonoidₓ N] (f : (Σi : ι, αs i) → M → N) :
    l.Sum f = ∑ i in splitSupport l, (split l i).Sum fun (a : αs i) b => f ⟨i, a⟩ b := by
  simp only [← Sum, ← sigma_support, ← sum_sigma, ← split_apply]

variable {η : Type _} [Fintype η] {ιs : η → Type _} [Zero α]

/-- On a `fintype η`, `finsupp.split` is an equivalence between `(Σ (j : η), ιs j) →₀ α`
and `Π j, (ιs j →₀ α)`.

This is the `finsupp` version of `equiv.Pi_curry`. -/
noncomputable def sigmaFinsuppEquivPiFinsupp : ((Σj, ιs j) →₀ α) ≃ ∀ j, ιs j →₀ α where
  toFun := split
  invFun := fun f =>
    onFinset (Finset.univ.Sigma fun j => (f j).Support) (fun ji => f ji.1 ji.2) fun g hg =>
      Finset.mem_sigma.mpr ⟨Finset.mem_univ _, mem_support_iff.mpr hg⟩
  left_inv := fun f => by
    ext
    simp [← split]
  right_inv := fun f => by
    ext
    simp [← split]

@[simp]
theorem sigma_finsupp_equiv_pi_finsupp_apply (f : (Σj, ιs j) →₀ α) (j i) :
    sigmaFinsuppEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

/-- On a `fintype η`, `finsupp.split` is an additive equivalence between
`(Σ (j : η), ιs j) →₀ α` and `Π j, (ιs j →₀ α)`.

This is the `add_equiv` version of `finsupp.sigma_finsupp_equiv_pi_finsupp`.
-/
noncomputable def sigmaFinsuppAddEquivPiFinsupp {α : Type _} {ιs : η → Type _} [AddMonoidₓ α] :
    ((Σj, ιs j) →₀ α) ≃+ ∀ j, ιs j →₀ α :=
  { sigmaFinsuppEquivPiFinsupp with
    map_add' := fun f g => by
      ext
      simp }

@[simp]
theorem sigma_finsupp_add_equiv_pi_finsupp_apply {α : Type _} {ιs : η → Type _} [AddMonoidₓ α] (f : (Σj, ιs j) →₀ α)
    (j i) : sigmaFinsuppAddEquivPiFinsupp f j i = f ⟨j, i⟩ :=
  rfl

end Sigma

end Finsupp

section CastFinsupp

variable [Zero M] (f : α →₀ M)

namespace Nat

@[simp, norm_cast]
theorem cast_finsupp_prod [CommSemiringₓ R] (g : α → M → ℕ) : (↑(f.Prod g) : R) = f.Prod fun a b => ↑(g a b) :=
  Nat.cast_prod _ _

@[simp, norm_cast]
theorem cast_finsupp_sum [CommSemiringₓ R] (g : α → M → ℕ) : (↑(f.Sum g) : R) = f.Sum fun a b => ↑(g a b) :=
  Nat.cast_sum _ _

end Nat

namespace Int

@[simp, norm_cast]
theorem cast_finsupp_prod [CommRingₓ R] (g : α → M → ℤ) : (↑(f.Prod g) : R) = f.Prod fun a b => ↑(g a b) :=
  Int.cast_prod _ _

@[simp, norm_cast]
theorem cast_finsupp_sum [CommRingₓ R] (g : α → M → ℤ) : (↑(f.Sum g) : R) = f.Sum fun a b => ↑(g a b) :=
  Int.cast_sum _ _

end Int

namespace Rat

@[simp, norm_cast]
theorem cast_finsupp_sum [DivisionRing R] [CharZero R] (g : α → M → ℚ) : (↑(f.Sum g) : R) = f.Sum fun a b => g a b :=
  cast_sum _ _

@[simp, norm_cast]
theorem cast_finsupp_prod [Field R] [CharZero R] (g : α → M → ℚ) : (↑(f.Prod g) : R) = f.Prod fun a b => g a b :=
  cast_prod _ _

end Rat

end CastFinsupp

