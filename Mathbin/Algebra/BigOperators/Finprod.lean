/-
Copyright (c) 2020 Kexing Ying and Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kexing Ying, Kevin Buzzard, Yury Kudryashov
-/
import Mathbin.Algebra.BigOperators.Order
import Mathbin.Algebra.IndicatorFunction

/-!
# Finite products and sums over types and sets

We define products and sums over types and subsets of types, with no finiteness hypotheses.
All infinite products and sums are defined to be junk values (i.e. one or zero).
This approach is sometimes easier to use than `finset.sum`,
when issues arise with `finset` and `fintype` being data.

## Main definitions

We use the following variables:

* `α`, `β` - types with no structure;
* `s`, `t` - sets
* `M`, `N` - additive or multiplicative commutative monoids
* `f`, `g` - functions

Definitions in this file:

* `finsum f : M` : the sum of `f x` as `x` ranges over the support of `f`, if it's finite.
   Zero otherwise.

* `finprod f : M` : the product of `f x` as `x` ranges over the multiplicative support of `f`, if
   it's finite. One otherwise.

## Notation

* `∑ᶠ i, f i` and `∑ᶠ i : α, f i` for `finsum f`

* `∏ᶠ i, f i` and `∏ᶠ i : α, f i` for `finprod f`

This notation works for functions `f : p → M`, where `p : Prop`, so the following works:

* `∑ᶠ i ∈ s, f i`, where `f : α → M`, `s : set α` : sum over the set `s`;
* `∑ᶠ n < 5, f n`, where `f : ℕ → M` : same as `f 0 + f 1 + f 2 + f 3 + f 4`;
* `∏ᶠ (n >= -2) (hn : n < 3), f n`, where `f : ℤ → M` : same as `f (-2) * f (-1) * f 0 * f 1 * f 2`.

## Implementation notes

`finsum` and `finprod` is "yet another way of doing finite sums and products in Lean". However
experiments in the wild (e.g. with matroids) indicate that it is a helpful approach in settings
where the user is not interested in computability and wants to do reasoning without running into
typeclass diamonds caused by the constructive finiteness used in definitions such as `finset` and
`fintype`. By sticking solely to `set.finite` we avoid these problems. We are aware that there are
other solutions but for beginner mathematicians this approach is easier in practice.

Another application is the construction of a partition of unity from a collection of “bump”
function. In this case the finite set depends on the point and it's convenient to have a definition
that does not mention the set explicitly.

The first arguments in all definitions and lemmas is the codomain of the function of the big
operator. This is necessary for the heuristic in `@[to_additive]`.
See the documentation of `to_additive.attr` for more information.

We did not add `is_finite (X : Type) : Prop`, because it is simply `nonempty (fintype X)`.

## Tags

finsum, finprod, finite sum, finite product
-/


open Function Set

/-!
### Definition and relation to `finset.sum` and `finset.prod`
-/


section Sort

variable {G M N : Type _} {α β ι : Sort _} [CommMonoidₓ M] [CommMonoidₓ N]

open BigOperators

section

/- Note: we use classical logic only for these definitions, to ensure that we do not write lemmas
with `classical.dec` in their statement. -/
open Classical

/-- Sum of `f x` as `x` ranges over the elements of the support of `f`, if it's finite. Zero
otherwise. -/
noncomputable irreducible_def finsum {M α} [AddCommMonoidₓ M] (f : α → M) : M :=
  if h : (Support (f ∘ Plift.down)).Finite then ∑ i in h.toFinset, f i.down else 0

/-- Product of `f x` as `x` ranges over the elements of the multiplicative support of `f`, if it's
finite. One otherwise. -/
@[to_additive]
noncomputable irreducible_def finprod (f : α → M) : M :=
  if h : (MulSupport (f ∘ Plift.down)).Finite then ∏ i in h.toFinset, f i.down else 1

end

-- mathport name: «expr∑ᶠ , »
localized [BigOperators] notation3"∑ᶠ "(...)", "r:(scoped f => finsum f) => r

-- mathport name: «expr∏ᶠ , »
localized [BigOperators] notation3"∏ᶠ "(...)", "r:(scoped f => finprod f) => r

@[to_additive]
theorem finprod_eq_prod_plift_of_mul_support_to_finset_subset {f : α → M} (hf : (MulSupport (f ∘ Plift.down)).Finite)
    {s : Finset (Plift α)} (hs : hf.toFinset ⊆ s) : (∏ᶠ i, f i) = ∏ i in s, f i.down := by
  rw [finprod, dif_pos]
  refine' Finset.prod_subset hs fun x hx hxf => _
  rwa [hf.mem_to_finset, nmem_mul_support] at hxf

@[to_additive]
theorem finprod_eq_prod_plift_of_mul_support_subset {f : α → M} {s : Finset (Plift α)}
    (hs : MulSupport (f ∘ Plift.down) ⊆ s) : (∏ᶠ i, f i) = ∏ i in s, f i.down :=
  (finprod_eq_prod_plift_of_mul_support_to_finset_subset (s.finite_to_set.Subset hs)) fun x hx => by
    rw [finite.mem_to_finset] at hx
    exact hs hx

@[simp, to_additive]
theorem finprod_one : (∏ᶠ i : α, (1 : M)) = 1 := by
  have : (mul_support fun x : Plift α => (fun _ => 1 : α → M) x.down) ⊆ (∅ : Finset (Plift α)) := fun x h => h rfl
  rw [finprod_eq_prod_plift_of_mul_support_subset this, Finset.prod_empty]

@[to_additive]
theorem finprod_of_is_empty [IsEmpty α] (f : α → M) : (∏ᶠ i, f i) = 1 := by
  rw [← finprod_one]
  congr

@[simp, to_additive]
theorem finprod_false (f : False → M) : (∏ᶠ i, f i) = 1 :=
  finprod_of_is_empty _

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (x «expr ≠ » a)
@[to_additive]
theorem finprod_eq_single (f : α → M) (a : α) (ha : ∀ (x) (_ : x ≠ a), f x = 1) : (∏ᶠ x, f x) = f a := by
  have : mul_support (f ∘ Plift.down) ⊆ ({Plift.up a} : Finset (Plift α)) := by
    intro x
    contrapose
    simpa [← Plift.eq_up_iff_down_eq] using ha x.down
  rw [finprod_eq_prod_plift_of_mul_support_subset this, Finset.prod_singleton]

@[to_additive]
theorem finprod_unique [Unique α] (f : α → M) : (∏ᶠ i, f i) = f default :=
  (finprod_eq_single f default) fun x hx => (hx <| Unique.eq_default _).elim

@[simp, to_additive]
theorem finprod_true (f : True → M) : (∏ᶠ i, f i) = f trivialₓ :=
  @finprod_unique M True _ ⟨⟨trivialₓ⟩, fun _ => rfl⟩ f

@[to_additive]
theorem finprod_eq_dif {p : Prop} [Decidable p] (f : p → M) : (∏ᶠ i, f i) = if h : p then f h else 1 := by
  split_ifs
  · have : Unique p := ⟨⟨h⟩, fun _ => rfl⟩
    exact finprod_unique f
    
  · have : IsEmpty p := ⟨h⟩
    exact finprod_of_is_empty f
    

@[to_additive]
theorem finprod_eq_if {p : Prop} [Decidable p] {x : M} : (∏ᶠ i : p, x) = if p then x else 1 :=
  finprod_eq_dif fun _ => x

@[to_additive]
theorem finprod_congr {f g : α → M} (h : ∀ x, f x = g x) : finprod f = finprod g :=
  congr_arg _ <| funext h

@[congr, to_additive]
theorem finprod_congr_Prop {p q : Prop} {f : p → M} {g : q → M} (hpq : p = q) (hfg : ∀ h : q, f (hpq.mpr h) = g h) :
    finprod f = finprod g := by
  subst q
  exact finprod_congr hfg

attribute [congr] finsum_congr_Prop

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on the factors. -/
@[to_additive
      "To prove a property of a finite sum, it suffices to prove that the property is\nadditive and holds on the summands."]
theorem finprod_induction {f : α → M} (p : M → Prop) (hp₀ : p 1) (hp₁ : ∀ x y, p x → p y → p (x * y))
    (hp₂ : ∀ i, p (f i)) : p (∏ᶠ i, f i) := by
  rw [finprod]
  split_ifs
  exacts[Finset.prod_induction _ _ hp₁ hp₀ fun i hi => hp₂ _, hp₀]

theorem finprod_nonneg {R : Type _} [OrderedCommSemiring R] {f : α → R} (hf : ∀ x, 0 ≤ f x) : 0 ≤ ∏ᶠ x, f x :=
  finprod_induction (fun x => 0 ≤ x) zero_le_one (fun x y => mul_nonneg) hf

@[to_additive finsum_nonneg]
theorem one_le_finprod' {M : Type _} [OrderedCommMonoid M] {f : α → M} (hf : ∀ i, 1 ≤ f i) : 1 ≤ ∏ᶠ i, f i :=
  finprod_induction _ le_rfl (fun _ _ => one_le_mul) hf

@[to_additive]
theorem MonoidHom.map_finprod_plift (f : M →* N) (g : α → M) (h : (mul_support <| g ∘ Plift.down).Finite) :
    f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) := by
  rw [finprod_eq_prod_plift_of_mul_support_subset h.coe_to_finset.ge, finprod_eq_prod_plift_of_mul_support_subset,
    f.map_prod]
  rw [h.coe_to_finset]
  exact mul_support_comp_subset f.map_one (g ∘ Plift.down)

@[to_additive]
theorem MonoidHom.map_finprod_Prop {p : Prop} (f : M →* N) (g : p → M) : f (∏ᶠ x, g x) = ∏ᶠ x, f (g x) :=
  f.map_finprod_plift g (Set.to_finite _)

@[to_additive]
theorem MonoidHom.map_finprod_of_preimage_one (f : M →* N) (hf : ∀ x, f x = 1 → x = 1) (g : α → M) :
    f (∏ᶠ i, g i) = ∏ᶠ i, f (g i) := by
  by_cases' hg : (mul_support <| g ∘ Plift.down).Finite
  · exact f.map_finprod_plift g hg
    
  rw [finprod, dif_neg, f.map_one, finprod, dif_neg]
  exacts[infinite.mono (fun x hx => mt (hf (g x.down)) hx) hg, hg]

@[to_additive]
theorem MonoidHom.map_finprod_of_injective (g : M →* N) (hg : Injective g) (f : α → M) :
    g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_of_preimage_one (fun x => (hg.eq_iff' g.map_one).mp) f

@[to_additive]
theorem MulEquiv.map_finprod (g : M ≃* N) (f : α → M) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.toMonoidHom.map_finprod_of_injective g.Injective f

theorem finsum_smul {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [NoZeroSmulDivisors R M] (f : ι → R)
    (x : M) : (∑ᶠ i, f i) • x = ∑ᶠ i, f i • x := by
  rcases eq_or_ne x 0 with (rfl | hx)
  · simp
    
  exact ((smulAddHom R M).flip x).map_finsum_of_injective (smul_left_injective R hx) _

theorem smul_finsum {R M : Type _} [Ringₓ R] [AddCommGroupₓ M] [Module R M] [NoZeroSmulDivisors R M] (c : R)
    (f : ι → M) : (c • ∑ᶠ i, f i) = ∑ᶠ i, c • f i := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp
    
  exact (smulAddHom R M c).map_finsum_of_injective (smul_right_injective M hc) _

@[to_additive]
theorem finprod_inv_distrib [DivisionCommMonoid G] (f : α → G) : (∏ᶠ x, (f x)⁻¹) = (∏ᶠ x, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod f).symm

end Sort

section Type

variable {α β ι G M N : Type _} [CommMonoidₓ M] [CommMonoidₓ N]

open BigOperators

@[to_additive]
theorem finprod_eq_mul_indicator_apply (s : Set α) (f : α → M) (a : α) : (∏ᶠ h : a ∈ s, f a) = mulIndicator s f a := by
  convert finprod_eq_if

@[simp, to_additive]
theorem finprod_mem_mul_support (f : α → M) (a : α) : (∏ᶠ h : f a ≠ 1, f a) = f a := by
  rw [← mem_mul_support, finprod_eq_mul_indicator_apply, mul_indicator_mul_support]

@[to_additive]
theorem finprod_mem_def (s : Set α) (f : α → M) : (∏ᶠ a ∈ s, f a) = ∏ᶠ a, mulIndicator s f a :=
  finprod_congr <| finprod_eq_mul_indicator_apply s f

@[to_additive]
theorem finprod_eq_prod_of_mul_support_subset (f : α → M) {s : Finset α} (h : MulSupport f ⊆ s) :
    (∏ᶠ i, f i) = ∏ i in s, f i := by
  have A : mul_support (f ∘ Plift.down) = equiv.plift.symm '' mul_support f := by
    rw [mul_support_comp_eq_preimage]
    exact (equiv.plift.symm.image_eq_preimage _).symm
  have : mul_support (f ∘ Plift.down) ⊆ s.map equiv.plift.symm.to_embedding := by
    rw [A, Finset.coe_map]
    exact image_subset _ h
  rw [finprod_eq_prod_plift_of_mul_support_subset this]
  simp

@[to_additive]
theorem finprod_eq_prod_of_mul_support_to_finset_subset (f : α → M) (hf : (MulSupport f).Finite) {s : Finset α}
    (h : hf.toFinset ⊆ s) : (∏ᶠ i, f i) = ∏ i in s, f i :=
  (finprod_eq_prod_of_mul_support_subset _) fun x hx => h <| hf.mem_to_finset.2 hx

@[to_additive]
theorem finprod_eq_finset_prod_of_mul_support_subset (f : α → M) {s : Finset α} (h : MulSupport f ⊆ (s : Set α)) :
    (∏ᶠ i, f i) = ∏ i in s, f i := by
  have h' : (s.finite_to_set.subset h).toFinset ⊆ s := by
    simpa [Finset.coe_subset, ← Set.coe_to_finset]
  exact finprod_eq_prod_of_mul_support_to_finset_subset _ _ h'

@[to_additive]
theorem finprod_def (f : α → M) [Decidable (MulSupport f).Finite] :
    (∏ᶠ i : α, f i) = if h : (MulSupport f).Finite then ∏ i in h.toFinset, f i else 1 := by
  split_ifs
  · exact finprod_eq_prod_of_mul_support_to_finset_subset _ h (Finset.Subset.refl _)
    
  · rw [finprod, dif_neg]
    rw [mul_support_comp_eq_preimage]
    exact mt (fun hf => hf.of_preimage equiv.plift.surjective) h
    

@[to_additive]
theorem finprod_of_infinite_mul_support {f : α → M} (hf : (MulSupport f).Infinite) : (∏ᶠ i, f i) = 1 := by
  classical
  rw [finprod_def, dif_neg hf]

@[to_additive]
theorem finprod_eq_prod (f : α → M) (hf : (MulSupport f).Finite) : (∏ᶠ i : α, f i) = ∏ i in hf.toFinset, f i := by
  classical
  rw [finprod_def, dif_pos hf]

@[to_additive]
theorem finprod_eq_prod_of_fintype [Fintype α] (f : α → M) : (∏ᶠ i : α, f i) = ∏ i, f i :=
  finprod_eq_prod_of_mul_support_to_finset_subset _ (Set.to_finite _) <| Finset.subset_univ _

@[to_additive]
theorem finprod_cond_eq_prod_of_cond_iff (f : α → M) {p : α → Prop} {t : Finset α}
    (h : ∀ {x}, f x ≠ 1 → (p x ↔ x ∈ t)) : (∏ᶠ (i) (hi : p i), f i) = ∏ i in t, f i := by
  set s := { x | p x }
  have : mul_support (s.mul_indicator f) ⊆ t := by
    rw [Set.mul_support_mul_indicator]
    intro x hx
    exact (h hx.2).1 hx.1
  erw [finprod_mem_def, finprod_eq_prod_of_mul_support_subset _ this]
  refine' Finset.prod_congr rfl fun x hx => mul_indicator_apply_eq_self.2 fun hxs => _
  contrapose! hxs
  exact (h hxs).2 hx

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ≠ » a)
@[to_additive]
theorem finprod_cond_ne (f : α → M) (a : α) [DecidableEq α] (hf : (MulSupport f).Finite) :
    (∏ᶠ (i) (_ : i ≠ a), f i) = ∏ i in hf.toFinset.erase a, f i := by
  apply finprod_cond_eq_prod_of_cond_iff
  intro x hx
  rw [Finset.mem_erase, finite.mem_to_finset, mem_mul_support]
  exact ⟨fun h => And.intro h hx, fun h => h.1⟩

@[to_additive]
theorem finprod_mem_eq_prod_of_inter_mul_support_eq (f : α → M) {s : Set α} {t : Finset α}
    (h : s ∩ MulSupport f = t ∩ MulSupport f) : (∏ᶠ i ∈ s, f i) = ∏ i in t, f i :=
  finprod_cond_eq_prod_of_cond_iff _ <| by
    simpa [← Set.ext_iff] using h

@[to_additive]
theorem finprod_mem_eq_prod_of_subset (f : α → M) {s : Set α} {t : Finset α} (h₁ : s ∩ MulSupport f ⊆ t) (h₂ : ↑t ⊆ s) :
    (∏ᶠ i ∈ s, f i) = ∏ i in t, f i :=
  (finprod_cond_eq_prod_of_cond_iff _) fun x hx => ⟨fun h => h₁ ⟨h, hx⟩, fun h => h₂ h⟩

@[to_additive]
theorem finprod_mem_eq_prod (f : α → M) {s : Set α} (hf : (s ∩ MulSupport f).Finite) :
    (∏ᶠ i ∈ s, f i) = ∏ i in hf.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mul_support_eq _ <| by
    simp [← inter_assoc]

@[to_additive]
theorem finprod_mem_eq_prod_filter (f : α → M) (s : Set α) [DecidablePred (· ∈ s)] (hf : (MulSupport f).Finite) :
    (∏ᶠ i ∈ s, f i) = ∏ i in Finset.filter (· ∈ s) hf.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mul_support_eq _ <| by
    simp [← inter_comm, ← inter_left_comm]

@[to_additive]
theorem finprod_mem_eq_to_finset_prod (f : α → M) (s : Set α) [Fintype s] : (∏ᶠ i ∈ s, f i) = ∏ i in s.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mul_support_eq _ <| by
    rw [coe_to_finset]

@[to_additive]
theorem finprod_mem_eq_finite_to_finset_prod (f : α → M) {s : Set α} (hs : s.Finite) :
    (∏ᶠ i ∈ s, f i) = ∏ i in hs.toFinset, f i :=
  finprod_mem_eq_prod_of_inter_mul_support_eq _ <| by
    rw [hs.coe_to_finset]

@[to_additive]
theorem finprod_mem_finset_eq_prod (f : α → M) (s : Finset α) : (∏ᶠ i ∈ s, f i) = ∏ i in s, f i :=
  finprod_mem_eq_prod_of_inter_mul_support_eq _ rfl

@[to_additive]
theorem finprod_mem_coe_finset (f : α → M) (s : Finset α) : (∏ᶠ i ∈ (s : Set α), f i) = ∏ i in s, f i :=
  finprod_mem_eq_prod_of_inter_mul_support_eq _ rfl

@[to_additive]
theorem finprod_mem_eq_one_of_infinite {f : α → M} {s : Set α} (hs : (s ∩ MulSupport f).Infinite) :
    (∏ᶠ i ∈ s, f i) = 1 := by
  rw [finprod_mem_def]
  apply finprod_of_infinite_mul_support
  rwa [← mul_support_mul_indicator] at hs

@[to_additive]
theorem finprod_mem_eq_one_of_forall_eq_one {f : α → M} {s : Set α} (h : ∀, ∀ x ∈ s, ∀, f x = 1) :
    (∏ᶠ i ∈ s, f i) = 1 := by
  simp (config := { contextual := true })[← h]

@[to_additive]
theorem finprod_mem_inter_mul_support (f : α → M) (s : Set α) : (∏ᶠ i ∈ s ∩ MulSupport f, f i) = ∏ᶠ i ∈ s, f i := by
  rw [finprod_mem_def, finprod_mem_def, mul_indicator_inter_mul_support]

@[to_additive]
theorem finprod_mem_inter_mul_support_eq (f : α → M) (s t : Set α) (h : s ∩ MulSupport f = t ∩ MulSupport f) :
    (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mul_support, h, finprod_mem_inter_mul_support]

@[to_additive]
theorem finprod_mem_inter_mul_support_eq' (f : α → M) (s t : Set α) (h : ∀, ∀ x ∈ MulSupport f, ∀, x ∈ s ↔ x ∈ t) :
    (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ t, f i := by
  apply finprod_mem_inter_mul_support_eq
  ext x
  exact and_congr_left (h x)

@[to_additive]
theorem finprod_mem_univ (f : α → M) : (∏ᶠ i ∈ @Set.Univ α, f i) = ∏ᶠ i : α, f i :=
  finprod_congr fun i => finprod_true _

variable {f g : α → M} {a b : α} {s t : Set α}

@[to_additive]
theorem finprod_mem_congr (h₀ : s = t) (h₁ : ∀, ∀ x ∈ t, ∀, f x = g x) : (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ t, g i :=
  h₀.symm ▸ finprod_congr fun i => finprod_congr_Prop rfl (h₁ i)

@[to_additive]
theorem finprod_eq_one_of_forall_eq_one {f : α → M} (h : ∀ x, f x = 1) : (∏ᶠ i, f i) = 1 := by
  simp (config := { contextual := true })[← h]

/-!
### Distributivity w.r.t. addition, subtraction, and (scalar) multiplication
-/


/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i * g i` equals
the product of `f i` multiplied by the product of `g i`. -/
@[to_additive
      "If the additive supports of `f` and `g` are finite, then the sum of `f i + g i`\nequals the sum of `f i` plus the sum of `g i`."]
theorem finprod_mul_distrib (hf : (MulSupport f).Finite) (hg : (MulSupport g).Finite) :
    (∏ᶠ i, f i * g i) = (∏ᶠ i, f i) * ∏ᶠ i, g i := by
  classical
  rw [finprod_eq_prod_of_mul_support_to_finset_subset _ hf (Finset.subset_union_left _ _),
    finprod_eq_prod_of_mul_support_to_finset_subset _ hg (Finset.subset_union_right _ _), ← Finset.prod_mul_distrib]
  refine' finprod_eq_prod_of_mul_support_subset _ _
  simp [← mul_support_mul]

/-- If the multiplicative supports of `f` and `g` are finite, then the product of `f i / g i`
equals the product of `f i` divided by the product of `g i`. -/
@[to_additive
      "If the additive supports of `f` and `g` are finite, then the sum of `f i - g i`\nequals the sum of `f i` minus the sum of `g i`."]
theorem finprod_div_distrib [DivisionCommMonoid G] {f g : α → G} (hf : (MulSupport f).Finite)
    (hg : (MulSupport g).Finite) : (∏ᶠ i, f i / g i) = (∏ᶠ i, f i) / ∏ᶠ i, g i := by
  simp only [← div_eq_mul_inv, ← finprod_mul_distrib hf ((mul_support_inv g).symm.rec hg), ← finprod_inv_distrib]

/-- A more general version of `finprod_mem_mul_distrib` that only requires `s ∩ mul_support f` and
`s ∩ mul_support g` rather than `s` to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_add_distrib` that only requires `s ∩ support f`\nand `s ∩ support g` rather than `s` to be finite."]
theorem finprod_mem_mul_distrib' (hf : (s ∩ MulSupport f).Finite) (hg : (s ∩ MulSupport g).Finite) :
    (∏ᶠ i ∈ s, f i * g i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i := by
  rw [← mul_support_mul_indicator] at hf hg
  simp only [← finprod_mem_def, ← mul_indicator_mul, ← finprod_mul_distrib hf hg]

/-- The product of the constant function `1` over any set equals `1`. -/
@[to_additive "The product of the constant function `0` over any set equals `0`."]
theorem finprod_mem_one (s : Set α) : (∏ᶠ i ∈ s, (1 : M)) = 1 := by
  simp

/-- If a function `f` equals `1` on a set `s`, then the product of `f i` over `i ∈ s` equals `1`. -/
@[to_additive "If a function `f` equals `0` on a set `s`, then the product of `f i` over `i ∈ s`\nequals `0`."]
theorem finprod_mem_of_eq_on_one (hf : s.EqOn f 1) : (∏ᶠ i ∈ s, f i) = 1 := by
  rw [← finprod_mem_one s]
  exact finprod_mem_congr rfl hf

/-- If the product of `f i` over `i ∈ s` is not equal to `1`, then there is some `x ∈ s` such that
`f x ≠ 1`. -/
@[to_additive
      "If the product of `f i` over `i ∈ s` is not equal to `0`, then there is some `x ∈ s`\nsuch that `f x ≠ 0`."]
theorem exists_ne_one_of_finprod_mem_ne_one (h : (∏ᶠ i ∈ s, f i) ≠ 1) : ∃ x ∈ s, f x ≠ 1 := by
  by_contra' h'
  exact h (finprod_mem_of_eq_on_one h')

/-- Given a finite set `s`, the product of `f i * g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` times the product of `g i` over `i ∈ s`. -/
@[to_additive
      "Given a finite set `s`, the sum of `f i + g i` over `i ∈ s` equals the sum of `f i`\nover `i ∈ s` plus the sum of `g i` over `i ∈ s`."]
theorem finprod_mem_mul_distrib (hs : s.Finite) : (∏ᶠ i ∈ s, f i * g i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ s, g i :=
  finprod_mem_mul_distrib' (hs.inter_of_left _) (hs.inter_of_left _)

@[to_additive]
theorem MonoidHom.map_finprod {f : α → M} (g : M →* N) (hf : (MulSupport f).Finite) : g (∏ᶠ i, f i) = ∏ᶠ i, g (f i) :=
  g.map_finprod_plift f <| hf.Preimage <| Equivₓ.plift.Injective.InjOn _

@[to_additive]
theorem finprod_pow (hf : (MulSupport f).Finite) (n : ℕ) : (∏ᶠ i, f i) ^ n = ∏ᶠ i, f i ^ n :=
  (powMonoidHom n).map_finprod hf

/-- A more general version of `monoid_hom.map_finprod_mem` that requires `s ∩ mul_support f` rather
than `s` to be finite. -/
@[to_additive
      "A more general version of `add_monoid_hom.map_finsum_mem` that requires\n`s ∩ support f` rather than `s` to be finite."]
theorem MonoidHom.map_finprod_mem' {f : α → M} (g : M →* N) (h₀ : (s ∩ MulSupport f).Finite) :
    g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) := by
  rw [g.map_finprod]
  · simp only [← g.map_finprod_Prop]
    
  · simpa only [← finprod_eq_mul_indicator_apply, ← mul_support_mul_indicator]
    

/-- Given a monoid homomorphism `g : M →* N` and a function `f : α → M`, the value of `g` at the
product of `f i` over `i ∈ s` equals the product of `g (f i)` over `s`. -/
@[to_additive
      "Given an additive monoid homomorphism `g : M →* N` and a function `f : α → M`, the\nvalue of `g` at the sum of `f i` over `i ∈ s` equals the sum of `g (f i)` over `s`."]
theorem MonoidHom.map_finprod_mem (f : α → M) (g : M →* N) (hs : s.Finite) : g (∏ᶠ j ∈ s, f j) = ∏ᶠ i ∈ s, g (f i) :=
  g.map_finprod_mem' (hs.inter_of_left _)

@[to_additive]
theorem MulEquiv.map_finprod_mem (g : M ≃* N) (f : α → M) {s : Set α} (hs : s.Finite) :
    g (∏ᶠ i ∈ s, f i) = ∏ᶠ i ∈ s, g (f i) :=
  g.toMonoidHom.map_finprod_mem f hs

@[to_additive]
theorem finprod_mem_inv_distrib [DivisionCommMonoid G] (f : α → G) (hs : s.Finite) :
    (∏ᶠ x ∈ s, (f x)⁻¹) = (∏ᶠ x ∈ s, f x)⁻¹ :=
  ((MulEquiv.inv G).map_finprod_mem f hs).symm

/-- Given a finite set `s`, the product of `f i / g i` over `i ∈ s` equals the product of `f i`
over `i ∈ s` divided by the product of `g i` over `i ∈ s`. -/
@[to_additive
      "Given a finite set `s`, the sum of `f i / g i` over `i ∈ s` equals the sum of `f i`\nover `i ∈ s` minus the sum of `g i` over `i ∈ s`."]
theorem finprod_mem_div_distrib [DivisionCommMonoid G] (f g : α → G) (hs : s.Finite) :
    (∏ᶠ i ∈ s, f i / g i) = (∏ᶠ i ∈ s, f i) / ∏ᶠ i ∈ s, g i := by
  simp only [← div_eq_mul_inv, ← finprod_mem_mul_distrib hs, ← finprod_mem_inv_distrib g hs]

/-!
### `∏ᶠ x ∈ s, f x` and set operations
-/


/-- The product of any function over an empty set is `1`. -/
@[to_additive "The sum of any function over an empty set is `0`."]
theorem finprod_mem_empty : (∏ᶠ i ∈ (∅ : Set α), f i) = 1 := by
  simp

/-- A set `s` is nonempty if the product of some function over `s` is not equal to `1`. -/
@[to_additive "A set `s` is nonempty if the sum of some function over `s` is not equal to `0`."]
theorem nonempty_of_finprod_mem_ne_one (h : (∏ᶠ i ∈ s, f i) ≠ 1) : s.Nonempty :=
  ne_empty_iff_nonempty.1 fun h' => h <| h'.symm ▸ finprod_mem_empty

/-- Given finite sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` times the product of
`f i` over `i ∈ s ∩ t` equals the product of `f i` over `i ∈ s` times the product of `f i`
over `i ∈ t`. -/
@[to_additive
      "Given finite sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` plus the sum of\n`f i` over `i ∈ s ∩ t` equals the sum of `f i` over `i ∈ s` plus the sum of `f i` over `i ∈ t`."]
theorem finprod_mem_union_inter (hs : s.Finite) (ht : t.Finite) :
    ((∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  lift s to Finset α using hs
  lift t to Finset α using ht
  classical
  rw [← Finset.coe_union, ← Finset.coe_inter]
  simp only [← finprod_mem_coe_finset, ← Finset.prod_union_inter]

/-- A more general version of `finprod_mem_union_inter` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` rather than `s` and `t` to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_union_inter` that requires `s ∩ support f` and\n`t ∩ support f` rather than `s` and `t` to be finite."]
theorem finprod_mem_union_inter' (hs : (s ∩ MulSupport f).Finite) (ht : (t ∩ MulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∪ t, f i) * ∏ᶠ i ∈ s ∩ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mul_support f s, ← finprod_mem_inter_mul_support f t, ← finprod_mem_union_inter hs ht, ←
    union_inter_distrib_right, finprod_mem_inter_mul_support, ← finprod_mem_inter_mul_support f (s ∩ t)]
  congr 2
  rw [inter_left_comm, inter_assoc, inter_assoc, inter_self, inter_left_comm]

/-- A more general version of `finprod_mem_union` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` rather than `s` and `t` to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_union` that requires `s ∩ support f` and\n`t ∩ support f` rather than `s` and `t` to be finite."]
theorem finprod_mem_union' (hst : Disjoint s t) (hs : (s ∩ MulSupport f).Finite) (ht : (t ∩ MulSupport f).Finite) :
    (∏ᶠ i ∈ s ∪ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_union_inter' hs ht, disjoint_iff_inter_eq_empty.1 hst, finprod_mem_empty, mul_oneₓ]

/-- Given two finite disjoint sets `s` and `t`, the product of `f i` over `i ∈ s ∪ t` equals the
product of `f i` over `i ∈ s` times the product of `f i` over `i ∈ t`. -/
@[to_additive
      "Given two finite disjoint sets `s` and `t`, the sum of `f i` over `i ∈ s ∪ t` equals\nthe sum of `f i` over `i ∈ s` plus the sum of `f i` over `i ∈ t`."]
theorem finprod_mem_union (hst : Disjoint s t) (hs : s.Finite) (ht : t.Finite) :
    (∏ᶠ i ∈ s ∪ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i :=
  finprod_mem_union' hst (hs.inter_of_left _) (ht.inter_of_left _)

/-- A more general version of `finprod_mem_union'` that requires `s ∩ mul_support f` and
`t ∩ mul_support f` rather than `s` and `t` to be disjoint -/
@[to_additive
      "A more general version of `finsum_mem_union'` that requires `s ∩ support f` and\n`t ∩ support f` rather than `s` and `t` to be disjoint"]
theorem finprod_mem_union'' (hst : Disjoint (s ∩ MulSupport f) (t ∩ MulSupport f)) (hs : (s ∩ MulSupport f).Finite)
    (ht : (t ∩ MulSupport f).Finite) : (∏ᶠ i ∈ s ∪ t, f i) = (∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mul_support f s, ← finprod_mem_inter_mul_support f t, ← finprod_mem_union hst hs ht, ←
    union_inter_distrib_right, finprod_mem_inter_mul_support]

/-- The product of `f i` over `i ∈ {a}` equals `f a`. -/
@[to_additive "The sum of `f i` over `i ∈ {a}` equals `f a`."]
theorem finprod_mem_singleton : (∏ᶠ i ∈ ({a} : Set α), f i) = f a := by
  rw [← Finset.coe_singleton, finprod_mem_coe_finset, Finset.prod_singleton]

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr = » a)
@[simp, to_additive]
theorem finprod_cond_eq_left : (∏ᶠ (i) (_ : i = a), f i) = f a :=
  finprod_mem_singleton

@[simp, to_additive]
theorem finprod_cond_eq_right : (∏ᶠ (i) (hi : a = i), f i) = f a := by
  simp [← @eq_comm _ a]

/-- A more general version of `finprod_mem_insert` that requires `s ∩ mul_support f` rather than `s`
to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_insert` that requires `s ∩ support f` rather\nthan `s` to be finite."]
theorem finprod_mem_insert' (f : α → M) (h : a ∉ s) (hs : (s ∩ MulSupport f).Finite) :
    (∏ᶠ i ∈ insert a s, f i) = f a * ∏ᶠ i ∈ s, f i := by
  rw [insert_eq, finprod_mem_union' _ _ hs, finprod_mem_singleton]
  · rwa [disjoint_singleton_left]
    
  · exact (finite_singleton a).inter_of_left _
    

/-- Given a finite set `s` and an element `a ∉ s`, the product of `f i` over `i ∈ insert a s` equals
`f a` times the product of `f i` over `i ∈ s`. -/
@[to_additive
      "Given a finite set `s` and an element `a ∉ s`, the sum of `f i` over `i ∈ insert a s`\nequals `f a` plus the sum of `f i` over `i ∈ s`."]
theorem finprod_mem_insert (f : α → M) (h : a ∉ s) (hs : s.Finite) : (∏ᶠ i ∈ insert a s, f i) = f a * ∏ᶠ i ∈ s, f i :=
  finprod_mem_insert' f h <| hs.inter_of_left _

/-- If `f a = 1` when `a ∉ s`, then the product of `f i` over `i ∈ insert a s` equals the product of
`f i` over `i ∈ s`. -/
@[to_additive
      "If `f a = 0` when `a ∉ s`, then the sum of `f i` over `i ∈ insert a s` equals the sum\nof `f i` over `i ∈ s`."]
theorem finprod_mem_insert_of_eq_one_if_not_mem (h : a ∉ s → f a = 1) : (∏ᶠ i ∈ insert a s, f i) = ∏ᶠ i ∈ s, f i := by
  refine' finprod_mem_inter_mul_support_eq' _ _ _ fun x hx => ⟨_, Or.inr⟩
  rintro (rfl | hxs)
  exacts[not_imp_comm.1 h hx, hxs]

/-- If `f a = 1`, then the product of `f i` over `i ∈ insert a s` equals the product of `f i` over
`i ∈ s`. -/
@[to_additive "If `f a = 0`, then the sum of `f i` over `i ∈ insert a s` equals the sum of `f i`\nover `i ∈ s`."]
theorem finprod_mem_insert_one (h : f a = 1) : (∏ᶠ i ∈ insert a s, f i) = ∏ᶠ i ∈ s, f i :=
  finprod_mem_insert_of_eq_one_if_not_mem fun _ => h

/-- If the multiplicative support of `f` is finite, then for every `x` in the domain of `f`, `f x`
divides `finprod f`.  -/
theorem finprod_mem_dvd {f : α → N} (a : α) (hf : (MulSupport f).Finite) : f a ∣ finprod f := by
  by_cases' ha : a ∈ mul_support f
  · rw [finprod_eq_prod_of_mul_support_to_finset_subset f hf (Set.Subset.refl _)]
    exact Finset.dvd_prod_of_mem f ((finite.mem_to_finset hf).mpr ha)
    
  · rw [nmem_mul_support.mp ha]
    exact one_dvd (finprod f)
    

/-- The product of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a * f b`. -/
@[to_additive "The sum of `f i` over `i ∈ {a, b}`, `a ≠ b`, is equal to `f a + f b`."]
theorem finprod_mem_pair (h : a ≠ b) : (∏ᶠ i ∈ ({a, b} : Set α), f i) = f a * f b := by
  rw [finprod_mem_insert, finprod_mem_singleton]
  exacts[h, finite_singleton b]

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s`
provided that `g` is injective on `s ∩ mul_support (f ∘ g)`. -/
@[to_additive
      "The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that\n`g` is injective on `s ∩ support (f ∘ g)`."]
theorem finprod_mem_image' {s : Set β} {g : β → α} (hg : (s ∩ MulSupport (f ∘ g)).InjOn g) :
    (∏ᶠ i ∈ g '' s, f i) = ∏ᶠ j ∈ s, f (g j) := by
  classical
  by_cases' hs : (s ∩ mul_support (f ∘ g)).Finite
  · have hg : ∀, ∀ x ∈ hs.to_finset, ∀, ∀ y ∈ hs.to_finset, ∀, g x = g y → x = y := by
      simpa only [← hs.mem_to_finset]
    rw [finprod_mem_eq_prod _ hs, ← Finset.prod_image hg]
    refine' finprod_mem_eq_prod_of_inter_mul_support_eq f _
    rw [Finset.coe_image, hs.coe_to_finset, ← image_inter_mul_support_eq, inter_assoc, inter_self]
    
  · rw [finprod_mem_eq_one_of_infinite hs, finprod_mem_eq_one_of_infinite]
    rwa [image_inter_mul_support_eq, infinite_image_iff hg]
    

/-- The product of `f y` over `y ∈ g '' s` equals the product of `f (g i)` over `s` provided that
`g` is injective on `s`. -/
@[to_additive
      "The sum of `f y` over `y ∈ g '' s` equals the sum of `f (g i)` over `s` provided that\n`g` is injective on `s`."]
theorem finprod_mem_image {s : Set β} {g : β → α} (hg : s.InjOn g) : (∏ᶠ i ∈ g '' s, f i) = ∏ᶠ j ∈ s, f (g j) :=
  finprod_mem_image' <| hg.mono <| inter_subset_left _ _

/-- The product of `f y` over `y ∈ set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective on `mul_support (f ∘ g)`. -/
@[to_additive
      "The sum of `f y` over `y ∈ set.range g` equals the sum of `f (g i)` over all `i`\nprovided that `g` is injective on `support (f ∘ g)`."]
theorem finprod_mem_range' {g : β → α} (hg : (MulSupport (f ∘ g)).InjOn g) : (∏ᶠ i ∈ Range g, f i) = ∏ᶠ j, f (g j) := by
  rw [← image_univ, finprod_mem_image', finprod_mem_univ]
  rwa [univ_inter]

/-- The product of `f y` over `y ∈ set.range g` equals the product of `f (g i)` over all `i`
provided that `g` is injective. -/
@[to_additive
      "The sum of `f y` over `y ∈ set.range g` equals the sum of `f (g i)` over all `i`\nprovided that `g` is injective."]
theorem finprod_mem_range {g : β → α} (hg : Injective g) : (∏ᶠ i ∈ Range g, f i) = ∏ᶠ j, f (g j) :=
  finprod_mem_range' (hg.InjOn _)

/-- See also `finset.prod_bij`. -/
@[to_additive "See also `finset.sum_bij`."]
theorem finprod_mem_eq_of_bij_on {s : Set α} {t : Set β} {f : α → M} {g : β → M} (e : α → β) (he₀ : s.BijOn e t)
    (he₁ : ∀, ∀ x ∈ s, ∀, f x = g (e x)) : (∏ᶠ i ∈ s, f i) = ∏ᶠ j ∈ t, g j := by
  rw [← Set.BijOn.image_eq he₀, finprod_mem_image he₀.2.1]
  exact finprod_mem_congr rfl he₁

/-- See `finprod_comp`, `fintype.prod_bijective` and `finset.prod_bij`. -/
@[to_additive "See `finsum_comp`, `fintype.sum_bijective` and `finset.sum_bij`."]
theorem finprod_eq_of_bijective {f : α → M} {g : β → M} (e : α → β) (he₀ : Bijective e) (he₁ : ∀ x, f x = g (e x)) :
    (∏ᶠ i, f i) = ∏ᶠ j, g j := by
  rw [← finprod_mem_univ f, ← finprod_mem_univ g]
  exact finprod_mem_eq_of_bij_on _ (bijective_iff_bij_on_univ.mp he₀) fun x _ => he₁ x

/-- See also `finprod_eq_of_bijective`, `fintype.prod_bijective` and `finset.prod_bij`. -/
@[to_additive "See also `finsum_eq_of_bijective`, `fintype.sum_bijective` and `finset.sum_bij`."]
theorem finprod_comp {g : β → M} (e : α → β) (he₀ : Function.Bijective e) : (∏ᶠ i, g (e i)) = ∏ᶠ j, g j :=
  finprod_eq_of_bijective e he₀ fun x => rfl

@[to_additive]
theorem finprod_set_coe_eq_finprod_mem (s : Set α) : (∏ᶠ j : s, f j) = ∏ᶠ i ∈ s, f i := by
  rw [← finprod_mem_range, Subtype.range_coe]
  exact Subtype.coe_injective

@[to_additive]
theorem finprod_subtype_eq_finprod_cond (p : α → Prop) : (∏ᶠ j : Subtype p, f j) = ∏ᶠ (i) (hi : p i), f i :=
  finprod_set_coe_eq_finprod_mem { i | p i }

@[to_additive]
theorem finprod_mem_inter_mul_diff' (t : Set α) (h : (s ∩ MulSupport f).Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i := by
  rw [← finprod_mem_union', inter_union_diff]
  exacts[fun x hx => hx.2.2 hx.1.2, h.subset fun x hx => ⟨hx.1.1, hx.2⟩, h.subset fun x hx => ⟨hx.1.1, hx.2⟩]

@[to_additive]
theorem finprod_mem_inter_mul_diff (t : Set α) (h : s.Finite) :
    ((∏ᶠ i ∈ s ∩ t, f i) * ∏ᶠ i ∈ s \ t, f i) = ∏ᶠ i ∈ s, f i :=
  finprod_mem_inter_mul_diff' _ <| h.inter_of_left _

/-- A more general version of `finprod_mem_mul_diff` that requires `t ∩ mul_support f` rather than
`t` to be finite. -/
@[to_additive
      "A more general version of `finsum_mem_add_diff` that requires `t ∩ support f` rather\nthan `t` to be finite."]
theorem finprod_mem_mul_diff' (hst : s ⊆ t) (ht : (t ∩ MulSupport f).Finite) :
    ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i := by
  rw [← finprod_mem_inter_mul_diff' _ ht, inter_eq_self_of_subset_right hst]

/-- Given a finite set `t` and a subset `s` of `t`, the product of `f i` over `i ∈ s`
times the product of `f i` over `t \ s` equals the product of `f i` over `i ∈ t`. -/
@[to_additive
      "Given a finite set `t` and a subset `s` of `t`, the sum of `f i` over `i ∈ s` plus\nthe sum of `f i` over `t \\ s` equals the sum of `f i` over `i ∈ t`."]
theorem finprod_mem_mul_diff (hst : s ⊆ t) (ht : t.Finite) : ((∏ᶠ i ∈ s, f i) * ∏ᶠ i ∈ t \ s, f i) = ∏ᶠ i ∈ t, f i :=
  finprod_mem_mul_diff' hst (ht.inter_of_left _)

/-- Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the product of
`f a` over the union `⋃ i, t i` is equal to the product over all indexes `i` of the products of
`f a` over `a ∈ t i`. -/
@[to_additive
      "Given a family of pairwise disjoint finite sets `t i` indexed by a finite type, the\nsum of `f a` over the union `⋃ i, t i` is equal to the sum over all indexes `i` of the sums of `f a`\nover `a ∈ t i`."]
theorem finprod_mem_Union [Fintype ι] {t : ι → Set α} (h : Pairwise (Disjoint on t)) (ht : ∀ i, (t i).Finite) :
    (∏ᶠ a ∈ ⋃ i : ι, t i, f a) = ∏ᶠ i, ∏ᶠ a ∈ t i, f a := by
  lift t to ι → Finset α using ht
  classical
  rw [← bUnion_univ, ← Finset.coe_univ, ← Finset.coe_bUnion, finprod_mem_coe_finset, Finset.prod_bUnion]
  · simp only [← finprod_mem_coe_finset, ← finprod_eq_prod_of_fintype]
    
  · exact fun x _ y _ hxy => Finset.disjoint_coe.1 (h x y hxy)
    

/-- Given a family of sets `t : ι → set α`, a finite set `I` in the index type such that all sets
`t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the product of `f a`
over `a ∈ ⋃ i ∈ I, t i` is equal to the product over `i ∈ I` of the products of `f a` over
`a ∈ t i`. -/
@[to_additive
      "Given a family of sets `t : ι → set α`, a finite set `I` in the index type such that\nall sets `t i`, `i ∈ I`, are finite, if all `t i`, `i ∈ I`, are pairwise disjoint, then the sum of\n`f a` over `a ∈ ⋃ i ∈ I, t i` is equal to the sum over `i ∈ I` of the sums of `f a` over\n`a ∈ t i`."]
theorem finprod_mem_bUnion {I : Set ι} {t : ι → Set α} (h : I.PairwiseDisjoint t) (hI : I.Finite)
    (ht : ∀, ∀ i ∈ I, ∀, (t i).Finite) : (∏ᶠ a ∈ ⋃ x ∈ I, t x, f a) = ∏ᶠ i ∈ I, ∏ᶠ j ∈ t i, f j := by
  have := hI.fintype
  rw [bUnion_eq_Union, finprod_mem_Union, ← finprod_set_coe_eq_finprod_mem]
  exacts[fun x y hxy => h x.2 y.2 (subtype.coe_injective.ne hxy), fun b => ht b b.2]

/-- If `t` is a finite set of pairwise disjoint finite sets, then the product of `f a`
over `a ∈ ⋃₀ t` is the product over `s ∈ t` of the products of `f a` over `a ∈ s`. -/
@[to_additive
      "If `t` is a finite set of pairwise disjoint finite sets, then the sum of `f a` over\n`a ∈ ⋃₀ t` is the sum over `s ∈ t` of the sums of `f a` over `a ∈ s`."]
theorem finprod_mem_sUnion {t : Set (Set α)} (h : t.PairwiseDisjoint id) (ht₀ : t.Finite)
    (ht₁ : ∀, ∀ x ∈ t, ∀, Set.Finite x) : (∏ᶠ a ∈ ⋃₀t, f a) = ∏ᶠ s ∈ t, ∏ᶠ a ∈ s, f a := by
  rw [Set.sUnion_eq_bUnion]
  exact finprod_mem_bUnion h ht₀ ht₁

-- ./././Mathport/Syntax/Translate/Basic.lean:710:2: warning: expanding binder collection (i «expr ≠ » a)
@[to_additive]
theorem mul_finprod_cond_ne (a : α) (hf : (MulSupport f).Finite) : (f a * ∏ᶠ (i) (_ : i ≠ a), f i) = ∏ᶠ i, f i := by
  classical
  rw [finprod_eq_prod _ hf]
  have h : ∀ x : α, f x ≠ 1 → (x ≠ a ↔ x ∈ hf.to_finset \ {a}) := by
    intro x hx
    rw [Finset.mem_sdiff, Finset.mem_singleton, finite.mem_to_finset, mem_mul_support]
    exact ⟨fun h => And.intro hx h, fun h => h.2⟩
  rw [finprod_cond_eq_prod_of_cond_iff f h, Finset.sdiff_singleton_eq_erase]
  by_cases' ha : a ∈ mul_support f
  · apply Finset.mul_prod_erase _ _ ((finite.mem_to_finset _).mpr ha)
    
  · rw [mem_mul_support, not_not] at ha
    rw [ha, one_mulₓ]
    apply Finset.prod_erase _ ha
    

/-- If `s : set α` and `t : set β` are finite sets, then taking the product over `s` commutes with
taking the product over `t`. -/
@[to_additive "If `s : set α` and `t : set β` are finite sets, then summing over `s` commutes with\nsumming over `t`."]
theorem finprod_mem_comm {s : Set α} {t : Set β} (f : α → β → M) (hs : s.Finite) (ht : t.Finite) :
    (∏ᶠ i ∈ s, ∏ᶠ j ∈ t, f i j) = ∏ᶠ j ∈ t, ∏ᶠ i ∈ s, f i j := by
  lift s to Finset α using hs
  lift t to Finset β using ht
  simp only [← finprod_mem_coe_finset]
  exact Finset.prod_comm

/-- To prove a property of a finite product, it suffices to prove that the property is
multiplicative and holds on factors. -/
@[to_additive
      "To prove a property of a finite sum, it suffices to prove that the property is\nadditive and holds on summands."]
theorem finprod_mem_induction (p : M → Prop) (hp₀ : p 1) (hp₁ : ∀ x y, p x → p y → p (x * y))
    (hp₂ : ∀, ∀ x ∈ s, ∀, p <| f x) : p (∏ᶠ i ∈ s, f i) :=
  (finprod_induction _ hp₀ hp₁) fun x => finprod_induction _ hp₀ hp₁ <| hp₂ x

theorem finprod_cond_nonneg {R : Type _} [OrderedCommSemiring R] {p : α → Prop} {f : α → R} (hf : ∀ x, p x → 0 ≤ f x) :
    0 ≤ ∏ᶠ (x) (h : p x), f x :=
  finprod_nonneg fun x => finprod_nonneg <| hf x

@[to_additive]
theorem single_le_finprod {M : Type _} [OrderedCommMonoid M] (i : α) {f : α → M} (hf : (MulSupport f).Finite)
    (h : ∀ j, 1 ≤ f j) : f i ≤ ∏ᶠ j, f j := by
  classical <;>
    calc f i ≤ ∏ j in insert i hf.to_finset, f j :=
        Finset.single_le_prod' (fun j hj => h j) (Finset.mem_insert_self _ _)_ = ∏ᶠ j, f j :=
        (finprod_eq_prod_of_mul_support_to_finset_subset _ hf (Finset.subset_insert _ _)).symm

theorem finprod_eq_zero {M₀ : Type _} [CommMonoidWithZero M₀] (f : α → M₀) (x : α) (hx : f x = 0)
    (hf : (MulSupport f).Finite) : (∏ᶠ x, f x) = 0 := by
  nontriviality
  rw [finprod_eq_prod f hf]
  refine' Finset.prod_eq_zero (hf.mem_to_finset.2 _) hx
  simp [← hx]

@[to_additive]
theorem finprod_prod_comm (s : Finset β) (f : α → β → M) (h : ∀, ∀ b ∈ s, ∀, (MulSupport fun a => f a b).Finite) :
    (∏ᶠ a : α, ∏ b in s, f a b) = ∏ b in s, ∏ᶠ a : α, f a b := by
  have hU :
    (mul_support fun a => ∏ b in s, f a b) ⊆ (s.finite_to_set.bUnion fun b hb => h b (Finset.mem_coe.1 hb)).toFinset :=
    by
    rw [finite.coe_to_finset]
    intro x hx
    simp only [← exists_prop, ← mem_Union, ← Ne.def, ← mem_mul_support, ← Finset.mem_coe]
    contrapose! hx
    rw [mem_mul_support, not_not, Finset.prod_congr rfl hx, Finset.prod_const_one]
  rw [finprod_eq_prod_of_mul_support_subset _ hU, Finset.prod_comm]
  refine' Finset.prod_congr rfl fun b hb => (finprod_eq_prod_of_mul_support_subset _ _).symm
  intro a ha
  simp only [← finite.coe_to_finset, ← mem_Union]
  exact ⟨b, hb, ha⟩

@[to_additive]
theorem prod_finprod_comm (s : Finset α) (f : α → β → M) (h : ∀, ∀ a ∈ s, ∀, (MulSupport (f a)).Finite) :
    (∏ a in s, ∏ᶠ b : β, f a b) = ∏ᶠ b : β, ∏ a in s, f a b :=
  (finprod_prod_comm s (fun b a => f a b) h).symm

theorem mul_finsum {R : Type _} [Semiringₓ R] (f : α → R) (r : R) (h : (Support f).Finite) :
    (r * ∑ᶠ a : α, f a) = ∑ᶠ a : α, r * f a :=
  (AddMonoidHom.mulLeft r).map_finsum h

theorem finsum_mul {R : Type _} [Semiringₓ R] (f : α → R) (r : R) (h : (Support f).Finite) :
    (∑ᶠ a : α, f a) * r = ∑ᶠ a : α, f a * r :=
  (AddMonoidHom.mulRight r).map_finsum h

@[to_additive]
theorem Finset.mul_support_of_fiberwise_prod_subset_image [DecidableEq β] (s : Finset α) (f : α → M) (g : α → β) :
    (MulSupport fun b => (s.filter fun a => g a = b).Prod f) ⊆ s.Image g := by
  simp only [← Finset.coe_image, ← Set.mem_image, ← Finset.mem_coe, ← Function.support_subset_iff]
  intro b h
  suffices (s.filter fun a : α => g a = b).Nonempty by
    simpa only [← s.fiber_nonempty_iff_mem_image g b, ← Finset.mem_image, ← exists_prop]
  exact Finset.nonempty_of_prod_ne_one h

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (a b)
/-- Note that `b ∈ (s.filter (λ ab, prod.fst ab = a)).image prod.snd` iff `(a, b) ∈ s` so we can
simplify the right hand side of this lemma. However the form stated here is more useful for
iterating this lemma, e.g., if we have `f : α × β × γ → M`. -/
@[to_additive
      "Note that `b ∈ (s.filter (λ ab, prod.fst ab = a)).image prod.snd` iff `(a, b) ∈ s` so\nwe can simplify the right hand side of this lemma. However the form stated here is more useful for\niterating this lemma, e.g., if we have `f : α × β × γ → M`."]
theorem finprod_mem_finset_product' [DecidableEq α] [DecidableEq β] (s : Finset (α × β)) (f : α × β → M) :
    (∏ᶠ (ab) (h : ab ∈ s), f ab) = ∏ᶠ (a) (b) (h : b ∈ (s.filter fun ab => Prod.fst ab = a).Image Prod.snd), f (a, b) :=
  by
  have :
    ∀ a,
      (∏ i : β in (s.filter fun ab => Prod.fst ab = a).Image Prod.snd, f (a, i)) =
        (Finset.filter (fun ab => Prod.fst ab = a) s).Prod f :=
    by
    refine' fun a => Finset.prod_bij (fun b _ => (a, b)) _ _ _ _ <;>-- `finish` closes these goals
      try
        simp
        done
    suffices ∀ a' b, (a', b) ∈ s → a' = a → (a, b) ∈ s ∧ a' = a by
      simpa
    rintro a' b hp rfl
    exact ⟨hp, rfl⟩
  rw [finprod_mem_finset_eq_prod]
  simp_rw [finprod_mem_finset_eq_prod, this]
  rw [finprod_eq_prod_of_mul_support_subset _ (s.mul_support_of_fiberwise_prod_subset_image f Prod.fst), ←
    Finset.prod_fiberwise_of_maps_to _ f]
  -- `finish` could close the goal here
  simp only [← Finset.mem_image, ← Prod.mk.eta]
  exact fun x hx => ⟨x, hx, rfl⟩

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (a b)
/-- See also `finprod_mem_finset_product'`. -/
@[to_additive "See also `finsum_mem_finset_product'`."]
theorem finprod_mem_finset_product (s : Finset (α × β)) (f : α × β → M) :
    (∏ᶠ (ab) (h : ab ∈ s), f ab) = ∏ᶠ (a) (b) (h : (a, b) ∈ s), f (a, b) := by
  classical
  rw [finprod_mem_finset_product']
  simp

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (a b c)
@[to_additive]
theorem finprod_mem_finset_product₃ {γ : Type _} (s : Finset (α × β × γ)) (f : α × β × γ → M) :
    (∏ᶠ (abc) (h : abc ∈ s), f abc) = ∏ᶠ (a) (b) (c) (h : (a, b, c) ∈ s), f (a, b, c) := by
  classical
  rw [finprod_mem_finset_product']
  simp_rw [finprod_mem_finset_product']
  simp

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (a b)
@[to_additive]
theorem finprod_curry (f : α × β → M) (hf : (MulSupport f).Finite) : (∏ᶠ ab, f ab) = ∏ᶠ (a) (b), f (a, b) := by
  have h₁ : ∀ a, (∏ᶠ h : a ∈ hf.to_finset, f a) = f a := by
    simp
  have h₂ : (∏ᶠ a, f a) = ∏ᶠ (a) (h : a ∈ hf.to_finset), f a := by
    simp
  simp_rw [h₂, finprod_mem_finset_product, h₁]

-- ./././Mathport/Syntax/Translate/Basic.lean:853:6: warning: expanding binder group (a b c)
@[to_additive]
theorem finprod_curry₃ {γ : Type _} (f : α × β × γ → M) (h : (MulSupport f).Finite) :
    (∏ᶠ abc, f abc) = ∏ᶠ (a) (b) (c), f (a, b, c) := by
  rw [finprod_curry f h]
  congr
  ext a
  rw [finprod_curry]
  simp [← h]

@[to_additive]
theorem finprod_dmem {s : Set α} [DecidablePred (· ∈ s)] (f : ∀ a : α, a ∈ s → M) :
    (∏ᶠ (a : α) (h : a ∈ s), f a h) = ∏ᶠ (a : α) (h : a ∈ s), if h' : a ∈ s then f a h' else 1 :=
  finprod_congr fun a => finprod_congr fun ha => (dif_pos ha).symm

@[to_additive]
theorem finprod_emb_domain' {f : α → β} (hf : Injective f) [DecidablePred (· ∈ Set.Range f)] (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.Range f then g (Classical.some h) else 1) = ∏ᶠ a : α, g a := by
  simp_rw [← finprod_eq_dif]
  rw [finprod_dmem, finprod_mem_range hf, finprod_congr fun a => _]
  rw [dif_pos (Set.mem_range_self a), hf (Classical.some_spec (Set.mem_range_self a))]

@[to_additive]
theorem finprod_emb_domain (f : α ↪ β) [DecidablePred (· ∈ Set.Range f)] (g : α → M) :
    (∏ᶠ b : β, if h : b ∈ Set.Range f then g (Classical.some h) else 1) = ∏ᶠ a : α, g a :=
  finprod_emb_domain' f.Injective g

end Type

