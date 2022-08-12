/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
import Mathbin.Analysis.NormedSpace.Basic
import Mathbin.Topology.Algebra.Order.LiminfLimsup
import Mathbin.Topology.LocalHomeomorph

/-!
# Asymptotics

We introduce these relations:

* `is_O_with c l f g` : "f is big O of g along l with constant c";
* `f =O[l] g` : "f is big O of g along l";
* `f =o[l] g` : "f is little o of g along l".

Here `l` is any filter on the domain of `f` and `g`, which are assumed to be the same. The codomains
of `f` and `g` do not need to be the same; all that is needed that there is a norm associated with
these types, and it is the norm that is compared asymptotically.

The relation `is_O_with c` is introduced to factor out common algebraic arguments in the proofs of
similar properties of `is_O` and `is_o`. Usually proofs outside of this file should use `is_O`
instead.

Often the ranges of `f` and `g` will be the real numbers, in which case the norm is the absolute
value. In general, we have

  `f =O[l] g ↔ (λ x, ∥f x∥) =O[l] (λ x, ∥g x∥)`,

and similarly for `is_o`. But our setup allows us to use the notions e.g. with functions
to the integers, rationals, complex numbers, or any normed vector space without mentioning the
norm explicitly.

If `f` and `g` are functions to a normed field like the reals or complex numbers and `g` is always
nonzero, we have

  `f =o[l] g ↔ tendsto (λ x, f x / (g x)) l (𝓝 0)`.

In fact, the right-to-left direction holds without the hypothesis on `g`, and in the other direction
it suffices to assume that `f` is zero wherever `g` is. (This generalization is useful in defining
the Fréchet derivative.)
-/


open Filter Set

open TopologicalSpace BigOperators Classical Filter Nnreal

namespace Asymptotics

variable {α : Type _} {β : Type _} {E : Type _} {F : Type _} {G : Type _} {E' : Type _} {F' : Type _} {G' : Type _}
  {E'' : Type _} {F'' : Type _} {G'' : Type _} {R : Type _} {R' : Type _} {𝕜 : Type _} {𝕜' : Type _}

variable [HasNorm E] [HasNorm F] [HasNorm G]

variable [SemiNormedGroup E'] [SemiNormedGroup F'] [SemiNormedGroup G']

variable [NormedGroup E''] [NormedGroup F''] [NormedGroup G'']

variable [SemiNormedRing R] [SemiNormedRing R']

variable [NormedField 𝕜] [NormedField 𝕜']

variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}

variable {f' : α → E'} {g' : α → F'} {k' : α → G'}

variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}

variable {l l' : Filter α}

section Defs

/-! ### Definitions -/


/-- This version of the Landau notation `is_O_with C l f g` where `f` and `g` are two functions on
a type `α` and `l` is a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by `C * ∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded by `C`, modulo division by zero issues that are
avoided by this definition. Probably you want to use `is_O` instead of this relation. -/
irreducible_def IsOWith (c : ℝ) (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥

/-- Definition of `is_O_with`. We record it in a lemma as `is_O_with` is irreducible. -/
theorem is_O_with_iff : IsOWith c l f g ↔ ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ := by
  rw [is_O_with]

alias is_O_with_iff ↔ is_O_with.bound is_O_with.of_bound

/-- The Landau notation `f =O[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by a constant multiple of `∥g∥`.
In other words, `∥f∥ / ∥g∥` is eventually bounded, modulo division by zero issues that are avoided
by this definition. -/
irreducible_def IsO (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∃ c : ℝ, IsOWith c l f g

-- mathport name: «expr =O[ ] »
notation:100 f " =O[" l "] " g:100 => IsO l f g

/-- Definition of `is_O` in terms of `is_O_with`. We record it in a lemma as `is_O` is
irreducible. -/
theorem is_O_iff_is_O_with : f =O[l] g ↔ ∃ c : ℝ, IsOWith c l f g := by
  rw [is_O]

/-- Definition of `is_O` in terms of filters. We record it in a lemma as we will set
`is_O` to be irreducible at the end of this file. -/
theorem is_O_iff : f =O[l] g ↔ ∃ c : ℝ, ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ := by
  simp only [← is_O, ← is_O_with]

theorem IsO.of_bound (c : ℝ) (h : ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥) : f =O[l] g :=
  is_O_iff.2 ⟨c, h⟩

theorem IsO.bound : f =O[l] g → ∃ c : ℝ, ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ :=
  is_O_iff.1

/-- The Landau notation `f =o[l] g` where `f` and `g` are two functions on a type `α` and `l` is
a filter on `α`, means that eventually for `l`, `∥f∥` is bounded by an arbitrarily small constant
multiple of `∥g∥`. In other words, `∥f∥ / ∥g∥` tends to `0` along `l`, modulo division by zero
issues that are avoided by this definition. -/
irreducible_def IsOₓ (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  ∀ ⦃c : ℝ⦄, 0 < c → IsOWith c l f g

-- mathport name: «expr =o[ ] »
notation:100 f " =o[" l "] " g:100 => IsOₓ l f g

/-- Definition of `is_o` in terms of `is_O_with`. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem is_o_iff_forall_is_O_with : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → IsOWith c l f g := by
  rw [is_o]

alias is_o_iff_forall_is_O_with ↔ is_o.forall_is_O_with is_o.of_is_O_with

/-- Definition of `is_o` in terms of filters. We record it in a lemma as we will set
`is_o` to be irreducible at the end of this file. -/
theorem is_o_iff : f =o[l] g ↔ ∀ ⦃c : ℝ⦄, 0 < c → ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ := by
  simp only [← is_o, ← is_O_with]

alias is_o_iff ↔ is_o.bound is_o.of_bound

theorem IsOₓ.def (h : f =o[l] g) (hc : 0 < c) : ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥ :=
  is_o_iff.1 h hc

theorem IsOₓ.def' (h : f =o[l] g) (hc : 0 < c) : IsOWith c l f g :=
  is_O_with_iff.2 <| is_o_iff.1 h hc

end Defs

/-! ### Conversions -/


theorem IsOWith.is_O (h : IsOWith c l f g) : f =O[l] g := by
  rw [is_O] <;> exact ⟨c, h⟩

theorem IsOₓ.is_O_with (hgf : f =o[l] g) : IsOWith 1 l f g :=
  hgf.def' zero_lt_one

theorem IsOₓ.is_O (hgf : f =o[l] g) : f =O[l] g :=
  hgf.IsOWith.IsO

theorem IsO.is_O_with : f =O[l] g → ∃ c : ℝ, IsOWith c l f g :=
  is_O_iff_is_O_with.1

theorem IsOWith.weaken (h : IsOWith c l f g') (hc : c ≤ c') : IsOWith c' l f g' :=
  is_O_with.of_bound <|
    (mem_of_superset h.bound) fun x hx =>
      calc
        ∥f x∥ ≤ c * ∥g' x∥ := hx
        _ ≤ _ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
        

theorem IsOWith.exists_pos (h : IsOWith c l f g') : ∃ (c' : _)(H : 0 < c'), IsOWith c' l f g' :=
  ⟨max c 1, lt_of_lt_of_leₓ zero_lt_one (le_max_rightₓ c 1), h.weaken <| le_max_leftₓ c 1⟩

theorem IsO.exists_pos (h : f =O[l] g') : ∃ (c : _)(H : 0 < c), IsOWith c l f g' :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.exists_pos

theorem IsOWith.exists_nonneg (h : IsOWith c l f g') : ∃ (c' : _)(H : 0 ≤ c'), IsOWith c' l f g' :=
  let ⟨c, cpos, hc⟩ := h.exists_pos
  ⟨c, le_of_ltₓ cpos, hc⟩

theorem IsO.exists_nonneg (h : f =O[l] g') : ∃ (c : _)(H : 0 ≤ c), IsOWith c l f g' :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.exists_nonneg

/-- `f = O(g)` if and only if `is_O_with c f g` for all sufficiently large `c`. -/
theorem is_O_iff_eventually_is_O_with : f =O[l] g' ↔ ∀ᶠ c in at_top, IsOWith c l f g' :=
  is_O_iff_is_O_with.trans ⟨fun ⟨c, hc⟩ => mem_at_top_sets.2 ⟨c, fun c' hc' => hc.weaken hc'⟩, fun h => h.exists⟩

/-- `f = O(g)` if and only if `∀ᶠ x in l, ∥f x∥ ≤ c * ∥g x∥` for all sufficiently large `c`. -/
theorem is_O_iff_eventually : f =O[l] g' ↔ ∀ᶠ c in at_top, ∀ᶠ x in l, ∥f x∥ ≤ c * ∥g' x∥ :=
  is_O_iff_eventually_is_O_with.trans <| by
    simp only [← is_O_with]

theorem IsO.exists_mem_basis {ι} {p : ι → Prop} {s : ι → Set α} (h : f =O[l] g') (hb : l.HasBasis p s) :
    ∃ (c : ℝ)(hc : 0 < c)(i : ι)(hi : p i), ∀, ∀ x ∈ s i, ∀, ∥f x∥ ≤ c * ∥g' x∥ :=
  (flip Exists₂.imp h.exists_pos) fun c hc h => by
    simpa only [← is_O_with_iff, ← hb.eventually_iff, ← exists_prop] using h

theorem is_O_with_inv (hc : 0 < c) : IsOWith c⁻¹ l f g ↔ ∀ᶠ x in l, c * ∥f x∥ ≤ ∥g x∥ := by
  simp only [← is_O_with, div_eq_inv_mul, ← le_div_iff' hc]

-- We prove this lemma with strange assumptions to get two lemmas below automatically
theorem is_o_iff_nat_mul_le_aux (h₀ : (∀ x, 0 ≤ ∥f x∥) ∨ ∀ x, 0 ≤ ∥g x∥) :
    f =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ∥f x∥ ≤ ∥g x∥ := by
  constructor
  · rintro H (_ | n)
    · refine' (H.def one_pos).mono fun x h₀' => _
      rw [Nat.cast_zeroₓ, zero_mul]
      refine' h₀.elim (fun hf => (hf x).trans _) fun hg => hg x
      rwa [one_mulₓ] at h₀'
      
    · have : (0 : ℝ) < n.succ := Nat.cast_pos.2 n.succ_pos
      exact (is_O_with_inv this).1 (H.def' <| inv_pos.2 this)
      
    
  · refine' fun H => is_o_iff.2 fun ε ε0 => _
    rcases exists_nat_gt ε⁻¹ with ⟨n, hn⟩
    have hn₀ : (0 : ℝ) < n := (inv_pos.2 ε0).trans hn
    refine' ((is_O_with_inv hn₀).2 (H n)).bound.mono fun x hfg => _
    refine' hfg.trans (mul_le_mul_of_nonneg_right (inv_le_of_inv_le ε0 hn.le) _)
    refine' h₀.elim (fun hf => nonneg_of_mul_nonneg_right ((hf x).trans hfg) _) fun h => h x
    exact inv_pos.2 hn₀
    

theorem is_o_iff_nat_mul_le : f =o[l] g' ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ∥f x∥ ≤ ∥g' x∥ :=
  is_o_iff_nat_mul_le_aux (Or.inr fun x => norm_nonneg _)

theorem is_o_iff_nat_mul_le' : f' =o[l] g ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ∥f' x∥ ≤ ∥g x∥ :=
  is_o_iff_nat_mul_le_aux (Or.inl fun x => norm_nonneg _)

/-! ### Subsingleton -/


@[nontriviality]
theorem is_o_of_subsingleton [Subsingleton E'] : f' =o[l] g' :=
  is_o.of_bound fun c hc => by
    simp [← Subsingleton.elimₓ (f' _) 0, ← mul_nonneg hc.le]

@[nontriviality]
theorem is_O_of_subsingleton [Subsingleton E'] : f' =O[l] g' :=
  is_o_of_subsingleton.IsO

section congr

variable {f₁ f₂ : α → E} {g₁ g₂ : α → F}

/-! ### Congruence -/


theorem is_O_with_congr (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsOWith c₁ l f₁ g₁ ↔ IsOWith c₂ l f₂ g₂ := by
  unfold is_O_with
  subst c₂
  apply Filter.eventually_congr
  filter_upwards [hf, hg] with _ e₁ e₂
  rw [e₁, e₂]

theorem IsOWith.congr' (h : IsOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) :
    IsOWith c₂ l f₂ g₂ :=
  (is_O_with_congr hc hf hg).mp h

theorem IsOWith.congr (h : IsOWith c₁ l f₁ g₁) (hc : c₁ = c₂) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) :
    IsOWith c₂ l f₂ g₂ :=
  h.congr' hc (univ_mem' hf) (univ_mem' hg)

theorem IsOWith.congr_left (h : IsOWith c l f₁ g) (hf : ∀ x, f₁ x = f₂ x) : IsOWith c l f₂ g :=
  h.congr rfl hf fun _ => rfl

theorem IsOWith.congr_right (h : IsOWith c l f g₁) (hg : ∀ x, g₁ x = g₂ x) : IsOWith c l f g₂ :=
  h.congr rfl (fun _ => rfl) hg

theorem IsOWith.congr_const (h : IsOWith c₁ l f g) (hc : c₁ = c₂) : IsOWith c₂ l f g :=
  h.congr hc (fun _ => rfl) fun _ => rfl

theorem is_O_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =O[l] g₁ ↔ f₂ =O[l] g₂ := by
  unfold is_O
  exact exists_congr fun c => is_O_with_congr rfl hf hg

theorem IsO.congr' (h : f₁ =O[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =O[l] g₂ :=
  (is_O_congr hf hg).mp h

theorem IsO.congr (h : f₁ =O[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) : f₂ =O[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsO.congr_left (h : f₁ =O[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =O[l] g :=
  h.congr hf fun _ => rfl

theorem IsO.congr_right (h : f =O[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =O[l] g₂ :=
  h.congr (fun _ => rfl) hg

theorem is_o_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂ := by
  unfold is_o
  exact forall₂_congrₓ fun c hc => is_O_with_congr (Eq.refl c) hf hg

theorem IsOₓ.congr' (h : f₁ =o[l] g₁) (hf : f₁ =ᶠ[l] f₂) (hg : g₁ =ᶠ[l] g₂) : f₂ =o[l] g₂ :=
  (is_o_congr hf hg).mp h

theorem IsOₓ.congr (h : f₁ =o[l] g₁) (hf : ∀ x, f₁ x = f₂ x) (hg : ∀ x, g₁ x = g₂ x) : f₂ =o[l] g₂ :=
  h.congr' (univ_mem' hf) (univ_mem' hg)

theorem IsOₓ.congr_left (h : f₁ =o[l] g) (hf : ∀ x, f₁ x = f₂ x) : f₂ =o[l] g :=
  h.congr hf fun _ => rfl

theorem IsOₓ.congr_right (h : f =o[l] g₁) (hg : ∀ x, g₁ x = g₂ x) : f =o[l] g₂ :=
  h.congr (fun _ => rfl) hg

@[trans]
theorem _root_.filter.eventually_eq.trans_is_O {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂) (h : f₂ =O[l] g) :
    f₁ =O[l] g :=
  h.congr' hf.symm EventuallyEq.rfl

@[trans]
theorem _root_.filter.eventually_eq.trans_is_o {f₁ f₂ : α → E} {g : α → F} (hf : f₁ =ᶠ[l] f₂) (h : f₂ =o[l] g) :
    f₁ =o[l] g :=
  h.congr' hf.symm EventuallyEq.rfl

@[trans]
theorem IsO.trans_eventually_eq {f : α → E} {g₁ g₂ : α → F} (h : f =O[l] g₁) (hg : g₁ =ᶠ[l] g₂) : f =O[l] g₂ :=
  h.congr' EventuallyEq.rfl hg

@[trans]
theorem IsOₓ.trans_eventually_eq {f : α → E} {g₁ g₂ : α → F} (h : f =o[l] g₁) (hg : g₁ =ᶠ[l] g₂) : f =o[l] g₂ :=
  h.congr' EventuallyEq.rfl hg

end congr

/-! ### Filter operations and transitivity -/


theorem IsOWith.comp_tendsto (hcfg : IsOWith c l f g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    IsOWith c l' (f ∘ k) (g ∘ k) :=
  is_O_with.of_bound <| hk hcfg.bound

theorem IsO.comp_tendsto (hfg : f =O[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) : (f ∘ k) =O[l'] (g ∘ k) :=
  is_O_iff_is_O_with.2 <| hfg.IsOWith.imp fun c h => h.comp_tendsto hk

theorem IsOₓ.comp_tendsto (hfg : f =o[l] g) {k : β → α} {l' : Filter β} (hk : Tendsto k l' l) :
    (f ∘ k) =o[l'] (g ∘ k) :=
  is_o.of_is_O_with fun c cpos => (hfg.forall_is_O_with cpos).comp_tendsto hk

@[simp]
theorem is_O_with_map {k : β → α} {l : Filter β} : IsOWith c (map k l) f g ↔ IsOWith c l (f ∘ k) (g ∘ k) := by
  unfold is_O_with
  exact eventually_map

@[simp]
theorem is_O_map {k : β → α} {l : Filter β} : f =O[map k l] g ↔ (f ∘ k) =O[l] (g ∘ k) := by
  simp only [← is_O, ← is_O_with_map]

@[simp]
theorem is_o_map {k : β → α} {l : Filter β} : f =o[map k l] g ↔ (f ∘ k) =o[l] (g ∘ k) := by
  simp only [← is_o, ← is_O_with_map]

theorem IsOWith.mono (h : IsOWith c l' f g) (hl : l ≤ l') : IsOWith c l f g :=
  is_O_with.of_bound <| hl h.bound

theorem IsO.mono (h : f =O[l'] g) (hl : l ≤ l') : f =O[l] g :=
  is_O_iff_is_O_with.2 <| h.IsOWith.imp fun c h => h.mono hl

theorem IsOₓ.mono (h : f =o[l'] g) (hl : l ≤ l') : f =o[l] g :=
  is_o.of_is_O_with fun c cpos => (h.forall_is_O_with cpos).mono hl

theorem IsOWith.trans (hfg : IsOWith c l f g) (hgk : IsOWith c' l g k) (hc : 0 ≤ c) : IsOWith (c * c') l f k := by
  unfold is_O_with  at *
  filter_upwards [hfg, hgk] with x hx hx'
  calc ∥f x∥ ≤ c * ∥g x∥ := hx _ ≤ c * (c' * ∥k x∥) := mul_le_mul_of_nonneg_left hx' hc _ = c * c' * ∥k x∥ :=
      (mul_assoc _ _ _).symm

@[trans]
theorem IsO.trans {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =O[l] k) : f =O[l] k :=
  let ⟨c, cnonneg, hc⟩ := hfg.exists_nonneg
  let ⟨c', hc'⟩ := hgk.IsOWith
  (hc.trans hc' cnonneg).IsO

theorem IsOₓ.trans_is_O_with (hfg : f =o[l] g) (hgk : IsOWith c l g k) (hc : 0 < c) : f =o[l] k := by
  unfold is_o  at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact ((hfg this).trans hgk this.le).congr_const (div_mul_cancel _ hc.ne')

@[trans]
theorem IsOₓ.trans_is_O {f : α → E} {g : α → F} {k : α → G'} (hfg : f =o[l] g) (hgk : g =O[l] k) : f =o[l] k :=
  let ⟨c, cpos, hc⟩ := hgk.exists_pos
  hfg.trans_is_O_with hc cpos

theorem IsOWith.trans_is_o (hfg : IsOWith c l f g) (hgk : g =o[l] k) (hc : 0 < c) : f =o[l] k := by
  unfold is_o  at *
  intro c' c'pos
  have : 0 < c' / c := div_pos c'pos hc
  exact (hfg.trans (hgk this) hc.le).congr_const (mul_div_cancel' _ hc.ne')

@[trans]
theorem IsO.trans_is_o {f : α → E} {g : α → F'} {k : α → G} (hfg : f =O[l] g) (hgk : g =o[l] k) : f =o[l] k :=
  let ⟨c, cpos, hc⟩ := hfg.exists_pos
  hc.trans_is_o hgk cpos

@[trans]
theorem IsOₓ.trans {f : α → E} {g : α → F} {k : α → G} (hfg : f =o[l] g) (hgk : g =o[l] k) : f =o[l] k :=
  hfg.trans_is_O_with hgk.IsOWith one_pos

section

variable (l)

theorem is_O_with_of_le' (hfg : ∀ x, ∥f x∥ ≤ c * ∥g x∥) : IsOWith c l f g :=
  is_O_with.of_bound <| univ_mem' hfg

theorem is_O_with_of_le (hfg : ∀ x, ∥f x∥ ≤ ∥g x∥) : IsOWith 1 l f g :=
  (is_O_with_of_le' l) fun x => by
    rw [one_mulₓ]
    exact hfg x

theorem is_O_of_le' (hfg : ∀ x, ∥f x∥ ≤ c * ∥g x∥) : f =O[l] g :=
  (is_O_with_of_le' l hfg).IsO

theorem is_O_of_le (hfg : ∀ x, ∥f x∥ ≤ ∥g x∥) : f =O[l] g :=
  (is_O_with_of_le l hfg).IsO

end

theorem is_O_with_refl (f : α → E) (l : Filter α) : IsOWith 1 l f f :=
  (is_O_with_of_le l) fun _ => le_rfl

theorem is_O_refl (f : α → E) (l : Filter α) : f =O[l] f :=
  (is_O_with_refl f l).IsO

theorem IsOWith.trans_le (hfg : IsOWith c l f g) (hgk : ∀ x, ∥g x∥ ≤ ∥k x∥) (hc : 0 ≤ c) : IsOWith c l f k :=
  (hfg.trans (is_O_with_of_le l hgk) hc).congr_const <| mul_oneₓ c

theorem IsO.trans_le (hfg : f =O[l] g') (hgk : ∀ x, ∥g' x∥ ≤ ∥k x∥) : f =O[l] k :=
  hfg.trans (is_O_of_le l hgk)

theorem IsOₓ.trans_le (hfg : f =o[l] g) (hgk : ∀ x, ∥g x∥ ≤ ∥k x∥) : f =o[l] k :=
  hfg.trans_is_O_with (is_O_with_of_le _ hgk) zero_lt_one

theorem is_o_irrefl' (h : ∃ᶠ x in l, ∥f' x∥ ≠ 0) : ¬f' =o[l] f' := by
  intro ho
  rcases((ho.bound one_half_pos).and_frequently h).exists with ⟨x, hle, hne⟩
  rw [one_div, ← div_eq_inv_mul] at hle
  exact (half_lt_self (lt_of_le_of_neₓ (norm_nonneg _) hne.symm)).not_le hle

theorem is_o_irrefl (h : ∃ᶠ x in l, f'' x ≠ 0) : ¬f'' =o[l] f'' :=
  is_o_irrefl' <| h.mono fun x => norm_ne_zero_iff.mpr

theorem IsO.not_is_o (h : f'' =O[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =o[l] f'' := fun h' =>
  is_o_irrefl hf (h.trans_is_o h')

theorem IsOₓ.not_is_O (h : f'' =o[l] g') (hf : ∃ᶠ x in l, f'' x ≠ 0) : ¬g' =O[l] f'' := fun h' =>
  is_o_irrefl hf (h.trans_is_O h')

section Bot

variable (c f g)

@[simp]
theorem is_O_with_bot : IsOWith c ⊥ f g :=
  is_O_with.of_bound <| trivialₓ

@[simp]
theorem is_O_bot : f =O[⊥] g :=
  (is_O_with_bot 1 f g).IsO

@[simp]
theorem is_o_bot : f =o[⊥] g :=
  is_o.of_is_O_with fun c _ => is_O_with_bot c f g

end Bot

@[simp]
theorem is_O_with_pure {x} : IsOWith c (pure x) f g ↔ ∥f x∥ ≤ c * ∥g x∥ :=
  is_O_with_iff

theorem IsOWith.sup (h : IsOWith c l f g) (h' : IsOWith c l' f g) : IsOWith c (l⊔l') f g :=
  is_O_with.of_bound <| mem_sup.2 ⟨h.bound, h'.bound⟩

theorem IsOWith.sup' (h : IsOWith c l f g') (h' : IsOWith c' l' f g') : IsOWith (max c c') (l⊔l') f g' :=
  is_O_with.of_bound <| mem_sup.2 ⟨(h.weaken <| le_max_leftₓ c c').bound, (h'.weaken <| le_max_rightₓ c c').bound⟩

theorem IsO.sup (h : f =O[l] g') (h' : f =O[l'] g') : f =O[l⊔l'] g' :=
  let ⟨c, hc⟩ := h.IsOWith
  let ⟨c', hc'⟩ := h'.IsOWith
  (hc.sup' hc').IsO

theorem IsOₓ.sup (h : f =o[l] g) (h' : f =o[l'] g) : f =o[l⊔l'] g :=
  is_o.of_is_O_with fun c cpos => (h.forall_is_O_with cpos).sup (h'.forall_is_O_with cpos)

@[simp]
theorem is_O_sup : f =O[l⊔l'] g' ↔ f =O[l] g' ∧ f =O[l'] g' :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

@[simp]
theorem is_o_sup : f =o[l⊔l'] g ↔ f =o[l] g ∧ f =o[l'] g :=
  ⟨fun h => ⟨h.mono le_sup_left, h.mono le_sup_right⟩, fun h => h.1.sup h.2⟩

/-! ### Simplification : norm, abs -/


section NormAbs

variable {u v : α → ℝ}

@[simp]
theorem is_O_with_norm_right : (IsOWith c l f fun x => ∥g' x∥) ↔ IsOWith c l f g' := by
  simp only [← is_O_with, ← norm_norm]

@[simp]
theorem is_O_with_abs_right : (IsOWith c l f fun x => abs (u x)) ↔ IsOWith c l f u :=
  @is_O_with_norm_right _ _ _ _ _ _ f u l

alias is_O_with_norm_right ↔ is_O_with.of_norm_right is_O_with.norm_right

alias is_O_with_abs_right ↔ is_O_with.of_abs_right is_O_with.abs_right

@[simp]
theorem is_O_norm_right : (f =O[l] fun x => ∥g' x∥) ↔ f =O[l] g' := by
  unfold is_O
  exact exists_congr fun _ => is_O_with_norm_right

@[simp]
theorem is_O_abs_right : (f =O[l] fun x => abs (u x)) ↔ f =O[l] u :=
  @is_O_norm_right _ _ ℝ _ _ _ _ _

alias is_O_norm_right ↔ is_O.of_norm_right is_O.norm_right

alias is_O_abs_right ↔ is_O.of_abs_right is_O.abs_right

@[simp]
theorem is_o_norm_right : (f =o[l] fun x => ∥g' x∥) ↔ f =o[l] g' := by
  unfold is_o
  exact forall₂_congrₓ fun _ _ => is_O_with_norm_right

@[simp]
theorem is_o_abs_right : (f =o[l] fun x => abs (u x)) ↔ f =o[l] u :=
  @is_o_norm_right _ _ ℝ _ _ _ _ _

alias is_o_norm_right ↔ is_o.of_norm_right is_o.norm_right

alias is_o_abs_right ↔ is_o.of_abs_right is_o.abs_right

@[simp]
theorem is_O_with_norm_left : IsOWith c l (fun x => ∥f' x∥) g ↔ IsOWith c l f' g := by
  simp only [← is_O_with, ← norm_norm]

@[simp]
theorem is_O_with_abs_left : IsOWith c l (fun x => abs (u x)) g ↔ IsOWith c l u g :=
  @is_O_with_norm_left _ _ _ _ _ _ g u l

alias is_O_with_norm_left ↔ is_O_with.of_norm_left is_O_with.norm_left

alias is_O_with_abs_left ↔ is_O_with.of_abs_left is_O_with.abs_left

@[simp]
theorem is_O_norm_left : (fun x => ∥f' x∥) =O[l] g ↔ f' =O[l] g := by
  unfold is_O
  exact exists_congr fun _ => is_O_with_norm_left

@[simp]
theorem is_O_abs_left : (fun x => abs (u x)) =O[l] g ↔ u =O[l] g :=
  @is_O_norm_left _ _ _ _ _ g u l

alias is_O_norm_left ↔ is_O.of_norm_left is_O.norm_left

alias is_O_abs_left ↔ is_O.of_abs_left is_O.abs_left

@[simp]
theorem is_o_norm_left : (fun x => ∥f' x∥) =o[l] g ↔ f' =o[l] g := by
  unfold is_o
  exact forall₂_congrₓ fun _ _ => is_O_with_norm_left

@[simp]
theorem is_o_abs_left : (fun x => abs (u x)) =o[l] g ↔ u =o[l] g :=
  @is_o_norm_left _ _ _ _ _ g u l

alias is_o_norm_left ↔ is_o.of_norm_left is_o.norm_left

alias is_o_abs_left ↔ is_o.of_abs_left is_o.abs_left

theorem is_O_with_norm_norm : (IsOWith c l (fun x => ∥f' x∥) fun x => ∥g' x∥) ↔ IsOWith c l f' g' :=
  is_O_with_norm_left.trans is_O_with_norm_right

theorem is_O_with_abs_abs : (IsOWith c l (fun x => abs (u x)) fun x => abs (v x)) ↔ IsOWith c l u v :=
  is_O_with_abs_left.trans is_O_with_abs_right

alias is_O_with_norm_norm ↔ is_O_with.of_norm_norm is_O_with.norm_norm

alias is_O_with_abs_abs ↔ is_O_with.of_abs_abs is_O_with.abs_abs

theorem is_O_norm_norm : ((fun x => ∥f' x∥) =O[l] fun x => ∥g' x∥) ↔ f' =O[l] g' :=
  is_O_norm_left.trans is_O_norm_right

theorem is_O_abs_abs : ((fun x => abs (u x)) =O[l] fun x => abs (v x)) ↔ u =O[l] v :=
  is_O_abs_left.trans is_O_abs_right

alias is_O_norm_norm ↔ is_O.of_norm_norm is_O.norm_norm

alias is_O_abs_abs ↔ is_O.of_abs_abs is_O.abs_abs

theorem is_o_norm_norm : ((fun x => ∥f' x∥) =o[l] fun x => ∥g' x∥) ↔ f' =o[l] g' :=
  is_o_norm_left.trans is_o_norm_right

theorem is_o_abs_abs : ((fun x => abs (u x)) =o[l] fun x => abs (v x)) ↔ u =o[l] v :=
  is_o_abs_left.trans is_o_abs_right

alias is_o_norm_norm ↔ is_o.of_norm_norm is_o.norm_norm

alias is_o_abs_abs ↔ is_o.of_abs_abs is_o.abs_abs

end NormAbs

/-! ### Simplification: negate -/


@[simp]
theorem is_O_with_neg_right : (IsOWith c l f fun x => -g' x) ↔ IsOWith c l f g' := by
  simp only [← is_O_with, ← norm_neg]

alias is_O_with_neg_right ↔ is_O_with.of_neg_right is_O_with.neg_right

@[simp]
theorem is_O_neg_right : (f =O[l] fun x => -g' x) ↔ f =O[l] g' := by
  unfold is_O
  exact exists_congr fun _ => is_O_with_neg_right

alias is_O_neg_right ↔ is_O.of_neg_right is_O.neg_right

@[simp]
theorem is_o_neg_right : (f =o[l] fun x => -g' x) ↔ f =o[l] g' := by
  unfold is_o
  exact forall₂_congrₓ fun _ _ => is_O_with_neg_right

alias is_o_neg_right ↔ is_o.of_neg_right is_o.neg_right

@[simp]
theorem is_O_with_neg_left : IsOWith c l (fun x => -f' x) g ↔ IsOWith c l f' g := by
  simp only [← is_O_with, ← norm_neg]

alias is_O_with_neg_left ↔ is_O_with.of_neg_left is_O_with.neg_left

@[simp]
theorem is_O_neg_left : (fun x => -f' x) =O[l] g ↔ f' =O[l] g := by
  unfold is_O
  exact exists_congr fun _ => is_O_with_neg_left

alias is_O_neg_left ↔ is_O.of_neg_left is_O.neg_left

@[simp]
theorem is_o_neg_left : (fun x => -f' x) =o[l] g ↔ f' =o[l] g := by
  unfold is_o
  exact forall₂_congrₓ fun _ _ => is_O_with_neg_left

alias is_o_neg_left ↔ is_o.of_neg_right is_o.neg_left

/-! ### Product of functions (right) -/


theorem is_O_with_fst_prod : IsOWith 1 l f' fun x => (f' x, g' x) :=
  (is_O_with_of_le l) fun x => le_max_leftₓ _ _

theorem is_O_with_snd_prod : IsOWith 1 l g' fun x => (f' x, g' x) :=
  (is_O_with_of_le l) fun x => le_max_rightₓ _ _

theorem is_O_fst_prod : f' =O[l] fun x => (f' x, g' x) :=
  is_O_with_fst_prod.IsO

theorem is_O_snd_prod : g' =O[l] fun x => (f' x, g' x) :=
  is_O_with_snd_prod.IsO

theorem is_O_fst_prod' {f' : α → E' × F'} : (fun x => (f' x).1) =O[l] f' := by
  simpa [← is_O, ← is_O_with] using is_O_fst_prod

theorem is_O_snd_prod' {f' : α → E' × F'} : (fun x => (f' x).2) =O[l] f' := by
  simpa [← is_O, ← is_O_with] using is_O_snd_prod

section

variable (f' k')

theorem IsOWith.prod_rightl (h : IsOWith c l f g') (hc : 0 ≤ c) : IsOWith c l f fun x => (g' x, k' x) :=
  (h.trans is_O_with_fst_prod hc).congr_const (mul_oneₓ c)

theorem IsO.prod_rightl (h : f =O[l] g') : f =O[l] fun x => (g' x, k' x) :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightl k' cnonneg).IsO

theorem IsOₓ.prod_rightl (h : f =o[l] g') : f =o[l] fun x => (g' x, k' x) :=
  is_o.of_is_O_with fun c cpos => (h.forall_is_O_with cpos).prod_rightl k' cpos.le

theorem IsOWith.prod_rightr (h : IsOWith c l f g') (hc : 0 ≤ c) : IsOWith c l f fun x => (f' x, g' x) :=
  (h.trans is_O_with_snd_prod hc).congr_const (mul_oneₓ c)

theorem IsO.prod_rightr (h : f =O[l] g') : f =O[l] fun x => (f' x, g' x) :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.prod_rightr f' cnonneg).IsO

theorem IsOₓ.prod_rightr (h : f =o[l] g') : f =o[l] fun x => (f' x, g' x) :=
  is_o.of_is_O_with fun c cpos => (h.forall_is_O_with cpos).prod_rightr f' cpos.le

end

theorem IsOWith.prod_left_same (hf : IsOWith c l f' k') (hg : IsOWith c l g' k') :
    IsOWith c l (fun x => (f' x, g' x)) k' := by
  rw [is_O_with_iff] at * <;> filter_upwards [hf, hg] with x using max_leₓ

theorem IsOWith.prod_left (hf : IsOWith c l f' k') (hg : IsOWith c' l g' k') :
    IsOWith (max c c') l (fun x => (f' x, g' x)) k' :=
  (hf.weaken <| le_max_leftₓ c c').prod_left_same (hg.weaken <| le_max_rightₓ c c')

theorem IsOWith.prod_left_fst (h : IsOWith c l (fun x => (f' x, g' x)) k') : IsOWith c l f' k' :=
  (is_O_with_fst_prod.trans h zero_le_one).congr_const <| one_mulₓ c

theorem IsOWith.prod_left_snd (h : IsOWith c l (fun x => (f' x, g' x)) k') : IsOWith c l g' k' :=
  (is_O_with_snd_prod.trans h zero_le_one).congr_const <| one_mulₓ c

theorem is_O_with_prod_left : IsOWith c l (fun x => (f' x, g' x)) k' ↔ IsOWith c l f' k' ∧ IsOWith c l g' k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prod_left_same h.2⟩

theorem IsO.prod_left (hf : f' =O[l] k') (hg : g' =O[l] k') : (fun x => (f' x, g' x)) =O[l] k' :=
  let ⟨c, hf⟩ := hf.IsOWith
  let ⟨c', hg⟩ := hg.IsOWith
  (hf.prodLeft hg).IsO

theorem IsO.prod_left_fst (h : (fun x => (f' x, g' x)) =O[l] k') : f' =O[l] k' :=
  is_O_fst_prod.trans h

theorem IsO.prod_left_snd (h : (fun x => (f' x, g' x)) =O[l] k') : g' =O[l] k' :=
  is_O_snd_prod.trans h

@[simp]
theorem is_O_prod_left : (fun x => (f' x, g' x)) =O[l] k' ↔ f' =O[l] k' ∧ g' =O[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩

theorem IsOₓ.prod_left (hf : f' =o[l] k') (hg : g' =o[l] k') : (fun x => (f' x, g' x)) =o[l] k' :=
  is_o.of_is_O_with fun c hc => (hf.forall_is_O_with hc).prod_left_same (hg.forall_is_O_with hc)

theorem IsOₓ.prod_left_fst (h : (fun x => (f' x, g' x)) =o[l] k') : f' =o[l] k' :=
  is_O_fst_prod.trans_is_o h

theorem IsOₓ.prod_left_snd (h : (fun x => (f' x, g' x)) =o[l] k') : g' =o[l] k' :=
  is_O_snd_prod.trans_is_o h

@[simp]
theorem is_o_prod_left : (fun x => (f' x, g' x)) =o[l] k' ↔ f' =o[l] k' ∧ g' =o[l] k' :=
  ⟨fun h => ⟨h.prod_left_fst, h.prod_left_snd⟩, fun h => h.1.prodLeft h.2⟩

theorem IsOWith.eq_zero_imp (h : IsOWith c l f'' g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  (Eventually.mono h.bound) fun x hx hg =>
    norm_le_zero_iff.1 <| by
      simpa [← hg] using hx

theorem IsO.eq_zero_imp (h : f'' =O[l] g'') : ∀ᶠ x in l, g'' x = 0 → f'' x = 0 :=
  let ⟨C, hC⟩ := h.IsOWith
  hC.eq_zero_imp

/-! ### Addition and subtraction -/


section add_sub

variable {f₁ f₂ : α → E'} {g₁ g₂ : α → F'}

theorem IsOWith.add (h₁ : IsOWith c₁ l f₁ g) (h₂ : IsOWith c₂ l f₂ g) : IsOWith (c₁ + c₂) l (fun x => f₁ x + f₂ x) g :=
  by
  rw [is_O_with] at * <;>
    filter_upwards [h₁,
      h₂] with x hx₁ hx₂ using calc
        ∥f₁ x + f₂ x∥ ≤ c₁ * ∥g x∥ + c₂ * ∥g x∥ := norm_add_le_of_le hx₁ hx₂
        _ = (c₁ + c₂) * ∥g x∥ := (add_mulₓ _ _ _).symm
        

theorem IsO.add (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  let ⟨c₁, hc₁⟩ := h₁.IsOWith
  let ⟨c₂, hc₂⟩ := h₂.IsOWith
  (hc₁.add hc₂).IsO

theorem IsOₓ.add (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =o[l] g :=
  is_o.of_is_O_with fun c cpos =>
    ((h₁.forall_is_O_with <| half_pos cpos).add (h₂.forall_is_O_with <| half_pos cpos)).congr_const (add_halves c)

theorem IsOₓ.add_add (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) : (fun x => f₁ x + f₂ x) =o[l] fun x => ∥g₁ x∥ + ∥g₂ x∥ := by
  refine' (h₁.trans_le fun x => _).add (h₂.trans_le _) <;> simp [← abs_of_nonneg, ← add_nonneg]

theorem IsO.add_is_o (h₁ : f₁ =O[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.add h₂.IsO

theorem IsOₓ.add_is_O (h₁ : f₁ =o[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x + f₂ x) =O[l] g :=
  h₁.IsO.add h₂

theorem IsOWith.add_is_o (h₁ : IsOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₁.add (h₂.forall_is_O_with (sub_pos.2 hc))).congr_const (add_sub_cancel'_right _ _)

theorem IsOₓ.add_is_O_with (h₁ : f₁ =o[l] g) (h₂ : IsOWith c₁ l f₂ g) (hc : c₁ < c₂) :
    IsOWith c₂ l (fun x => f₁ x + f₂ x) g :=
  (h₂.add_is_o h₁ hc).congr_left fun _ => add_commₓ _ _

theorem IsOWith.sub (h₁ : IsOWith c₁ l f₁ g) (h₂ : IsOWith c₂ l f₂ g) : IsOWith (c₁ + c₂) l (fun x => f₁ x - f₂ x) g :=
  by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsOWith.sub_is_o (h₁ : IsOWith c₁ l f₁ g) (h₂ : f₂ =o[l] g) (hc : c₁ < c₂) :
    IsOWith c₂ l (fun x => f₁ x - f₂ x) g := by
  simpa only [← sub_eq_add_neg] using h₁.add_is_o h₂.neg_left hc

theorem IsO.sub (h₁ : f₁ =O[l] g) (h₂ : f₂ =O[l] g) : (fun x => f₁ x - f₂ x) =O[l] g := by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_left

theorem IsOₓ.sub (h₁ : f₁ =o[l] g) (h₂ : f₂ =o[l] g) : (fun x => f₁ x - f₂ x) =o[l] g := by
  simpa only [← sub_eq_add_neg] using h₁.add h₂.neg_left

end add_sub

/-! ### Lemmas about `is_O (f₁ - f₂) g l` / `is_o (f₁ - f₂) g l` treated as a binary relation -/


section IsOOAsRel

variable {f₁ f₂ f₃ : α → E'}

theorem IsOWith.symm (h : IsOWith c l (fun x => f₁ x - f₂ x) g) : IsOWith c l (fun x => f₂ x - f₁ x) g :=
  h.neg_left.congr_left fun x => neg_sub _ _

theorem is_O_with_comm : IsOWith c l (fun x => f₁ x - f₂ x) g ↔ IsOWith c l (fun x => f₂ x - f₁ x) g :=
  ⟨IsOWith.symm, IsOWith.symm⟩

theorem IsO.symm (h : (fun x => f₁ x - f₂ x) =O[l] g) : (fun x => f₂ x - f₁ x) =O[l] g :=
  h.neg_left.congr_left fun x => neg_sub _ _

theorem is_O_comm : (fun x => f₁ x - f₂ x) =O[l] g ↔ (fun x => f₂ x - f₁ x) =O[l] g :=
  ⟨IsO.symm, IsO.symm⟩

theorem IsOₓ.symm (h : (fun x => f₁ x - f₂ x) =o[l] g) : (fun x => f₂ x - f₁ x) =o[l] g := by
  simpa only [← neg_sub] using h.neg_left

theorem is_o_comm : (fun x => f₁ x - f₂ x) =o[l] g ↔ (fun x => f₂ x - f₁ x) =o[l] g :=
  ⟨IsOₓ.symm, IsOₓ.symm⟩

theorem IsOWith.triangle (h₁ : IsOWith c l (fun x => f₁ x - f₂ x) g) (h₂ : IsOWith c' l (fun x => f₂ x - f₃ x) g) :
    IsOWith (c + c') l (fun x => f₁ x - f₃ x) g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _

theorem IsO.triangle (h₁ : (fun x => f₁ x - f₂ x) =O[l] g) (h₂ : (fun x => f₂ x - f₃ x) =O[l] g) :
    (fun x => f₁ x - f₃ x) =O[l] g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _

theorem IsOₓ.triangle (h₁ : (fun x => f₁ x - f₂ x) =o[l] g) (h₂ : (fun x => f₂ x - f₃ x) =o[l] g) :
    (fun x => f₁ x - f₃ x) =o[l] g :=
  (h₁.add h₂).congr_left fun x => sub_add_sub_cancel _ _ _

theorem IsO.congr_of_sub (h : (fun x => f₁ x - f₂ x) =O[l] g) : f₁ =O[l] g ↔ f₂ =O[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩

theorem IsOₓ.congr_of_sub (h : (fun x => f₁ x - f₂ x) =o[l] g) : f₁ =o[l] g ↔ f₂ =o[l] g :=
  ⟨fun h' => (h'.sub h).congr_left fun x => sub_sub_cancel _ _, fun h' =>
    (h.add h').congr_left fun x => sub_add_cancel _ _⟩

end IsOOAsRel

/-! ### Zero, one, and other constants -/


section ZeroConst

variable (g g' l)

theorem is_o_zero : (fun x => (0 : E')) =o[l] g' :=
  is_o.of_bound fun c hc =>
    univ_mem' fun x => by
      simpa using mul_nonneg hc.le (norm_nonneg <| g' x)

theorem is_O_with_zero (hc : 0 ≤ c) : IsOWith c l (fun x => (0 : E')) g' :=
  is_O_with.of_bound <|
    univ_mem' fun x => by
      simpa using mul_nonneg hc (norm_nonneg <| g' x)

theorem is_O_with_zero' : IsOWith 0 l (fun x => (0 : E')) g :=
  is_O_with.of_bound <|
    univ_mem' fun x => by
      simp

theorem is_O_zero : (fun x => (0 : E')) =O[l] g :=
  is_O_iff_is_O_with.2 ⟨0, is_O_with_zero' _ _⟩

theorem is_O_refl_left : (fun x => f' x - f' x) =O[l] g' :=
  (is_O_zero g' l).congr_left fun x => (sub_self _).symm

theorem is_o_refl_left : (fun x => f' x - f' x) =o[l] g' :=
  (is_o_zero g' l).congr_left fun x => (sub_self _).symm

variable {g g' l}

@[simp]
theorem is_O_with_zero_right_iff : (IsOWith c l f'' fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 := by
  simp only [← is_O_with, ← exists_prop, ← true_andₓ, ← norm_zero, ← mul_zero, ← norm_le_zero_iff, ← eventually_eq, ←
    Pi.zero_apply]

@[simp]
theorem is_O_zero_right_iff : (f'' =O[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h =>
    let ⟨c, hc⟩ := h.IsOWith
    is_O_with_zero_right_iff.1 hc,
    fun h => (is_O_with_zero_right_iff.2 h : IsOWith 1 _ _ _).IsO⟩

@[simp]
theorem is_o_zero_right_iff : (f'' =o[l] fun x => (0 : F')) ↔ f'' =ᶠ[l] 0 :=
  ⟨fun h => is_O_zero_right_iff.1 h.IsO, fun h => is_o.of_is_O_with fun c hc => is_O_with_zero_right_iff.2 h⟩

theorem is_O_with_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) :
    IsOWith (∥c∥ / ∥c'∥) l (fun x : α => c) fun x => c' := by
  unfold is_O_with
  apply univ_mem'
  intro x
  rw [mem_set_of_eq, div_mul_cancel]
  rwa [Ne.def, norm_eq_zero]

theorem is_O_const_const (c : E) {c' : F''} (hc' : c' ≠ 0) (l : Filter α) : (fun x : α => c) =O[l] fun x => c' :=
  (is_O_with_const_const c hc' l).IsO

@[simp]
theorem is_O_const_const_iff {c : E''} {c' : F''} (l : Filter α) [l.ne_bot] :
    ((fun x : α => c) =O[l] fun x => c') ↔ c' = 0 → c = 0 := by
  rcases eq_or_ne c' 0 with (rfl | hc')
  · simp [← eventually_eq]
    
  · simp [← hc', ← is_O_const_const _ hc']
    

@[simp]
theorem is_O_pure {x} : f'' =O[pure x] g'' ↔ g'' x = 0 → f'' x = 0 :=
  calc
    f'' =O[pure x] g'' ↔ (fun y : α => f'' x) =O[pure x] fun _ => g'' x := is_O_congr rfl rfl
    _ ↔ g'' x = 0 → f'' x = 0 := is_O_const_const_iff _
    

end ZeroConst

@[simp]
theorem is_O_with_top : IsOWith c ⊤ f g ↔ ∀ x, ∥f x∥ ≤ c * ∥g x∥ := by
  rw [is_O_with] <;> rfl

@[simp]
theorem is_O_top : f =O[⊤] g ↔ ∃ C, ∀ x, ∥f x∥ ≤ C * ∥g x∥ := by
  rw [is_O_iff] <;> rfl

@[simp]
theorem is_o_top : f'' =o[⊤] g'' ↔ ∀ x, f'' x = 0 := by
  refine' ⟨_, fun h => (is_o_zero g'' ⊤).congr (fun x => (h x).symm) fun x => rfl⟩
  simp only [← is_o_iff, ← eventually_top]
  refine' fun h x => norm_le_zero_iff.1 _
  have : tendsto (fun c : ℝ => c * ∥g'' x∥) (𝓝[>] 0) (𝓝 0) :=
    ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left inf_le_left
  exact
    le_of_tendsto_of_tendsto tendsto_const_nhds this
      (eventually_nhds_within_iff.2 <| eventually_of_forall fun c hc => h hc x)

@[simp]
theorem is_O_with_principal {s : Set α} : IsOWith c (𝓟 s) f g ↔ ∀, ∀ x ∈ s, ∀, ∥f x∥ ≤ c * ∥g x∥ := by
  rw [is_O_with] <;> rfl

theorem is_O_principal {s : Set α} : f =O[𝓟 s] g ↔ ∃ c, ∀, ∀ x ∈ s, ∀, ∥f x∥ ≤ c * ∥g x∥ := by
  rw [is_O_iff] <;> rfl

section

variable (F) [One F] [NormOneClass F]

theorem is_O_with_const_one (c : E) (l : Filter α) : IsOWith ∥c∥ l (fun x : α => c) fun x => (1 : F) := by
  simp [← is_O_with_iff]

theorem is_O_const_one (c : E) (l : Filter α) : (fun x : α => c) =O[l] fun x => (1 : F) :=
  (is_O_with_const_one F c l).IsO

theorem is_o_const_iff_is_o_one {c : F''} (hc : c ≠ 0) : (f =o[l] fun x => c) ↔ f =o[l] fun x => (1 : F) :=
  ⟨fun h => h.trans_is_O_with (is_O_with_const_one _ _ _) (norm_pos_iff.2 hc), fun h =>
    h.trans_is_O <| is_O_const_const _ hc _⟩

@[simp]
theorem is_o_one_iff : f' =o[l] (fun x => 1 : α → F) ↔ Tendsto f' l (𝓝 0) := by
  simp only [← is_o_iff, ← norm_one, ← mul_oneₓ, ← metric.nhds_basis_closed_ball.tendsto_right_iff, ←
    Metric.mem_closed_ball, ← dist_zero_right]

@[simp]
theorem is_O_one_iff : f =O[l] (fun x => 1 : α → F) ↔ IsBoundedUnder (· ≤ ·) l fun x => ∥f x∥ := by
  simp only [← is_O_iff, ← norm_one, ← mul_oneₓ]
  rfl

alias is_O_one_iff ↔ _ _root_.filter.is_bounded_under.is_O_one

@[simp]
theorem is_o_one_left_iff : (fun x => 1 : α → F) =o[l] f ↔ Tendsto (fun x => ∥f x∥) l atTop :=
  calc
    (fun x => 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ∥(1 : F)∥ ≤ ∥f x∥ :=
      is_o_iff_nat_mul_le_aux <|
        Or.inl fun x => by
          simp only [← norm_one, ← zero_le_one]
    _ ↔ ∀ n : ℕ, True → ∀ᶠ x in l, ∥f x∥ ∈ Ici (n : ℝ) := by
      simp only [← norm_one, ← mul_oneₓ, ← true_implies_iff, ← mem_Ici]
    _ ↔ Tendsto (fun x => ∥f x∥) l atTop := at_top_countable_basis_of_archimedean.1.tendsto_right_iff.symm
    

theorem _root_.filter.tendsto.is_O_one {c : E'} (h : Tendsto f' l (𝓝 c)) : f' =O[l] (fun x => 1 : α → F) :=
  h.norm.is_bounded_under_le.is_O_one F

theorem IsO.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) : f =O[l] (fun x => 1 : α → F) :=
  hfg.trans <| hg.is_O_one F

end

theorem is_o_const_iff {c : F''} (hc : c ≠ 0) : (f'' =o[l] fun x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (is_o_const_iff_is_o_one ℝ hc).trans (is_o_one_iff _)

theorem is_o_id_const {c : F''} (hc : c ≠ 0) : (fun x : E'' => x) =o[𝓝 0] fun x => c :=
  (is_o_const_iff hc).mpr (continuous_id.Tendsto 0)

theorem _root_.filter.is_bounded_under.is_O_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) {c : F''} (hc : c ≠ 0) :
    f =O[l] fun x => c :=
  (h.is_O_one ℝ).trans (is_O_const_const _ hc _)

theorem is_O_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) : f'' =O[l] fun x => c :=
  h.norm.is_bounded_under_le.is_O_const hc

theorem IsO.is_bounded_under_le {c : F} (h : f =O[l] fun x => c) : IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ∥c∥, eventually_map.2 hc'⟩

theorem is_O_const_of_ne {c : F''} (hc : c ≠ 0) : (f =O[l] fun x => c) ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  ⟨fun h => h.is_bounded_under_le, fun h => h.is_O_const hc⟩

theorem is_O_const_iff {c : F''} :
    (f'' =O[l] fun x => c) ↔ (c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· ≤ ·) l fun x => ∥f'' x∥ := by
  refine'
    ⟨fun h =>
      ⟨fun hc =>
        is_O_zero_right_iff.1
          (by
            rwa [← hc]),
        h.is_bounded_under_le⟩,
      _⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts[(hcf hc).trans_is_O (is_O_zero _ _), hf.is_O_const hc]

theorem is_O_iff_is_bounded_under_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· ≤ ·) l fun x => ∥f x∥ / ∥g'' x∥ := by
  simp only [← is_O_iff, ← is_bounded_under, ← is_bounded, ← eventually_map]
  exact exists_congr fun c => eventually_congr <| h.mono fun x hx => (div_le_iff <| norm_pos_iff.2 hx).symm

/-- `(λ x, c) =O[l] f` if and only if `f` is bounded away from zero. -/
theorem is_O_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
    (fun x => c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ∥f' x∥ := by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine' ⟨∥c∥ / C, div_pos (norm_pos_iff.2 hc) hC₀, _⟩
    exact hC.bound.mono fun x => (div_le_iff' hC₀).2
    
  · rintro ⟨b, hb₀, hb⟩
    refine' is_O.of_bound (∥c∥ / b) (hb.mono fun x hx => _)
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)
    

section

variable (𝕜)

end

theorem IsO.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) : Tendsto f'' l (𝓝 0) :=
  (is_o_one_iff ℝ).1 <| hfg.trans_is_o <| (is_o_one_iff ℝ).2 hg

theorem IsOₓ.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) : Tendsto f'' l (𝓝 0) :=
  hfg.IsO.trans_tendsto hg

/-! ### Multiplication by a constant -/


theorem is_O_with_const_mul_self (c : R) (f : α → R) (l : Filter α) : IsOWith ∥c∥ l (fun x => c * f x) f :=
  (is_O_with_of_le' _) fun x => norm_mul_le _ _

theorem is_O_const_mul_self (c : R) (f : α → R) (l : Filter α) : (fun x => c * f x) =O[l] f :=
  (is_O_with_const_mul_self c f l).IsO

theorem IsOWith.const_mul_left {f : α → R} (h : IsOWith c l f g) (c' : R) :
    IsOWith (∥c'∥ * c) l (fun x => c' * f x) g :=
  (is_O_with_const_mul_self c' f l).trans h (norm_nonneg c')

theorem IsO.const_mul_left {f : α → R} (h : f =O[l] g) (c' : R) : (fun x => c' * f x) =O[l] g :=
  let ⟨c, hc⟩ := h.IsOWith
  (hc.const_mul_left c').IsO

theorem is_O_with_self_const_mul' (u : Rˣ) (f : α → R) (l : Filter α) : IsOWith ∥(↑u⁻¹ : R)∥ l f fun x => ↑u * f x :=
  (is_O_with_const_mul_self ↑u⁻¹ _ l).congr_left fun x => u.inv_mul_cancel_left (f x)

theorem is_O_with_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) : IsOWith ∥c∥⁻¹ l f fun x => c * f x :=
  (is_O_with_self_const_mul' (Units.mk0 c hc) f l).congr_const <| norm_inv c

theorem is_O_self_const_mul' {c : R} (hc : IsUnit c) (f : α → R) (l : Filter α) : f =O[l] fun x => c * f x :=
  let ⟨u, hu⟩ := hc
  hu ▸ (is_O_with_self_const_mul' u f l).IsO

theorem is_O_self_const_mul (c : 𝕜) (hc : c ≠ 0) (f : α → 𝕜) (l : Filter α) : f =O[l] fun x => c * f x :=
  is_O_self_const_mul' (IsUnit.mk0 c hc) f l

theorem is_O_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) : (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  ⟨(is_O_self_const_mul' hc f l).trans, fun h => h.const_mul_left c⟩

theorem is_O_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) : (fun x => c * f x) =O[l] g ↔ f =O[l] g :=
  is_O_const_mul_left_iff' <| IsUnit.mk0 c hc

theorem IsOₓ.const_mul_left {f : α → R} (h : f =o[l] g) (c : R) : (fun x => c * f x) =o[l] g :=
  (is_O_const_mul_self c f l).trans_is_o h

theorem is_o_const_mul_left_iff' {f : α → R} {c : R} (hc : IsUnit c) : (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  ⟨(is_O_self_const_mul' hc f l).trans_is_o, fun h => h.const_mul_left c⟩

theorem is_o_const_mul_left_iff {f : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) : (fun x => c * f x) =o[l] g ↔ f =o[l] g :=
  is_o_const_mul_left_iff' <| IsUnit.mk0 c hc

theorem IsOWith.of_const_mul_right {g : α → R} {c : R} (hc' : 0 ≤ c') (h : IsOWith c' l f fun x => c * g x) :
    IsOWith (c' * ∥c∥) l f g :=
  h.trans (is_O_with_const_mul_self c g l) hc'

theorem IsO.of_const_mul_right {g : α → R} {c : R} (h : f =O[l] fun x => c * g x) : f =O[l] g :=
  let ⟨c, cnonneg, hc⟩ := h.exists_nonneg
  (hc.of_const_mul_right cnonneg).IsO

theorem IsOWith.const_mul_right' {g : α → R} {u : Rˣ} {c' : ℝ} (hc' : 0 ≤ c') (h : IsOWith c' l f g) :
    IsOWith (c' * ∥(↑u⁻¹ : R)∥) l f fun x => ↑u * g x :=
  h.trans (is_O_with_self_const_mul' _ _ _) hc'

theorem IsOWith.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) {c' : ℝ} (hc' : 0 ≤ c') (h : IsOWith c' l f g) :
    IsOWith (c' * ∥c∥⁻¹) l f fun x => c * g x :=
  h.trans (is_O_with_self_const_mul c hc g l) hc'

theorem IsO.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =O[l] g) : f =O[l] fun x => c * g x :=
  h.trans (is_O_self_const_mul' hc g l)

theorem IsO.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =O[l] g) : f =O[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc

theorem is_O_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) : (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

theorem is_O_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) : (f =O[l] fun x => c * g x) ↔ f =O[l] g :=
  is_O_const_mul_right_iff' <| IsUnit.mk0 c hc

theorem IsOₓ.of_const_mul_right {g : α → R} {c : R} (h : f =o[l] fun x => c * g x) : f =o[l] g :=
  h.trans_is_O (is_O_const_mul_self c g l)

theorem IsOₓ.const_mul_right' {g : α → R} {c : R} (hc : IsUnit c) (h : f =o[l] g) : f =o[l] fun x => c * g x :=
  h.trans_is_O (is_O_self_const_mul' hc g l)

theorem IsOₓ.const_mul_right {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) (h : f =o[l] g) : f =o[l] fun x => c * g x :=
  h.const_mul_right' <| IsUnit.mk0 c hc

theorem is_o_const_mul_right_iff' {g : α → R} {c : R} (hc : IsUnit c) : (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  ⟨fun h => h.of_const_mul_right, fun h => h.const_mul_right' hc⟩

theorem is_o_const_mul_right_iff {g : α → 𝕜} {c : 𝕜} (hc : c ≠ 0) : (f =o[l] fun x => c * g x) ↔ f =o[l] g :=
  is_o_const_mul_right_iff' <| IsUnit.mk0 c hc

/-! ### Multiplication -/


theorem IsOWith.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} {c₁ c₂ : ℝ} (h₁ : IsOWith c₁ l f₁ g₁) (h₂ : IsOWith c₂ l f₂ g₂) :
    IsOWith (c₁ * c₂) l (fun x => f₁ x * f₂ x) fun x => g₁ x * g₂ x := by
  unfold is_O_with  at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_transₓ (norm_mul_le _ _)
  convert mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_transₓ (norm_nonneg _) hx₁) using 1
  rw [norm_mul, mul_mul_mul_commₓ]

theorem IsO.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =O[l] fun x => g₁ x * g₂ x :=
  let ⟨c, hc⟩ := h₁.IsOWith
  let ⟨c', hc'⟩ := h₂.IsOWith
  (hc.mul hc').IsO

theorem IsO.mul_is_o {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =O[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  unfold is_o  at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.mul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel' _ (ne_of_gtₓ c'pos))

theorem IsOₓ.mul_is_O {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =O[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x := by
  unfold is_o  at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).mul hc').congr_const (div_mul_cancel _ (ne_of_gtₓ c'pos))

theorem IsOₓ.mul {f₁ f₂ : α → R} {g₁ g₂ : α → 𝕜} (h₁ : f₁ =o[l] g₁) (h₂ : f₂ =o[l] g₂) :
    (fun x => f₁ x * f₂ x) =o[l] fun x => g₁ x * g₂ x :=
  h₁.mul_is_O h₂.IsO

theorem IsOWith.pow' {f : α → R} {g : α → 𝕜} (h : IsOWith c l f g) :
    ∀ n : ℕ, IsOWith (Nat.casesOn n ∥(1 : R)∥ fun n => c ^ (n + 1)) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by
    simpa using is_O_with_const_const (1 : R) (@one_ne_zero 𝕜 _ _) l
  | 1 => by
    simpa
  | n + 2 => by
    simpa [← pow_succₓ] using h.mul (is_O_with.pow' (n + 1))

theorem IsOWith.pow [NormOneClass R] {f : α → R} {g : α → 𝕜} (h : IsOWith c l f g) :
    ∀ n : ℕ, IsOWith (c ^ n) l (fun x => f x ^ n) fun x => g x ^ n
  | 0 => by
    simpa using h.pow' 0
  | n + 1 => h.pow' (n + 1)

theorem IsO.pow {f : α → R} {g : α → 𝕜} (h : f =O[l] g) (n : ℕ) : (fun x => f x ^ n) =O[l] fun x => g x ^ n :=
  let ⟨C, hC⟩ := h.IsOWith
  is_O_iff_is_O_with.2 ⟨_, hC.pow' n⟩

theorem IsOₓ.pow {f : α → R} {g : α → 𝕜} (h : f =o[l] g) {n : ℕ} (hn : 0 < n) :
    (fun x => f x ^ n) =o[l] fun x => g x ^ n := by
  cases n
  exact hn.false.elim
  clear hn
  induction' n with n ihn
  · simpa only [← pow_oneₓ]
    
  convert h.mul ihn <;> simp [← pow_succₓ]

/-! ### Inverse -/


theorem IsOWith.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : IsOWith c l f g) (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    IsOWith c l (fun x => (g x)⁻¹) fun x => (f x)⁻¹ := by
  refine' is_O_with.of_bound (h.bound.mp (h₀.mono fun x h₀ hle => _))
  cases' eq_or_ne (f x) 0 with hx hx
  · simp only [← hx, ← h₀ hx, ← inv_zero, ← norm_zero, ← mul_zero]
    
  · have hc : 0 < c := pos_of_mul_pos_left ((norm_pos_iff.2 hx).trans_le hle) (norm_nonneg _)
    replace hle := inv_le_inv_of_le (norm_pos_iff.2 hx) hle
    simpa only [← norm_inv, ← mul_inv, div_eq_inv_mul, ← div_le_iff hc] using hle
    

theorem IsO.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =O[l] g) (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    (fun x => (g x)⁻¹) =O[l] fun x => (f x)⁻¹ :=
  let ⟨c, hc⟩ := h.IsOWith
  (hc.inv_rev h₀).IsO

theorem IsOₓ.inv_rev {f : α → 𝕜} {g : α → 𝕜'} (h : f =o[l] g) (h₀ : ∀ᶠ x in l, f x = 0 → g x = 0) :
    (fun x => (g x)⁻¹) =o[l] fun x => (f x)⁻¹ :=
  is_o.of_is_O_with fun c hc => (h.def' hc).inv_rev h₀

/-! ### Scalar multiplication -/


section SmulConst

variable [NormedSpace 𝕜 E']

theorem IsOWith.const_smul_left (h : IsOWith c l f' g) (c' : 𝕜) : IsOWith (∥c'∥ * c) l (fun x => c' • f' x) g :=
  is_O_with.of_norm_left <| by
    simpa only [norm_smul, ← norm_norm] using h.norm_left.const_mul_left ∥c'∥

theorem IsO.const_smul_left (h : f' =O[l] g) (c : 𝕜) : (c • f') =O[l] g :=
  let ⟨b, hb⟩ := h.IsOWith
  (hb.const_smul_left _).IsO

theorem IsOₓ.const_smul_left (h : f' =o[l] g) (c : 𝕜) : (c • f') =o[l] g :=
  is_o.of_norm_left <| by
    simpa only [norm_smul] using h.norm_left.const_mul_left ∥c∥

theorem is_O_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g := by
  have cne0 : ∥c∥ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_left]
  simp only [← norm_smul]
  rw [is_O_const_mul_left_iff cne0, is_O_norm_left]

theorem is_o_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =o[l] g ↔ f' =o[l] g := by
  have cne0 : ∥c∥ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_left]
  simp only [← norm_smul]
  rw [is_o_const_mul_left_iff cne0, is_o_norm_left]

theorem is_O_const_smul_right {c : 𝕜} (hc : c ≠ 0) : (f =O[l] fun x => c • f' x) ↔ f =O[l] f' := by
  have cne0 : ∥c∥ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_O_norm_right]
  simp only [← norm_smul]
  rw [is_O_const_mul_right_iff cne0, is_O_norm_right]

theorem is_o_const_smul_right {c : 𝕜} (hc : c ≠ 0) : (f =o[l] fun x => c • f' x) ↔ f =o[l] f' := by
  have cne0 : ∥c∥ ≠ 0 := mt norm_eq_zero.mp hc
  rw [← is_o_norm_right]
  simp only [← norm_smul]
  rw [is_o_const_mul_right_iff cne0, is_o_norm_right]

end SmulConst

section Smul

variable [NormedSpace 𝕜 E'] [NormedSpace 𝕜' F'] {k₁ : α → 𝕜} {k₂ : α → 𝕜'}

theorem IsOWith.smul (h₁ : IsOWith c l k₁ k₂) (h₂ : IsOWith c' l f' g') :
    IsOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr rfl _ _).of_norm_norm <;>
    · intros <;> simp only [← norm_smul]
      

theorem IsO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') : (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [← norm_smul]
      

theorem IsO.smul_is_o (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') : (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is_o h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [← norm_smul]
      

theorem IsOₓ.smul_is_O (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') : (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul_is_O h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [← norm_smul]
      

theorem IsOₓ.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') : (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  refine' ((h₁.norm_norm.mul h₂.norm_norm).congr _ _).of_norm_norm <;>
    · intros <;> simp only [← norm_smul]
      

end Smul

/-! ### Sum -/


section Sum

variable {ι : Type _} {A : ι → α → E'} {C : ι → ℝ} {s : Finset ι}

theorem IsOWith.sum (h : ∀, ∀ i ∈ s, ∀, IsOWith (C i) l (A i) g) :
    IsOWith (∑ i in s, C i) l (fun x => ∑ i in s, A i x) g := by
  induction' s using Finset.induction_on with i s is IH
  · simp only [← is_O_with_zero', ← Finset.sum_empty, ← forall_true_iff]
    
  · simp only [← is, ← Finset.sum_insert, ← not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
    

theorem IsO.sum (h : ∀, ∀ i ∈ s, ∀, A i =O[l] g) : (fun x => ∑ i in s, A i x) =O[l] g := by
  unfold is_O  at *
  choose! C hC using h
  exact ⟨_, is_O_with.sum hC⟩

theorem IsOₓ.sum (h : ∀, ∀ i ∈ s, ∀, A i =o[l] g') : (fun x => ∑ i in s, A i x) =o[l] g' := by
  induction' s using Finset.induction_on with i s is IH
  · simp only [← is_o_zero, ← Finset.sum_empty, ← forall_true_iff]
    
  · simp only [← is, ← Finset.sum_insert, ← not_false_iff]
    exact (h _ (Finset.mem_insert_self i s)).add (IH fun j hj => h _ (Finset.mem_insert_of_mem hj))
    

end Sum

/-! ### Relation between `f = o(g)` and `f / g → 0` -/


theorem IsOₓ.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) : Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (is_o_one_iff 𝕜).mp <|
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [← div_eq_mul_inv] using h.mul_is_O (is_O_refl _ _)
      _ =O[l] fun x => (1 : 𝕜) :=
        is_O_of_le _ fun x => by
          simp [← div_self_le_one]
      

theorem IsOₓ.tendsto_inv_smul_nhds_zero [NormedSpace 𝕜 E'] {f : α → E'} {g : α → 𝕜} {l : Filter α} (h : f =o[l] g) :
    Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [← div_eq_inv_mul, norm_inv, norm_smul, tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero

theorem is_o_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨IsOₓ.tendsto_div_nhds_zero, fun h =>
    (((is_o_one_iff _).mpr h).mul_is_O (is_O_refl g l)).congr' (hgf.mono fun x => div_mul_cancel_of_imp)
      (eventually_of_forall fun x => one_mulₓ _)⟩

theorem is_o_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  is_o_iff_tendsto' (eventually_of_forall hgf)

alias is_o_iff_tendsto' ↔ _ is_o_of_tendsto'

alias is_o_iff_tendsto ↔ _ is_o_of_tendsto

theorem is_o_const_left_of_ne {c : E''} (hc : c ≠ 0) : (fun x => c) =o[l] g ↔ Tendsto (fun x => ∥g x∥) l atTop := by
  simp only [is_o_one_left_iff ℝ]
  exact ⟨(is_O_const_const (1 : ℝ) hc l).trans_is_o, (is_O_const_one ℝ c l).trans_is_o⟩

@[simp]
theorem is_o_const_left {c : E''} : (fun x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [← is_o_zero, ← eq_self_iff_true, ← true_orₓ]
    
  · simp only [← hc, ← false_orₓ, ← is_o_const_left_of_ne hc]
    

@[simp]
theorem is_o_const_const_iff [NeBot l] {d : E''} {c : F''} : ((fun x => d) =o[l] fun x => c) ↔ d = 0 := by
  have : ¬Tendsto (Function.const α ∥c∥) l atTop := not_tendsto_at_top_of_tendsto_nhds tendsto_const_nhds
  simp [← Function.const, ← this]

@[simp]
theorem is_o_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun y : α => f'' x) =o[pure x] fun _ => g'' x := is_o_congr rfl rfl
    _ ↔ f'' x = 0 := is_o_const_const_iff
    

theorem is_o_const_id_comap_norm_at_top (c : F'') : (fun x : E'' => c) =o[comap norm atTop] id :=
  is_o_const_left.2 <| Or.inr tendsto_comap

theorem is_o_const_id_at_top (c : E'') : (fun x : ℝ => c) =o[at_top] id :=
  is_o_const_left.2 <| Or.inr tendsto_abs_at_top_at_top

theorem is_o_const_id_at_bot (c : E'') : (fun x : ℝ => c) =o[at_bot] id :=
  is_o_const_left.2 <| Or.inr tendsto_abs_at_bot_at_top

/-!
### Eventually (u / v) * v = u

If `u` and `v` are linked by an `is_O_with` relation, then we
eventually have `(u / v) * v = u`, even if `v` vanishes.
-/


section EventuallyMulDivCancel

variable {u v : α → 𝕜}

theorem IsOWith.eventually_mul_div_cancel (h : IsOWith c l u v) : u / v * v =ᶠ[l] u :=
  Eventually.mono h.bound fun y hy =>
    div_mul_cancel_of_imp fun hv => by
      simpa [← hv] using hy

/-- If `u = O(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsO.eventually_mul_div_cancel (h : u =O[l] v) : u / v * v =ᶠ[l] u :=
  let ⟨c, hc⟩ := h.IsOWith
  hc.eventually_mul_div_cancel

/-- If `u = o(v)` along `l`, then `(u / v) * v = u` eventually at `l`. -/
theorem IsOₓ.eventually_mul_div_cancel (h : u =o[l] v) : u / v * v =ᶠ[l] u :=
  (h.forall_is_O_with zero_lt_one).eventually_mul_div_cancel

end EventuallyMulDivCancel

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `normed_field`. -/


section ExistsMulEq

variable {u v : α → 𝕜}

/-- If `∥φ∥` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `is_O_with c u v l`.
    This does not require any assumptions on `c`, which is why we keep this version along with
    `is_O_with_iff_exists_eq_mul`. -/
theorem is_O_with_of_eq_mul (φ : α → 𝕜) (hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c) (h : u =ᶠ[l] φ * v) : IsOWith c l u v := by
  unfold is_O_with
  refine' h.symm.rw (fun x a => ∥a∥ ≤ c * ∥v x∥) (hφ.mono fun x hx => _)
  simp only [← norm_mul, ← Pi.mul_apply]
  exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)

theorem is_O_with_iff_exists_eq_mul (hc : 0 ≤ c) :
    IsOWith c l u v ↔ ∃ (φ : α → 𝕜)(hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c), u =ᶠ[l] φ * v := by
  constructor
  · intro h
    use fun x => u x / v x
    refine' ⟨eventually.mono h.bound fun y hy => _, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_nonneg_of_le_mul (norm_nonneg _) hc hy
    
  · rintro ⟨φ, hφ, h⟩
    exact is_O_with_of_eq_mul φ hφ h
    

theorem IsOWith.exists_eq_mul (h : IsOWith c l u v) (hc : 0 ≤ c) :
    ∃ (φ : α → 𝕜)(hφ : ∀ᶠ x in l, ∥φ x∥ ≤ c), u =ᶠ[l] φ * v :=
  (is_O_with_iff_exists_eq_mul hc).mp h

theorem is_O_iff_exists_eq_mul : u =O[l] v ↔ ∃ (φ : α → 𝕜)(hφ : l.IsBoundedUnder (· ≤ ·) (norm ∘ φ)), u =ᶠ[l] φ * v :=
  by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
    
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact is_O_iff_is_O_with.2 ⟨c, is_O_with_of_eq_mul φ hφ huvφ⟩
    

alias is_O_iff_exists_eq_mul ↔ is_O.exists_eq_mul _

theorem is_o_iff_exists_eq_mul : u =o[l] v ↔ ∃ (φ : α → 𝕜)(hφ : Tendsto φ l (𝓝 0)), u =ᶠ[l] φ * v := by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
    
  · unfold is_o
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedGroup.tendsto_nhds_zero] at hφ
    exact is_O_with_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_ltₓ) huvφ
    

alias is_o_iff_exists_eq_mul ↔ is_o.exists_eq_mul _

end ExistsMulEq

/-! ### Miscellanous lemmas -/


theorem div_is_bounded_under_of_is_O {α : Type _} {l : Filter α} {f g : α → 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· ≤ ·) l fun x => ∥f x / g x∥ := by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine' ⟨c, eventually_map.2 (hc.bound.mono fun x hx => _)⟩
  rw [norm_div]
  exact div_le_of_nonneg_of_le_mul (norm_nonneg _) h₀ hx

theorem is_O_iff_div_is_bounded_under {α : Type _} {l : Filter α} {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· ≤ ·) l fun x => ∥f x / g x∥ := by
  refine' ⟨div_is_bounded_under_of_is_O, fun h => _⟩
  obtain ⟨c, hc⟩ := h
  simp only [← eventually_map, ← norm_div] at hc
  refine' is_O.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => _)
  by_cases' hgx : g x = 0
  · simp [← hx₁ hgx, ← hgx]
    
  · exact (div_le_iff (norm_pos_iff.2 hgx)).mp hx₂
    

theorem is_O_of_div_tendsto_nhds {α : Type _} {l : Filter α} {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜)
    (H : Filter.Tendsto (f / g) l (𝓝 c)) : f =O[l] g :=
  (is_O_iff_div_is_bounded_under hgf).2 <| H.norm.is_bounded_under_le

theorem IsOₓ.tendsto_zero_of_tendsto {α E 𝕜 : Type _} [NormedGroup E] [NormedField 𝕜] {u : α → E} {v : α → 𝕜}
    {l : Filter α} {y : 𝕜} (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) : Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun x => (1 : 𝕜)
  · rwa [is_o_one_iff] at h
    
  exact huv.trans_is_O (hv.is_O_one 𝕜)

theorem is_o_pow_pow {m n : ℕ} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m := by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [← pow_addₓ, ← one_pow, ← mul_oneₓ]
  exact is_O.mul_is_o (is_O_refl _ _) (is_o.pow ((is_o_one_iff _).2 tendsto_id) hp0)

theorem is_o_norm_pow_norm_pow {m n : ℕ} (h : m < n) : (fun x : E' => ∥x∥ ^ n) =o[𝓝 0] fun x => ∥x∥ ^ m :=
  (is_o_pow_pow h).comp_tendsto tendsto_norm_zero

theorem is_o_pow_id {n : ℕ} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x := by
  convert is_o_pow_pow h
  simp only [← pow_oneₓ]

theorem is_o_norm_pow_id {n : ℕ} (h : 1 < n) : (fun x : E' => ∥x∥ ^ n) =o[𝓝 0] fun x => x := by
  simpa only [← pow_oneₓ, ← is_o_norm_right] using @is_o_norm_pow_norm_pow E' _ _ _ h

theorem IsOWith.right_le_sub_of_lt_1 {f₁ f₂ : α → E'} (h : IsOWith c l f₁ f₂) (hc : c < 1) :
    IsOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
  is_O_with.of_bound <|
    (mem_of_superset h.bound) fun x hx => by
      simp only [← mem_set_of_eq] at hx⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff, mul_sub, mul_oneₓ, mul_comm]
      · exact le_transₓ (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
        
      · exact sub_pos.2 hc
        

theorem IsOWith.right_le_add_of_lt_1 {f₁ f₂ : α → E'} (h : IsOWith c l f₁ f₂) (hc : c < 1) :
    IsOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_1 hc).neg_right.of_neg_left.congr rfl (fun x => rfl) fun x => by
    rw [neg_sub, sub_neg_eq_add]

theorem IsOₓ.right_is_O_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) : f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_1 one_half_lt_one).IsO

theorem IsOₓ.right_is_O_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) : f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_1 one_half_lt_one).IsO

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`∥f x∥ ≤ C * ∥g x∥` whenever `g x ≠ 0`. -/
theorem bound_of_is_O_cofinite (h : f =O[cofinite] g'') : ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ∥f x∥ ≤ C * ∥g'' x∥ := by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [is_O_with, eventually_cofinite] at hC
  rcases(hC.to_finset.image fun x => ∥f x∥ / ∥g'' x∥).exists_le with ⟨C', hC'⟩
  have : ∀ x, C * ∥g'' x∥ < ∥f x∥ → ∥f x∥ / ∥g'' x∥ ≤ C' := by
    simpa using hC'
  refine' ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => _⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_leₓ]
  exact fun hx => (div_le_iff (norm_pos_iff.2 h₀)).1 (this _ hx)

theorem is_O_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) : f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ∥f'' x∥ ≤ C * ∥g'' x∥ :=
  ⟨fun h' =>
    let ⟨C, C₀, hC⟩ := bound_of_is_O_cofinite h'
    ⟨C, fun x =>
      if hx : g'' x = 0 then by
        simp [← h _ hx, ← hx]
      else hC hx⟩,
    fun h => (is_O_top.2 h).mono le_top⟩

theorem bound_of_is_O_nat_at_top {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[at_top] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ∥f x∥ ≤ C * ∥g'' x∥ :=
  bound_of_is_O_cofinite <| by
    rwa [Nat.cofinite_eq_at_top]

theorem is_O_nat_at_top_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    f =O[at_top] g ↔ ∃ C, ∀ x, ∥f x∥ ≤ C * ∥g x∥ := by
  rw [← Nat.cofinite_eq_at_top, is_O_cofinite_iff h]

theorem is_O_one_nat_at_top_iff {f : ℕ → E''} : f =O[at_top] (fun n => 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ∥f n∥ ≤ C :=
  Iff.trans (is_O_nat_at_top_iff fun n h => (one_ne_zero h).elim) <| by
    simp only [← norm_one, ← mul_oneₓ]

theorem is_O_with_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedGroup (E' i)] {f : α → ∀ i, E' i} {C : ℝ}
    (hC : 0 ≤ C) : IsOWith C l f g' ↔ ∀ i, IsOWith C l (fun x => f x i) g' := by
  have : ∀ x, 0 ≤ C * ∥g' x∥ := fun x => mul_nonneg hC (norm_nonneg _)
  simp only [← is_O_with_iff, ← pi_norm_le_iff (this _), ← eventually_all]

@[simp]
theorem is_O_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedGroup (E' i)] {f : α → ∀ i, E' i} :
    f =O[l] g' ↔ ∀ i, (fun x => f x i) =O[l] g' := by
  simp only [← is_O_iff_eventually_is_O_with, eventually_all]
  exact eventually_congr (eventually_at_top.2 ⟨0, fun c => is_O_with_pi⟩)

@[simp]
theorem is_o_pi {ι : Type _} [Fintype ι] {E' : ι → Type _} [∀ i, NormedGroup (E' i)] {f : α → ∀ i, E' i} :
    f =o[l] g' ↔ ∀ i, (fun x => f x i) =o[l] g' := by
  simp (config := { contextual := true })only [← is_o, ← is_O_with_pi, ← le_of_ltₓ]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩

end Asymptotics

open Asymptotics

theorem summable_of_is_O {ι E} [NormedGroup E] [CompleteSpace E] {f : ι → E} {g : ι → ℝ} (hg : Summable g)
    (h : f =O[cofinite] g) : Summable f :=
  let ⟨C, hC⟩ := h.IsOWith
  summable_of_norm_bounded_eventually (fun x => C * ∥g x∥) (hg.abs.mul_left _) hC.bound

theorem summable_of_is_O_nat {E} [NormedGroup E] [CompleteSpace E] {f : ℕ → E} {g : ℕ → ℝ} (hg : Summable g)
    (h : f =O[at_top] g) : Summable f :=
  summable_of_is_O hg <| Nat.cofinite_eq_at_top.symm ▸ h

namespace LocalHomeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [HasNorm E] {F : Type _} [HasNorm F]

/-- Transfer `is_O_with` over a `local_homeomorph`. -/
theorem is_O_with_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.Target) {f : β → E} {g : β → F} {C : ℝ} :
    IsOWith C (𝓝 b) f g ↔ IsOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
    h.comp_tendsto <| by
      convert e.continuous_at (e.map_target hb)
      exact (e.right_inv hb).symm,
    fun h =>
    (h.comp_tendsto (e.continuous_at_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun x hx => congr_arg g hx)⟩

/-- Transfer `is_O` over a `local_homeomorph`. -/
theorem is_O_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.Target) {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  unfold is_O
  exact exists_congr fun C => e.is_O_with_congr hb

/-- Transfer `is_o` over a `local_homeomorph`. -/
theorem is_o_congr (e : LocalHomeomorph α β) {b : β} (hb : b ∈ e.Target) {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  unfold is_o
  exact forall₂_congrₓ fun c hc => e.is_O_with_congr hb

end LocalHomeomorph

namespace Homeomorph

variable {α : Type _} {β : Type _} [TopologicalSpace α] [TopologicalSpace β]

variable {E : Type _} [HasNorm E] {F : Type _} [HasNorm F]

open Asymptotics

/-- Transfer `is_O_with` over a `homeomorph`. -/
theorem is_O_with_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    IsOWith C (𝓝 b) f g ↔ IsOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toLocalHomeomorph.is_O_with_congr trivialₓ

/-- Transfer `is_O` over a `homeomorph`. -/
theorem is_O_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} : f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  unfold is_O
  exact exists_congr fun C => e.is_O_with_congr

/-- Transfer `is_o` over a `homeomorph`. -/
theorem is_o_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} : f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  unfold is_o
  exact forall₂_congrₓ fun c hc => e.is_O_with_congr

end Homeomorph

