/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import Mathbin.Algebra.BigOperators.Basic
import Mathbin.Algebra.Ring.Pi

/-!
# Big operators for Pi Types

This file contains theorems relevant to big operators in binary and arbitrary product
of monoids and groups
-/


open BigOperators

namespace Pi

@[to_additive]
theorem list_prod_apply {α : Type _} {β : α → Type _} [∀ a, Monoidₓ (β a)] (a : α) (l : List (∀ a, β a)) :
    l.Prod a = (l.map fun f : ∀ a, β a => f a).Prod :=
  (evalMonoidHom β a).map_list_prod _

@[to_additive]
theorem multiset_prod_apply {α : Type _} {β : α → Type _} [∀ a, CommMonoidₓ (β a)] (a : α) (s : Multiset (∀ a, β a)) :
    s.Prod a = (s.map fun f : ∀ a, β a => f a).Prod :=
  (evalMonoidHom β a).map_multiset_prod _

end Pi

@[simp, to_additive]
theorem Finset.prod_apply {α : Type _} {β : α → Type _} {γ} [∀ a, CommMonoidₓ (β a)] (a : α) (s : Finset γ)
    (g : γ → ∀ a, β a) : (∏ c in s, g c) a = ∏ c in s, g c a :=
  (Pi.evalMonoidHom β a).map_prod _ _

/-- An 'unapplied' analogue of `finset.prod_apply`. -/
@[to_additive "An 'unapplied' analogue of `finset.sum_apply`."]
theorem Finset.prod_fn {α : Type _} {β : α → Type _} {γ} [∀ a, CommMonoidₓ (β a)] (s : Finset γ) (g : γ → ∀ a, β a) :
    (∏ c in s, g c) = fun a => ∏ c in s, g c a :=
  funext fun a => Finset.prod_apply _ _ _

@[simp, to_additive]
theorem Fintype.prod_apply {α : Type _} {β : α → Type _} {γ : Type _} [Fintype γ] [∀ a, CommMonoidₓ (β a)] (a : α)
    (g : γ → ∀ a, β a) : (∏ c, g c) a = ∏ c, g c a :=
  Finset.prod_apply a Finset.univ g

@[to_additive prod_mk_sum]
theorem prod_mk_prod {α β γ : Type _} [CommMonoidₓ α] [CommMonoidₓ β] (s : Finset γ) (f : γ → α) (g : γ → β) :
    (∏ x in s, f x, ∏ x in s, g x) = ∏ x in s, (f x, g x) :=
  have := Classical.decEq γ
  Finset.induction_on s rfl
    (by
      simp (config := { contextual := true })[← Prod.ext_iff])

section Single

variable {I : Type _} [DecidableEq I] {Z : I → Type _}

variable [∀ i, AddCommMonoidₓ (Z i)]

-- As we only defined `single` into `add_monoid`, we only prove the `finset.sum` version here.
theorem Finset.univ_sum_single [Fintype I] (f : ∀ i, Z i) : (∑ i, Pi.single i (f i)) = f := by
  ext a
  simp

theorem AddMonoidHom.functions_ext [Fintype I] (G : Type _) [AddCommMonoidₓ G] (g h : (∀ i, Z i) →+ G)
    (w : ∀ (i : I) (x : Z i), g (Pi.single i x) = h (Pi.single i x)) : g = h := by
  ext k
  rw [← Finset.univ_sum_single k, g.map_sum, h.map_sum]
  simp only [← w]

/-- This is used as the ext lemma instead of `add_monoid_hom.functions_ext` for reasons explained in
note [partially-applied ext lemmas]. -/
@[ext]
theorem AddMonoidHom.functions_ext' [Fintype I] (M : Type _) [AddCommMonoidₓ M] (g h : (∀ i, Z i) →+ M)
    (H : ∀ i, g.comp (AddMonoidHom.single Z i) = h.comp (AddMonoidHom.single Z i)) : g = h :=
  have := fun i => AddMonoidHom.congr_fun (H i)
  -- elab without an expected type
      g.functions_ext
    M h this

end Single

section RingHom

open Pi

variable {I : Type _} [DecidableEq I] {f : I → Type _}

variable [∀ i, NonAssocSemiringₓ (f i)]

@[ext]
theorem RingHom.functions_ext [Fintype I] (G : Type _) [NonAssocSemiringₓ G] (g h : (∀ i, f i) →+* G)
    (w : ∀ (i : I) (x : f i), g (single i x) = h (single i x)) : g = h :=
  RingHom.coe_add_monoid_hom_injective <| @AddMonoidHom.functions_ext I _ f _ _ G _ (g : (∀ i, f i) →+ G) h w

end RingHom

namespace Prod

variable {α β γ : Type _} [CommMonoidₓ α] [CommMonoidₓ β] {s : Finset γ} {f : γ → α × β}

@[to_additive]
theorem fst_prod : (∏ c in s, f c).1 = ∏ c in s, (f c).1 :=
  (MonoidHom.fst α β).map_prod f s

@[to_additive]
theorem snd_prod : (∏ c in s, f c).2 = ∏ c in s, (f c).2 :=
  (MonoidHom.snd α β).map_prod f s

end Prod

