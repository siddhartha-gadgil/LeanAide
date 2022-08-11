/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Johan Commelin, Patrick Massot
-/
import Mathbin.Algebra.Order.WithZero
import Mathbin.Algebra.PunitInstances
import Mathbin.RingTheory.Ideal.Operations

/-!

# The basics of valuation theory.

The basic theory of valuations (non-archimedean norms) on a commutative ring,
following T. Wedhorn's unpublished notes “Adic Spaces” ([wedhorn_adic]).

The definition of a valuation we use here is Definition 1.22 of [wedhorn_adic].
A valuation on a ring `R` is a monoid homomorphism `v` to a linearly ordered
commutative monoid with zero, that in addition satisfies the following two axioms:
 * `v 0 = 0`
 * `∀ x y, v (x + y) ≤ max (v x) (v y)`

`valuation R Γ₀`is the type of valuations `R → Γ₀`, with a coercion to the underlying
function. If `v` is a valuation from `R` to `Γ₀` then the induced group
homomorphism `units(R) → Γ₀` is called `unit_map v`.

The equivalence "relation" `is_equiv v₁ v₂ : Prop` defined in 1.27 of [wedhorn_adic] is not strictly
speaking a relation, because `v₁ : valuation R Γ₁` and `v₂ : valuation R Γ₂` might
not have the same type. This corresponds in ZFC to the set-theoretic difficulty
that the class of all valuations (as `Γ₀` varies) on a ring `R` is not a set.
The "relation" is however reflexive, symmetric and transitive in the obvious
sense. Note that we use 1.27(iii) of [wedhorn_adic] as the definition of equivalence.

The support of a valuation `v : valuation R Γ₀` is `supp v`. If `J` is an ideal of `R`
with `h : J ⊆ supp v` then the induced valuation
on R / J = `ideal.quotient J` is `on_quot v h`.

## Main definitions

* `valuation R Γ₀`, the type of valuations on `R` with values in `Γ₀`
* `valuation.is_equiv`, the heterogeneous equivalence relation on valuations
* `valuation.supp`, the support of a valuation

* `add_valuation R Γ₀`, the type of additive valuations on `R` with values in a
  linearly ordered additive commutative group with a top element, `Γ₀`.

## Implementation Details

`add_valuation R Γ₀` is implemented as `valuation R (multiplicative Γ₀)ᵒᵈ`.

## Notation

In the `discrete_valuation` locale:

 * `ℕₘ₀` is a shorthand for `with_zero (multiplicative ℕ)`
 * `ℤₘ₀` is a shorthand for `with_zero (multiplicative ℤ)`

## TODO

If ever someone extends `valuation`, we should fully comply to the `fun_like` by migrating the
boilerplate lemmas to `valuation_class`.
-/


open Classical BigOperators

noncomputable section

open Function Ideal

variable {F R : Type _}

-- This will be a ring, assumed commutative in some sections
section

variable (F R) (Γ₀ : Type _) [LinearOrderedCommMonoidWithZero Γ₀] [Ringₓ R]

/-- The type of `Γ₀`-valued valuations on `R`.

When you extend this structure, make sure to extend `valuation_class`. -/
@[nolint has_inhabited_instance]
structure Valuation extends R →*₀ Γ₀ where
  map_add_le_max' : ∀ x y, to_fun (x + y) ≤ max (to_fun x) (to_fun y)

/-- `valuation_class F α β` states that `F` is a type of valuations.

You should also extend this typeclass when you extend `valuation`. -/
class ValuationClass extends MonoidWithZeroHomClass F R Γ₀ where
  map_add_le_max (f : F) (x y : R) : f (x + y) ≤ max (f x) (f y)

export ValuationClass (map_add_le_max)

instance [ValuationClass F R Γ₀] : CoeTₓ F (Valuation R Γ₀) :=
  ⟨fun f =>
    { toFun := f, map_one' := map_one f, map_zero' := map_zero f, map_mul' := map_mul f,
      map_add_le_max' := map_add_le_max f }⟩

end

namespace Valuation

variable {Γ₀ : Type _}

variable {Γ'₀ : Type _}

variable {Γ''₀ : Type _} [LinearOrderedCommMonoidWithZero Γ''₀]

section Basic

variable [Ringₓ R]

section Monoidₓ

variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]

instance : ValuationClass (Valuation R Γ₀) R Γ₀ where
  coe := fun f => f.toFun
  coe_injective' := fun f g h => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_mul := fun f => f.map_mul'
  map_one := fun f => f.map_one'
  map_zero := fun f => f.map_zero'
  map_add_le_max := fun f => f.map_add_le_max'

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (Valuation R Γ₀) fun _ => R → Γ₀ :=
  FunLike.hasCoeToFun

@[simp]
theorem to_fun_eq_coe (v : Valuation R Γ₀) : v.toFun = v :=
  rfl

@[ext]
theorem ext {v₁ v₂ : Valuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
  FunLike.ext _ _ h

variable (v : Valuation R Γ₀) {x y z : R}

@[simp, norm_cast]
theorem coe_coe : ⇑(v : R →*₀ Γ₀) = v :=
  rfl

@[simp]
theorem map_zero : v 0 = 0 :=
  v.map_zero'

@[simp]
theorem map_one : v 1 = 1 :=
  v.map_one'

@[simp]
theorem map_mul : ∀ x y, v (x * y) = v x * v y :=
  v.map_mul'

@[simp]
theorem map_add : ∀ x y, v (x + y) ≤ max (v x) (v y) :=
  v.map_add_le_max'

theorem map_add_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x + y) ≤ g :=
  le_transₓ (v.map_add x y) <| max_leₓ hx hy

theorem map_add_lt {x y g} (hx : v x < g) (hy : v y < g) : v (x + y) < g :=
  lt_of_le_of_ltₓ (v.map_add x y) <| max_ltₓ hx hy

theorem map_sum_le {ι : Type _} {s : Finset ι} {f : ι → R} {g : Γ₀} (hf : ∀, ∀ i ∈ s, ∀, v (f i) ≤ g) :
    v (∑ i in s, f i) ≤ g := by
  refine' Finset.induction_on s (fun _ => trans_rel_right (· ≤ ·) v.map_zero zero_le') (fun a s has ih hf => _) hf
  rw [Finset.forall_mem_insert] at hf
  rw [Finset.sum_insert has]
  exact v.map_add_le hf.1 (ih hf.2)

theorem map_sum_lt {ι : Type _} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ 0) (hf : ∀, ∀ i ∈ s, ∀, v (f i) < g) :
    v (∑ i in s, f i) < g := by
  refine'
    Finset.induction_on s (fun _ => trans_rel_right (· < ·) v.map_zero (zero_lt_iff.2 hg)) (fun a s has ih hf => _) hf
  rw [Finset.forall_mem_insert] at hf
  rw [Finset.sum_insert has]
  exact v.map_add_lt hf.1 (ih hf.2)

theorem map_sum_lt' {ι : Type _} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : 0 < g) (hf : ∀, ∀ i ∈ s, ∀, v (f i) < g) :
    v (∑ i in s, f i) < g :=
  v.map_sum_lt (ne_of_gtₓ hg) hf

@[simp]
theorem map_pow : ∀ (x) (n : ℕ), v (x ^ n) = v x ^ n :=
  v.toMonoidWithZeroHom.toMonoidHom.map_pow

/-- Deprecated. Use `fun_like.ext_iff`. -/
theorem ext_iff {v₁ v₂ : Valuation R Γ₀} : v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r :=
  FunLike.ext_iff

/-- A valuation gives a preorder on the underlying ring. -/
-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
def toPreorder : Preorderₓ R :=
  Preorderₓ.lift v

/-- If `v` is a valuation on a division ring then `v(x) = 0` iff `x = 0`. -/
@[simp]
theorem zero_iff [Nontrivial Γ₀] {K : Type _} [DivisionRing K] (v : Valuation K Γ₀) {x : K} : v x = 0 ↔ x = 0 :=
  v.toMonoidWithZeroHom.map_eq_zero

theorem ne_zero_iff [Nontrivial Γ₀] {K : Type _} [DivisionRing K] (v : Valuation K Γ₀) {x : K} : v x ≠ 0 ↔ x ≠ 0 :=
  v.toMonoidWithZeroHom.map_ne_zero

theorem unit_map_eq (u : Rˣ) : (Units.map (v : R →* Γ₀) u : Γ₀) = v u :=
  rfl

/-- A ring homomorphism `S → R` induces a map `valuation R Γ₀ → valuation S Γ₀`. -/
def comap {S : Type _} [Ringₓ S] (f : S →+* R) (v : Valuation R Γ₀) : Valuation S Γ₀ :=
  { v.toMonoidWithZeroHom.comp f.toMonoidWithZeroHom with toFun := v ∘ f,
    map_add_le_max' := fun x y => by
      simp only [← comp_app, ← map_add, ← f.map_add] }

@[simp]
theorem comap_apply {S : Type _} [Ringₓ S] (f : S →+* R) (v : Valuation R Γ₀) (s : S) : v.comap f s = v (f s) :=
  rfl

@[simp]
theorem comap_id : v.comap (RingHom.id R) = v :=
  ext fun r => rfl

theorem comap_comp {S₁ : Type _} {S₂ : Type _} [Ringₓ S₁] [Ringₓ S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  ext fun r => rfl

/-- A `≤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map `valuation R Γ₀ → valuation R Γ'₀`.
-/
def map (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (v : Valuation R Γ₀) : Valuation R Γ'₀ :=
  { MonoidWithZeroHom.comp f v.toMonoidWithZeroHom with toFun := f ∘ v,
    map_add_le_max' := fun r s =>
      calc
        f (v (r + s)) ≤ f (max (v r) (v s)) := hf (v.map_add r s)
        _ = max (f (v r)) (f (v s)) := hf.map_max
         }

/-- Two valuations on `R` are defined to be equivalent if they induce the same preorder on `R`. -/
def IsEquiv (v₁ : Valuation R Γ₀) (v₂ : Valuation R Γ'₀) : Prop :=
  ∀ r s, v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s

end Monoidₓ

section Groupₓ

variable [LinearOrderedCommGroupWithZero Γ₀] {R} {Γ₀} (v : Valuation R Γ₀) {x y z : R}

@[simp]
theorem map_inv {K : Type _} [DivisionRing K] (v : Valuation K Γ₀) {x : K} : v x⁻¹ = (v x)⁻¹ :=
  v.toMonoidWithZeroHom.map_inv x

@[simp]
theorem map_zpow {K : Type _} [DivisionRing K] (v : Valuation K Γ₀) {x : K} {n : ℤ} : v (x ^ n) = v x ^ n :=
  v.toMonoidWithZeroHom.map_zpow x n

theorem map_units_inv (x : Rˣ) : v (x⁻¹ : Rˣ) = (v x)⁻¹ :=
  v.toMonoidWithZeroHom.toMonoidHom.map_units_inv x

@[simp]
theorem map_neg (x : R) : v (-x) = v x :=
  v.toMonoidWithZeroHom.toMonoidHom.map_neg x

theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  v.toMonoidWithZeroHom.toMonoidHom.map_sub_swap x y

theorem map_sub (x y : R) : v (x - y) ≤ max (v x) (v y) :=
  calc
    v (x - y) = v (x + -y) := by
      rw [sub_eq_add_neg]
    _ ≤ max (v x) (v <| -y) := v.map_add _ _
    _ = max (v x) (v y) := by
      rw [map_neg]
    

theorem map_sub_le {x y g} (hx : v x ≤ g) (hy : v y ≤ g) : v (x - y) ≤ g := by
  rw [sub_eq_add_neg]
  exact v.map_add_le hx (le_transₓ (le_of_eqₓ (v.map_neg y)) hy)

theorem map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = max (v x) (v y) := by
  suffices : ¬v (x + y) < max (v x) (v y)
  exact or_iff_not_imp_right.1 (le_iff_eq_or_lt.1 (v.map_add x y)) this
  intro h'
  wlog vyx : v y < v x using x y
  · apply lt_or_gt_of_neₓ h.symm
    
  · rw [max_eq_left_of_ltₓ vyx] at h'
    apply lt_irreflₓ (v x)
    calc v x = v (x + y - y) := by
        simp _ ≤ max (v <| x + y) (v y) := map_sub _ _ _ _ < v x := max_ltₓ h' vyx
    
  · apply this h.symm
    rwa [add_commₓ, max_commₓ] at h'
    

theorem map_add_eq_of_lt_right (h : v x < v y) : v (x + y) = v y := by
  convert v.map_add_of_distinct_val _
  · symm
    rw [max_eq_right_iff]
    exact le_of_ltₓ h
    
  · exact ne_of_ltₓ h
    

theorem map_add_eq_of_lt_left (h : v y < v x) : v (x + y) = v x := by
  rw [add_commₓ]
  exact map_add_eq_of_lt_right _ h

theorem map_eq_of_sub_lt (h : v (y - x) < v x) : v y = v x := by
  have := Valuation.map_add_of_distinct_val v (ne_of_gtₓ h).symm
  rw [max_eq_rightₓ (le_of_ltₓ h)] at this
  simpa using this

theorem map_one_add_of_lt (h : v x < 1) : v (1 + x) = 1 := by
  rw [← v.map_one] at h
  simpa only [← v.map_one] using v.map_add_eq_of_lt_left h

theorem map_one_sub_of_lt (h : v x < 1) : v (1 - x) = 1 := by
  rw [← v.map_one, ← v.map_neg] at h
  rw [sub_eq_add_neg 1 x]
  simpa only [← v.map_one, ← v.map_neg] using v.map_add_eq_of_lt_left h

/-- The subgroup of elements whose valuation is less than a certain unit.-/
def ltAddSubgroup (v : Valuation R Γ₀) (γ : Γ₀ˣ) : AddSubgroup R where
  Carrier := { x | v x < γ }
  zero_mem' := by
    have h := Units.ne_zero γ
    contrapose! h
    simpa using h
  add_mem' := fun x y x_in y_in => lt_of_le_of_ltₓ (v.map_add x y) (max_ltₓ x_in y_in)
  neg_mem' := fun x x_in => by
    rwa [Set.mem_set_of_eq, map_neg]

end Groupₓ

end Basic

-- end of section
namespace IsEquiv

variable [Ringₓ R]

variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]

variable {v : Valuation R Γ₀}

variable {v₁ : Valuation R Γ₀} {v₂ : Valuation R Γ'₀} {v₃ : Valuation R Γ''₀}

@[refl]
theorem refl : v.IsEquiv v := fun _ _ => Iff.refl _

@[symm]
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ := fun _ _ => Iff.symm (h _ _)

@[trans]
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ := fun _ _ => Iff.trans (h₁₂ _ _) (h₂₃ _ _)

theorem of_eq {v' : Valuation R Γ₀} (h : v = v') : v.IsEquiv v' := by
  subst h

theorem map {v' : Valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀) (hf : Monotone f) (inf : Injective f) (h : v.IsEquiv v') :
    (v.map f hf).IsEquiv (v'.map f hf) :=
  let H : StrictMono f := hf.strict_mono_of_injective inf
  fun r s =>
  calc
    f (v r) ≤ f (v s) ↔ v r ≤ v s := by
      rw [H.le_iff_le]
    _ ↔ v' r ≤ v' s := h r s
    _ ↔ f (v' r) ≤ f (v' s) := by
      rw [H.le_iff_le]
    

/-- `comap` preserves equivalence. -/
theorem comap {S : Type _} [Ringₓ S] (f : S →+* R) (h : v₁.IsEquiv v₂) : (v₁.comap f).IsEquiv (v₂.comap f) := fun r s =>
  h (f r) (f s)

theorem val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s := by
  simpa only [← le_antisymm_iffₓ] using and_congr (h r s) (h s r)

theorem ne_zero (h : v₁.IsEquiv v₂) {r : R} : v₁ r ≠ 0 ↔ v₂ r ≠ 0 := by
  have : v₁ r ≠ v₁ 0 ↔ v₂ r ≠ v₂ 0 := not_iff_not_of_iff h.val_eq
  rwa [v₁.map_zero, v₂.map_zero] at this

end IsEquiv

-- end of namespace
section

theorem is_equiv_of_map_strict_mono [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀] [Ringₓ R]
    {v : Valuation R Γ₀} (f : Γ₀ →*₀ Γ'₀) (H : StrictMono f) : IsEquiv (v.map f H.Monotone) v := fun x y =>
  ⟨H.le_iff_le.mp, fun h => H.Monotone h⟩

theorem is_equiv_of_val_le_one [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀] {K : Type _}
    [DivisionRing K] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) (h : ∀ {x : K}, v x ≤ 1 ↔ v' x ≤ 1) : v.IsEquiv v' :=
  by
  intro x y
  by_cases' hy : y = 0
  · simp [← hy, ← zero_iff]
    
  rw
    [show y = 1 * y by
      rw [one_mulₓ]]
  rw [← inv_mul_cancel_right₀ hy x]
  iterate 2 
    rw [v.map_mul _ y, v'.map_mul _ y]
  rw [v.map_one, v'.map_one]
  constructor <;> intro H
  · apply mul_le_mul_right'
    replace hy := v.ne_zero_iff.mpr hy
    replace H := le_of_le_mul_right hy H
    rwa [h] at H
    
  · apply mul_le_mul_right'
    replace hy := v'.ne_zero_iff.mpr hy
    replace H := le_of_le_mul_right hy H
    rwa [h]
    

theorem is_equiv_iff_val_le_one [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀] {K : Type _}
    [DivisionRing K] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) : v.IsEquiv v' ↔ ∀ {x : K}, v x ≤ 1 ↔ v' x ≤ 1 :=
  ⟨fun h x => by
    simpa using h x 1, is_equiv_of_val_le_one _ _⟩

theorem is_equiv_iff_val_eq_one [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ'₀] {K : Type _}
    [DivisionRing K] (v : Valuation K Γ₀) (v' : Valuation K Γ'₀) : v.IsEquiv v' ↔ ∀ {x : K}, v x = 1 ↔ v' x = 1 := by
  constructor
  · intro h x
    simpa using @is_equiv.val_eq _ _ _ _ _ _ v v' h x 1
    
  · intro h
    apply is_equiv_of_val_le_one
    intro x
    constructor
    · intro hx
      cases' lt_or_eq_of_leₓ hx with hx' hx'
      · have : v (1 + x) = 1 := by
          rw [← v.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [h] at this
        rw
          [show x = -1 + (1 + x) by
            simp ]
        refine' le_transₓ (v'.map_add _ _) _
        simp [← this]
        
      · rw [h] at hx'
        exact le_of_eqₓ hx'
        
      
    · intro hx
      cases' lt_or_eq_of_leₓ hx with hx' hx'
      · have : v' (1 + x) = 1 := by
          rw [← v'.map_one]
          apply map_add_eq_of_lt_left
          simpa
        rw [← h] at this
        rw
          [show x = -1 + (1 + x) by
            simp ]
        refine' le_transₓ (v.map_add _ _) _
        simp [← this]
        
      · rw [← h] at hx'
        exact le_of_eqₓ hx'
        
      
    

end

section Supp

variable [CommRingₓ R]

variable [LinearOrderedCommMonoidWithZero Γ₀] [LinearOrderedCommMonoidWithZero Γ'₀]

variable (v : Valuation R Γ₀)

/-- The support of a valuation `v : R → Γ₀` is the ideal of `R` where `v` vanishes. -/
def supp : Ideal R where
  Carrier := { x | v x = 0 }
  zero_mem' := map_zero v
  add_mem' := fun x y hx hy =>
    le_zero_iff.mp <|
      calc
        v (x + y) ≤ max (v x) (v y) := v.map_add x y
        _ ≤ 0 := max_leₓ (le_zero_iff.mpr hx) (le_zero_iff.mpr hy)
        
  smul_mem' := fun c x hx =>
    calc
      v (c * x) = v c * v x := map_mul v c x
      _ = v c * 0 := congr_arg _ hx
      _ = 0 := mul_zero _
      

@[simp]
theorem mem_supp_iff (x : R) : x ∈ supp v ↔ v x = 0 :=
  Iff.rfl

/-- The support of a valuation is a prime ideal. -/
-- @[simp] lemma mem_supp_iff' (x : R) : x ∈ (supp v : set R) ↔ v x = 0 := iff.rfl
instance [Nontrivial Γ₀] [NoZeroDivisors Γ₀] : Ideal.IsPrime (supp v) :=
  ⟨fun h : v.Supp = ⊤ =>
    one_ne_zero <|
      show (1 : Γ₀) = 0 from
        calc
          1 = v 1 := v.map_one.symm
          _ = 0 :=
            show (1 : R) ∈ supp v by
              rw [h]
              trivial
          ,
    fun x y hxy => by
    show v x = 0 ∨ v y = 0
    change v (x * y) = 0 at hxy
    rw [v.map_mul x y] at hxy
    exact eq_zero_or_eq_zero_of_mul_eq_zero hxy⟩

theorem map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a := by
  have aux : ∀ a s, v s = 0 → v (a + s) ≤ v a := by
    intro a' s' h'
    refine' le_transₓ (v.map_add a' s') (max_leₓ le_rfl _)
    simp [← h']
  apply le_antisymmₓ (aux a s h)
  calc v a = v (a + s + -s) := by
      simp _ ≤ v (a + s) :=
      aux (a + s) (-s)
        (by
          rwa [← Ideal.neg_mem_iff] at h)

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
def onQuotVal {J : Ideal R} (hJ : J ≤ supp v) : R ⧸ J → Γ₀ := fun q =>
  (Quotientₓ.liftOn' q v) fun a b h =>
    calc
      v a = v (b + -(-a + b)) := by
        simp
      _ = v b := v.map_add_supp b <| (Ideal.neg_mem_iff _).2 <| hJ <| QuotientAddGroup.left_rel_apply.mp h
      

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
def onQuot {J : Ideal R} (hJ : J ≤ supp v) : Valuation (R ⧸ J) Γ₀ where
  toFun := v.onQuotVal hJ
  map_zero' := v.map_zero
  map_one' := v.map_one
  map_mul' := fun xbar ybar => Quotientₓ.ind₂' v.map_mul xbar ybar
  map_add_le_max' := fun xbar ybar => Quotientₓ.ind₂' v.map_add xbar ybar

@[simp]
theorem on_quot_comap_eq {J : Ideal R} (hJ : J ≤ supp v) : (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v :=
  ext fun r => rfl

theorem comap_supp {S : Type _} [CommRingₓ S] (f : S →+* R) : supp (v.comap f) = Ideal.comap f v.Supp :=
  Ideal.ext fun x => by
    rw [mem_supp_iff, Ideal.mem_comap, mem_supp_iff]
    rfl

theorem self_le_supp_comap (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) : J ≤ (v.comap (Ideal.Quotient.mk J)).Supp := by
  rw [comap_supp, ← Ideal.map_le_iff_le_comap]
  simp

@[simp]
theorem comap_on_quot_eq (J : Ideal R) (v : Valuation (R ⧸ J) Γ₀) :
    (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v :=
  ext <| by
    rintro ⟨x⟩
    rfl

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
theorem supp_quot {J : Ideal R} (hJ : J ≤ supp v) : supp (v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J) := by
  apply le_antisymmₓ
  · rintro ⟨x⟩ hx
    apply Ideal.subset_span
    exact ⟨x, hx, rfl⟩
    
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact hx
    

theorem supp_quot_supp : supp (v.onQuot le_rfl) = 0 := by
  rw [supp_quot]
  exact Ideal.map_quotient_self _

end Supp

-- end of section
end Valuation

section AddMonoidₓ

variable (R) [Ringₓ R] (Γ₀ : Type _) [LinearOrderedAddCommMonoidWithTop Γ₀]

/-- The type of `Γ₀`-valued additive valuations on `R`. -/
@[nolint has_inhabited_instance]
def AddValuation :=
  Valuation R (Multiplicative Γ₀ᵒᵈ)

end AddMonoidₓ

namespace AddValuation

variable {Γ₀ : Type _} {Γ'₀ : Type _}

section Basic

section Monoidₓ

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]

variable (R) (Γ₀) [Ringₓ R]

/-- A valuation is coerced to the underlying function `R → Γ₀`. -/
instance : CoeFun (AddValuation R Γ₀) fun _ => R → Γ₀ where coe := fun v => v.toMonoidWithZeroHom.toFun

variable {R} {Γ₀} (v : AddValuation R Γ₀) {x y z : R}

section

variable (f : R → Γ₀) (h0 : f 0 = ⊤) (h1 : f 1 = 0)

variable (hadd : ∀ x y, min (f x) (f y) ≤ f (x + y)) (hmul : ∀ x y, f (x * y) = f x + f y)

/-- An alternate constructor of `add_valuation`, that doesn't reference `multiplicative Γ₀ᵒᵈ` -/
def of : AddValuation R Γ₀ where
  toFun := f
  map_one' := h1
  map_zero' := h0
  map_add_le_max' := hadd
  map_mul' := hmul

variable {h0} {h1} {hadd} {hmul} {r : R}

@[simp]
theorem of_apply : (of f h0 h1 hadd hmul) r = f r :=
  rfl

/-- The `valuation` associated to an `add_valuation` (useful if the latter is constructed using
`add_valuation.of`). -/
def valuation : Valuation R (Multiplicative Γ₀ᵒᵈ) :=
  v

@[simp]
theorem valuation_apply (r : R) : v.Valuation r = Multiplicative.ofAdd (OrderDual.toDual (v r)) :=
  rfl

end

@[simp]
theorem map_zero : v 0 = ⊤ :=
  v.map_zero

@[simp]
theorem map_one : v 1 = 0 :=
  v.map_one

@[simp]
theorem map_mul : ∀ x y, v (x * y) = v x + v y :=
  v.map_mul

@[simp]
theorem map_add : ∀ x y, min (v x) (v y) ≤ v (x + y) :=
  v.map_add

theorem map_le_add {x y g} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x + y) :=
  v.map_add_le hx hy

theorem map_lt_add {x y g} (hx : g < v x) (hy : g < v y) : g < v (x + y) :=
  v.map_add_lt hx hy

theorem map_le_sum {ι : Type _} {s : Finset ι} {f : ι → R} {g : Γ₀} (hf : ∀, ∀ i ∈ s, ∀, g ≤ v (f i)) :
    g ≤ v (∑ i in s, f i) :=
  v.map_sum_le hf

theorem map_lt_sum {ι : Type _} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g ≠ ⊤) (hf : ∀, ∀ i ∈ s, ∀, g < v (f i)) :
    g < v (∑ i in s, f i) :=
  v.map_sum_lt hg hf

theorem map_lt_sum' {ι : Type _} {s : Finset ι} {f : ι → R} {g : Γ₀} (hg : g < ⊤) (hf : ∀, ∀ i ∈ s, ∀, g < v (f i)) :
    g < v (∑ i in s, f i) :=
  v.map_sum_lt' hg hf

@[simp]
theorem map_pow : ∀ (x) (n : ℕ), v (x ^ n) = n • v x :=
  v.map_pow

@[ext]
theorem ext {v₁ v₂ : AddValuation R Γ₀} (h : ∀ r, v₁ r = v₂ r) : v₁ = v₂ :=
  Valuation.ext h

theorem ext_iff {v₁ v₂ : AddValuation R Γ₀} : v₁ = v₂ ↔ ∀ r, v₁ r = v₂ r :=
  Valuation.ext_iff

/-- A valuation gives a preorder on the underlying ring. -/
-- The following definition is not an instance, because we have more than one `v` on a given `R`.
-- In addition, type class inference would not be able to infer `v`.
def toPreorder : Preorderₓ R :=
  Preorderₓ.lift v

/-- If `v` is an additive valuation on a division ring then `v(x) = ⊤` iff `x = 0`. -/
@[simp]
theorem top_iff [Nontrivial Γ₀] {K : Type _} [DivisionRing K] (v : AddValuation K Γ₀) {x : K} : v x = ⊤ ↔ x = 0 :=
  v.zero_iff

theorem ne_top_iff [Nontrivial Γ₀] {K : Type _} [DivisionRing K] (v : AddValuation K Γ₀) {x : K} : v x ≠ ⊤ ↔ x ≠ 0 :=
  v.ne_zero_iff

/-- A ring homomorphism `S → R` induces a map `add_valuation R Γ₀ → add_valuation S Γ₀`. -/
def comap {S : Type _} [Ringₓ S] (f : S →+* R) (v : AddValuation R Γ₀) : AddValuation S Γ₀ :=
  v.comap f

@[simp]
theorem comap_id : v.comap (RingHom.id R) = v :=
  v.comap_id

theorem comap_comp {S₁ : Type _} {S₂ : Type _} [Ringₓ S₁] [Ringₓ S₂] (f : S₁ →+* S₂) (g : S₂ →+* R) :
    v.comap (g.comp f) = (v.comap g).comap f :=
  v.comap_comp f g

/-- A `≤`-preserving, `⊤`-preserving group homomorphism `Γ₀ → Γ'₀` induces a map
  `add_valuation R Γ₀ → add_valuation R Γ'₀`.
-/
def map (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (v : AddValuation R Γ₀) : AddValuation R Γ'₀ :=
  v.map { toFun := f, map_mul' := f.map_add, map_one' := f.map_zero, map_zero' := ht } fun x y h => hf h

/-- Two additive valuations on `R` are defined to be equivalent if they induce the same
  preorder on `R`. -/
def IsEquiv (v₁ : AddValuation R Γ₀) (v₂ : AddValuation R Γ'₀) : Prop :=
  v₁.IsEquiv v₂

end Monoidₓ

section Groupₓ

variable [LinearOrderedAddCommGroupWithTop Γ₀] [Ringₓ R] (v : AddValuation R Γ₀) {x y z : R}

@[simp]
theorem map_inv {K : Type _} [DivisionRing K] (v : AddValuation K Γ₀) {x : K} : v x⁻¹ = -v x :=
  v.map_inv

theorem map_units_inv (x : Rˣ) : v (x⁻¹ : Rˣ) = -v x :=
  v.map_units_inv x

@[simp]
theorem map_neg (x : R) : v (-x) = v x :=
  v.map_neg x

theorem map_sub_swap (x y : R) : v (x - y) = v (y - x) :=
  v.map_sub_swap x y

theorem map_sub (x y : R) : min (v x) (v y) ≤ v (x - y) :=
  v.map_sub x y

theorem map_le_sub {x y g} (hx : g ≤ v x) (hy : g ≤ v y) : g ≤ v (x - y) :=
  v.map_sub_le hx hy

theorem map_add_of_distinct_val (h : v x ≠ v y) : v (x + y) = min (v x) (v y) :=
  v.map_add_of_distinct_val h

theorem map_eq_of_lt_sub (h : v x < v (y - x)) : v y = v x :=
  v.map_eq_of_sub_lt h

end Groupₓ

end Basic

namespace IsEquiv

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]

variable [Ringₓ R]

variable {Γ''₀ : Type _} [LinearOrderedAddCommMonoidWithTop Γ''₀]

variable {v : AddValuation R Γ₀}

variable {v₁ : AddValuation R Γ₀} {v₂ : AddValuation R Γ'₀} {v₃ : AddValuation R Γ''₀}

@[refl]
theorem refl : v.IsEquiv v :=
  Valuation.IsEquiv.refl

@[symm]
theorem symm (h : v₁.IsEquiv v₂) : v₂.IsEquiv v₁ :=
  h.symm

@[trans]
theorem trans (h₁₂ : v₁.IsEquiv v₂) (h₂₃ : v₂.IsEquiv v₃) : v₁.IsEquiv v₃ :=
  h₁₂.trans h₂₃

theorem of_eq {v' : AddValuation R Γ₀} (h : v = v') : v.IsEquiv v' :=
  Valuation.IsEquiv.of_eq h

theorem map {v' : AddValuation R Γ₀} (f : Γ₀ →+ Γ'₀) (ht : f ⊤ = ⊤) (hf : Monotone f) (inf : Injective f)
    (h : v.IsEquiv v') : (v.map f ht hf).IsEquiv (v'.map f ht hf) :=
  h.map { toFun := f, map_mul' := f.map_add, map_one' := f.map_zero, map_zero' := ht } (fun x y h => hf h) inf

/-- `comap` preserves equivalence. -/
theorem comap {S : Type _} [Ringₓ S] (f : S →+* R) (h : v₁.IsEquiv v₂) : (v₁.comap f).IsEquiv (v₂.comap f) :=
  h.comap f

theorem val_eq (h : v₁.IsEquiv v₂) {r s : R} : v₁ r = v₁ s ↔ v₂ r = v₂ s :=
  h.val_eq

theorem ne_top (h : v₁.IsEquiv v₂) {r : R} : v₁ r ≠ ⊤ ↔ v₂ r ≠ ⊤ :=
  h.ne_zero

end IsEquiv

section Supp

variable [LinearOrderedAddCommMonoidWithTop Γ₀] [LinearOrderedAddCommMonoidWithTop Γ'₀]

variable [CommRingₓ R]

variable (v : AddValuation R Γ₀)

/-- The support of an additive valuation `v : R → Γ₀` is the ideal of `R` where `v x = ⊤` -/
def supp : Ideal R :=
  v.Supp

@[simp]
theorem mem_supp_iff (x : R) : x ∈ supp v ↔ v x = ⊤ :=
  v.mem_supp_iff x

theorem map_add_supp (a : R) {s : R} (h : s ∈ supp v) : v (a + s) = v a :=
  v.map_add_supp a h

/-- If `hJ : J ⊆ supp v` then `on_quot_val hJ` is the induced function on R/J as a function.
Note: it's just the function; the valuation is `on_quot hJ`. -/
def onQuotVal {J : Ideal R} (hJ : J ≤ supp v) : R ⧸ J → Γ₀ :=
  v.onQuotVal hJ

/-- The extension of valuation v on R to valuation on R/J if J ⊆ supp v -/
def onQuot {J : Ideal R} (hJ : J ≤ supp v) : AddValuation (R ⧸ J) Γ₀ :=
  v.onQuot hJ

@[simp]
theorem on_quot_comap_eq {J : Ideal R} (hJ : J ≤ supp v) : (v.onQuot hJ).comap (Ideal.Quotient.mk J) = v :=
  v.on_quot_comap_eq hJ

theorem comap_supp {S : Type _} [CommRingₓ S] (f : S →+* R) : supp (v.comap f) = Ideal.comap f v.Supp :=
  v.comap_supp f

theorem self_le_supp_comap (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) : J ≤ (v.comap (Ideal.Quotient.mk J)).Supp :=
  v.self_le_supp_comap J

@[simp]
theorem comap_on_quot_eq (J : Ideal R) (v : AddValuation (R ⧸ J) Γ₀) :
    (v.comap (Ideal.Quotient.mk J)).onQuot (v.self_le_supp_comap J) = v :=
  v.comap_on_quot_eq J

/-- The quotient valuation on R/J has support supp(v)/J if J ⊆ supp v. -/
theorem supp_quot {J : Ideal R} (hJ : J ≤ supp v) : supp (v.onQuot hJ) = (supp v).map (Ideal.Quotient.mk J) :=
  v.supp_quot hJ

theorem supp_quot_supp : supp (v.onQuot le_rfl) = 0 :=
  v.supp_quot_supp

end Supp

-- end of section
end AddValuation

section ValuationNotation

-- mathport name: «exprℕₘ₀»
localized [DiscreteValuation] notation "ℕₘ₀" => WithZero (Multiplicative ℕ)

-- mathport name: «exprℤₘ₀»
localized [DiscreteValuation] notation "ℤₘ₀" => WithZero (Multiplicative ℤ)

end ValuationNotation

