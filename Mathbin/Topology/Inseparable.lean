/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Yury G. Kudryashov
-/
import Mathbin.Topology.ContinuousOn
import Mathbin.Data.Setoid.Basic
import Mathbin.Tactic.Tfae

/-!
# Inseparable points in a topological space

In this file we define

* `specializes` (notation: `x ⤳ y`) : a relation saying that `𝓝 x ≤ 𝓝 y`;

* `inseparable`: a relation saying that two points in a topological space have the same
  neighbourhoods; equivalently, they can't be separated by an open set;

* `inseparable_setoid X`: same relation, as a `setoid`;

* `separation_quotient X`: the quotient of `X` by its `inseparable_setoid`.

We also prove various basic properties of the relation `inseparable`.

## Notations

- `x ⤳ y`: notation for `specializes x y`;
- `x ~ y` is used as a local notation for `inseparable x y`;
- `𝓝 x` is the neighbourhoods filter `nhds x` of a point `x`, defined elsewhere.

## Tags

topological space, separation setoid
-/


open Set Filter Function

open TopologicalSpace

variable {X Y : Type _} [TopologicalSpace X] [TopologicalSpace Y] {x y z : X} {s : Set X} {f : X → Y}

/-!
### `specializes` relation
-/


/-- `x` specializes to `y` (notation: `x ⤳ y`) if either of the following equivalent properties
hold:

* `𝓝 x ≤ 𝓝 y`; this property is used as the definition;
* `pure x ≤ 𝓝 y`; in other words, any neighbourhood of `y` contains `x`;
* `y ∈ closure {x}`;
* `closure {y} ⊆ closure {x}`;
* for any closed set `s` we have `x ∈ s → y ∈ s`;
* for any open set `s` we have `y ∈ s → x ∈ s`;
* `y` is a cluster point of the filter `pure x = 𝓟 {x}`.

This relation defines a `preorder` on `X`. If `X` is a T₀ space, then this preorder is a partial
order. If `X` is a T₁ space, then this partial order is trivial : `x ⤳ y ↔ x = y`. -/
def Specializes (x y : X) : Prop :=
  𝓝 x ≤ 𝓝 y

-- mathport name: «expr ⤳ »
infixl:300 " ⤳ " => Specializes

/-- A collection of equivalent definitions of `x ⤳ y`. The public API is given by `iff` lemmas
below. -/
theorem specializes_tfae (x y : X) :
    Tfae
      [x ⤳ y, pure x ≤ 𝓝 y, ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s, ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s,
        y ∈ Closure ({x} : Set X), Closure ({y} : Set X) ⊆ Closure {x}, ClusterPt y (pure x)] :=
  by
  tfae_have 1 → 2
  exact (pure_le_nhds _).trans
  tfae_have 2 → 3
  exact fun h s hso hy => h (hso.mem_nhds hy)
  tfae_have 3 → 4
  exact fun h s hsc hx => of_not_not fun hy => h (sᶜ) hsc.is_open_compl hy hx
  tfae_have 4 → 5
  exact fun h => h _ is_closed_closure (subset_closure <| mem_singleton _)
  tfae_have 6 ↔ 5
  exact is_closed_closure.closure_subset_iff.trans singleton_subset_iff
  tfae_have 5 ↔ 7
  · rw [mem_closure_iff_cluster_pt, principal_singleton]
    
  tfae_have 5 → 1
  · refine' fun h => (nhds_basis_opens _).ge_iff.2 _
    rintro s ⟨hy, ho⟩
    rcases mem_closure_iff.1 h s ho hy with ⟨z, hxs, rfl : z = x⟩
    exact ho.mem_nhds hxs
    
  tfae_finish

theorem specializes_iff_nhds : x ⤳ y ↔ 𝓝 x ≤ 𝓝 y :=
  Iff.rfl

theorem specializes_iff_pure : x ⤳ y ↔ pure x ≤ 𝓝 y :=
  (specializes_tfae x y).out 0 1

alias specializes_iff_nhds ↔ Specializes.nhds_le_nhds _

alias specializes_iff_pure ↔ Specializes.pure_le_nhds _

theorem specializes_iff_forall_open : x ⤳ y ↔ ∀ s : Set X, IsOpen s → y ∈ s → x ∈ s :=
  (specializes_tfae x y).out 0 2

theorem Specializes.mem_open (h : x ⤳ y) (hs : IsOpen s) (hy : y ∈ s) : x ∈ s :=
  specializes_iff_forall_open.1 h s hs hy

theorem IsOpen.not_specializes (hs : IsOpen s) (hx : x ∉ s) (hy : y ∈ s) : ¬x ⤳ y := fun h => hx <| h.mem_open hs hy

theorem specializes_iff_forall_closed : x ⤳ y ↔ ∀ s : Set X, IsClosed s → x ∈ s → y ∈ s :=
  (specializes_tfae x y).out 0 3

theorem Specializes.mem_closed (h : x ⤳ y) (hs : IsClosed s) (hx : x ∈ s) : y ∈ s :=
  specializes_iff_forall_closed.1 h s hs hx

theorem IsClosed.not_specializes (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬x ⤳ y := fun h =>
  hy <| h.mem_closed hs hx

theorem specializes_iff_mem_closure : x ⤳ y ↔ y ∈ Closure ({x} : Set X) :=
  (specializes_tfae x y).out 0 4

alias specializes_iff_mem_closure ↔ Specializes.mem_closure _

theorem specializes_iff_closure_subset : x ⤳ y ↔ Closure ({y} : Set X) ⊆ Closure {x} :=
  (specializes_tfae x y).out 0 5

alias specializes_iff_closure_subset ↔ Specializes.closure_subset _

theorem specializes_rfl : x ⤳ x :=
  le_rfl

@[refl]
theorem specializes_refl (x : X) : x ⤳ x :=
  specializes_rfl

@[trans]
theorem Specializes.trans : x ⤳ y → y ⤳ z → x ⤳ z :=
  le_transₓ

theorem specializes_of_nhds_within (h₁ : 𝓝[s] x ≤ 𝓝[s] y) (h₂ : x ∈ s) : x ⤳ y :=
  specializes_iff_pure.2 <|
    calc
      pure x ≤ 𝓝[s] x := le_inf (pure_le_nhds _) (le_principal_iff.2 h₂)
      _ ≤ 𝓝[s] y := h₁
      _ ≤ 𝓝 y := inf_le_left
      

theorem Specializes.map_of_continuous_at (h : x ⤳ y) (hy : ContinuousAt f y) : f x ⤳ f y :=
  specializes_iff_pure.2 fun s hs => mem_pure.2 <| mem_preimage.1 <| mem_of_mem_nhds <| hy.mono_left h hs

theorem Specializes.map (h : x ⤳ y) (hf : Continuous f) : f x ⤳ f y :=
  h.map_of_continuous_at hf.ContinuousAt

theorem Inducing.specializes_iff (hf : Inducing f) : f x ⤳ f y ↔ x ⤳ y := by
  simp only [← specializes_iff_mem_closure, ← hf.closure_eq_preimage_closure_image, ← image_singleton, ← mem_preimage]

theorem subtype_specializes_iff {p : X → Prop} (x y : Subtype p) : x ⤳ y ↔ (x : X) ⤳ y :=
  inducing_coe.specializes_iff.symm

variable (X)

/-- Specialization forms a preorder on the topological space. -/
def specializationPreorder : Preorderₓ X :=
  { Preorderₓ.lift (OrderDual.toDual ∘ 𝓝) with le := fun x y => y ⤳ x, lt := fun x y => y ⤳ x ∧ ¬x ⤳ y }

variable {X}

/-- A continuous function is monotone with respect to the specialization preorders on the domain and
the codomain. -/
theorem Continuous.specialization_monotone (hf : Continuous f) :
    @Monotone _ _ (specializationPreorder X) (specializationPreorder Y) f := fun x y h => h.map hf

/-!
### `inseparable` relation
-/


/-- Two points `x` and `y` in a topological space are `inseparable` if any of the following
equivalent properties hold:

- `𝓝 x = 𝓝 y`; we use this property as the definition;
- for any open set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_open`;
- for any closed set `s`, `x ∈ s ↔ y ∈ s`, see `inseparable_iff_closed`;
- `x ∈ closure {y}` and `y ∈ closure {x}`, see `inseparable_iff_mem_closure`;
- `closure {x} = closure {y}`, see `inseparable_iff_closure_eq`.
-/
def Inseparable (x y : X) : Prop :=
  𝓝 x = 𝓝 y

-- mathport name: «expr ~ »
local infixl:0 " ~ " => Inseparable

theorem inseparable_def : (x ~ y) ↔ 𝓝 x = 𝓝 y :=
  Iff.rfl

theorem inseparable_iff_specializes_and : (x ~ y) ↔ x ⤳ y ∧ y ⤳ x :=
  le_antisymm_iffₓ

theorem Inseparable.specializes (h : x ~ y) : x ⤳ y :=
  h.le

theorem Inseparable.specializes' (h : x ~ y) : y ⤳ x :=
  h.Ge

theorem Specializes.antisymm (h₁ : x ⤳ y) (h₂ : y ⤳ x) : x ~ y :=
  le_antisymmₓ h₁ h₂

theorem inseparable_iff_forall_open : (x ~ y) ↔ ∀ s : Set X, IsOpen s → (x ∈ s ↔ y ∈ s) := by
  simp only [← inseparable_iff_specializes_and, ← specializes_iff_forall_open, forall_and_distrib, iff_def, ← Iff.comm]

theorem not_inseparable_iff_exists_open : ¬(x ~ y) ↔ ∃ s : Set X, IsOpen s ∧ Xorₓ (x ∈ s) (y ∈ s) := by
  simp [← inseparable_iff_forall_open, xor_iff_not_iff]

theorem inseparable_iff_forall_closed : (x ~ y) ↔ ∀ s : Set X, IsClosed s → (x ∈ s ↔ y ∈ s) := by
  simp only [← inseparable_iff_specializes_and, ← specializes_iff_forall_closed, forall_and_distrib, iff_def]

theorem inseparable_iff_mem_closure : (x ~ y) ↔ x ∈ Closure ({y} : Set X) ∧ y ∈ Closure ({x} : Set X) :=
  inseparable_iff_specializes_and.trans <| by
    simp only [← specializes_iff_mem_closure, ← and_comm]

theorem inseparable_iff_closure_eq : (x ~ y) ↔ Closure ({x} : Set X) = Closure {y} := by
  simp only [← inseparable_iff_specializes_and, ← specializes_iff_closure_subset, subset_antisymm_iff, ← eq_comm]

theorem inseparable_of_nhds_within_eq (hx : x ∈ s) (hy : y ∈ s) (h : 𝓝[s] x = 𝓝[s] y) : x ~ y :=
  (specializes_of_nhds_within h.le hx).antisymm (specializes_of_nhds_within h.Ge hy)

theorem Inducing.inseparable_iff (hf : Inducing f) : (f x ~ f y) ↔ (x ~ y) := by
  simp only [← inseparable_iff_specializes_and, ← hf.specializes_iff]

theorem subtype_inseparable_iff {p : X → Prop} (x y : Subtype p) : (x ~ y) ↔ ((x : X) ~ y) :=
  inducing_coe.inseparable_iff.symm

namespace Inseparable

@[refl]
theorem refl (x : X) : x ~ x :=
  Eq.refl (𝓝 x)

theorem rfl : x ~ x :=
  refl x

@[symm]
theorem symm (h : x ~ y) : y ~ x :=
  h.symm

@[trans]
theorem trans (h₁ : x ~ y) (h₂ : y ~ z) : x ~ z :=
  h₁.trans h₂

theorem nhds_eq (h : x ~ y) : 𝓝 x = 𝓝 y :=
  h

theorem mem_open_iff (h : x ~ y) (hs : IsOpen s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_open.1 h s hs

theorem mem_closed_iff (h : x ~ y) (hs : IsClosed s) : x ∈ s ↔ y ∈ s :=
  inseparable_iff_forall_closed.1 h s hs

theorem map_of_continuous_at (h : x ~ y) (hx : ContinuousAt f x) (hy : ContinuousAt f y) : f x ~ f y :=
  (h.Specializes.map_of_continuous_at hy).antisymm (h.specializes'.map_of_continuous_at hx)

theorem map (h : x ~ y) (hf : Continuous f) : f x ~ f y :=
  h.map_of_continuous_at hf.ContinuousAt hf.ContinuousAt

end Inseparable

theorem IsClosed.not_inseparable (hs : IsClosed s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ y) := fun h =>
  hy <| (h.mem_closed_iff hs).1 hx

theorem IsOpen.not_inseparable (hs : IsOpen s) (hx : x ∈ s) (hy : y ∉ s) : ¬(x ~ y) := fun h =>
  hy <| (h.mem_open_iff hs).1 hx

/-!
### Separation quotient

In this section we define the quotient of a topological space by the `inseparable` relation.
-/


variable (X)

/-- A `setoid` version of `inseparable`, used to define the `separation_quotient`. -/
def inseparableSetoid : Setoidₓ X :=
  { Setoidₓ.comap 𝓝 ⊥ with R := (· ~ ·) }

/-- The quotient of a topological space by its `inseparable_setoid`. This quotient is guaranteed to
be a T₀ space. -/
def SeparationQuotient :=
  Quotientₓ (inseparableSetoid X)deriving TopologicalSpace

variable {X}

namespace SeparationQuotient

/-- The natural map from a topological space to its separation quotient. -/
def mk : X → SeparationQuotient X :=
  Quotientₓ.mk'

theorem quotient_map_mk : QuotientMap (mk : X → SeparationQuotient X) :=
  quotient_map_quot_mk

theorem continuous_mk : Continuous (mk : X → SeparationQuotient X) :=
  continuous_quot_mk

@[simp]
theorem mk_eq_mk : mk x = mk y ↔ (x ~ y) :=
  Quotientₓ.eq'

theorem surjective_mk : Surjective (mk : X → SeparationQuotient X) :=
  surjective_quot_mk _

@[simp]
theorem range_mk : Range (mk : X → SeparationQuotient X) = univ :=
  surjective_mk.range_eq

instance [Nonempty X] : Nonempty (SeparationQuotient X) :=
  Nonempty.map mk ‹_›

instance [Inhabited X] : Inhabited (SeparationQuotient X) :=
  ⟨mk default⟩

instance [Subsingleton X] : Subsingleton (SeparationQuotient X) :=
  surjective_mk.Subsingleton

theorem preimage_image_mk_open (hs : IsOpen s) : mk ⁻¹' (mk '' s) = s := by
  refine' subset.antisymm _ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_open_iff hs).1 hys

theorem is_open_map_mk : IsOpenMap (mk : X → SeparationQuotient X) := fun s hs =>
  quotient_map_mk.is_open_preimage.1 <| by
    rwa [preimage_image_mk_open hs]

theorem preimage_image_mk_closed (hs : IsClosed s) : mk ⁻¹' (mk '' s) = s := by
  refine' subset.antisymm _ (subset_preimage_image _ _)
  rintro x ⟨y, hys, hxy⟩
  exact ((mk_eq_mk.1 hxy).mem_closed_iff hs).1 hys

theorem inducing_mk : Inducing (mk : X → SeparationQuotient X) :=
  ⟨le_antisymmₓ (continuous_iff_le_induced.1 continuous_mk) fun s hs =>
      ⟨mk '' s, is_open_map_mk s hs, preimage_image_mk_open hs⟩⟩

theorem is_closed_map_mk : IsClosedMap (mk : X → SeparationQuotient X) :=
  inducing_mk.IsClosedMap <| by
    rw [range_mk]
    exact is_closed_univ

theorem map_mk_nhds : map mk (𝓝 x) = 𝓝 (mk x) := by
  rw [inducing_mk.nhds_eq_comap, map_comap_of_surjective surjective_mk]

end SeparationQuotient

