/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathbin.Topology.Algebra.Constructions
import Mathbin.GroupTheory.GroupAction.Prod
import Mathbin.GroupTheory.GroupAction.Basic
import Mathbin.Topology.Algebra.ConstMulAction

/-!
# Continuous monoid action

In this file we define class `has_continuous_smul`. We say `has_continuous_smul M X` if `M` acts on
`X` and the map `(c, x) ↦ c • x` is continuous on `M × X`. We reuse this class for topological
(semi)modules, vector spaces and algebras.

## Main definitions

* `has_continuous_smul M X` : typeclass saying that the map `(c, x) ↦ c • x` is continuous
  on `M × X`;
* `homeomorph.smul_of_ne_zero`: if a group with zero `G₀` (e.g., a field) acts on `X` and `c : G₀`
  is a nonzero element of `G₀`, then scalar multiplication by `c` is a homeomorphism of `X`;
* `homeomorph.smul`: scalar multiplication by an element of a group `G` acting on `X`
  is a homeomorphism of `X`.
* `units.has_continuous_smul`: scalar multiplication by `Mˣ` is continuous when scalar
  multiplication by `M` is continuous. This allows `homeomorph.smul` to be used with on monoids
  with `G = Mˣ`.

## Main results

Besides homeomorphisms mentioned above, in this file we provide lemmas like `continuous.smul`
or `filter.tendsto.smul` that provide dot-syntax access to `continuous_smul`.
-/


open TopologicalSpace Pointwise

open Filter

/-- Class `has_continuous_smul M X` says that the scalar multiplication `(•) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of multiplicative actions,
including (semi)modules and algebras. -/
class HasContinuousSmul (M X : Type _) [HasSmul M X] [TopologicalSpace M] [TopologicalSpace X] : Prop where
  continuous_smul : Continuous fun p : M × X => p.1 • p.2

export HasContinuousSmul (continuous_smul)

/-- Class `has_continuous_vadd M X` says that the additive action `(+ᵥ) : M → X → X`
is continuous in both arguments. We use the same class for all kinds of additive actions,
including (semi)modules and algebras. -/
class HasContinuousVadd (M X : Type _) [HasVadd M X] [TopologicalSpace M] [TopologicalSpace X] : Prop where
  continuous_vadd : Continuous fun p : M × X => p.1 +ᵥ p.2

export HasContinuousVadd (continuous_vadd)

attribute [to_additive] HasContinuousSmul

section Main

variable {M X Y α : Type _} [TopologicalSpace M] [TopologicalSpace X] [TopologicalSpace Y]

section HasSmul

variable [HasSmul M X] [HasContinuousSmul M X]

@[to_additive]
instance (priority := 100) HasContinuousSmul.has_continuous_const_smul :
    HasContinuousConstSmul M
      X where continuous_const_smul := fun _ => continuous_smul.comp (continuous_const.prod_mk continuous_id)

@[to_additive]
theorem Filter.Tendsto.smul {f : α → M} {g : α → X} {l : Filter α} {c : M} {a : X} (hf : Tendsto f l (𝓝 c))
    (hg : Tendsto g l (𝓝 a)) : Tendsto (fun x => f x • g x) l (𝓝 <| c • a) :=
  (continuous_smul.Tendsto _).comp (hf.prod_mk_nhds hg)

@[to_additive]
theorem Filter.Tendsto.smul_const {f : α → M} {l : Filter α} {c : M} (hf : Tendsto f l (𝓝 c)) (a : X) :
    Tendsto (fun x => f x • a) l (𝓝 (c • a)) :=
  hf.smul tendsto_const_nhds

variable {f : Y → M} {g : Y → X} {b : Y} {s : Set Y}

@[to_additive]
theorem ContinuousWithinAt.smul (hf : ContinuousWithinAt f s b) (hg : ContinuousWithinAt g s b) :
    ContinuousWithinAt (fun x => f x • g x) s b :=
  hf.smul hg

@[to_additive]
theorem ContinuousAt.smul (hf : ContinuousAt f b) (hg : ContinuousAt g b) : ContinuousAt (fun x => f x • g x) b :=
  hf.smul hg

@[to_additive]
theorem ContinuousOn.smul (hf : ContinuousOn f s) (hg : ContinuousOn g s) : ContinuousOn (fun x => f x • g x) s :=
  fun x hx => (hf x hx).smul (hg x hx)

@[continuity, to_additive]
theorem Continuous.smul (hf : Continuous f) (hg : Continuous g) : Continuous fun x => f x • g x :=
  continuous_smul.comp (hf.prod_mk hg)

/-- If a scalar is central, then its right action is continuous when its left action is. -/
instance HasContinuousSmul.op [HasSmul Mᵐᵒᵖ X] [IsCentralScalar M X] : HasContinuousSmul Mᵐᵒᵖ X :=
  ⟨by
    suffices Continuous fun p : M × X => MulOpposite.op p.fst • p.snd from
      this.comp (MulOpposite.continuous_unop.prod_map continuous_id)
    simpa only [← op_smul_eq_smul] using (continuous_smul : Continuous fun p : M × X => _)⟩

@[to_additive]
instance MulOpposite.has_continuous_smul : HasContinuousSmul M Xᵐᵒᵖ :=
  ⟨MulOpposite.continuous_op.comp <| continuous_smul.comp <| continuous_id.prod_map MulOpposite.continuous_unop⟩

end HasSmul

section Monoidₓ

variable [Monoidₓ M] [MulAction M X] [HasContinuousSmul M X]

@[to_additive]
instance Units.has_continuous_smul :
    HasContinuousSmul Mˣ
      X where continuous_smul :=
    show Continuous ((fun p : M × X => p.fst • p.snd) ∘ fun p : Mˣ × X => (p.1, p.2)) from
      continuous_smul.comp ((Units.continuous_coe.comp continuous_fst).prod_mk continuous_snd)

end Monoidₓ

@[to_additive]
instance [HasSmul M X] [HasSmul M Y] [HasContinuousSmul M X] [HasContinuousSmul M Y] : HasContinuousSmul M (X × Y) :=
  ⟨(continuous_fst.smul (continuous_fst.comp continuous_snd)).prod_mk
      (continuous_fst.smul (continuous_snd.comp continuous_snd))⟩

@[to_additive]
instance {ι : Type _} {γ : ι → Type _} [∀ i, TopologicalSpace (γ i)] [∀ i, HasSmul M (γ i)]
    [∀ i, HasContinuousSmul M (γ i)] : HasContinuousSmul M (∀ i, γ i) :=
  ⟨continuous_pi fun i =>
      (continuous_fst.smul continuous_snd).comp <| continuous_fst.prod_mk ((continuous_apply i).comp continuous_snd)⟩

end Main

section LatticeOps

variable {ι : Sort _} {M X : Type _} [TopologicalSpace M] [HasSmul M X]

@[to_additive]
theorem has_continuous_smul_Inf {ts : Set (TopologicalSpace X)} (h : ∀, ∀ t ∈ ts, ∀, @HasContinuousSmul M X _ _ t) :
    @HasContinuousSmul M X _ _ (inf ts) :=
  { continuous_smul := by
      rw [← @Inf_singleton _ _ ‹TopologicalSpace M›]
      exact
        continuous_Inf_rng fun t ht =>
          continuous_Inf_dom₂ (Eq.refl _) ht (@HasContinuousSmul.continuous_smul _ _ _ _ t (h t ht)) }

@[to_additive]
theorem has_continuous_smul_infi {ts' : ι → TopologicalSpace X} (h : ∀ i, @HasContinuousSmul M X _ _ (ts' i)) :
    @HasContinuousSmul M X _ _ (⨅ i, ts' i) :=
  has_continuous_smul_Inf <| Set.forall_range_iff.mpr h

@[to_additive]
theorem has_continuous_smul_inf {t₁ t₂ : TopologicalSpace X} [@HasContinuousSmul M X _ _ t₁]
    [@HasContinuousSmul M X _ _ t₂] : @HasContinuousSmul M X _ _ (t₁⊓t₂) := by
  rw [inf_eq_infi]
  refine' has_continuous_smul_infi fun b => _
  cases b <;> assumption

end LatticeOps

