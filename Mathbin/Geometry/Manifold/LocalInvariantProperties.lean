/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Geometry.Manifold.ChartedSpace

/-!
# Local properties invariant under a groupoid

We study properties of a triple `(g, s, x)` where `g` is a function between two spaces `H` and `H'`,
`s` is a subset of `H` and `x` is a point of `H`. Our goal is to register how such a property
should behave to make sense in charted spaces modelled on `H` and `H'`.

The main examples we have in mind are the properties "`g` is differentiable at `x` within `s`", or
"`g` is smooth at `x` within `s`". We want to develop general results that, when applied in these
specific situations, say that the notion of smooth function in a manifold behaves well under
restriction, intersection, is local, and so on.

## Main definitions

* `local_invariant_prop G G' P` says that a property `P` of a triple `(g, s, x)` is local, and
  invariant under composition by elements of the groupoids `G` and `G'` of `H` and `H'`
  respectively.
* `charted_space.lift_prop_within_at` (resp. `lift_prop_at`, `lift_prop_on` and `lift_prop`):
  given a property `P` of `(g, s, x)` where `g : H → H'`, define the corresponding property
  for functions `M → M'` where `M` and `M'` are charted spaces modelled respectively on `H` and
  `H'`. We define these properties within a set at a point, or at a point, or on a set, or in the
  whole space. This lifting process (obtained by restricting to suitable chart domains) can always
  be done, but it only behaves well under locality and invariance assumptions.

Given `hG : local_invariant_prop G G' P`, we deduce many properties of the lifted property on the
charted spaces. For instance, `hG.lift_prop_within_at_inter` says that `P g s x` is equivalent to
`P g (s ∩ t) x` whenever `t` is a neighborhood of `x`.

## Implementation notes

We do not use dot notation for properties of the lifted property. For instance, we have
`hG.lift_prop_within_at_congr` saying that if `lift_prop_within_at P g s x` holds, and `g` and `g'`
coincide on `s`, then `lift_prop_within_at P g' s x` holds. We can't call it
`lift_prop_within_at.congr` as it is in the namespace associated to `local_invariant_prop`, not
in the one for `lift_prop_within_at`.
-/


noncomputable section

open Classical Manifold TopologicalSpace

open Set Filter

variable {H : Type _} {M : Type _} [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M] {H' : Type _}
  {M' : Type _} [TopologicalSpace H'] [TopologicalSpace M'] [ChartedSpace H' M']

namespace StructureGroupoid

variable (G : StructureGroupoid H) (G' : StructureGroupoid H')

/-- Structure recording good behavior of a property of a triple `(f, s, x)` where `f` is a function,
`s` a set and `x` a point. Good behavior here means locality and invariance under given groupoids
(both in the source and in the target). Given such a good behavior, the lift of this property
to charted spaces admitting these groupoids will inherit the good behavior. -/
structure LocalInvariantProp (P : (H → H') → Set H → H → Prop) : Prop where
  is_local : ∀ {s x u} {f : H → H'}, IsOpen u → x ∈ u → (P f s x ↔ P f (s ∩ u) x)
  right_invariance :
    ∀ {s x f} {e : LocalHomeomorph H H}, e ∈ G → x ∈ e.Source → P f s x → P (f ∘ e.symm) (e.symm ⁻¹' s) (e x)
  congr_of_forall : ∀ {s x} {f g : H → H'}, (∀, ∀ y ∈ s, ∀, f y = g y) → f x = g x → P f s x → P g s x
  left_invariance' :
    ∀ {s x f} {e' : LocalHomeomorph H' H'}, e' ∈ G' → s ⊆ f ⁻¹' e'.Source → f x ∈ e'.Source → P f s x → P (e' ∘ f) s x

variable {G G'} {P : (H → H') → Set H → H → Prop} {s t u : Set H} {x : H}

variable (hG : G.LocalInvariantProp G' P)

include hG

namespace LocalInvariantProp

theorem congr_set {s t : Set H} {x : H} {f : H → H'} (hu : s =ᶠ[𝓝 x] t) : P f s x ↔ P f t x := by
  obtain ⟨o, host, ho, hxo⟩ := mem_nhds_iff.mp hu.mem_iff
  simp_rw [subset_def, mem_set_of, ← And.congr_left_iff, ← mem_inter_iff, ← Set.ext_iff] at host
  rw [hG.is_local ho hxo, host, ← hG.is_local ho hxo]

theorem is_local_nhds {s u : Set H} {x : H} {f : H → H'} (hu : u ∈ 𝓝[s] x) : P f s x ↔ P f (s ∩ u) x :=
  hG.congr_set <| mem_nhds_within_iff_eventually_eq.mp hu

theorem left_invariance {s : Set H} {x : H} {f : H → H'} {e' : LocalHomeomorph H' H'} (he' : e' ∈ G')
    (hfs : ContinuousWithinAt f s x) (hxe' : f x ∈ e'.Source) (hP : P f s x) : P (e' ∘ f) s x := by
  rw [hG.is_local_nhds (hfs.preimage_mem_nhds_within <| e'.open_source.mem_nhds hxe')] at hP⊢
  exact hG.left_invariance' he' (inter_subset_right _ _) hxe' hP

theorem congr_iff_nhds_within {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x) :
    P f s x ↔ P g s x := by
  simp_rw [hG.is_local_nhds h1]
  exact ⟨hG.congr_of_forall (fun y hy => hy.2) h2, hG.congr_of_forall (fun y hy => hy.2.symm) h2.symm⟩

theorem congr_nhds_within {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x) (hP : P f s x) :
    P g s x :=
  (hG.congr_iff_nhds_within h1 h2).mp hP

theorem congr_nhds_within' {s : Set H} {x : H} {f g : H → H'} (h1 : f =ᶠ[𝓝[s] x] g) (h2 : f x = g x) (hP : P g s x) :
    P f s x :=
  (hG.congr_iff_nhds_within h1 h2).mpr hP

theorem congr_iff {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) : P f s x ↔ P g s x :=
  hG.congr_iff_nhds_within (mem_nhds_within_of_mem_nhds h) (mem_of_mem_nhds h : _)

theorem congr {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P f s x) : P g s x :=
  (hG.congr_iff h).mp hP

theorem congr' {s : Set H} {x : H} {f g : H → H'} (h : f =ᶠ[𝓝 x] g) (hP : P g s x) : P f s x :=
  hG.congr h.symm hP

end LocalInvariantProp

end StructureGroupoid

namespace ChartedSpace

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property in a charted space, by requiring that it holds at the preferred chart at
this point. (When the property is local and invariant, it will in fact hold using any chart, see
`lift_prop_within_at_indep_chart`). We require continuity in the lifted property, as otherwise one
single chart might fail to capture the behavior of the function.
-/
def LiftPropWithinAt (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) (x : M) : Prop :=
  ContinuousWithinAt f s x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) ((chartAt H x).symm ⁻¹' s) (chartAt H x x)

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of functions on sets in a charted space, by requiring that it holds
around each point of the set, in the preferred charts. -/
def LiftPropOn (P : (H → H') → Set H → H → Prop) (f : M → M') (s : Set M) :=
  ∀, ∀ x ∈ s, ∀, LiftPropWithinAt P f s x

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function at a point in a charted space, by requiring that it holds
in the preferred chart. -/
def LiftPropAt (P : (H → H') → Set H → H → Prop) (f : M → M') (x : M) :=
  LiftPropWithinAt P f Univ x

theorem lift_prop_at_iff {P : (H → H') → Set H → H → Prop} {f : M → M'} {x : M} :
    LiftPropAt P f x ↔ ContinuousAt f x ∧ P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) Univ (chartAt H x x) := by
  rw [lift_prop_at, lift_prop_within_at, continuous_within_at_univ, preimage_univ]

/-- Given a property of germs of functions and sets in the model space, then one defines
a corresponding property of a function in a charted space, by requiring that it holds
in the preferred chart around every point. -/
def LiftProp (P : (H → H') → Set H → H → Prop) (f : M → M') :=
  ∀ x, LiftPropAt P f x

theorem lift_prop_iff {P : (H → H') → Set H → H → Prop} {f : M → M'} :
    LiftProp P f ↔ Continuous f ∧ ∀ x, P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm) Univ (chartAt H x x) := by
  simp_rw [lift_prop, lift_prop_at_iff, forall_and_distrib, continuous_iff_continuous_at]

end ChartedSpace

open ChartedSpace

namespace StructureGroupoid

variable {G : StructureGroupoid H} {G' : StructureGroupoid H'} {e e' : LocalHomeomorph M H}
  {f f' : LocalHomeomorph M' H'} {P : (H → H') → Set H → H → Prop} {g g' : M → M'} {s t : Set M} {x : M}
  {Q : (H → H) → Set H → H → Prop}

theorem lift_prop_within_at_univ : LiftPropWithinAt P g Univ x ↔ LiftPropAt P g x :=
  Iff.rfl

theorem lift_prop_on_univ : LiftPropOn P g Univ ↔ LiftProp P g := by
  simp [← lift_prop_on, ← lift_prop, ← lift_prop_at]

namespace LocalInvariantProp

variable (hG : G.LocalInvariantProp G' P)

include hG

/-- `lift_prop_within_at P f s x` is equivalent to a definition where we restrict the set we are
  considering to the domain of the charts at `x` and `f x`. -/
theorem lift_prop_within_at_iff {f : M → M'} (hf : ContinuousWithinAt f s x) :
    LiftPropWithinAt P f s x ↔
      P (chartAt H' (f x) ∘ f ∘ (chartAt H x).symm)
        ((chartAt H x).Target ∩ (chartAt H x).symm ⁻¹' (s ∩ f ⁻¹' (chartAt H' (f x)).Source)) (chartAt H x x) :=
  by
  rw [lift_prop_within_at, iff_true_intro hf, true_andₓ, hG.congr_set]
  exact
    LocalHomeomorph.preimage_eventually_eq_target_inter_preimage_inter hf (mem_chart_source H x)
      (chart_source_mem_nhds H' (f x))

/-- If a property of a germ of function `g` on a pointed set `(s, x)` is invariant under the
structure groupoid (by composition in the source space and in the target space), then
expressing it in charted spaces does not depend on the element of the maximal atlas one uses
both in the source and in the target manifolds, provided they are defined around `x` and `g x`
respectively, and provided `g` is continuous within `s` at `x` (otherwise, the local behavior
of `g` at `x` can not be captured with a chart in the target). -/
theorem lift_prop_within_at_indep_chart_aux (he : e ∈ G.MaximalAtlas M) (xe : x ∈ e.Source)
    (he' : e' ∈ G.MaximalAtlas M) (xe' : x ∈ e'.Source) (hf : f ∈ G'.MaximalAtlas M') (xf : g x ∈ f.Source)
    (hf' : f' ∈ G'.MaximalAtlas M') (xf' : g x ∈ f'.Source) (hgs : ContinuousWithinAt g s x)
    (h : P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x)) : P (f' ∘ g ∘ e'.symm) (e'.symm ⁻¹' s) (e' x) := by
  have hcont : ContinuousWithinAt (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
    rw [← e.left_inv xe] at hgs xf
    refine' (f.continuous_at <| xf).comp_continuous_within_at _
    exact hgs.comp (e.symm.continuous_at <| e.maps_to xe).ContinuousWithinAt subset.rfl
  have A : P (f.symm ≫ₕ f' ∘ f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
    refine'
      hG.left_invariance (compatible_of_mem_maximal_atlas hf hf') hcont
        (by
          simp' only [← xe, ← xf, ← xf'] with mfld_simps)
        h
  have B : P (f' ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) := by
    refine'
      hG.congr_nhds_within _
        (by
          simp' only [← xe, ← xf] with mfld_simps)
        A
    simp_rw [LocalHomeomorph.coe_trans, eventually_eq]
    have := (e.eventually_nhds_within' _ xe).mpr (hgs.eventually <| f.eventually_left_inverse xf)
    exact this.mono fun y => congr_arg f'
  let w := e.symm ≫ₕ e'
  let ow := w.symm ⁻¹' (e.symm ⁻¹' s)
  have wG : w ∈ G := compatible_of_mem_maximal_atlas he he'
  have C : P ((f' ∘ g ∘ e.symm) ∘ w.symm) ow (w (e x)) :=
    hG.right_invariance wG
      (by
        simp' only [← w, ← xe, ← xe'] with mfld_simps)
      B
  have : ∀, ∀ y ∈ e.source, ∀, w (e y) = e' y := fun y hy => by
    simp' only [← w, ← hy] with mfld_simps
  rw [this x xe] at C
  have D : P (f' ∘ g ∘ e'.symm) ow (e' x) := by
    refine' hG.congr _ C
    refine' ((e'.eventually_nhds' _ xe').mpr <| e.eventually_left_inverse xe).mono fun y hy => _
    simp' only [← w] with mfld_simps
    rw [hy]
  refine' (hG.congr_set _).2 D
  refine' ((eventually_of_mem _) fun y (hy : y ∈ e'.symm ⁻¹' e.source) => _).set_eq
  · refine' (e'.symm.continuous_at <| e'.maps_to xe').preimage_mem_nhds (e.open_source.mem_nhds _)
    simp_rw [e'.left_inv xe', xe]
    
  simp_rw [ow, mem_preimage, w, LocalHomeomorph.coe_trans_symm, LocalHomeomorph.symm_symm, Function.comp_applyₓ,
    e.left_inv hy]

theorem lift_prop_within_at_indep_chart [HasGroupoid M G] [HasGroupoid M' G'] (he : e ∈ G.MaximalAtlas M)
    (xe : x ∈ e.Source) (hf : f ∈ G'.MaximalAtlas M') (xf : g x ∈ f.Source) :
    LiftPropWithinAt P g s x ↔ ContinuousWithinAt g s x ∧ P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) (e x) :=
  ⟨fun H =>
    ⟨H.1,
      hG.lift_prop_within_at_indep_chart_aux (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) he xe
        (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf H.1 H.2⟩,
    fun H =>
    ⟨H.1,
      hG.lift_prop_within_at_indep_chart_aux he xe (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) hf xf
        (chart_mem_maximal_atlas _ _) (mem_chart_source _ _) H.1 H.2⟩⟩

theorem lift_prop_on_indep_chart [HasGroupoid M G] [HasGroupoid M' G'] (he : e ∈ G.MaximalAtlas M)
    (hf : f ∈ G'.MaximalAtlas M') (h : LiftPropOn P g s) {y : H} (hy : y ∈ e.Target ∩ e.symm ⁻¹' (s ∩ g ⁻¹' f.Source)) :
    P (f ∘ g ∘ e.symm) (e.symm ⁻¹' s) y := by
  convert ((hG.lift_prop_within_at_indep_chart he (e.symm_maps_to hy.1) hf hy.2.2).1 (h _ hy.2.1)).2
  rw [e.right_inv hy.1]

theorem lift_prop_within_at_inter' (ht : t ∈ 𝓝[s] x) : LiftPropWithinAt P g (s ∩ t) x ↔ LiftPropWithinAt P g s x := by
  rw [lift_prop_within_at, lift_prop_within_at, continuous_within_at_inter' ht, hG.congr_set]
  simp_rw [eventually_eq_set, mem_preimage,
    (chart_at H x).eventually_nhds' (fun x => x ∈ s ∩ t ↔ x ∈ s) (mem_chart_source H x)]
  exact (mem_nhds_within_iff_eventually_eq.mp ht).symm.mem_iff

theorem lift_prop_within_at_inter (ht : t ∈ 𝓝 x) : LiftPropWithinAt P g (s ∩ t) x ↔ LiftPropWithinAt P g s x :=
  hG.lift_prop_within_at_inter' (mem_nhds_within_of_mem_nhds ht)

theorem lift_prop_at_of_lift_prop_within_at (h : LiftPropWithinAt P g s x) (hs : s ∈ 𝓝 x) : LiftPropAt P g x := by
  have : s = univ ∩ s := by
    rw [univ_inter]
  rwa [this, hG.lift_prop_within_at_inter hs] at h

theorem lift_prop_within_at_of_lift_prop_at_of_mem_nhds (h : LiftPropAt P g x) (hs : s ∈ 𝓝 x) :
    LiftPropWithinAt P g s x := by
  have : s = univ ∩ s := by
    rw [univ_inter]
  rwa [this, hG.lift_prop_within_at_inter hs]

theorem lift_prop_on_of_locally_lift_prop_on (h : ∀, ∀ x ∈ s, ∀, ∃ u, IsOpen u ∧ x ∈ u ∧ LiftPropOn P g (s ∩ u)) :
    LiftPropOn P g s := by
  intro x hx
  rcases h x hx with ⟨u, u_open, xu, hu⟩
  have := hu x ⟨hx, xu⟩
  rwa [hG.lift_prop_within_at_inter] at this
  exact IsOpen.mem_nhds u_open xu

theorem lift_prop_of_locally_lift_prop_on (h : ∀ x, ∃ u, IsOpen u ∧ x ∈ u ∧ LiftPropOn P g u) : LiftProp P g := by
  rw [← lift_prop_on_univ]
  apply hG.lift_prop_on_of_locally_lift_prop_on fun x hx => _
  simp [← h x]

theorem lift_prop_within_at_congr_of_eventually_eq (h : LiftPropWithinAt P g s x) (h₁ : g' =ᶠ[𝓝[s] x] g)
    (hx : g' x = g x) : LiftPropWithinAt P g' s x := by
  refine' ⟨h.1.congr_of_eventually_eq h₁ hx, _⟩
  refine'
    hG.congr_nhds_within' _
      (by
        simp_rw [Function.comp_applyₓ, (chart_at H x).left_inv (mem_chart_source H x), hx])
      h.2
  simp_rw [eventually_eq, Function.comp_app,
    (chart_at H x).eventually_nhds_within' (fun y => chart_at H' (g' x) (g' y) = chart_at H' (g x) (g y))
      (mem_chart_source H x)]
  exact
    h₁.mono fun y hy => by
      rw [hx, hy]

theorem lift_prop_within_at_congr_iff_of_eventually_eq (h₁ : g' =ᶠ[𝓝[s] x] g) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  ⟨fun h => hG.lift_prop_within_at_congr_of_eventually_eq h h₁.symm hx.symm, fun h =>
    hG.lift_prop_within_at_congr_of_eventually_eq h h₁ hx⟩

theorem lift_prop_within_at_congr_iff (h₁ : ∀, ∀ y ∈ s, ∀, g' y = g y) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x ↔ LiftPropWithinAt P g s x :=
  hG.lift_prop_within_at_congr_iff_of_eventually_eq (eventually_nhds_within_of_forall h₁) hx

theorem lift_prop_within_at_congr (h : LiftPropWithinAt P g s x) (h₁ : ∀, ∀ y ∈ s, ∀, g' y = g y) (hx : g' x = g x) :
    LiftPropWithinAt P g' s x :=
  (hG.lift_prop_within_at_congr_iff h₁ hx).mpr h

theorem lift_prop_at_congr_iff_of_eventually_eq (h₁ : g' =ᶠ[𝓝 x] g) : LiftPropAt P g' x ↔ LiftPropAt P g x :=
  hG.lift_prop_within_at_congr_iff_of_eventually_eq
    (by
      simp_rw [nhds_within_univ, h₁])
    h₁.eq_of_nhds

theorem lift_prop_at_congr_of_eventually_eq (h : LiftPropAt P g x) (h₁ : g' =ᶠ[𝓝 x] g) : LiftPropAt P g' x :=
  (hG.lift_prop_at_congr_iff_of_eventually_eq h₁).mpr h

theorem lift_prop_on_congr (h : LiftPropOn P g s) (h₁ : ∀, ∀ y ∈ s, ∀, g' y = g y) : LiftPropOn P g' s := fun x hx =>
  hG.lift_prop_within_at_congr (h x hx) h₁ (h₁ x hx)

theorem lift_prop_on_congr_iff (h₁ : ∀, ∀ y ∈ s, ∀, g' y = g y) : LiftPropOn P g' s ↔ LiftPropOn P g s :=
  ⟨fun h => hG.lift_prop_on_congr h fun y hy => (h₁ y hy).symm, fun h => hG.lift_prop_on_congr h h₁⟩

omit hG

theorem lift_prop_within_at_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropWithinAt P g t x) (hst : s ⊆ t) : LiftPropWithinAt P g s x := by
  refine' ⟨h.1.mono hst, _⟩
  apply mono (fun y hy => _) h.2
  simp' only with mfld_simps  at hy
  simp' only [← hy, ← hst _] with mfld_simps

theorem lift_prop_within_at_of_lift_prop_at (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x)
    (h : LiftPropAt P g x) : LiftPropWithinAt P g s x := by
  rw [← lift_prop_within_at_univ] at h
  exact lift_prop_within_at_mono mono h (subset_univ _)

theorem lift_prop_on_mono (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x) (h : LiftPropOn P g t)
    (hst : s ⊆ t) : LiftPropOn P g s := fun x hx => lift_prop_within_at_mono mono (h x (hst hx)) hst

theorem lift_prop_on_of_lift_prop (mono : ∀ ⦃s x t⦄ ⦃f : H → H'⦄, t ⊆ s → P f s x → P f t x) (h : LiftProp P g) :
    LiftPropOn P g s := by
  rw [← lift_prop_on_univ] at h
  exact lift_prop_on_mono mono h (subset_univ _)

theorem lift_prop_at_of_mem_maximal_atlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id Univ y)
    (he : e ∈ MaximalAtlas M G) (hx : x ∈ e.Source) : LiftPropAt Q e x := by
  simp_rw [lift_prop_at, hG.lift_prop_within_at_indep_chart he hx G.id_mem_maximal_atlas (mem_univ _),
    (e.continuous_at hx).ContinuousWithinAt, true_andₓ]
  exact hG.congr' (e.eventually_right_inverse' hx) (hQ _)

theorem lift_prop_on_of_mem_maximal_atlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id Univ y)
    (he : e ∈ MaximalAtlas M G) : LiftPropOn Q e e.Source := by
  intro x hx
  apply hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds (hG.lift_prop_at_of_mem_maximal_atlas hQ he hx)
  exact IsOpen.mem_nhds e.open_source hx

theorem lift_prop_at_symm_of_mem_maximal_atlas [HasGroupoid M G] {x : H} (hG : G.LocalInvariantProp G Q)
    (hQ : ∀ y, Q id Univ y) (he : e ∈ MaximalAtlas M G) (hx : x ∈ e.Target) : LiftPropAt Q e.symm x := by
  suffices h : Q (e ∘ e.symm) univ x
  · have A : e.symm ⁻¹' e.source ∩ e.target = e.target := by
      mfld_set_tac
    have : e.symm x ∈ e.source := by
      simp' only [← hx] with mfld_simps
    rw [lift_prop_at, hG.lift_prop_within_at_indep_chart G.id_mem_maximal_atlas (mem_univ _) he this]
    refine' ⟨(e.symm.continuous_at hx).ContinuousWithinAt, _⟩
    simp' only [← h] with mfld_simps
    
  exact hG.congr' (e.eventually_right_inverse hx) (hQ x)

theorem lift_prop_on_symm_of_mem_maximal_atlas [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id Univ y)
    (he : e ∈ MaximalAtlas M G) : LiftPropOn Q e.symm e.Target := by
  intro x hx
  apply hG.lift_prop_within_at_of_lift_prop_at_of_mem_nhds (hG.lift_prop_at_symm_of_mem_maximal_atlas hQ he hx)
  exact IsOpen.mem_nhds e.open_target hx

theorem lift_prop_at_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id Univ y) :
    LiftPropAt Q (chartAt H x) x :=
  hG.lift_prop_at_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x) (mem_chart_source H x)

theorem lift_prop_on_chart [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id Univ y) :
    LiftPropOn Q (chartAt H x) (chartAt H x).Source :=
  hG.lift_prop_on_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)

theorem lift_prop_at_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id Univ y) :
    LiftPropAt Q (chartAt H x).symm ((chartAt H x) x) :=
  hG.lift_prop_at_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)
    (by
      simp )

theorem lift_prop_on_chart_symm [HasGroupoid M G] (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id Univ y) :
    LiftPropOn Q (chartAt H x).symm (chartAt H x).Target :=
  hG.lift_prop_on_symm_of_mem_maximal_atlas hQ (chart_mem_maximal_atlas G x)

theorem lift_prop_id (hG : G.LocalInvariantProp G Q) (hQ : ∀ y, Q id Univ y) : LiftProp Q (id : M → M) := by
  simp_rw [lift_prop_iff, continuous_id, true_andₓ]
  exact fun x => hG.congr' ((chart_at H x).eventually_right_inverse <| mem_chart_target H x) (hQ _)

end LocalInvariantProp

section LocalStructomorph

variable (G)

open LocalHomeomorph

/-- A function from a model space `H` to itself is a local structomorphism, with respect to a
structure groupoid `G` for `H`, relative to a set `s` in `H`, if for all points `x` in the set, the
function agrees with a `G`-structomorphism on `s` in a neighbourhood of `x`. -/
def IsLocalStructomorphWithinAt (f : H → H) (s : Set H) (x : H) : Prop :=
  x ∈ s → ∃ e : LocalHomeomorph H H, e ∈ G ∧ EqOn f e.toFun (s ∩ e.Source) ∧ x ∈ e.Source

/-- For a groupoid `G` which is `closed_under_restriction`, being a local structomorphism is a local
invariant property. -/
theorem is_local_structomorph_within_at_local_invariant_prop [ClosedUnderRestriction G] :
    LocalInvariantProp G G (IsLocalStructomorphWithinAt G) :=
  { is_local := by
      intro s x u f hu hux
      constructor
      · rintro h hx
        rcases h hx.1 with ⟨e, heG, hef, hex⟩
        have : s ∩ u ∩ e.source ⊆ s ∩ e.source := by
          mfld_set_tac
        exact ⟨e, heG, hef.mono this, hex⟩
        
      · rintro h hx
        rcases h ⟨hx, hux⟩ with ⟨e, heG, hef, hex⟩
        refine' ⟨e.restr (Interior u), _, _, _⟩
        · exact closed_under_restriction' heG is_open_interior
          
        · have : s ∩ u ∩ e.source = s ∩ (e.source ∩ u) := by
            mfld_set_tac
          simpa only [← this, ← interior_interior, ← hu.interior_eq] with mfld_simps using hef
          
        · simp' only [*, ← interior_interior, ← hu.interior_eq] with mfld_simps
          
        ,
    right_invariance := by
      intro s x f e' he'G he'x h hx
      have hxs : x ∈ s := by
        simpa only [← e'.left_inv he'x] with mfld_simps using hx
      rcases h hxs with ⟨e, heG, hef, hex⟩
      refine' ⟨e'.symm.trans e, G.trans (G.symm he'G) heG, _, _⟩
      · intro y hy
        simp' only with mfld_simps  at hy
        simp' only [← hef ⟨hy.1, hy.2.2⟩] with mfld_simps
        
      · simp' only [← hex, ← he'x] with mfld_simps
        ,
    congr_of_forall := by
      intro s x f g hfgs hfg' h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine' ⟨e, heG, _, hex⟩
      intro y hy
      rw [← hef hy, hfgs y hy.1],
    left_invariance' := by
      intro s x f e' he'G he' hfx h hx
      rcases h hx with ⟨e, heG, hef, hex⟩
      refine' ⟨e.trans e', G.trans heG he'G, _, _⟩
      · intro y hy
        simp' only with mfld_simps  at hy
        simp' only [← hef ⟨hy.1, hy.2.1⟩] with mfld_simps
        
      · simpa only [← hex, ← hef ⟨hx, hex⟩] with mfld_simps using hfx
         }

end LocalStructomorph

end StructureGroupoid

