/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Logic.Equiv.LocalEquiv
import Mathbin.Topology.Sets.Opens

/-!
# Local homeomorphisms

This file defines homeomorphisms between open subsets of topological spaces. An element `e` of
`local_homeomorph α β` is an extension of `local_equiv α β`, i.e., it is a pair of functions
`e.to_fun` and `e.inv_fun`, inverse of each other on the sets `e.source` and `e.target`.
Additionally, we require that these sets are open, and that the functions are continuous on them.
Equivalently, they are homeomorphisms there.

As in equivs, we register a coercion to functions, and we use `e x` and `e.symm x` throughout
instead of `e.to_fun x` and `e.inv_fun x`.

## Main definitions

`homeomorph.to_local_homeomorph`: associating a local homeomorphism to a homeomorphism, with
                                  source = target = univ
`local_homeomorph.symm`  : the inverse of a local homeomorphism
`local_homeomorph.trans` : the composition of two local homeomorphisms
`local_homeomorph.refl`  : the identity local homeomorphism
`local_homeomorph.of_set`: the identity on a set `s`
`eq_on_source`           : equivalence relation describing the "right" notion of equality for local
                           homeomorphisms

## Implementation notes

Most statements are copied from their local_equiv versions, although some care is required
especially when restricting to subsets, as these should be open subsets.

For design notes, see `local_equiv.lean`.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `local_equiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.
-/


open Function Set Filter

open TopologicalSpace (SecondCountableTopology)

open TopologicalSpace

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _} [TopologicalSpace α] [TopologicalSpace β]
  [TopologicalSpace γ] [TopologicalSpace δ]

/-- local homeomorphisms, defined on open subsets of the space -/
@[nolint has_inhabited_instance]
structure LocalHomeomorph (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] extends
  LocalEquiv α β where
  open_source : IsOpen source
  open_target : IsOpen target
  continuous_to_fun : ContinuousOn to_fun source
  continuous_inv_fun : ContinuousOn inv_fun target

namespace LocalHomeomorph

variable (e : LocalHomeomorph α β) (e' : LocalHomeomorph β γ)

instance : CoeFun (LocalHomeomorph α β) fun _ => α → β :=
  ⟨fun e => e.toFun⟩

/-- The inverse of a local homeomorphism -/
protected def symm : LocalHomeomorph β α :=
  { e.toLocalEquiv.symm with open_source := e.open_target, open_target := e.open_source,
    continuous_to_fun := e.continuous_inv_fun, continuous_inv_fun := e.continuous_to_fun }

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (e : LocalHomeomorph α β) : α → β :=
  e

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : LocalHomeomorph α β) : β → α :=
  e.symm

initialize_simps_projections LocalHomeomorph (to_local_equiv_to_fun → apply, to_local_equiv_inv_fun → symmApply,
  to_local_equiv_source → Source, to_local_equiv_target → Target, -toLocalEquiv)

protected theorem continuous_on : ContinuousOn e e.Source :=
  e.continuous_to_fun

theorem continuous_on_symm : ContinuousOn e.symm e.Target :=
  e.continuous_inv_fun

@[simp, mfld_simps]
theorem mk_coe (e : LocalEquiv α β) (a b c d) : (LocalHomeomorph.mk e a b c d : α → β) = e :=
  rfl

@[simp, mfld_simps]
theorem mk_coe_symm (e : LocalEquiv α β) (a b c d) : ((LocalHomeomorph.mk e a b c d).symm : β → α) = e.symm :=
  rfl

theorem to_local_equiv_injective : Injective (toLocalEquiv : LocalHomeomorph α β → LocalEquiv α β)
  | ⟨e, h₁, h₂, h₃, h₄⟩, ⟨e', h₁', h₂', h₃', h₄'⟩, rfl => rfl

/- Register a few simp lemmas to make sure that `simp` puts the application of a local
homeomorphism in its normal form, i.e., in terms of its coercion to a function. -/
@[simp, mfld_simps]
theorem to_fun_eq_coe (e : LocalHomeomorph α β) : e.toFun = e :=
  rfl

@[simp, mfld_simps]
theorem inv_fun_eq_coe (e : LocalHomeomorph α β) : e.invFun = e.symm :=
  rfl

@[simp, mfld_simps]
theorem coe_coe : (e.toLocalEquiv : α → β) = e :=
  rfl

@[simp, mfld_simps]
theorem coe_coe_symm : (e.toLocalEquiv.symm : β → α) = e.symm :=
  rfl

@[simp, mfld_simps]
theorem map_source {x : α} (h : x ∈ e.Source) : e x ∈ e.Target :=
  e.map_source' h

@[simp, mfld_simps]
theorem map_target {x : β} (h : x ∈ e.Target) : e.symm x ∈ e.Source :=
  e.map_target' h

@[simp, mfld_simps]
theorem left_inv {x : α} (h : x ∈ e.Source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
theorem right_inv {x : β} (h : x ∈ e.Target) : e (e.symm x) = x :=
  e.right_inv' h

theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.Source) (hy : y ∈ e.Target) : x = e.symm y ↔ e x = y :=
  e.toLocalEquiv.eq_symm_apply hx hy

protected theorem maps_to : MapsTo e e.Source e.Target := fun x => e.map_source

protected theorem symm_maps_to : MapsTo e.symm e.Target e.Source :=
  e.symm.MapsTo

protected theorem left_inv_on : LeftInvOn e.symm e e.Source := fun x => e.left_inv

protected theorem right_inv_on : RightInvOn e.symm e e.Target := fun x => e.right_inv

protected theorem inv_on : InvOn e.symm e e.Source e.Target :=
  ⟨e.LeftInvOn, e.RightInvOn⟩

protected theorem inj_on : InjOn e e.Source :=
  e.LeftInvOn.InjOn

protected theorem bij_on : BijOn e e.Source e.Target :=
  e.InvOn.BijOn e.MapsTo e.symm_maps_to

protected theorem surj_on : SurjOn e e.Source e.Target :=
  e.BijOn.SurjOn

/-- A homeomorphism induces a local homeomorphism on the whole space -/
@[simps (config := { mfldCfg with simpRhs := true })]
def _root_.homeomorph.to_local_homeomorph (e : α ≃ₜ β) : LocalHomeomorph α β :=
  { e.toEquiv.toLocalEquiv with open_source := is_open_univ, open_target := is_open_univ,
    continuous_to_fun := by
      erw [← continuous_iff_continuous_on_univ]
      exact e.continuous_to_fun,
    continuous_inv_fun := by
      erw [← continuous_iff_continuous_on_univ]
      exact e.continuous_inv_fun }

/-- Replace `to_local_equiv` field to provide better definitional equalities. -/
def replaceEquiv (e : LocalHomeomorph α β) (e' : LocalEquiv α β) (h : e.toLocalEquiv = e') : LocalHomeomorph α β where
  toLocalEquiv := e'
  open_source := h ▸ e.open_source
  open_target := h ▸ e.open_target
  continuous_to_fun := h ▸ e.continuous_to_fun
  continuous_inv_fun := h ▸ e.continuous_inv_fun

theorem replace_equiv_eq_self (e : LocalHomeomorph α β) (e' : LocalEquiv α β) (h : e.toLocalEquiv = e') :
    e.replaceEquiv e' h = e := by
  cases e
  subst e'
  rfl

theorem source_preimage_target : e.Source ⊆ e ⁻¹' e.Target :=
  e.MapsTo

theorem eq_of_local_equiv_eq {e e' : LocalHomeomorph α β} (h : e.toLocalEquiv = e'.toLocalEquiv) : e = e' := by
  cases e
  cases e'
  cases h
  rfl

theorem eventually_left_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.Source) : ∀ᶠ y in 𝓝 x, e.symm (e y) = y :=
  (e.open_source.eventually_mem hx).mono e.left_inv'

theorem eventually_left_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.Target) :
    ∀ᶠ y in 𝓝 (e.symm x), e.symm (e y) = y :=
  e.eventually_left_inverse (e.map_target hx)

theorem eventually_right_inverse (e : LocalHomeomorph α β) {x} (hx : x ∈ e.Target) : ∀ᶠ y in 𝓝 x, e (e.symm y) = y :=
  (e.open_target.eventually_mem hx).mono e.right_inv'

theorem eventually_right_inverse' (e : LocalHomeomorph α β) {x} (hx : x ∈ e.Source) :
    ∀ᶠ y in 𝓝 (e x), e (e.symm y) = y :=
  e.eventually_right_inverse (e.map_source hx)

theorem eventually_ne_nhds_within (e : LocalHomeomorph α β) {x} (hx : x ∈ e.Source) : ∀ᶠ x' in 𝓝[≠] x, e x' ≠ e x :=
  eventually_nhds_within_iff.2 <|
    (e.eventually_left_inverse hx).mono fun x' hx' =>
      mt fun h => by
        rw [mem_singleton_iff, ← e.left_inv hx, ← h, hx']

theorem nhds_within_source_inter {x} (hx : x ∈ e.Source) (s : Set α) : 𝓝[e.Source ∩ s] x = 𝓝[s] x :=
  nhds_within_inter_of_mem (mem_nhds_within_of_mem_nhds <| IsOpen.mem_nhds e.open_source hx)

theorem nhds_within_target_inter {x} (hx : x ∈ e.Target) (s : Set β) : 𝓝[e.Target ∩ s] x = 𝓝[s] x :=
  e.symm.nhds_within_source_inter hx s

theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.Source) : e '' s = e.Target ∩ e.symm ⁻¹' s :=
  e.toLocalEquiv.image_eq_target_inter_inv_preimage h

theorem image_source_inter_eq' (s : Set α) : e '' (e.Source ∩ s) = e.Target ∩ e.symm ⁻¹' s :=
  e.toLocalEquiv.image_source_inter_eq' s

theorem image_source_inter_eq (s : Set α) : e '' (e.Source ∩ s) = e.Target ∩ e.symm ⁻¹' (e.Source ∩ s) :=
  e.toLocalEquiv.image_source_inter_eq s

theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.Target) : e.symm '' s = e.Source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

theorem symm_image_target_inter_eq (s : Set β) : e.symm '' (e.Target ∩ s) = e.Source ∩ e ⁻¹' (e.Target ∩ s) :=
  e.symm.image_source_inter_eq _

theorem source_inter_preimage_inv_preimage (s : Set α) : e.Source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.Source ∩ s :=
  e.toLocalEquiv.source_inter_preimage_inv_preimage s

theorem target_inter_inv_preimage_preimage (s : Set β) : e.Target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.Target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _

theorem source_inter_preimage_target_inter (s : Set β) : e.Source ∩ e ⁻¹' (e.Target ∩ s) = e.Source ∩ e ⁻¹' s :=
  e.toLocalEquiv.source_inter_preimage_target_inter s

theorem image_source_eq_target (e : LocalHomeomorph α β) : e '' e.Source = e.Target :=
  e.toLocalEquiv.image_source_eq_target

theorem symm_image_target_eq_source (e : LocalHomeomorph α β) : e.symm '' e.Target = e.Source :=
  e.symm.image_source_eq_target

/-- Two local homeomorphisms are equal when they have equal `to_fun`, `inv_fun` and `source`.
It is not sufficient to have equal `to_fun` and `source`, as this only determines `inv_fun` on
the target. This would only be true for a weaker notion of equality, arguably the right one,
called `eq_on_source`. -/
@[ext]
protected theorem ext (e' : LocalHomeomorph α β) (h : ∀ x, e x = e' x) (hinv : ∀ x, e.symm x = e'.symm x)
    (hs : e.Source = e'.Source) : e = e' :=
  eq_of_local_equiv_eq (LocalEquiv.ext h hinv hs)

protected theorem ext_iff {e e' : LocalHomeomorph α β} :
    e = e' ↔ (∀ x, e x = e' x) ∧ (∀ x, e.symm x = e'.symm x) ∧ e.Source = e'.Source :=
  ⟨by
    rintro rfl
    exact ⟨fun x => rfl, fun x => rfl, rfl⟩, fun h => e.ext e' h.1 h.2.1 h.2.2⟩

@[simp, mfld_simps]
theorem symm_to_local_equiv : e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
  rfl

-- The following lemmas are already simp via local_equiv
theorem symm_source : e.symm.Source = e.Target :=
  rfl

theorem symm_target : e.symm.Target = e.Source :=
  rfl

@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e :=
  eq_of_local_equiv_eq <| by
    simp

/-- A local homeomorphism is continuous at any point of its source -/
protected theorem continuous_at {x : α} (h : x ∈ e.Source) : ContinuousAt e x :=
  (e.ContinuousOn x h).ContinuousAt (e.open_source.mem_nhds h)

/-- A local homeomorphism inverse is continuous at any point of its target -/
theorem continuous_at_symm {x : β} (h : x ∈ e.Target) : ContinuousAt e.symm x :=
  e.symm.ContinuousAt h

theorem tendsto_symm {x} (hx : x ∈ e.Source) : Tendsto e.symm (𝓝 (e x)) (𝓝 x) := by
  simpa only [← ContinuousAt, ← e.left_inv hx] using e.continuous_at_symm (e.map_source hx)

theorem map_nhds_eq {x} (hx : x ∈ e.Source) : map e (𝓝 x) = 𝓝 (e x) :=
  le_antisymmₓ (e.ContinuousAt hx) <| le_map_of_right_inverse (e.eventually_right_inverse' hx) (e.tendsto_symm hx)

theorem symm_map_nhds_eq {x} (hx : x ∈ e.Source) : map e.symm (𝓝 (e x)) = 𝓝 x :=
  (e.symm.map_nhds_eq <| e.map_source hx).trans <| by
    rw [e.left_inv hx]

theorem image_mem_nhds {x} (hx : x ∈ e.Source) {s : Set α} (hs : s ∈ 𝓝 x) : e '' s ∈ 𝓝 (e x) :=
  e.map_nhds_eq hx ▸ Filter.image_mem_map hs

theorem map_nhds_within_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.Source) (s : Set α) :
    map e (𝓝[s] x) = 𝓝[e '' (e.Source ∩ s)] e x :=
  calc
    map e (𝓝[s] x) = map e (𝓝[e.Source ∩ s] x) := congr_arg (map e) (e.nhds_within_source_inter hx _).symm
    _ = 𝓝[e '' (e.Source ∩ s)] e x :=
      (e.LeftInvOn.mono <| inter_subset_left _ _).map_nhds_within_eq (e.left_inv hx)
        (e.continuous_at_symm (e.map_source hx)).ContinuousWithinAt (e.ContinuousAt hx).ContinuousWithinAt
    

theorem map_nhds_within_preimage_eq (e : LocalHomeomorph α β) {x} (hx : x ∈ e.Source) (s : Set β) :
    map e (𝓝[e ⁻¹' s] x) = 𝓝[s] e x := by
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.target_inter_inv_preimage_preimage,
    e.nhds_within_target_inter (e.map_source hx)]

theorem eventually_nhds (e : LocalHomeomorph α β) {x : α} (p : β → Prop) (hx : x ∈ e.Source) :
    (∀ᶠ y in 𝓝 (e x), p y) ↔ ∀ᶠ x in 𝓝 x, p (e x) :=
  Iff.trans
    (by
      rw [e.map_nhds_eq hx])
    eventually_map

theorem eventually_nhds' (e : LocalHomeomorph α β) {x : α} (p : α → Prop) (hx : x ∈ e.Source) :
    (∀ᶠ y in 𝓝 (e x), p (e.symm y)) ↔ ∀ᶠ x in 𝓝 x, p x := by
  rw [e.eventually_nhds _ hx]
  refine' eventually_congr ((e.eventually_left_inverse hx).mono fun y hy => _)
  rw [hy]

theorem eventually_nhds_within (e : LocalHomeomorph α β) {x : α} (p : β → Prop) {s : Set α} (hx : x ∈ e.Source) :
    (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p y) ↔ ∀ᶠ x in 𝓝[s] x, p (e x) := by
  refine' Iff.trans _ eventually_map
  rw [e.map_nhds_within_eq hx, e.image_source_inter_eq', e.nhds_within_target_inter (e.maps_to hx)]

theorem eventually_nhds_within' (e : LocalHomeomorph α β) {x : α} (p : α → Prop) {s : Set α} (hx : x ∈ e.Source) :
    (∀ᶠ y in 𝓝[e.symm ⁻¹' s] e x, p (e.symm y)) ↔ ∀ᶠ x in 𝓝[s] x, p x := by
  rw [e.eventually_nhds_within _ hx]
  refine'
    eventually_congr ((eventually_nhds_within_of_eventually_nhds <| e.eventually_left_inverse hx).mono fun y hy => _)
  rw [hy]

/-- This lemma is useful in the manifold library in the case that `e` is a chart. It states that
  locally around `e x` the set `e.symm ⁻¹' s` is the same as the set intersected with the target
  of `e` and some other neighborhood of `f x` (which will be the source of a chart on `γ`).  -/
theorem preimage_eventually_eq_target_inter_preimage_inter {e : LocalHomeomorph α β} {s : Set α} {t : Set γ} {x : α}
    {f : α → γ} (hf : ContinuousWithinAt f s x) (hxe : x ∈ e.Source) (ht : t ∈ 𝓝 (f x)) :
    e.symm ⁻¹' s =ᶠ[𝓝 (e x)] (e.Target ∩ e.symm ⁻¹' (s ∩ f ⁻¹' t) : Set β) := by
  rw [eventually_eq_set, e.eventually_nhds _ hxe]
  filter_upwards [e.open_source.mem_nhds hxe, mem_nhds_within_iff_eventually.mp (hf.preimage_mem_nhds_within ht)]
  intro y hy hyu
  simp_rw [mem_inter_iff, mem_preimage, mem_inter_iff, e.maps_to hy, true_andₓ, iff_self_and, e.left_inv hy,
    iff_true_intro hyu]

theorem preimage_open_of_open {s : Set β} (hs : IsOpen s) : IsOpen (e.Source ∩ e ⁻¹' s) :=
  e.ContinuousOn.preimage_open_of_open e.open_source hs

/-!
### `local_homeomorph.is_image` relation

We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).

This definition is a restatement of `local_equiv.is_image` for local homeomorphisms. In this section
we transfer API about `local_equiv.is_image` to local homeomorphisms and add a few
`local_homeomorph`-specific lemmas like `local_homeomorph.is_image.closure`.
-/


/-- We say that `t : set β` is an image of `s : set α` under a local homeomorphism `e` if any of the
following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.Source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

theorem to_local_equiv (h : e.IsImage s t) : e.toLocalEquiv.IsImage s t :=
  h

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.Source) : e x ∈ t ↔ x ∈ s :=
  h hx

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.toLocalEquiv.symm

theorem symm_apply_mem_iff (h : e.IsImage s t) (hy : y ∈ e.Target) : e.symm y ∈ s ↔ y ∈ t :=
  h.symm hy

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

protected theorem maps_to (h : e.IsImage s t) : MapsTo e (e.Source ∩ s) (e.Target ∩ t) :=
  h.toLocalEquiv.MapsTo

theorem symm_maps_to (h : e.IsImage s t) : MapsTo e.symm (e.Target ∩ t) (e.Source ∩ s) :=
  h.symm.MapsTo

theorem image_eq (h : e.IsImage s t) : e '' (e.Source ∩ s) = e.Target ∩ t :=
  h.toLocalEquiv.image_eq

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.Target ∩ t) = e.Source ∩ s :=
  h.symm.image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.Source ∩ e ⁻¹' t = e.Source ∩ s :=
  LocalEquiv.IsImage.iff_preimage_eq

alias iff_preimage_eq ↔ preimage_eq of_preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.Target ∩ e.symm ⁻¹' s = e.Target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias iff_symm_preimage_eq ↔ symm_preimage_eq of_symm_preimage_eq

theorem iff_symm_preimage_eq' : e.IsImage s t ↔ e.Target ∩ e.symm ⁻¹' (e.Source ∩ s) = e.Target ∩ t := by
  rw [iff_symm_preimage_eq, ← image_source_inter_eq, ← image_source_inter_eq']

alias iff_symm_preimage_eq' ↔ symm_preimage_eq' of_symm_preimage_eq'

theorem iff_preimage_eq' : e.IsImage s t ↔ e.Source ∩ e ⁻¹' (e.Target ∩ t) = e.Source ∩ s :=
  symm_iff.symm.trans iff_symm_preimage_eq'

alias iff_preimage_eq' ↔ preimage_eq' of_preimage_eq'

theorem of_image_eq (h : e '' (e.Source ∩ s) = e.Target ∩ t) : e.IsImage s t :=
  LocalEquiv.IsImage.of_image_eq h

theorem of_symm_image_eq (h : e.symm '' (e.Target ∩ t) = e.Source ∩ s) : e.IsImage s t :=
  LocalEquiv.IsImage.of_symm_image_eq h

protected theorem compl (h : e.IsImage s t) : e.IsImage (sᶜ) (tᶜ) := fun x hx => not_congr (h hx)

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') : e.IsImage (s ∩ s') (t ∩ t') := fun x hx =>
  and_congr (h hx) (h' hx)

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') : e.IsImage (s ∪ s') (t ∪ t') := fun x hx =>
  or_congr (h hx) (h' hx)

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') : e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

theorem left_inv_on_piecewise {e' : LocalHomeomorph α β} [∀ i, Decidable (i ∈ s)] [∀ i, Decidable (i ∈ t)]
    (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.Source e'.Source) :=
  h.toLocalEquiv.left_inv_on_piecewise h'

theorem inter_eq_of_inter_eq_of_eq_on {e' : LocalHomeomorph α β} (h : e.IsImage s t) (h' : e'.IsImage s t)
    (hs : e.Source ∩ s = e'.Source ∩ s) (Heq : EqOn e e' (e.Source ∩ s)) : e.Target ∩ t = e'.Target ∩ t :=
  h.toLocalEquiv.inter_eq_of_inter_eq_of_eq_on h' hs Heq

theorem symm_eq_on_of_inter_eq_of_eq_on {e' : LocalHomeomorph α β} (h : e.IsImage s t)
    (hs : e.Source ∩ s = e'.Source ∩ s) (Heq : EqOn e e' (e.Source ∩ s)) : EqOn e.symm e'.symm (e.Target ∩ t) :=
  h.toLocalEquiv.symm_eq_on_of_inter_eq_of_eq_on hs Heq

theorem map_nhds_within_eq (h : e.IsImage s t) (hx : x ∈ e.Source) : map e (𝓝[s] x) = 𝓝[t] e x := by
  rw [e.map_nhds_within_eq hx, h.image_eq, e.nhds_within_target_inter (e.map_source hx)]

protected theorem closure (h : e.IsImage s t) : e.IsImage (Closure s) (Closure t) := fun x hx => by
  simp only [← mem_closure_iff_nhds_within_ne_bot, h.map_nhds_within_eq hx, ← map_ne_bot_iff]

protected theorem interior (h : e.IsImage s t) : e.IsImage (Interior s) (Interior t) := by
  simpa only [← closure_compl, ← compl_compl] using h.compl.closure.compl

protected theorem frontier (h : e.IsImage s t) : e.IsImage (Frontier s) (Frontier t) :=
  h.closure.diff h.Interior

theorem is_open_iff (h : e.IsImage s t) : IsOpen (e.Source ∩ s) ↔ IsOpen (e.Target ∩ t) :=
  ⟨fun hs => h.symm_preimage_eq' ▸ e.symm.preimage_open_of_open hs, fun hs =>
    h.preimage_eq' ▸ e.preimage_open_of_open hs⟩

/-- Restrict a `local_homeomorph` to a pair of corresponding open sets. -/
@[simps toLocalEquiv]
def restr (h : e.IsImage s t) (hs : IsOpen (e.Source ∩ s)) : LocalHomeomorph α β where
  toLocalEquiv := h.toLocalEquiv.restr
  open_source := hs
  open_target := h.is_open_iff.1 hs
  continuous_to_fun := e.ContinuousOn.mono (inter_subset_left _ _)
  continuous_inv_fun := e.symm.ContinuousOn.mono (inter_subset_left _ _)

end IsImage

theorem is_image_source_target : e.IsImage e.Source e.Target :=
  e.toLocalEquiv.is_image_source_target

theorem is_image_source_target_of_disjoint (e' : LocalHomeomorph α β) (hs : Disjoint e.Source e'.Source)
    (ht : Disjoint e.Target e'.Target) : e.IsImage e'.Source e'.Target :=
  e.toLocalEquiv.is_image_source_target_of_disjoint e'.toLocalEquiv hs ht

/-- Preimage of interior or interior of preimage coincide for local homeomorphisms, when restricted
to the source. -/
theorem preimage_interior (s : Set β) : e.Source ∩ e ⁻¹' Interior s = e.Source ∩ Interior (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).Interior.preimage_eq

theorem preimage_closure (s : Set β) : e.Source ∩ e ⁻¹' Closure s = e.Source ∩ Closure (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).closure.preimage_eq

theorem preimage_frontier (s : Set β) : e.Source ∩ e ⁻¹' Frontier s = e.Source ∩ Frontier (e ⁻¹' s) :=
  (IsImage.of_preimage_eq rfl).Frontier.preimage_eq

theorem preimage_open_of_open_symm {s : Set α} (hs : IsOpen s) : IsOpen (e.Target ∩ e.symm ⁻¹' s) :=
  e.symm.ContinuousOn.preimage_open_of_open e.open_target hs

/-- The image of an open set in the source is open. -/
theorem image_open_of_open {s : Set α} (hs : IsOpen s) (h : s ⊆ e.Source) : IsOpen (e '' s) := by
  have : e '' s = e.target ∩ e.symm ⁻¹' s := e.to_local_equiv.image_eq_target_inter_inv_preimage h
  rw [this]
  exact e.continuous_on_symm.preimage_open_of_open e.open_target hs

/-- The image of the restriction of an open set to the source is open. -/
theorem image_open_of_open' {s : Set α} (hs : IsOpen s) : IsOpen (e '' (e.Source ∩ s)) :=
  image_open_of_open _ (IsOpen.inter e.open_source hs) (inter_subset_left _ _)

/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def ofContinuousOpenRestrict (e : LocalEquiv α β) (hc : ContinuousOn e e.Source) (ho : IsOpenMap (e.Source.restrict e))
    (hs : IsOpen e.Source) : LocalHomeomorph α β where
  toLocalEquiv := e
  open_source := hs
  open_target := by
    simpa only [← range_restrict, ← e.image_source_eq_target] using ho.is_open_range
  continuous_to_fun := hc
  continuous_inv_fun := e.image_source_eq_target ▸ ho.continuous_on_image_of_left_inv_on e.LeftInvOn

/-- A `local_equiv` with continuous open forward map and an open source is a `local_homeomorph`. -/
def ofContinuousOpen (e : LocalEquiv α β) (hc : ContinuousOn e e.Source) (ho : IsOpenMap e) (hs : IsOpen e.Source) :
    LocalHomeomorph α β :=
  ofContinuousOpenRestrict e hc (ho.restrict hs) hs

/-- Restricting a local homeomorphism `e` to `e.source ∩ s` when `s` is open. This is sometimes hard
to use because of the openness assumption, but it has the advantage that when it can
be used then its local_equiv is defeq to local_equiv.restr -/
protected def restrOpen (s : Set α) (hs : IsOpen s) : LocalHomeomorph α β :=
  (@IsImage.of_symm_preimage_eq α β _ _ e s (e.symm ⁻¹' s) rfl).restr (IsOpen.inter e.open_source hs)

@[simp, mfld_simps]
theorem restr_open_to_local_equiv (s : Set α) (hs : IsOpen s) :
    (e.restrOpen s hs).toLocalEquiv = e.toLocalEquiv.restr s :=
  rfl

-- Already simp via local_equiv
theorem restr_open_source (s : Set α) (hs : IsOpen s) : (e.restrOpen s hs).Source = e.Source ∩ s :=
  rfl

/-- Restricting a local homeomorphism `e` to `e.source ∩ interior s`. We use the interior to make
sure that the restriction is well defined whatever the set s, since local homeomorphisms are by
definition defined on open sets. In applications where `s` is open, this coincides with the
restriction of local equivalences -/
@[simps (config := mfldCfg) apply symmApply, simps (config := { attrs := [] }) Source Target]
protected def restr (s : Set α) : LocalHomeomorph α β :=
  e.restrOpen (Interior s) is_open_interior

@[simp, mfld_simps]
theorem restr_to_local_equiv (s : Set α) : (e.restr s).toLocalEquiv = e.toLocalEquiv.restr (Interior s) :=
  rfl

theorem restr_source' (s : Set α) (hs : IsOpen s) : (e.restr s).Source = e.Source ∩ s := by
  rw [e.restr_source, hs.interior_eq]

theorem restr_to_local_equiv' (s : Set α) (hs : IsOpen s) : (e.restr s).toLocalEquiv = e.toLocalEquiv.restr s := by
  rw [e.restr_to_local_equiv, hs.interior_eq]

theorem restr_eq_of_source_subset {e : LocalHomeomorph α β} {s : Set α} (h : e.Source ⊆ s) : e.restr s = e := by
  apply eq_of_local_equiv_eq
  rw [restr_to_local_equiv]
  apply LocalEquiv.restr_eq_of_source_subset
  exact interior_maximal h e.open_source

@[simp, mfld_simps]
theorem restr_univ {e : LocalHomeomorph α β} : e.restr Univ = e :=
  restr_eq_of_source_subset (subset_univ _)

theorem restr_source_inter (s : Set α) : e.restr (e.Source ∩ s) = e.restr s := by
  refine' LocalHomeomorph.ext _ _ (fun x => rfl) (fun x => rfl) _
  simp [← e.open_source.interior_eq, inter_assoc]

/-- The identity on the whole space as a local homeomorphism. -/
@[simps (config := mfldCfg) apply, simps (config := { attrs := [] }) Source Target]
protected def refl (α : Type _) [TopologicalSpace α] : LocalHomeomorph α α :=
  (Homeomorph.refl α).toLocalHomeomorph

@[simp, mfld_simps]
theorem refl_local_equiv : (LocalHomeomorph.refl α).toLocalEquiv = LocalEquiv.refl α :=
  rfl

@[simp, mfld_simps]
theorem refl_symm : (LocalHomeomorph.refl α).symm = LocalHomeomorph.refl α :=
  rfl

section

variable {s : Set α} (hs : IsOpen s)

/-- The identity local equiv on a set `s` -/
@[simps (config := mfldCfg) apply, simps (config := { attrs := [] }) Source Target]
def ofSet (s : Set α) (hs : IsOpen s) : LocalHomeomorph α α :=
  { LocalEquiv.ofSet s with open_source := hs, open_target := hs, continuous_to_fun := continuous_id.ContinuousOn,
    continuous_inv_fun := continuous_id.ContinuousOn }

@[simp, mfld_simps]
theorem of_set_to_local_equiv : (ofSet s hs).toLocalEquiv = LocalEquiv.ofSet s :=
  rfl

@[simp, mfld_simps]
theorem of_set_symm : (ofSet s hs).symm = ofSet s hs :=
  rfl

@[simp, mfld_simps]
theorem of_set_univ_eq_refl : ofSet Univ is_open_univ = LocalHomeomorph.refl α := by
  ext <;> simp

end

/-- Composition of two local homeomorphisms when the target of the first and the source of
the second coincide. -/
protected def trans' (h : e.Target = e'.Source) : LocalHomeomorph α γ :=
  { LocalEquiv.trans' e.toLocalEquiv e'.toLocalEquiv h with open_source := e.open_source, open_target := e'.open_target,
    continuous_to_fun := by
      apply e'.continuous_to_fun.comp e.continuous_to_fun
      rw [← h]
      exact e.to_local_equiv.source_subset_preimage_target,
    continuous_inv_fun := by
      apply e.continuous_inv_fun.comp e'.continuous_inv_fun
      rw [h]
      exact e'.to_local_equiv.target_subset_preimage_source }

/-- Composing two local homeomorphisms, by restricting to the maximal domain where their
composition is well defined. -/
protected def trans : LocalHomeomorph α γ :=
  LocalHomeomorph.trans' (e.symm.restrOpen e'.Source e'.open_source).symm (e'.restrOpen e.Target e.open_target)
    (by
      simp [← inter_comm])

@[simp, mfld_simps]
theorem trans_to_local_equiv : (e.trans e').toLocalEquiv = e.toLocalEquiv.trans e'.toLocalEquiv :=
  rfl

@[simp, mfld_simps]
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl

theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl

theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := by
  cases e <;> cases e' <;> rfl

/- This could be considered as a simp lemma, but there are many situations where it makes something
simple into something more complicated. -/
theorem trans_source : (e.trans e').Source = e.Source ∩ e ⁻¹' e'.Source :=
  LocalEquiv.trans_source e.toLocalEquiv e'.toLocalEquiv

theorem trans_source' : (e.trans e').Source = e.Source ∩ e ⁻¹' (e.Target ∩ e'.Source) :=
  LocalEquiv.trans_source' e.toLocalEquiv e'.toLocalEquiv

theorem trans_source'' : (e.trans e').Source = e.symm '' (e.Target ∩ e'.Source) :=
  LocalEquiv.trans_source'' e.toLocalEquiv e'.toLocalEquiv

theorem image_trans_source : e '' (e.trans e').Source = e.Target ∩ e'.Source :=
  LocalEquiv.image_trans_source e.toLocalEquiv e'.toLocalEquiv

theorem trans_target : (e.trans e').Target = e'.Target ∩ e'.symm ⁻¹' e.Target :=
  rfl

theorem trans_target' : (e.trans e').Target = e'.Target ∩ e'.symm ⁻¹' (e'.Source ∩ e.Target) :=
  trans_source' e'.symm e.symm

theorem trans_target'' : (e.trans e').Target = e' '' (e'.Source ∩ e.Target) :=
  trans_source'' e'.symm e.symm

theorem inv_image_trans_target : e'.symm '' (e.trans e').Target = e'.Source ∩ e.Target :=
  image_trans_source e'.symm e.symm

theorem trans_assoc (e'' : LocalHomeomorph γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  eq_of_local_equiv_eq <| LocalEquiv.trans_assoc e.toLocalEquiv e'.toLocalEquiv e''.toLocalEquiv

@[simp, mfld_simps]
theorem trans_refl : e.trans (LocalHomeomorph.refl β) = e :=
  eq_of_local_equiv_eq <| LocalEquiv.trans_refl e.toLocalEquiv

@[simp, mfld_simps]
theorem refl_trans : (LocalHomeomorph.refl α).trans e = e :=
  eq_of_local_equiv_eq <| LocalEquiv.refl_trans e.toLocalEquiv

theorem trans_of_set {s : Set β} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e ⁻¹' s) :=
  (LocalHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [← LocalEquiv.trans_source, ← (e.preimage_interior _).symm, ← hs.interior_eq]

theorem trans_of_set' {s : Set β} (hs : IsOpen s) : e.trans (ofSet s hs) = e.restr (e.Source ∩ e ⁻¹' s) := by
  rw [trans_of_set, restr_source_inter]

theorem of_set_trans {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr s :=
  (LocalHomeomorph.ext _ _ (fun x => rfl) fun x => rfl) <| by
    simp [← LocalEquiv.trans_source, ← hs.interior_eq, ← inter_comm]

theorem of_set_trans' {s : Set α} (hs : IsOpen s) : (ofSet s hs).trans e = e.restr (e.Source ∩ s) := by
  rw [of_set_trans, restr_source_inter]

@[simp, mfld_simps]
theorem of_set_trans_of_set {s : Set α} (hs : IsOpen s) {s' : Set α} (hs' : IsOpen s') :
    (ofSet s hs).trans (ofSet s' hs') = ofSet (s ∩ s') (IsOpen.inter hs hs') := by
  rw [(of_set s hs).trans_of_set hs']
  ext <;> simp [← hs'.interior_eq]

theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  eq_of_local_equiv_eq <| LocalEquiv.restr_trans e.toLocalEquiv e'.toLocalEquiv (Interior s)

/-- Postcompose a local homeomorphism with an homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps (config := { fullyApplied := false })]
def transHomeomorph (e' : β ≃ₜ γ) : LocalHomeomorph α γ where
  toLocalEquiv := e.toLocalEquiv.transEquiv e'.toEquiv
  open_source := e.open_source
  open_target := e.open_target.Preimage e'.symm.Continuous
  continuous_to_fun := e'.Continuous.comp_continuous_on e.ContinuousOn
  continuous_inv_fun := e.symm.ContinuousOn.comp e'.symm.Continuous.ContinuousOn fun x h => h

theorem trans_equiv_eq_trans (e' : β ≃ₜ γ) : e.transHomeomorph e' = e.trans e'.toLocalHomeomorph :=
  to_local_equiv_injective <| LocalEquiv.trans_equiv_eq_trans _ _

/-- Precompose a local homeomorphism with an homeomorphism.
We modify the source and target to have better definitional behavior. -/
@[simps (config := { fullyApplied := false })]
def _root_.homeomorph.trans_local_homeomorph (e : α ≃ₜ β) : LocalHomeomorph α γ where
  toLocalEquiv := e.toEquiv.transLocalEquiv e'.toLocalEquiv
  open_source := e'.open_source.Preimage e.Continuous
  open_target := e'.open_target
  continuous_to_fun := e'.ContinuousOn.comp e.Continuous.ContinuousOn fun x h => h
  continuous_inv_fun := e.symm.Continuous.comp_continuous_on e'.symm.ContinuousOn

theorem _root_.homeomorph.trans_local_homeomorph_eq_trans (e : α ≃ₜ β) :
    e.transLocalHomeomorph e' = e.toLocalHomeomorph.trans e' :=
  to_local_equiv_injective <| Equivₓ.trans_local_equiv_eq_trans _ _

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. They
should really be considered the same local equiv. -/
def EqOnSource (e e' : LocalHomeomorph α β) : Prop :=
  e.Source = e'.Source ∧ EqOn e e' e.Source

theorem eq_on_source_iff (e e' : LocalHomeomorph α β) :
    EqOnSource e e' ↔ LocalEquiv.EqOnSource e.toLocalEquiv e'.toLocalEquiv :=
  Iff.rfl

/-- `eq_on_source` is an equivalence relation -/
instance : Setoidₓ (LocalHomeomorph α β) where
  R := EqOnSource
  iseqv :=
    ⟨fun e => (@LocalEquiv.eqOnSourceSetoid α β).iseqv.1 e.toLocalEquiv, fun e e' h =>
      (@LocalEquiv.eqOnSourceSetoid α β).iseqv.2.1 ((eq_on_source_iff e e').1 h), fun e e' e'' h h' =>
      (@LocalEquiv.eqOnSourceSetoid α β).iseqv.2.2 ((eq_on_source_iff e e').1 h) ((eq_on_source_iff e' e'').1 h')⟩

theorem eq_on_source_refl : e ≈ e :=
  Setoidₓ.refl _

/-- If two local homeomorphisms are equivalent, so are their inverses -/
theorem EqOnSource.symm' {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.symm ≈ e'.symm :=
  LocalEquiv.EqOnSource.symm' h

/-- Two equivalent local homeomorphisms have the same source -/
theorem EqOnSource.source_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.Source = e'.Source :=
  h.1

/-- Two equivalent local homeomorphisms have the same target -/
theorem EqOnSource.target_eq {e e' : LocalHomeomorph α β} (h : e ≈ e') : e.Target = e'.Target :=
  h.symm'.1

/-- Two equivalent local homeomorphisms have coinciding `to_fun` on the source -/
theorem EqOnSource.eq_on {e e' : LocalHomeomorph α β} (h : e ≈ e') : EqOn e e' e.Source :=
  h.2

/-- Two equivalent local homeomorphisms have coinciding `inv_fun` on the target -/
theorem EqOnSource.symm_eq_on_target {e e' : LocalHomeomorph α β} (h : e ≈ e') : EqOn e.symm e'.symm e.Target :=
  h.symm'.2

/-- Composition of local homeomorphisms respects equivalence -/
theorem EqOnSource.trans' {e e' : LocalHomeomorph α β} {f f' : LocalHomeomorph β γ} (he : e ≈ e') (hf : f ≈ f') :
    e.trans f ≈ e'.trans f' :=
  LocalEquiv.EqOnSource.trans' he hf

/-- Restriction of local homeomorphisms respects equivalence -/
theorem EqOnSource.restr {e e' : LocalHomeomorph α β} (he : e ≈ e') (s : Set α) : e.restr s ≈ e'.restr s :=
  LocalEquiv.EqOnSource.restr he _

/-- Composition of a local homeomorphism and its inverse is equivalent to the restriction of the
identity to the source -/
theorem trans_self_symm : e.trans e.symm ≈ LocalHomeomorph.ofSet e.Source e.open_source :=
  LocalEquiv.trans_self_symm _

theorem trans_symm_self : e.symm.trans e ≈ LocalHomeomorph.ofSet e.Target e.open_target :=
  e.symm.trans_self_symm

theorem eq_of_eq_on_source_univ {e e' : LocalHomeomorph α β} (h : e ≈ e') (s : e.Source = univ) (t : e.Target = univ) :
    e = e' :=
  eq_of_local_equiv_eq <| LocalEquiv.eq_of_eq_on_source_univ _ _ h s t

section Prod

/-- The product of two local homeomorphisms, as a local homeomorphism on the product space. -/
@[simps (config := mfldCfg) toLocalEquiv apply, simps (config := { attrs := [] }) Source Target symmApply]
def prod (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) : LocalHomeomorph (α × γ) (β × δ) where
  open_source := e.open_source.Prod e'.open_source
  open_target := e.open_target.Prod e'.open_target
  continuous_to_fun := e.ContinuousOn.prod_map e'.ContinuousOn
  continuous_inv_fun := e.continuous_on_symm.prod_map e'.continuous_on_symm
  toLocalEquiv := e.toLocalEquiv.Prod e'.toLocalEquiv

@[simp, mfld_simps]
theorem prod_symm (e : LocalHomeomorph α β) (e' : LocalHomeomorph γ δ) : (e.Prod e').symm = e.symm.Prod e'.symm :=
  rfl

@[simp, mfld_simps]
theorem prod_trans {η : Type _} {ε : Type _} [TopologicalSpace η] [TopologicalSpace ε] (e : LocalHomeomorph α β)
    (f : LocalHomeomorph β γ) (e' : LocalHomeomorph δ η) (f' : LocalHomeomorph η ε) :
    (e.Prod e').trans (f.Prod f') = (e.trans f).Prod (e'.trans f') :=
  LocalHomeomorph.eq_of_local_equiv_eq <| by
    dsimp' only [← trans_to_local_equiv, ← prod_to_local_equiv] <;> apply LocalEquiv.prod_trans

theorem prod_eq_prod_of_nonempty {e₁ e₁' : LocalHomeomorph α β} {e₂ e₂' : LocalHomeomorph γ δ}
    (h : (e₁.Prod e₂).Source.Nonempty) : e₁.Prod e₂ = e₁'.Prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  obtain ⟨⟨x, y⟩, -⟩ := id h
  have : Nonempty α := ⟨x⟩
  have : Nonempty β := ⟨e₁ x⟩
  have : Nonempty γ := ⟨y⟩
  have : Nonempty δ := ⟨e₂ y⟩
  simp_rw [LocalHomeomorph.ext_iff, prod_apply, prod_symm_apply, prod_source, Prod.ext_iff,
    Set.prod_eq_prod_iff_of_nonempty h, forall_and_distrib, Prod.forall, forall_const, forall_forall_const, and_assoc,
    And.left_comm]

theorem prod_eq_prod_of_nonempty' {e₁ e₁' : LocalHomeomorph α β} {e₂ e₂' : LocalHomeomorph γ δ}
    (h : (e₁'.Prod e₂').Source.Nonempty) : e₁.Prod e₂ = e₁'.Prod e₂' ↔ e₁ = e₁' ∧ e₂ = e₂' := by
  rw [eq_comm, prod_eq_prod_of_nonempty h, eq_comm, @eq_comm _ e₂']

end Prod

section Piecewise

/-- Combine two `local_homeomorph`s using `set.piecewise`. The source of the new `local_homeomorph`
is `s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The
function sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t`
using `e'`, and similarly for the inverse function. To ensure that the maps `to_fun` and `inv_fun`
are inverse of each other on the new `source` and `target`, the definition assumes that the sets `s`
and `t` are related both by `e.is_image` and `e'.is_image`. To ensure that the new maps are
continuous on `source`/`target`, it also assumes that `e.source` and `e'.source` meet `frontier s`
on the same set and `e x = e' x` on this intersection. -/
@[simps (config := { fullyApplied := false }) toLocalEquiv apply]
def piecewise (e e' : LocalHomeomorph α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)]
    (H : e.IsImage s t) (H' : e'.IsImage s t) (Hs : e.Source ∩ Frontier s = e'.Source ∩ Frontier s)
    (Heq : EqOn e e' (e.Source ∩ Frontier s)) : LocalHomeomorph α β where
  toLocalEquiv := e.toLocalEquiv.piecewise e'.toLocalEquiv s t H H'
  open_source := e.open_source.ite e'.open_source Hs
  open_target := e.open_target.ite e'.open_target <| H.Frontier.inter_eq_of_inter_eq_of_eq_on H'.Frontier Hs Heq
  continuous_to_fun := continuous_on_piecewise_ite e.ContinuousOn e'.ContinuousOn Hs Heq
  continuous_inv_fun :=
    continuous_on_piecewise_ite e.continuous_on_symm e'.continuous_on_symm
      (H.Frontier.inter_eq_of_inter_eq_of_eq_on H'.Frontier Hs Heq) (H.Frontier.symm_eq_on_of_inter_eq_of_eq_on Hs Heq)

@[simp]
theorem symm_piecewise (e e' : LocalHomeomorph α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t)
    (Hs : e.Source ∩ Frontier s = e'.Source ∩ Frontier s) (Heq : EqOn e e' (e.Source ∩ Frontier s)) :
    (e.piecewise e' s t H H' Hs Heq).symm =
      e.symm.piecewise e'.symm t s H.symm H'.symm (H.Frontier.inter_eq_of_inter_eq_of_eq_on H'.Frontier Hs Heq)
        (H.Frontier.symm_eq_on_of_inter_eq_of_eq_on Hs Heq) :=
  rfl

/-- Combine two `local_homeomorph`s with disjoint sources and disjoint targets. We reuse
`local_homeomorph.piecewise` then override `to_local_equiv` to `local_equiv.disjoint_union`.
This way we have better definitional equalities for `source` and `target`. -/
def disjointUnion (e e' : LocalHomeomorph α β) [∀ x, Decidable (x ∈ e.Source)] [∀ y, Decidable (y ∈ e.Target)]
    (Hs : Disjoint e.Source e'.Source) (Ht : Disjoint e.Target e'.Target) : LocalHomeomorph α β :=
  (e.piecewise e' e.Source e.Target e.is_image_source_target (e'.is_image_source_target_of_disjoint e Hs.symm Ht.symm)
        (by
          rw [e.open_source.inter_frontier_eq, (Hs.symm.frontier_right e'.open_source).inter_eq])
        (by
          rw [e.open_source.inter_frontier_eq]
          exact eq_on_empty _ _)).replaceEquiv
    (e.toLocalEquiv.disjointUnion e'.toLocalEquiv Hs Ht) (LocalEquiv.disjoint_union_eq_piecewise _ _ _ _).symm

end Piecewise

section Pi

variable {ι : Type _} [Fintype ι] {Xi Yi : ι → Type _} [∀ i, TopologicalSpace (Xi i)] [∀ i, TopologicalSpace (Yi i)]
  (ei : ∀ i, LocalHomeomorph (Xi i) (Yi i))

/-- The product of a finite family of `local_homeomorph`s. -/
@[simps toLocalEquiv]
def pi : LocalHomeomorph (∀ i, Xi i) (∀ i, Yi i) where
  toLocalEquiv := LocalEquiv.pi fun i => (ei i).toLocalEquiv
  open_source := (is_open_set_pi finite_univ) fun i hi => (ei i).open_source
  open_target := (is_open_set_pi finite_univ) fun i hi => (ei i).open_target
  continuous_to_fun :=
    continuous_on_pi.2 fun i => (ei i).ContinuousOn.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivialₓ
  continuous_inv_fun :=
    continuous_on_pi.2 fun i =>
      (ei i).continuous_on_symm.comp (continuous_apply _).ContinuousOn fun f hf => hf i trivialₓ

end Pi

section Continuity

/-- Continuity within a set at a point can be read under right composition with a local
homeomorphism, if the point is in its target -/
theorem continuous_within_at_iff_continuous_within_at_comp_right {f : β → γ} {s : Set β} {x : β} (h : x ∈ e.Target) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (f ∘ e) (e ⁻¹' s) (e.symm x) := by
  simp_rw [ContinuousWithinAt, ← @tendsto_map'_iff _ _ _ _ e, e.map_nhds_within_preimage_eq (e.map_target h), (· ∘ ·),
    e.right_inv h]

/-- Continuity at a point can be read under right composition with a local homeomorphism, if the
point is in its target -/
theorem continuous_at_iff_continuous_at_comp_right {f : β → γ} {x : β} (h : x ∈ e.Target) :
    ContinuousAt f x ↔ ContinuousAt (f ∘ e) (e.symm x) := by
  rw [← continuous_within_at_univ, e.continuous_within_at_iff_continuous_within_at_comp_right h, preimage_univ,
    continuous_within_at_univ]

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the right is continuous on the corresponding set. -/
theorem continuous_on_iff_continuous_on_comp_right {f : β → γ} {s : Set β} (h : s ⊆ e.Target) :
    ContinuousOn f s ↔ ContinuousOn (f ∘ e) (e.Source ∩ e ⁻¹' s) := by
  simp only [e.symm_image_eq_source_inter_preimage h, ← ContinuousOn, ← ball_image_iff]
  refine' forall₂_congrₓ fun x hx => _
  rw [e.continuous_within_at_iff_continuous_within_at_comp_right (h hx), e.symm_image_eq_source_inter_preimage h,
    inter_comm, continuous_within_at_inter]
  exact IsOpen.mem_nhds e.open_source (e.map_target (h hx))

/-- Continuity within a set at a point can be read under left composition with a local
homeomorphism if a neighborhood of the initial point is sent to the source of the local
homeomorphism-/
theorem continuous_within_at_iff_continuous_within_at_comp_left {f : γ → α} {s : Set γ} {x : γ} (hx : f x ∈ e.Source)
    (h : f ⁻¹' e.Source ∈ 𝓝[s] x) : ContinuousWithinAt f s x ↔ ContinuousWithinAt (e ∘ f) s x := by
  refine' ⟨(e.continuous_at hx).Tendsto.comp, fun fe_cont => _⟩
  rw [← continuous_within_at_inter' h] at fe_cont⊢
  have : ContinuousWithinAt (e.symm ∘ e ∘ f) (s ∩ f ⁻¹' e.source) x := by
    have : ContinuousWithinAt e.symm univ (e (f x)) := (e.continuous_at_symm (e.map_source hx)).ContinuousWithinAt
    exact ContinuousWithinAt.comp this fe_cont (subset_univ _)
  exact
    this.congr
      (fun y hy => by
        simp [← e.left_inv hy.2])
      (by
        simp [← e.left_inv hx])

/-- Continuity at a point can be read under left composition with a local homeomorphism if a
neighborhood of the initial point is sent to the source of the local homeomorphism-/
theorem continuous_at_iff_continuous_at_comp_left {f : γ → α} {x : γ} (h : f ⁻¹' e.Source ∈ 𝓝 x) :
    ContinuousAt f x ↔ ContinuousAt (e ∘ f) x := by
  have hx : f x ∈ e.source := (mem_of_mem_nhds h : _)
  have h' : f ⁻¹' e.source ∈ 𝓝[univ] x := by
    rwa [nhds_within_univ]
  rw [← continuous_within_at_univ, ← continuous_within_at_univ,
    e.continuous_within_at_iff_continuous_within_at_comp_left hx h']

/-- A function is continuous on a set if and only if its composition with a local homeomorphism
on the left is continuous on the corresponding set. -/
theorem continuous_on_iff_continuous_on_comp_left {f : γ → α} {s : Set γ} (h : s ⊆ f ⁻¹' e.Source) :
    ContinuousOn f s ↔ ContinuousOn (e ∘ f) s :=
  forall₂_congrₓ fun x hx =>
    e.continuous_within_at_iff_continuous_within_at_comp_left (h hx) (mem_of_superset self_mem_nhds_within h)

/-- A function is continuous if and only if its composition with a local homeomorphism
on the left is continuous and its image is contained in the source. -/
theorem continuous_iff_continuous_comp_left {f : γ → α} (h : f ⁻¹' e.Source = univ) :
    Continuous f ↔ Continuous (e ∘ f) := by
  simp only [← continuous_iff_continuous_on_univ]
  exact e.continuous_on_iff_continuous_on_comp_left (Eq.symm h).Subset

end Continuity

/-- A local homeomrphism defines a homeomorphism between its source and target. -/
def toHomeomorphSourceTarget : e.Source ≃ₜ e.Target where
  toFun := e.MapsTo.restrict _ _ _
  invFun := e.symm_maps_to.restrict _ _ _
  left_inv := fun x => Subtype.eq <| e.left_inv x.2
  right_inv := fun x => Subtype.eq <| e.right_inv x.2
  continuous_to_fun := continuous_subtype_mk _ <| continuous_on_iff_continuous_restrict.1 e.ContinuousOn
  continuous_inv_fun := continuous_subtype_mk _ <| continuous_on_iff_continuous_restrict.1 e.symm.ContinuousOn

theorem second_countable_topology_source [SecondCountableTopology β] (e : LocalHomeomorph α β) :
    SecondCountableTopology e.Source :=
  e.toHomeomorphSourceTarget.SecondCountableTopology

/-- If a local homeomorphism has source and target equal to univ, then it induces a homeomorphism
between the whole spaces, expressed in this definition. -/
@[simps (config := mfldCfg) apply symmApply]
def toHomeomorphOfSourceEqUnivTargetEqUniv (h : e.Source = (Univ : Set α)) (h' : e.Target = univ) : α ≃ₜ β where
  toFun := e
  invFun := e.symm
  left_inv := fun x =>
    e.left_inv <| by
      rw [h]
      exact mem_univ _
  right_inv := fun x =>
    e.right_inv <| by
      rw [h']
      exact mem_univ _
  continuous_to_fun := by
    rw [continuous_iff_continuous_on_univ]
    convert e.continuous_to_fun
    rw [h]
  continuous_inv_fun := by
    rw [continuous_iff_continuous_on_univ]
    convert e.continuous_inv_fun
    rw [h']

/-- A local homeomorphism whose source is all of `α` defines an open embedding of `α` into `β`.  The
converse is also true; see `open_embedding.to_local_homeomorph`. -/
theorem to_open_embedding (h : e.Source = Set.Univ) : OpenEmbedding e := by
  apply open_embedding_of_continuous_injective_open
  · apply continuous_iff_continuous_on_univ.mpr
    rw [← h]
    exact e.continuous_to_fun
    
  · apply set.injective_iff_inj_on_univ.mpr
    rw [← h]
    exact e.inj_on
    
  · intro U hU
    simpa only [← h, ← subset_univ] with mfld_simps using e.image_open_of_open hU
    

end LocalHomeomorph

namespace Homeomorph

variable (e : α ≃ₜ β) (e' : β ≃ₜ γ)

/- Register as simp lemmas that the fields of a local homeomorphism built from a homeomorphism
correspond to the fields of the original homeomorphism. -/
@[simp, mfld_simps]
theorem refl_to_local_homeomorph : (Homeomorph.refl α).toLocalHomeomorph = LocalHomeomorph.refl α :=
  rfl

@[simp, mfld_simps]
theorem symm_to_local_homeomorph : e.symm.toLocalHomeomorph = e.toLocalHomeomorph.symm :=
  rfl

@[simp, mfld_simps]
theorem trans_to_local_homeomorph : (e.trans e').toLocalHomeomorph = e.toLocalHomeomorph.trans e'.toLocalHomeomorph :=
  LocalHomeomorph.eq_of_local_equiv_eq <| Equivₓ.trans_to_local_equiv _ _

end Homeomorph

namespace OpenEmbedding

variable (f : α → β) (h : OpenEmbedding f)

/-- An open embedding of `α` into `β`, with `α` nonempty, defines a local homeomorphism whose source
is all of `α`.  The converse is also true; see `local_homeomorph.to_open_embedding`. -/
@[simps (config := mfldCfg) apply Source Target]
noncomputable def toLocalHomeomorph [Nonempty α] : LocalHomeomorph α β :=
  LocalHomeomorph.ofContinuousOpen ((h.toEmbedding.inj.InjOn Univ).toLocalEquiv _ _) h.Continuous.ContinuousOn
    h.IsOpenMap is_open_univ

theorem continuous_at_iff {f : α → β} {g : β → γ} (hf : OpenEmbedding f) {x : α} :
    ContinuousAt (g ∘ f) x ↔ ContinuousAt g (f x) := by
  have : Nonempty α := ⟨x⟩
  convert ((hf.to_local_homeomorph f).continuous_at_iff_continuous_at_comp_right _).symm
  · apply (LocalHomeomorph.left_inv _ _).symm
    simp
    
  · simp
    

end OpenEmbedding

namespace TopologicalSpace.Opens

open TopologicalSpace

variable (s : Opens α) [Nonempty s]

/-- The inclusion of an open subset `s` of a space `α` into `α` is a local homeomorphism from the
subtype `s` to `α`. -/
noncomputable def localHomeomorphSubtypeCoe : LocalHomeomorph s α :=
  OpenEmbedding.toLocalHomeomorph _ s.2.open_embedding_subtype_coe

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_coe : (s.localHomeomorphSubtypeCoe : s → α) = coe :=
  rfl

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_source : s.localHomeomorphSubtypeCoe.Source = Set.Univ :=
  rfl

@[simp, mfld_simps]
theorem local_homeomorph_subtype_coe_target : s.localHomeomorphSubtypeCoe.Target = s := by
  simp' only [← local_homeomorph_subtype_coe, ← Subtype.range_coe_subtype] with mfld_simps
  rfl

end TopologicalSpace.Opens

namespace LocalHomeomorph

open TopologicalSpace

variable (e : LocalHomeomorph α β)

variable (s : Opens α) [Nonempty s]

/-- The restriction of a local homeomorphism `e` to an open subset `s` of the domain type produces a
local homeomorphism whose domain is the subtype `s`.-/
noncomputable def subtypeRestr : LocalHomeomorph s β :=
  s.localHomeomorphSubtypeCoe.trans e

theorem subtype_restr_def : e.subtypeRestr s = s.localHomeomorphSubtypeCoe.trans e :=
  rfl

@[simp, mfld_simps]
theorem subtype_restr_coe : ((e.subtypeRestr s : LocalHomeomorph s β) : s → β) = Set.restrict ↑s (e : α → β) :=
  rfl

@[simp, mfld_simps]
theorem subtype_restr_source : (e.subtypeRestr s).Source = coe ⁻¹' e.Source := by
  simp' only [← subtype_restr_def] with mfld_simps

/- This lemma characterizes the transition functions of an open subset in terms of the transition
functions of the original space. -/
theorem subtype_restr_symm_trans_subtype_restr (f f' : LocalHomeomorph α β) :
    (f.subtypeRestr s).symm.trans (f'.subtypeRestr s) ≈ (f.symm.trans f').restr (f.Target ∩ f.symm ⁻¹' s) := by
  simp only [← subtype_restr_def, ← trans_symm_eq_symm_trans_symm]
  have openness₁ : IsOpen (f.target ∩ f.symm ⁻¹' s) := f.preimage_open_of_open_symm s.2
  rw [← of_set_trans _ openness₁, ← trans_assoc, ← trans_assoc]
  refine' eq_on_source.trans' _ (eq_on_source_refl _)
  -- f' has been eliminated !!!
  have sets_identity : f.symm.source ∩ (f.target ∩ f.symm ⁻¹' s) = f.symm.source ∩ f.symm ⁻¹' s := by
    mfld_set_tac
  have openness₂ : IsOpen (s : Set α) := s.2
  rw [of_set_trans', sets_identity, ← trans_of_set' _ openness₂, trans_assoc]
  refine' eq_on_source.trans' (eq_on_source_refl _) _
  -- f has been eliminated !!!
  refine' Setoidₓ.trans (trans_symm_self s.local_homeomorph_subtype_coe) _
  simp' only with mfld_simps

end LocalHomeomorph

