/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathbin.Data.Set.Function
import Mathbin.Logic.Equiv.Basic

/-!
# Local equivalences

This files defines equivalences between subsets of given types.
An element `e` of `local_equiv α β` is made of two maps `e.to_fun` and `e.inv_fun` respectively
from α to β and from  β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two local equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.to_fun x` and `e.inv_fun y`.

## Main definitions

`equiv.to_local_equiv`: associating a local equiv to an equiv, with source = target = univ
`local_equiv.symm`    : the inverse of a local equiv
`local_equiv.trans`   : the composition of two local equivs
`local_equiv.refl`    : the identity local equiv
`local_equiv.of_set`  : the identity on a set `s`
`eq_on_source`        : equivalence relation describing the "right" notion of equality for local
                        equivs (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of local equivalences:
* equivs on subtypes
* pairs of functions taking values in `option α` and `option β`, equal to none where the local
equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
restriction of domains. Checking that one always belongs to the right subtype makes things very
tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
the domain is restricted automatically). These are implemented in `pequiv.lean`. For manifolds,
where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
overhead as one would need to extend all classes of smoothness to option-valued maps.
* The local_equiv version as explained above is easier to use for manifolds. The drawback is that
there is extra useless data (the values of `to_fun` and `inv_fun` outside of `source` and `target`).
In particular, the equality notion between local equivs is not "the right one", i.e., coinciding
source and target and equality there. Moreover, there are no local equivs in this sense between
an empty type and a nonempty type. Since empty types are not that useful, and since one almost never
needs to talk about equal local equivs, this is not an issue in practice.
Still, we introduce an equivalence relation `eq_on_source` that captures this right notion of
equality, and show that many properties are invariant under this equivalence relation.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `local_equiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.

-/


mk_simp_attribute mfld_simps :=
  "The simpset `mfld_simps` records several simp lemmas that are\nespecially useful in manifolds. It is a subset of the whole set of simp lemmas, but it makes it\npossible to have quicker proofs (when used with `squeeze_simp` or `simp only`) while retaining\nreadability.\n\nThe typical use case is the following, in a file on manifolds:\nIf `simp [foo, bar]` is slow, replace it with `squeeze_simp [foo, bar] with mfld_simps` and paste\nits output. The list of lemmas should be reasonable (contrary to the output of\n`squeeze_simp [foo, bar]` which might contain tens of lemmas), and the outcome should be quick\nenough.\n"

-- register in the simpset `mfld_simps` several lemmas that are often useful when dealing
-- with manifolds
attribute [mfld_simps]
  id.def Function.comp.left_id Set.mem_set_of_eq Set.image_eq_empty Set.univ_inter Set.preimage_univ Set.prod_mk_mem_set_prod_eq and_trueₓ Set.mem_univ Set.mem_image_of_mem true_andₓ Set.mem_inter_eq Set.mem_preimage Function.comp_app Set.inter_subset_left Set.mem_prod Set.range_id Set.range_prod_map and_selfₓ Set.mem_range_self eq_self_iff_true forall_const forall_true_iff Set.inter_univ Set.preimage_id Function.comp.right_id not_false_iff and_imp Set.prod_inter_prod Set.univ_prod_univ true_orₓ or_trueₓ Prod.map_mkₓ Set.preimage_inter heq_iff_eq Equivₓ.sigma_equiv_prod_apply Equivₓ.sigma_equiv_prod_symm_apply Subtype.coe_mk Equivₓ.to_fun_as_coe Equivₓ.inv_fun_as_coe

/-- Common `@[simps]` configuration options used for manifold-related declarations. -/
def mfldCfg : SimpsCfg where
  attrs := [`simp, `mfld_simps]
  fullyApplied := false

namespace Tactic.Interactive

-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
-- ./././Mathport/Syntax/Translate/Basic.lean:1087:4: warning: unsupported (TODO): `[tacs]
/-- A very basic tactic to show that sets showing up in manifolds coincide or are included in
one another. -/
unsafe def mfld_set_tac : tactic Unit := do
  let goal ← tactic.target
  match goal with
    | quote.1 ((%%ₓe₁) = %%ₓe₂) => sorry
    | quote.1 ((%%ₓe₁) ⊆ %%ₓe₂) => sorry
    | _ => tactic.fail "goal should be an equality or an inclusion"

end Tactic.Interactive

open Function Set

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

/-- Local equivalence between subsets `source` and `target` of α and β respectively. The (global)
maps `to_fun : α → β` and `inv_fun : β → α` map `source` to `target` and conversely, and are inverse
to each other there. The values of `to_fun` outside of `source` and of `inv_fun` outside of `target`
are irrelevant. -/
structure LocalEquiv (α : Type _) (β : Type _) where
  toFun : α → β
  invFun : β → α
  Source : Set α
  Target : Set β
  map_source' : ∀ {x}, x ∈ source → to_fun x ∈ target
  map_target' : ∀ {x}, x ∈ target → inv_fun x ∈ source
  left_inv' : ∀ {x}, x ∈ source → inv_fun (to_fun x) = x
  right_inv' : ∀ {x}, x ∈ target → to_fun (inv_fun x) = x

namespace LocalEquiv

variable (e : LocalEquiv α β) (e' : LocalEquiv β γ)

instance [Inhabited α] [Inhabited β] : Inhabited (LocalEquiv α β) :=
  ⟨⟨const α default, const β default, ∅, ∅, maps_to_empty _ _, maps_to_empty _ _, eq_on_empty _ _, eq_on_empty _ _⟩⟩

/-- The inverse of a local equiv -/
protected def symm : LocalEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  Source := e.Target
  Target := e.Source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'

instance : CoeFun (LocalEquiv α β) fun _ => α → β :=
  ⟨LocalEquiv.toFun⟩

/-- See Note [custom simps projection] -/
def Simps.symmApply (e : LocalEquiv α β) : β → α :=
  e.symm

initialize_simps_projections LocalEquiv (toFun → apply, invFun → symmApply)

@[simp, mfld_simps]
theorem coe_mk (f : α → β) (g s t ml mr il ir) : (LocalEquiv.mk f g s t ml mr il ir : α → β) = f :=
  rfl

@[simp, mfld_simps]
theorem coe_symm_mk (f : α → β) (g s t ml mr il ir) : ((LocalEquiv.mk f g s t ml mr il ir).symm : β → α) = g :=
  rfl

@[simp, mfld_simps]
theorem to_fun_as_coe : e.toFun = e :=
  rfl

@[simp, mfld_simps]
theorem inv_fun_as_coe : e.invFun = e.symm :=
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
  ⟨fun h => by
    rw [← e.right_inv hy, h], fun h => by
    rw [← e.left_inv hx, h]⟩

protected theorem maps_to : MapsTo e e.Source e.Target := fun x => e.map_source

theorem symm_maps_to : MapsTo e.symm e.Target e.Source :=
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

/-- Associating a local_equiv to an equiv-/
@[simps (config := mfldCfg)]
def _root_.equiv.to_local_equiv (e : α ≃ β) : LocalEquiv α β where
  toFun := e
  invFun := e.symm
  Source := Univ
  Target := Univ
  map_source' := fun x hx => mem_univ _
  map_target' := fun y hy => mem_univ _
  left_inv' := fun x hx => e.left_inv x
  right_inv' := fun x hx => e.right_inv x

instance inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (LocalEquiv α β) :=
  ⟨((Equivₓ.equivEmpty α).trans (Equivₓ.equivEmpty β).symm).toLocalEquiv⟩

/-- Create a copy of a `local_equiv` providing better definitional equalities. -/
@[simps (config := { fullyApplied := false })]
def copy (e : LocalEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α) (hs : e.Source = s)
    (t : Set β) (ht : e.Target = t) : LocalEquiv α β where
  toFun := f
  invFun := g
  Source := s
  Target := t
  map_source' := fun x => ht ▸ hs ▸ hf ▸ e.map_source
  map_target' := fun y => hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' := fun x => hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' := fun x => ht ▸ hf ▸ hg ▸ e.right_inv

theorem copy_eq_self (e : LocalEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α)
    (hs : e.Source = s) (t : Set β) (ht : e.Target = t) : e.copy f hf g hg s hs t ht = e := by
  substs f g s t
  cases e
  rfl

/-- Associating to a local_equiv an equiv between the source and the target -/
protected def toEquiv : Equivₓ e.Source e.Target where
  toFun := fun x => ⟨e x, e.map_source x.Mem⟩
  invFun := fun y => ⟨e.symm y, e.map_target y.Mem⟩
  left_inv := fun ⟨x, hx⟩ => Subtype.eq <| e.left_inv hx
  right_inv := fun ⟨y, hy⟩ => Subtype.eq <| e.right_inv hy

@[simp, mfld_simps]
theorem symm_source : e.symm.Source = e.Target :=
  rfl

@[simp, mfld_simps]
theorem symm_target : e.symm.Target = e.Source :=
  rfl

@[simp, mfld_simps]
theorem symm_symm : e.symm.symm = e := by
  cases e
  rfl

theorem image_source_eq_target : e '' e.Source = e.Target :=
  e.BijOn.image_eq

theorem forall_mem_target {p : β → Prop} : (∀, ∀ y ∈ e.Target, ∀, p y) ↔ ∀, ∀ x ∈ e.Source, ∀, p (e x) := by
  rw [← image_source_eq_target, ball_image_iff]

theorem exists_mem_target {p : β → Prop} : (∃ y ∈ e.Target, p y) ↔ ∃ x ∈ e.Source, p (e x) := by
  rw [← image_source_eq_target, bex_image_iff]

/-- We say that `t : set β` is an image of `s : set α` under a local equivalence if
any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.Source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α} {y : β}

theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.Source) : e x ∈ t ↔ x ∈ s :=
  h hx

theorem symm_apply_mem_iff (h : e.IsImage s t) : ∀ ⦃y⦄, y ∈ e.Target → (e.symm y ∈ s ↔ y ∈ t) :=
  e.forall_mem_target.mpr fun x hx => by
    rw [e.left_inv hx, h hx]

protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.symm_apply_mem_iff

@[simp]
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩

protected theorem maps_to (h : e.IsImage s t) : MapsTo e (e.Source ∩ s) (e.Target ∩ t) := fun x hx =>
  ⟨e.MapsTo hx.1, (h hx.1).2 hx.2⟩

theorem symm_maps_to (h : e.IsImage s t) : MapsTo e.symm (e.Target ∩ t) (e.Source ∩ s) :=
  h.symm.MapsTo

/-- Restrict a `local_equiv` to a pair of corresponding sets. -/
@[simps (config := { fullyApplied := false })]
def restr (h : e.IsImage s t) : LocalEquiv α β where
  toFun := e
  invFun := e.symm
  Source := e.Source ∩ s
  Target := e.Target ∩ t
  map_source' := h.MapsTo
  map_target' := h.symm_maps_to
  left_inv' := e.LeftInvOn.mono (inter_subset_left _ _)
  right_inv' := e.RightInvOn.mono (inter_subset_left _ _)

theorem image_eq (h : e.IsImage s t) : e '' (e.Source ∩ s) = e.Target ∩ t :=
  h.restr.image_source_eq_target

theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.Target ∩ t) = e.Source ∩ s :=
  h.symm.image_eq

theorem iff_preimage_eq : e.IsImage s t ↔ e.Source ∩ e ⁻¹' t = e.Source ∩ s := by
  simp only [← is_image, ← Set.ext_iff, ← mem_inter_eq, ← And.congr_right_iff, ← mem_preimage]

alias iff_preimage_eq ↔ preimage_eq of_preimage_eq

theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.Target ∩ e.symm ⁻¹' s = e.Target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias iff_symm_preimage_eq ↔ symm_preimage_eq of_symm_preimage_eq

theorem of_image_eq (h : e '' (e.Source ∩ s) = e.Target ∩ t) : e.IsImage s t :=
  of_symm_preimage_eq <| Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h

theorem of_symm_image_eq (h : e.symm '' (e.Target ∩ t) = e.Source ∩ s) : e.IsImage s t :=
  of_preimage_eq <| Eq.trans (of_preimage_eq rfl).symm_image_eq.symm h

protected theorem compl (h : e.IsImage s t) : e.IsImage (sᶜ) (tᶜ) := fun x hx => not_congr (h hx)

protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') : e.IsImage (s ∩ s') (t ∩ t') := fun x hx =>
  and_congr (h hx) (h' hx)

protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') : e.IsImage (s ∪ s') (t ∪ t') := fun x hx =>
  or_congr (h hx) (h' hx)

protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') : e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl

theorem left_inv_on_piecewise {e' : LocalEquiv α β} [∀ i, Decidable (i ∈ s)] [∀ i, Decidable (i ∈ t)]
    (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.Source e'.Source) := by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
    
  · rw [piecewise_eq_of_not_mem _ _ _ hs, piecewise_eq_of_not_mem _ _ _ ((h'.compl he).2 hs), e'.left_inv he]
    

theorem inter_eq_of_inter_eq_of_eq_on {e' : LocalEquiv α β} (h : e.IsImage s t) (h' : e'.IsImage s t)
    (hs : e.Source ∩ s = e'.Source ∩ s) (Heq : EqOn e e' (e.Source ∩ s)) : e.Target ∩ t = e'.Target ∩ t := by
  rw [← h.image_eq, ← h'.image_eq, ← hs, Heq.image_eq]

theorem symm_eq_on_of_inter_eq_of_eq_on {e' : LocalEquiv α β} (h : e.IsImage s t) (hs : e.Source ∩ s = e'.Source ∩ s)
    (Heq : EqOn e e' (e.Source ∩ s)) : EqOn e.symm e'.symm (e.Target ∩ t) := by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx
  rw [hs] at hx'
  rw [e.left_inv hx.1, Heq hx, e'.left_inv hx'.1]

end IsImage

theorem is_image_source_target : e.IsImage e.Source e.Target := fun x hx => by
  simp [← hx]

theorem is_image_source_target_of_disjoint (e' : LocalEquiv α β) (hs : Disjoint e.Source e'.Source)
    (ht : Disjoint e.Target e'.Target) : e.IsImage e'.Source e'.Target := fun x hx => by
  have : x ∉ e'.Source := fun hx' => hs ⟨hx, hx'⟩
  have : e x ∉ e'.Target := fun hx' => ht ⟨e.MapsTo hx, hx'⟩
  simp only [*]

theorem image_source_inter_eq' (s : Set α) : e '' (e.Source ∩ s) = e.Target ∩ e.symm ⁻¹' s := by
  rw [inter_comm, e.left_inv_on.image_inter', image_source_eq_target, inter_comm]

theorem image_source_inter_eq (s : Set α) : e '' (e.Source ∩ s) = e.Target ∩ e.symm ⁻¹' (e.Source ∩ s) := by
  rw [inter_comm, e.left_inv_on.image_inter, image_source_eq_target, inter_comm]

theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.Source) : e '' s = e.Target ∩ e.symm ⁻¹' s := by
  rw [← e.image_source_inter_eq', inter_eq_self_of_subset_right h]

theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.Target) : e.symm '' s = e.Source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h

theorem symm_image_target_inter_eq (s : Set β) : e.symm '' (e.Target ∩ s) = e.Source ∩ e ⁻¹' (e.Target ∩ s) :=
  e.symm.image_source_inter_eq _

theorem symm_image_target_inter_eq' (s : Set β) : e.symm '' (e.Target ∩ s) = e.Source ∩ e ⁻¹' s :=
  e.symm.image_source_inter_eq' _

theorem source_inter_preimage_inv_preimage (s : Set α) : e.Source ∩ e ⁻¹' (e.symm ⁻¹' s) = e.Source ∩ s :=
  Set.ext fun x =>
    And.congr_right_iff.2 fun hx => by
      simp only [← mem_preimage, ← e.left_inv hx]

theorem source_inter_preimage_target_inter (s : Set β) : e.Source ∩ e ⁻¹' (e.Target ∩ s) = e.Source ∩ e ⁻¹' s :=
  ext fun x => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩

theorem target_inter_inv_preimage_preimage (s : Set β) : e.Target ∩ e.symm ⁻¹' (e ⁻¹' s) = e.Target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _

theorem source_subset_preimage_target : e.Source ⊆ e ⁻¹' e.Target :=
  e.MapsTo

theorem symm_image_target_eq_source : e.symm '' e.Target = e.Source :=
  e.symm.image_source_eq_target

theorem target_subset_preimage_source : e.Target ⊆ e.symm ⁻¹' e.Source :=
  e.symm_maps_to

/-- Two local equivs that have the same `source`, same `to_fun` and same `inv_fun`, coincide. -/
@[ext]
protected theorem ext {e e' : LocalEquiv α β} (h : ∀ x, e x = e' x) (hsymm : ∀ x, e.symm x = e'.symm x)
    (hs : e.Source = e'.Source) : e = e' := by
  have A : (e : α → β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β → α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  rw [A, hs, I'] at I
  cases e <;> cases e'
  simp_all

/-- Restricting a local equivalence to e.source ∩ s -/
protected def restr (s : Set α) : LocalEquiv α β :=
  (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr

@[simp, mfld_simps]
theorem restr_coe (s : Set α) : (e.restr s : α → β) = e :=
  rfl

@[simp, mfld_simps]
theorem restr_coe_symm (s : Set α) : ((e.restr s).symm : β → α) = e.symm :=
  rfl

@[simp, mfld_simps]
theorem restr_source (s : Set α) : (e.restr s).Source = e.Source ∩ s :=
  rfl

@[simp, mfld_simps]
theorem restr_target (s : Set α) : (e.restr s).Target = e.Target ∩ e.symm ⁻¹' s :=
  rfl

theorem restr_eq_of_source_subset {e : LocalEquiv α β} {s : Set α} (h : e.Source ⊆ s) : e.restr s = e :=
  LocalEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by
      simp [← inter_eq_self_of_subset_left h])

@[simp, mfld_simps]
theorem restr_univ {e : LocalEquiv α β} : e.restr Univ = e :=
  restr_eq_of_source_subset (subset_univ _)

/-- The identity local equiv -/
protected def refl (α : Type _) : LocalEquiv α α :=
  (Equivₓ.refl α).toLocalEquiv

@[simp, mfld_simps]
theorem refl_source : (LocalEquiv.refl α).Source = univ :=
  rfl

@[simp, mfld_simps]
theorem refl_target : (LocalEquiv.refl α).Target = univ :=
  rfl

@[simp, mfld_simps]
theorem refl_coe : (LocalEquiv.refl α : α → α) = id :=
  rfl

@[simp, mfld_simps]
theorem refl_symm : (LocalEquiv.refl α).symm = LocalEquiv.refl α :=
  rfl

@[simp, mfld_simps]
theorem refl_restr_source (s : Set α) : ((LocalEquiv.refl α).restr s).Source = s := by
  simp

@[simp, mfld_simps]
theorem refl_restr_target (s : Set α) : ((LocalEquiv.refl α).restr s).Target = s := by
  change univ ∩ id ⁻¹' s = s
  simp

/-- The identity local equiv on a set `s` -/
def ofSet (s : Set α) : LocalEquiv α α where
  toFun := id
  invFun := id
  Source := s
  Target := s
  map_source' := fun x hx => hx
  map_target' := fun x hx => hx
  left_inv' := fun x hx => rfl
  right_inv' := fun x hx => rfl

@[simp, mfld_simps]
theorem of_set_source (s : Set α) : (LocalEquiv.ofSet s).Source = s :=
  rfl

@[simp, mfld_simps]
theorem of_set_target (s : Set α) : (LocalEquiv.ofSet s).Target = s :=
  rfl

@[simp, mfld_simps]
theorem of_set_coe (s : Set α) : (LocalEquiv.ofSet s : α → α) = id :=
  rfl

@[simp, mfld_simps]
theorem of_set_symm (s : Set α) : (LocalEquiv.ofSet s).symm = LocalEquiv.ofSet s :=
  rfl

/-- Composing two local equivs if the target of the first coincides with the source of the
second. -/
protected def trans' (e' : LocalEquiv β γ) (h : e.Target = e'.Source) : LocalEquiv α γ where
  toFun := e' ∘ e
  invFun := e.symm ∘ e'.symm
  Source := e.Source
  Target := e'.Target
  map_source' := fun x hx => by
    simp [← h.symm, ← hx]
  map_target' := fun y hy => by
    simp [← h, ← hy]
  left_inv' := fun x hx => by
    simp [← hx, ← h.symm]
  right_inv' := fun y hy => by
    simp [← hy, ← h]

/-- Composing two local equivs, by restricting to the maximal domain where their composition
is well defined. -/
protected def trans : LocalEquiv α γ :=
  LocalEquiv.trans' (e.symm.restr e'.Source).symm (e'.restr e.Target) (inter_comm _ _)

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

@[simp, mfld_simps]
theorem trans_source : (e.trans e').Source = e.Source ∩ e ⁻¹' e'.Source :=
  rfl

theorem trans_source' : (e.trans e').Source = e.Source ∩ e ⁻¹' (e.Target ∩ e'.Source) := by
  mfld_set_tac

theorem trans_source'' : (e.trans e').Source = e.symm '' (e.Target ∩ e'.Source) := by
  rw [e.trans_source', e.symm_image_target_inter_eq]

theorem image_trans_source : e '' (e.trans e').Source = e.Target ∩ e'.Source :=
  (e.symm.restr e'.Source).symm.image_source_eq_target

@[simp, mfld_simps]
theorem trans_target : (e.trans e').Target = e'.Target ∩ e'.symm ⁻¹' e.Target :=
  rfl

theorem trans_target' : (e.trans e').Target = e'.Target ∩ e'.symm ⁻¹' (e'.Source ∩ e.Target) :=
  trans_source' e'.symm e.symm

theorem trans_target'' : (e.trans e').Target = e' '' (e'.Source ∩ e.Target) :=
  trans_source'' e'.symm e.symm

theorem inv_image_trans_target : e'.symm '' (e.trans e').Target = e'.Source ∩ e.Target :=
  image_trans_source e'.symm e.symm

theorem trans_assoc (e'' : LocalEquiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by
      simp [← trans_source, ← @preimage_comp α β γ, ← inter_assoc])

@[simp, mfld_simps]
theorem trans_refl : e.trans (LocalEquiv.refl β) = e :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by
      simp [← trans_source])

@[simp, mfld_simps]
theorem refl_trans : (LocalEquiv.refl α).trans e = e :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by
      simp [← trans_source, ← preimage_id])

theorem trans_refl_restr (s : Set β) : e.trans ((LocalEquiv.refl β).restr s) = e.restr (e ⁻¹' s) :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by
      simp [← trans_source])

theorem trans_refl_restr' (s : Set β) : e.trans ((LocalEquiv.refl β).restr s) = e.restr (e.Source ∩ e ⁻¹' s) :=
  (LocalEquiv.ext (fun x => rfl) fun x => rfl) <| by
    simp [← trans_source]
    rw [← inter_assoc, inter_self]

theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  (LocalEquiv.ext (fun x => rfl) fun x => rfl) <| by
    simp [← trans_source, ← inter_comm]
    rwa [inter_assoc]

/-- A lemma commonly useful when `e` and `e'` are charts of a manifold. -/
theorem mem_symm_trans_source {e' : LocalEquiv α γ} {x : α} (he : x ∈ e.Source) (he' : x ∈ e'.Source) :
    e x ∈ (e.symm.trans e').Source :=
  ⟨e.MapsTo he, by
    rwa [mem_preimage, LocalEquiv.symm_symm, e.left_inv he]⟩

/-- Postcompose a local equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps]
def transEquiv (e' : β ≃ γ) : LocalEquiv α γ :=
  (e.trans e'.toLocalEquiv).copy _ rfl _ rfl e.Source (inter_univ _) (e'.symm ⁻¹' e.Target) (univ_inter _)

theorem trans_equiv_eq_trans (e' : β ≃ γ) : e.transEquiv e' = e.trans e'.toLocalEquiv :=
  copy_eq_self _ _ _ _ _ _ _ _ _

/-- Precompose a local equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps]
def _root_.equiv.trans_local_equiv (e : α ≃ β) : LocalEquiv α γ :=
  (e.toLocalEquiv.trans e').copy _ rfl _ rfl (e ⁻¹' e'.Source) (univ_inter _) e'.Target (inter_univ _)

theorem _root_.equiv.trans_local_equiv_eq_trans (e : α ≃ β) : e.transLocalEquiv e' = e.toLocalEquiv.trans e' :=
  copy_eq_self _ _ _ _ _ _ _ _ _

/-- `eq_on_source e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same local equiv. -/
def EqOnSource (e e' : LocalEquiv α β) : Prop :=
  e.Source = e'.Source ∧ e.Source.EqOn e e'

/-- `eq_on_source` is an equivalence relation -/
instance eqOnSourceSetoid : Setoidₓ (LocalEquiv α β) where
  R := EqOnSource
  iseqv :=
    ⟨fun e => by
      simp [← eq_on_source], fun e e' h => by
      simp [← eq_on_source, ← h.1.symm]
      exact fun x hx => (h.2 hx).symm, fun e e' e'' h h' =>
      ⟨by
        rwa [← h'.1, ← h.1], fun x hx => by
        rw [← h'.2, h.2 hx]
        rwa [← h.1]⟩⟩

theorem eq_on_source_refl : e ≈ e :=
  Setoidₓ.refl _

/-- Two equivalent local equivs have the same source -/
theorem EqOnSource.source_eq {e e' : LocalEquiv α β} (h : e ≈ e') : e.Source = e'.Source :=
  h.1

/-- Two equivalent local equivs coincide on the source -/
theorem EqOnSource.eq_on {e e' : LocalEquiv α β} (h : e ≈ e') : e.Source.EqOn e e' :=
  h.2

/-- Two equivalent local equivs have the same target -/
theorem EqOnSource.target_eq {e e' : LocalEquiv α β} (h : e ≈ e') : e.Target = e'.Target := by
  simp only [image_source_eq_target, h.source_eq, ← h.2.image_eq]

/-- If two local equivs are equivalent, so are their inverses. -/
theorem EqOnSource.symm' {e e' : LocalEquiv α β} (h : e ≈ e') : e.symm ≈ e'.symm := by
  refine' ⟨h.target_eq, eq_on_of_left_inv_on_of_right_inv_on e.left_inv_on _ _⟩ <;>
    simp only [← symm_source, ← h.target_eq, ← h.source_eq, ← e'.symm_maps_to]
  exact e'.right_inv_on.congr_right e'.symm_maps_to (h.source_eq ▸ h.eq_on.symm)

/-- Two equivalent local equivs have coinciding inverses on the target -/
theorem EqOnSource.symm_eq_on {e e' : LocalEquiv α β} (h : e ≈ e') : EqOn e.symm e'.symm e.Target :=
  h.symm'.EqOn

/-- Composition of local equivs respects equivalence -/
theorem EqOnSource.trans' {e e' : LocalEquiv α β} {f f' : LocalEquiv β γ} (he : e ≈ e') (hf : f ≈ f') :
    e.trans f ≈ e'.trans f' := by
  constructor
  · rw [trans_source'', trans_source'', ← he.target_eq, ← hf.1]
    exact (he.symm'.eq_on.mono <| inter_subset_left _ _).image_eq
    
  · intro x hx
    rw [trans_source] at hx
    simp [← (he.2 hx.1).symm, ← hf.2 hx.2]
    

/-- Restriction of local equivs respects equivalence -/
theorem EqOnSource.restr {e e' : LocalEquiv α β} (he : e ≈ e') (s : Set α) : e.restr s ≈ e'.restr s := by
  constructor
  · simp [← he.1]
    
  · intro x hx
    simp only [← mem_inter_eq, ← restr_source] at hx
    exact he.2 hx.1
    

/-- Preimages are respected by equivalence -/
theorem EqOnSource.source_inter_preimage_eq {e e' : LocalEquiv α β} (he : e ≈ e') (s : Set β) :
    e.Source ∩ e ⁻¹' s = e'.Source ∩ e' ⁻¹' s := by
  rw [he.eq_on.inter_preimage_eq, he.source_eq]

/-- Composition of a local equiv and its inverse is equivalent to the restriction of the identity
to the source -/
theorem trans_self_symm : e.trans e.symm ≈ LocalEquiv.ofSet e.Source := by
  have A : (e.trans e.symm).Source = e.source := by
    mfld_set_tac
  refine'
    ⟨by
      simp [← A], fun x hx => _⟩
  rw [A] at hx
  simp' only [← hx] with mfld_simps

/-- Composition of the inverse of a local equiv and this local equiv is equivalent to the
restriction of the identity to the target -/
theorem trans_symm_self : e.symm.trans e ≈ LocalEquiv.ofSet e.Target :=
  trans_self_symm e.symm

/-- Two equivalent local equivs are equal when the source and target are univ -/
theorem eq_of_eq_on_source_univ (e e' : LocalEquiv α β) (h : e ≈ e') (s : e.Source = univ) (t : e.Target = univ) :
    e = e' := by
  apply LocalEquiv.ext (fun x => _) (fun x => _) h.1
  · apply h.2
    rw [s]
    exact mem_univ _
    
  · apply h.symm'.2
    rw [symm_source, t]
    exact mem_univ _
    

section Prod

/-- The product of two local equivs, as a local equiv on the product. -/
def prod (e : LocalEquiv α β) (e' : LocalEquiv γ δ) : LocalEquiv (α × γ) (β × δ) where
  Source := e.Source ×ˢ e'.Source
  Target := e.Target ×ˢ e'.Target
  toFun := fun p => (e p.1, e' p.2)
  invFun := fun p => (e.symm p.1, e'.symm p.2)
  map_source' := fun p hp => by
    simp at hp
    simp [← hp]
  map_target' := fun p hp => by
    simp at hp
    simp [← map_target, ← hp]
  left_inv' := fun p hp => by
    simp at hp
    simp [← hp]
  right_inv' := fun p hp => by
    simp at hp
    simp [← hp]

@[simp, mfld_simps]
theorem prod_source (e : LocalEquiv α β) (e' : LocalEquiv γ δ) : (e.Prod e').Source = e.Source ×ˢ e'.Source :=
  rfl

@[simp, mfld_simps]
theorem prod_target (e : LocalEquiv α β) (e' : LocalEquiv γ δ) : (e.Prod e').Target = e.Target ×ˢ e'.Target :=
  rfl

@[simp, mfld_simps]
theorem prod_coe (e : LocalEquiv α β) (e' : LocalEquiv γ δ) : (e.Prod e' : α × γ → β × δ) = fun p => (e p.1, e' p.2) :=
  rfl

theorem prod_coe_symm (e : LocalEquiv α β) (e' : LocalEquiv γ δ) :
    ((e.Prod e').symm : β × δ → α × γ) = fun p => (e.symm p.1, e'.symm p.2) :=
  rfl

@[simp, mfld_simps]
theorem prod_symm (e : LocalEquiv α β) (e' : LocalEquiv γ δ) : (e.Prod e').symm = e.symm.Prod e'.symm := by
  ext x <;> simp [← prod_coe_symm]

@[simp, mfld_simps]
theorem prod_trans {η : Type _} {ε : Type _} (e : LocalEquiv α β) (f : LocalEquiv β γ) (e' : LocalEquiv δ η)
    (f' : LocalEquiv η ε) : (e.Prod e').trans (f.Prod f') = (e.trans f).Prod (e'.trans f') := by
  ext x <;> simp [← ext_iff] <;> tauto

end Prod

/-- Combine two `local_equiv`s using `set.piecewise`. The source of the new `local_equiv` is
`s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The function
sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t` using `e'`,
and similarly for the inverse function. The definition assumes `e.is_image s t` and
`e'.is_image s t`. -/
@[simps (config := { fullyApplied := false })]
def piecewise (e e' : LocalEquiv α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)]
    (H : e.IsImage s t) (H' : e'.IsImage s t) : LocalEquiv α β where
  toFun := s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  Source := s.ite e.Source e'.Source
  Target := t.ite e.Target e'.Target
  map_source' := H.MapsTo.piecewise_ite H'.compl.MapsTo
  map_target' := H.symm.MapsTo.piecewise_ite H'.symm.compl.MapsTo
  left_inv' := H.left_inv_on_piecewise H'
  right_inv' := H.symm.left_inv_on_piecewise H'.symm

theorem symm_piecewise (e e' : LocalEquiv α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)] [∀ y, Decidable (y ∈ t)]
    (H : e.IsImage s t) (H' : e'.IsImage s t) :
    (e.piecewise e' s t H H').symm = e.symm.piecewise e'.symm t s H.symm H'.symm :=
  rfl

/-- Combine two `local_equiv`s with disjoint sources and disjoint targets. We reuse
`local_equiv.piecewise`, then override `source` and `target` to ensure better definitional
equalities. -/
@[simps (config := { fullyApplied := false })]
def disjointUnion (e e' : LocalEquiv α β) (hs : Disjoint e.Source e'.Source) (ht : Disjoint e.Target e'.Target)
    [∀ x, Decidable (x ∈ e.Source)] [∀ y, Decidable (y ∈ e.Target)] : LocalEquiv α β :=
  (e.piecewise e' e.Source e.Target e.is_image_source_target <|
        e'.is_image_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.Source ∪ e'.Source) (ite_left _ _) (e.Target ∪ e'.Target) (ite_left _ _)

theorem disjoint_union_eq_piecewise (e e' : LocalEquiv α β) (hs : Disjoint e.Source e'.Source)
    (ht : Disjoint e.Target e'.Target) [∀ x, Decidable (x ∈ e.Source)] [∀ y, Decidable (y ∈ e.Target)] :
    e.disjointUnion e' hs ht =
      e.piecewise e' e.Source e.Target e.is_image_source_target
        (e'.is_image_source_target_of_disjoint _ hs.symm ht.symm) :=
  copy_eq_self _ _ _ _ _ _ _ _ _

section Pi

variable {ι : Type _} {αi βi : ι → Type _} (ei : ∀ i, LocalEquiv (αi i) (βi i))

/-- The product of a family of local equivs, as a local equiv on the pi type. -/
@[simps (config := mfldCfg)]
protected def pi : LocalEquiv (∀ i, αi i) (∀ i, βi i) where
  toFun := fun f i => ei i (f i)
  invFun := fun f i => (ei i).symm (f i)
  Source := Pi Univ fun i => (ei i).Source
  Target := Pi Univ fun i => (ei i).Target
  map_source' := fun f hf i hi => (ei i).map_source (hf i hi)
  map_target' := fun f hf i hi => (ei i).map_target (hf i hi)
  left_inv' := fun f hf => funext fun i => (ei i).left_inv (hf i trivialₓ)
  right_inv' := fun f hf => funext fun i => (ei i).right_inv (hf i trivialₓ)

end Pi

end LocalEquiv

namespace Set

/-- A bijection between two sets `s : set α` and `t : set β` provides a local equivalence
between `α` and `β`. -/
-- All arguments are explicit to avoid missing information in the pretty printer output
@[simps (config := { fullyApplied := false })]
noncomputable def BijOn.toLocalEquiv [Nonempty α] (f : α → β) (s : Set α) (t : Set β) (hf : BijOn f s t) :
    LocalEquiv α β where
  toFun := f
  invFun := invFunOn f s
  Source := s
  Target := t
  map_source' := hf.MapsTo
  map_target' := hf.SurjOn.maps_to_inv_fun_on
  left_inv' := hf.inv_on_inv_fun_on.1
  right_inv' := hf.inv_on_inv_fun_on.2

/-- A map injective on a subset of its domain provides a local equivalence. -/
@[simp, mfld_simps]
noncomputable def InjOn.toLocalEquiv [Nonempty α] (f : α → β) (s : Set α) (hf : InjOn f s) : LocalEquiv α β :=
  hf.bij_on_image.toLocalEquiv f s (f '' s)

end Set

namespace Equivₓ

/- equivs give rise to local_equiv. We set up simp lemmas to reduce most properties of the local
equiv to that of the equiv. -/
variable (e : α ≃ β) (e' : β ≃ γ)

@[simp, mfld_simps]
theorem refl_to_local_equiv : (Equivₓ.refl α).toLocalEquiv = LocalEquiv.refl α :=
  rfl

@[simp, mfld_simps]
theorem symm_to_local_equiv : e.symm.toLocalEquiv = e.toLocalEquiv.symm :=
  rfl

@[simp, mfld_simps]
theorem trans_to_local_equiv : (e.trans e').toLocalEquiv = e.toLocalEquiv.trans e'.toLocalEquiv :=
  LocalEquiv.ext (fun x => rfl) (fun x => rfl)
    (by
      simp [← LocalEquiv.trans_source, ← Equivₓ.toLocalEquiv])

end Equivₓ

