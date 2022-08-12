/-
Copyright (c) 2019 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton
-/
import Mathbin.Logic.Equiv.Fin
import Mathbin.Topology.DenseEmbedding
import Mathbin.Topology.Support

/-!
# Homeomorphisms

This file defines homeomorphisms between two topological spaces. They are bijections with both
directions continuous. We denote homeomorphisms with the notation `≃ₜ`.

# Main definitions

* `homeomorph α β`: The type of homeomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ₜ β`.

# Main results

* Pretty much every topological property is preserved under homeomorphisms.
* `homeomorph.homeomorph_of_continuous_open`: A continuous bijection that is
  an open map is a homeomorphism.

-/


open Set Filter

open TopologicalSpace

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

/-- Homeomorphism between `α` and `β`, also called topological isomorphism -/
-- not all spaces are homeomorphic to each other
@[nolint has_inhabited_instance]
structure Homeomorph (α : Type _) (β : Type _) [TopologicalSpace α] [TopologicalSpace β] extends α ≃ β where
  continuous_to_fun : Continuous to_fun := by
    run_tac
      tactic.interactive.continuity'
  continuous_inv_fun : Continuous inv_fun := by
    run_tac
      tactic.interactive.continuity'

-- mathport name: «expr ≃ₜ »
infixl:25 " ≃ₜ " => Homeomorph

namespace Homeomorph

variable [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ] [TopologicalSpace δ]

instance : CoeFun (α ≃ₜ β) fun _ => α → β :=
  ⟨fun e => e.toEquiv⟩

@[simp]
theorem homeomorph_mk_coe (a : Equivₓ α β) (b c) : (Homeomorph.mk a b c : α → β) = a :=
  rfl

/-- Inverse of a homeomorphism. -/
protected def symm (h : α ≃ₜ β) : β ≃ₜ α where
  continuous_to_fun := h.continuous_inv_fun
  continuous_inv_fun := h.continuous_to_fun
  toEquiv := h.toEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ₜ β) : α → β :=
  h

/-- See Note [custom simps projection] -/
def Simps.symmApply (h : α ≃ₜ β) : β → α :=
  h.symm

initialize_simps_projections Homeomorph (to_equiv_to_fun → apply, to_equiv_inv_fun → symmApply, -toEquiv)

@[simp]
theorem coe_to_equiv (h : α ≃ₜ β) : ⇑h.toEquiv = h :=
  rfl

@[simp]
theorem coe_symm_to_equiv (h : α ≃ₜ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl

theorem to_equiv_injective : Function.Injective (toEquiv : α ≃ₜ β → α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, rfl => rfl

@[ext]
theorem ext {h h' : α ≃ₜ β} (H : ∀ x, h x = h' x) : h = h' :=
  to_equiv_injective <| Equivₓ.ext H

/-- Identity map as a homeomorphism. -/
@[simps (config := { fullyApplied := false }) apply]
protected def refl (α : Type _) [TopologicalSpace α] : α ≃ₜ α where
  continuous_to_fun := continuous_id
  continuous_inv_fun := continuous_id
  toEquiv := Equivₓ.refl α

/-- Composition of two homeomorphisms. -/
protected def trans (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) : α ≃ₜ γ where
  continuous_to_fun := h₂.continuous_to_fun.comp h₁.continuous_to_fun
  continuous_inv_fun := h₁.continuous_inv_fun.comp h₂.continuous_inv_fun
  toEquiv := Equivₓ.trans h₁.toEquiv h₂.toEquiv

@[simp]
theorem trans_apply (h₁ : α ≃ₜ β) (h₂ : β ≃ₜ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl

@[simp]
theorem homeomorph_mk_coe_symm (a : Equivₓ α β) (b c) : ((Homeomorph.mk a b c).symm : β → α) = a.symm :=
  rfl

@[simp]
theorem refl_symm : (Homeomorph.refl α).symm = Homeomorph.refl α :=
  rfl

@[continuity]
protected theorem continuous (h : α ≃ₜ β) : Continuous h :=
  h.continuous_to_fun

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : α ≃ₜ β) : Continuous h.symm :=
  h.continuous_inv_fun

@[simp]
theorem apply_symm_apply (h : α ≃ₜ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (h : α ≃ₜ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

protected theorem bijective (h : α ≃ₜ β) : Function.Bijective h :=
  h.toEquiv.Bijective

protected theorem injective (h : α ≃ₜ β) : Function.Injective h :=
  h.toEquiv.Injective

protected theorem surjective (h : α ≃ₜ β) : Function.Surjective h :=
  h.toEquiv.Surjective

/-- Change the homeomorphism `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : α ≃ₜ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ₜ β :=
  have : g = f.symm :=
    funext fun x =>
      calc
        g x = f.symm (f (g x)) := (f.left_inv (g x)).symm
        _ = f.symm x := by
          rw [hg x]
        
  { toFun := f, invFun := g,
    left_inv := by
      convert f.left_inv,
    right_inv := by
      convert f.right_inv,
    continuous_to_fun := f.Continuous,
    continuous_inv_fun := by
      convert f.symm.continuous }

@[simp]
theorem symm_comp_self (h : α ≃ₜ β) : ⇑h.symm ∘ ⇑h = id :=
  funext h.symm_apply_apply

@[simp]
theorem self_comp_symm (h : α ≃ₜ β) : ⇑h ∘ ⇑h.symm = id :=
  funext h.apply_symm_apply

@[simp]
theorem range_coe (h : α ≃ₜ β) : Range h = univ :=
  h.Surjective.range_eq

theorem image_symm (h : α ≃ₜ β) : Image h.symm = Preimage h :=
  funext h.symm.toEquiv.image_eq_preimage

theorem preimage_symm (h : α ≃ₜ β) : Preimage h.symm = Image h :=
  (funext h.toEquiv.image_eq_preimage).symm

@[simp]
theorem image_preimage (h : α ≃ₜ β) (s : Set β) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s

@[simp]
theorem preimage_image (h : α ≃ₜ β) (s : Set α) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s

protected theorem inducing (h : α ≃ₜ β) : Inducing h :=
  inducing_of_inducing_compose h.Continuous h.symm.Continuous <| by
    simp only [← symm_comp_self, ← inducing_id]

theorem induced_eq (h : α ≃ₜ β) : TopologicalSpace.induced h ‹_› = ‹_› :=
  h.Inducing.1.symm

protected theorem quotient_map (h : α ≃ₜ β) : QuotientMap h :=
  QuotientMap.of_quotient_map_compose h.symm.Continuous h.Continuous <| by
    simp only [← self_comp_symm, ← QuotientMap.id]

theorem coinduced_eq (h : α ≃ₜ β) : TopologicalSpace.coinduced h ‹_› = ‹_› :=
  h.QuotientMap.2.symm

protected theorem embedding (h : α ≃ₜ β) : Embedding h :=
  ⟨h.Inducing, h.Injective⟩

/-- Homeomorphism given an embedding. -/
noncomputable def ofEmbedding (f : α → β) (hf : Embedding f) : α ≃ₜ Set.Range f :=
  { Equivₓ.ofInjective f hf.inj with continuous_to_fun := continuous_subtype_mk _ hf.Continuous,
    continuous_inv_fun := by
      simp [← hf.continuous_iff, ← continuous_subtype_coe] }

protected theorem second_countable_topology [TopologicalSpace.SecondCountableTopology β] (h : α ≃ₜ β) :
    TopologicalSpace.SecondCountableTopology α :=
  h.Inducing.SecondCountableTopology

theorem compact_image {s : Set α} (h : α ≃ₜ β) : IsCompact (h '' s) ↔ IsCompact s :=
  h.Embedding.is_compact_iff_is_compact_image.symm

theorem compact_preimage {s : Set β} (h : α ≃ₜ β) : IsCompact (h ⁻¹' s) ↔ IsCompact s := by
  rw [← image_symm] <;> exact h.symm.compact_image

@[simp]
theorem comap_cocompact (h : α ≃ₜ β) : comap h (cocompact β) = cocompact α :=
  (comap_cocompact_le h.Continuous).antisymm <|
    (has_basis_cocompact.le_basis_iff (has_basis_cocompact.comap h)).2 fun K hK =>
      ⟨h ⁻¹' K, h.compact_preimage.2 hK, Subset.rfl⟩

@[simp]
theorem map_cocompact (h : α ≃ₜ β) : map h (cocompact α) = cocompact β := by
  rw [← h.comap_cocompact, map_comap_of_surjective h.surjective]

protected theorem compact_space [CompactSpace α] (h : α ≃ₜ β) : CompactSpace β :=
  { compact_univ := by
      rw [← image_univ_of_surjective h.surjective, h.compact_image]
      apply CompactSpace.compact_univ }

protected theorem t0_space [T0Space α] (h : α ≃ₜ β) : T0Space β :=
  h.symm.Embedding.T0Space

protected theorem t1_space [T1Space α] (h : α ≃ₜ β) : T1Space β :=
  h.symm.Embedding.T1Space

protected theorem t2_space [T2Space α] (h : α ≃ₜ β) : T2Space β :=
  h.symm.Embedding.T2Space

protected theorem t3_space [T3Space α] (h : α ≃ₜ β) : T3Space β :=
  h.symm.Embedding.T3Space

protected theorem dense_embedding (h : α ≃ₜ β) : DenseEmbedding h :=
  { h.Embedding with dense := h.Surjective.DenseRange }

@[simp]
theorem is_open_preimage (h : α ≃ₜ β) {s : Set β} : IsOpen (h ⁻¹' s) ↔ IsOpen s :=
  h.QuotientMap.is_open_preimage

@[simp]
theorem is_open_image (h : α ≃ₜ β) {s : Set α} : IsOpen (h '' s) ↔ IsOpen s := by
  rw [← preimage_symm, is_open_preimage]

protected theorem is_open_map (h : α ≃ₜ β) : IsOpenMap h := fun s => h.is_open_image.2

@[simp]
theorem is_closed_preimage (h : α ≃ₜ β) {s : Set β} : IsClosed (h ⁻¹' s) ↔ IsClosed s := by
  simp only [is_open_compl_iff, preimage_compl, ← is_open_preimage]

@[simp]
theorem is_closed_image (h : α ≃ₜ β) {s : Set α} : IsClosed (h '' s) ↔ IsClosed s := by
  rw [← preimage_symm, is_closed_preimage]

protected theorem is_closed_map (h : α ≃ₜ β) : IsClosedMap h := fun s => h.is_closed_image.2

protected theorem open_embedding (h : α ≃ₜ β) : OpenEmbedding h :=
  open_embedding_of_embedding_open h.Embedding h.IsOpenMap

protected theorem closed_embedding (h : α ≃ₜ β) : ClosedEmbedding h :=
  closed_embedding_of_embedding_closed h.Embedding h.IsClosedMap

protected theorem normal_space [NormalSpace α] (h : α ≃ₜ β) : NormalSpace β :=
  h.symm.ClosedEmbedding.NormalSpace

theorem preimage_closure (h : α ≃ₜ β) (s : Set β) : h ⁻¹' Closure s = Closure (h ⁻¹' s) :=
  h.IsOpenMap.preimage_closure_eq_closure_preimage h.Continuous _

theorem image_closure (h : α ≃ₜ β) (s : Set α) : h '' Closure s = Closure (h '' s) := by
  rw [← preimage_symm, preimage_closure]

theorem preimage_interior (h : α ≃ₜ β) (s : Set β) : h ⁻¹' Interior s = Interior (h ⁻¹' s) :=
  h.IsOpenMap.preimage_interior_eq_interior_preimage h.Continuous _

theorem image_interior (h : α ≃ₜ β) (s : Set α) : h '' Interior s = Interior (h '' s) := by
  rw [← preimage_symm, preimage_interior]

theorem preimage_frontier (h : α ≃ₜ β) (s : Set β) : h ⁻¹' Frontier s = Frontier (h ⁻¹' s) :=
  h.IsOpenMap.preimage_frontier_eq_frontier_preimage h.Continuous _

@[to_additive]
theorem _root_.has_compact_mul_support.comp_homeomorph {M} [One M] {f : β → M} (hf : HasCompactMulSupport f)
    (φ : α ≃ₜ β) : HasCompactMulSupport (f ∘ φ) :=
  hf.comp_closed_embedding φ.ClosedEmbedding

@[simp]
theorem map_nhds_eq (h : α ≃ₜ β) (x : α) : map h (𝓝 x) = 𝓝 (h x) :=
  h.Embedding.map_nhds_of_mem _
    (by
      simp )

theorem symm_map_nhds_eq (h : α ≃ₜ β) (x : α) : map h.symm (𝓝 (h x)) = 𝓝 x := by
  rw [h.symm.map_nhds_eq, h.symm_apply_apply]

theorem nhds_eq_comap (h : α ≃ₜ β) (x : α) : 𝓝 x = comap h (𝓝 (h x)) :=
  h.Embedding.to_inducing.nhds_eq_comap x

@[simp]
theorem comap_nhds_eq (h : α ≃ₜ β) (y : β) : comap h (𝓝 y) = 𝓝 (h.symm y) := by
  rw [h.nhds_eq_comap, h.apply_symm_apply]

/-- If an bijective map `e : α ≃ β` is continuous and open, then it is a homeomorphism. -/
def homeomorphOfContinuousOpen (e : α ≃ β) (h₁ : Continuous e) (h₂ : IsOpenMap e) : α ≃ₜ β where
  continuous_to_fun := h₁
  continuous_inv_fun := by
    rw [continuous_def]
    intro s hs
    convert ← h₂ s hs using 1
    apply e.image_eq_preimage
  toEquiv := e

@[simp]
theorem comp_continuous_on_iff (h : α ≃ₜ β) (f : γ → α) (s : Set γ) : ContinuousOn (h ∘ f) s ↔ ContinuousOn f s :=
  h.Inducing.continuous_on_iff.symm

@[simp]
theorem comp_continuous_iff (h : α ≃ₜ β) {f : γ → α} : Continuous (h ∘ f) ↔ Continuous f :=
  h.Inducing.continuous_iff.symm

@[simp]
theorem comp_continuous_iff' (h : α ≃ₜ β) {f : β → γ} : Continuous (f ∘ h) ↔ Continuous f :=
  h.QuotientMap.continuous_iff.symm

theorem comp_continuous_at_iff (h : α ≃ₜ β) (f : γ → α) (x : γ) : ContinuousAt (h ∘ f) x ↔ ContinuousAt f x :=
  h.Inducing.continuous_at_iff.symm

theorem comp_continuous_at_iff' (h : α ≃ₜ β) (f : β → γ) (x : α) : ContinuousAt (f ∘ h) x ↔ ContinuousAt f (h x) :=
  h.Inducing.continuous_at_iff'
    (by
      simp )

theorem comp_continuous_within_at_iff (h : α ≃ₜ β) (f : γ → α) (s : Set γ) (x : γ) :
    ContinuousWithinAt f s x ↔ ContinuousWithinAt (h ∘ f) s x :=
  h.Inducing.continuous_within_at_iff

@[simp]
theorem comp_is_open_map_iff (h : α ≃ₜ β) {f : γ → α} : IsOpenMap (h ∘ f) ↔ IsOpenMap f := by
  refine' ⟨_, fun hf => h.is_open_map.comp hf⟩
  intro hf
  rw [← Function.comp.left_id f, ← h.symm_comp_self, Function.comp.assoc]
  exact h.symm.is_open_map.comp hf

@[simp]
theorem comp_is_open_map_iff' (h : α ≃ₜ β) {f : β → γ} : IsOpenMap (f ∘ h) ↔ IsOpenMap f := by
  refine' ⟨_, fun hf => hf.comp h.is_open_map⟩
  intro hf
  rw [← Function.comp.right_id f, ← h.self_comp_symm, ← Function.comp.assoc]
  exact hf.comp h.symm.is_open_map

/-- If two sets are equal, then they are homeomorphic. -/
def setCongr {s t : Set α} (h : s = t) : s ≃ₜ t where
  continuous_to_fun := continuous_subtype_mk _ continuous_subtype_val
  continuous_inv_fun := continuous_subtype_mk _ continuous_subtype_val
  toEquiv := Equivₓ.setCongr h

/-- Sum of two homeomorphisms. -/
def sumCongr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : Sum α γ ≃ₜ Sum β δ where
  continuous_to_fun := h₁.Continuous.sum_map h₂.Continuous
  continuous_inv_fun := h₁.symm.Continuous.sum_map h₂.symm.Continuous
  toEquiv := h₁.toEquiv.sumCongr h₂.toEquiv

/-- Product of two homeomorphisms. -/
def prodCongr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : α × γ ≃ₜ β × δ where
  continuous_to_fun := (h₁.Continuous.comp continuous_fst).prod_mk (h₂.Continuous.comp continuous_snd)
  continuous_inv_fun := (h₁.symm.Continuous.comp continuous_fst).prod_mk (h₂.symm.Continuous.comp continuous_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
theorem prod_congr_symm (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
theorem coe_prod_congr (h₁ : α ≃ₜ β) (h₂ : γ ≃ₜ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (α β γ)

/-- `α × β` is homeomorphic to `β × α`. -/
def prodComm : α × β ≃ₜ β × α where
  continuous_to_fun := continuous_snd.prod_mk continuous_fst
  continuous_inv_fun := continuous_snd.prod_mk continuous_fst
  toEquiv := Equivₓ.prodComm α β

@[simp]
theorem prod_comm_symm : (prodComm α β).symm = prodComm β α :=
  rfl

@[simp]
theorem coe_prod_comm : ⇑(prodComm α β) = Prod.swap :=
  rfl

/-- `(α × β) × γ` is homeomorphic to `α × (β × γ)`. -/
def prodAssoc : (α × β) × γ ≃ₜ α × β × γ where
  continuous_to_fun :=
    (continuous_fst.comp continuous_fst).prod_mk ((continuous_snd.comp continuous_fst).prod_mk continuous_snd)
  continuous_inv_fun :=
    (continuous_fst.prod_mk (continuous_fst.comp continuous_snd)).prod_mk (continuous_snd.comp continuous_snd)
  toEquiv := Equivₓ.prodAssoc α β γ

/-- `α × {*}` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false }) apply]
def prodPunit : α × PUnit ≃ₜ α where
  toEquiv := Equivₓ.prodPunit α
  continuous_to_fun := continuous_fst
  continuous_inv_fun := continuous_id.prod_mk continuous_const

/-- `{*} × α` is homeomorphic to `α`. -/
def punitProd : PUnit × α ≃ₜ α :=
  (prodComm _ _).trans (prodPunit _)

@[simp]
theorem coe_punit_prod : ⇑(punitProd α) = Prod.snd :=
  rfl

end

/-- `ulift α` is homeomorphic to `α`. -/
def ulift.{u, v} {α : Type u} [TopologicalSpace α] : ULift.{v, u} α ≃ₜ α where
  continuous_to_fun := continuous_ulift_down
  continuous_inv_fun := continuous_ulift_up
  toEquiv := Equivₓ.ulift

section Distribₓ

/-- `(α ⊕ β) × γ` is homeomorphic to `α × γ ⊕ β × γ`. -/
def sumProdDistrib : Sum α β × γ ≃ₜ Sum (α × γ) (β × γ) :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equivₓ.sumProdDistrib α β γ).symm
        ((continuous_inl.prod_map continuous_id).sum_elim (continuous_inr.prod_map continuous_id)) <|
      is_open_map_sum (open_embedding_inl.IsOpenMap.Prod IsOpenMap.id) (open_embedding_inr.IsOpenMap.Prod IsOpenMap.id)

/-- `α × (β ⊕ γ)` is homeomorphic to `α × β ⊕ α × γ`. -/
def prodSumDistrib : α × Sum β γ ≃ₜ Sum (α × β) (α × γ) :=
  (prodComm _ _).trans <| sumProdDistrib.trans <| sumCongr (prodComm _ _) (prodComm _ _)

variable {ι : Type _} {σ : ι → Type _} [∀ i, TopologicalSpace (σ i)]

/-- `(Σ i, σ i) × β` is homeomorphic to `Σ i, (σ i × β)`. -/
def sigmaProdDistrib : (Σi, σ i) × β ≃ₜ Σi, σ i × β :=
  Homeomorph.symm <|
    homeomorphOfContinuousOpen (Equivₓ.sigmaProdDistrib σ β).symm
      (continuous_sigma fun i => (continuous_sigma_mk.comp continuous_fst).prod_mk continuous_snd)
      (is_open_map_sigma fun i => (open_embedding_sigma_mk.Prod open_embedding_id).IsOpenMap)

end Distribₓ

/-- If `ι` has a unique element, then `ι → α` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (ι α : Type _) [Unique ι] [TopologicalSpace α] : (ι → α) ≃ₜ α where
  toEquiv := Equivₓ.funUnique ι α
  continuous_to_fun := continuous_apply _
  continuous_inv_fun := continuous_pi fun _ => continuous_id

/-- Homeomorphism between dependent functions `Π i : fin 2, α i` and `α 0 × α 1`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwo.{u} (α : Finₓ 2 → Type u) [∀ i, TopologicalSpace (α i)] : (∀ i, α i) ≃ₜ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  continuous_to_fun := (continuous_apply 0).prod_mk (continuous_apply 1)
  continuous_inv_fun := continuous_pi <| Finₓ.forall_fin_two.2 ⟨continuous_fst, continuous_snd⟩

/-- Homeomorphism between `α² = fin 2 → α` and `α × α`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrow : (Finₓ 2 → α) ≃ₜ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }

/-- A subset of a topological space is homeomorphic to its image under a homeomorphism.
-/
@[simps]
def image (e : α ≃ₜ β) (s : Set α) : s ≃ₜ e '' s where
  continuous_to_fun := by
    continuity!
  continuous_inv_fun := by
    continuity!
  toEquiv := e.toEquiv.Image s

/-- `set.univ α` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false })]
def Set.univ (α : Type _) [TopologicalSpace α] : (Univ : Set α) ≃ₜ α where
  toEquiv := Equivₓ.Set.univ α
  continuous_to_fun := continuous_subtype_coe
  continuous_inv_fun := continuous_subtype_mk _ continuous_id

end Homeomorph

/-- An inducing equiv between topological spaces is a homeomorphism. -/
@[simps]
def Equivₓ.toHomeomorphOfInducing [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ β) (hf : Inducing f) : α ≃ₜ β :=
  { f with continuous_to_fun := hf.Continuous,
    continuous_inv_fun :=
      hf.continuous_iff.2 <| by
        simpa using continuous_id }

namespace Continuous

variable [TopologicalSpace α] [TopologicalSpace β]

theorem continuous_symm_of_equiv_compact_to_t2 [CompactSpace α] [T2Space β] {f : α ≃ β} (hf : Continuous f) :
    Continuous f.symm := by
  rw [continuous_iff_is_closed]
  intro C hC
  have hC' : IsClosed (f '' C) := (hC.is_compact.image hf).IsClosed
  rwa [Equivₓ.image_eq_preimage] at hC'

/-- Continuous equivalences from a compact space to a T2 space are homeomorphisms.

This is not true when T2 is weakened to T1
(see `continuous.homeo_of_equiv_compact_to_t2.t1_counterexample`). -/
@[simps]
def homeoOfEquivCompactToT2 [CompactSpace α] [T2Space β] {f : α ≃ β} (hf : Continuous f) : α ≃ₜ β :=
  { f with continuous_to_fun := hf, continuous_inv_fun := hf.continuous_symm_of_equiv_compact_to_t2 }

end Continuous

