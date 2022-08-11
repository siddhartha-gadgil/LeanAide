/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Sébastien Gouëzel, Zhouhang Zhou, Reid Barton,
Anatole Dedecker
-/
import Mathbin.Topology.Homeomorph
import Mathbin.Topology.UniformSpace.UniformEmbedding
import Mathbin.Topology.UniformSpace.Pi

/-!
# Uniform isomorphisms

This file defines uniform isomorphisms between two uniform spaces. They are bijections with both
directions uniformly continuous. We denote uniform isomorphisms with the notation `≃ᵤ`.

# Main definitions

* `uniform_equiv α β`: The type of uniform isomorphisms from `α` to `β`.
  This type can be denoted using the following notation: `α ≃ᵤ β`.

-/


open Set Filter

variable {α : Type _} {β : Type _} {γ : Type _} {δ : Type _}

/-- Uniform isomorphism between `α` and `β` -/
-- not all spaces are homeomorphic to each other
@[nolint has_inhabited_instance]
structure UniformEquiv (α : Type _) (β : Type _) [UniformSpace α] [UniformSpace β] extends α ≃ β where
  uniform_continuous_to_fun : UniformContinuous to_fun
  uniform_continuous_inv_fun : UniformContinuous inv_fun

-- mathport name: «expr ≃ᵤ »
infixl:25 " ≃ᵤ " => UniformEquiv

namespace UniformEquiv

variable [UniformSpace α] [UniformSpace β] [UniformSpace γ] [UniformSpace δ]

instance : CoeFun (α ≃ᵤ β) fun _ => α → β :=
  ⟨fun e => e.toEquiv⟩

@[simp]
theorem uniform_equiv_mk_coe (a : Equivₓ α β) (b c) : (UniformEquiv.mk a b c : α → β) = a :=
  rfl

/-- Inverse of a uniform isomorphism. -/
protected def symm (h : α ≃ᵤ β) : β ≃ᵤ α where
  uniform_continuous_to_fun := h.uniform_continuous_inv_fun
  uniform_continuous_inv_fun := h.uniform_continuous_to_fun
  toEquiv := h.toEquiv.symm

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because it is a composition of multiple projections. -/
def Simps.apply (h : α ≃ᵤ β) : α → β :=
  h

/-- See Note [custom simps projection] -/
def Simps.symmApply (h : α ≃ᵤ β) : β → α :=
  h.symm

initialize_simps_projections UniformEquiv (to_equiv_to_fun → apply, to_equiv_inv_fun → symmApply, -toEquiv)

@[simp]
theorem coe_to_equiv (h : α ≃ᵤ β) : ⇑h.toEquiv = h :=
  rfl

@[simp]
theorem coe_symm_to_equiv (h : α ≃ᵤ β) : ⇑h.toEquiv.symm = h.symm :=
  rfl

theorem to_equiv_injective : Function.Injective (toEquiv : α ≃ᵤ β → α ≃ β)
  | ⟨e, h₁, h₂⟩, ⟨e', h₁', h₂'⟩, rfl => rfl

@[ext]
theorem ext {h h' : α ≃ᵤ β} (H : ∀ x, h x = h' x) : h = h' :=
  to_equiv_injective <| Equivₓ.ext H

/-- Identity map as a uniform isomorphism. -/
@[simps (config := { fullyApplied := false }) apply]
protected def refl (α : Type _) [UniformSpace α] : α ≃ᵤ α where
  uniform_continuous_to_fun := uniform_continuous_id
  uniform_continuous_inv_fun := uniform_continuous_id
  toEquiv := Equivₓ.refl α

/-- Composition of two uniform isomorphisms. -/
protected def trans (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) : α ≃ᵤ γ where
  uniform_continuous_to_fun := h₂.uniform_continuous_to_fun.comp h₁.uniform_continuous_to_fun
  uniform_continuous_inv_fun := h₁.uniform_continuous_inv_fun.comp h₂.uniform_continuous_inv_fun
  toEquiv := Equivₓ.trans h₁.toEquiv h₂.toEquiv

@[simp]
theorem trans_apply (h₁ : α ≃ᵤ β) (h₂ : β ≃ᵤ γ) (a : α) : h₁.trans h₂ a = h₂ (h₁ a) :=
  rfl

@[simp]
theorem uniform_equiv_mk_coe_symm (a : Equivₓ α β) (b c) : ((UniformEquiv.mk a b c).symm : β → α) = a.symm :=
  rfl

@[simp]
theorem refl_symm : (UniformEquiv.refl α).symm = UniformEquiv.refl α :=
  rfl

protected theorem uniform_continuous (h : α ≃ᵤ β) : UniformContinuous h :=
  h.uniform_continuous_to_fun

@[continuity]
protected theorem continuous (h : α ≃ᵤ β) : Continuous h :=
  h.UniformContinuous.Continuous

protected theorem uniform_continuous_symm (h : α ≃ᵤ β) : UniformContinuous h.symm :=
  h.uniform_continuous_inv_fun

-- otherwise `by continuity` can't prove continuity of `h.to_equiv.symm`
@[continuity]
protected theorem continuous_symm (h : α ≃ᵤ β) : Continuous h.symm :=
  h.uniform_continuous_symm.Continuous

/-- A uniform isomorphism as a homeomorphism. -/
@[simps]
protected def toHomeomorph (e : α ≃ᵤ β) : α ≃ₜ β :=
  { e.toEquiv with continuous_to_fun := e.Continuous, continuous_inv_fun := e.continuous_symm }

@[simp]
theorem apply_symm_apply (h : α ≃ᵤ β) (x : β) : h (h.symm x) = x :=
  h.toEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (h : α ≃ᵤ β) (x : α) : h.symm (h x) = x :=
  h.toEquiv.symm_apply_apply x

protected theorem bijective (h : α ≃ᵤ β) : Function.Bijective h :=
  h.toEquiv.Bijective

protected theorem injective (h : α ≃ᵤ β) : Function.Injective h :=
  h.toEquiv.Injective

protected theorem surjective (h : α ≃ᵤ β) : Function.Surjective h :=
  h.toEquiv.Surjective

/-- Change the uniform equiv `f` to make the inverse function definitionally equal to `g`. -/
def changeInv (f : α ≃ᵤ β) (g : β → α) (hg : Function.RightInverse g f) : α ≃ᵤ β :=
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
    uniform_continuous_to_fun := f.UniformContinuous,
    uniform_continuous_inv_fun := by
      convert f.symm.uniform_continuous }

@[simp]
theorem symm_comp_self (h : α ≃ᵤ β) : ⇑h.symm ∘ ⇑h = id :=
  funext h.symm_apply_apply

@[simp]
theorem self_comp_symm (h : α ≃ᵤ β) : ⇑h ∘ ⇑h.symm = id :=
  funext h.apply_symm_apply

@[simp]
theorem range_coe (h : α ≃ᵤ β) : Range h = univ :=
  h.Surjective.range_eq

theorem image_symm (h : α ≃ᵤ β) : Image h.symm = Preimage h :=
  funext h.symm.toEquiv.image_eq_preimage

theorem preimage_symm (h : α ≃ᵤ β) : Preimage h.symm = Image h :=
  (funext h.toEquiv.image_eq_preimage).symm

@[simp]
theorem image_preimage (h : α ≃ᵤ β) (s : Set β) : h '' (h ⁻¹' s) = s :=
  h.toEquiv.image_preimage s

@[simp]
theorem preimage_image (h : α ≃ᵤ β) (s : Set α) : h ⁻¹' (h '' s) = s :=
  h.toEquiv.preimage_image s

protected theorem uniform_inducing (h : α ≃ᵤ β) : UniformInducing h :=
  uniform_inducing_of_compose h.UniformContinuous h.symm.UniformContinuous <| by
    simp only [← symm_comp_self, ← uniform_inducing_id]

theorem comap_eq (h : α ≃ᵤ β) : UniformSpace.comap h ‹_› = ‹_› := by
  ext : 1 <;> exact h.uniform_inducing.comap_uniformity

protected theorem uniform_embedding (h : α ≃ᵤ β) : UniformEmbedding h :=
  ⟨h.UniformInducing, h.Injective⟩

/-- Uniform equiv given a uniform embedding. -/
noncomputable def ofUniformEmbedding (f : α → β) (hf : UniformEmbedding f) : α ≃ᵤ Set.Range f where
  uniform_continuous_to_fun := uniform_continuous_subtype_mk hf.to_uniform_inducing.UniformContinuous _
  uniform_continuous_inv_fun := by
    simp [← hf.to_uniform_inducing.uniform_continuous_iff, ← uniform_continuous_subtype_coe]
  toEquiv := Equivₓ.ofInjective f hf.inj

/-- If two sets are equal, then they are uniformly equivalent. -/
def setCongr {s t : Set α} (h : s = t) : s ≃ᵤ t where
  uniform_continuous_to_fun := uniform_continuous_subtype_mk uniform_continuous_subtype_val _
  uniform_continuous_inv_fun := uniform_continuous_subtype_mk uniform_continuous_subtype_val _
  toEquiv := Equivₓ.setCongr h

/-- Product of two uniform isomorphisms. -/
def prodCongr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : α × γ ≃ᵤ β × δ where
  uniform_continuous_to_fun :=
    (h₁.UniformContinuous.comp uniform_continuous_fst).prod_mk (h₂.UniformContinuous.comp uniform_continuous_snd)
  uniform_continuous_inv_fun :=
    (h₁.symm.UniformContinuous.comp uniform_continuous_fst).prod_mk
      (h₂.symm.UniformContinuous.comp uniform_continuous_snd)
  toEquiv := h₁.toEquiv.prodCongr h₂.toEquiv

@[simp]
theorem prod_congr_symm (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : (h₁.prodCongr h₂).symm = h₁.symm.prodCongr h₂.symm :=
  rfl

@[simp]
theorem coe_prod_congr (h₁ : α ≃ᵤ β) (h₂ : γ ≃ᵤ δ) : ⇑(h₁.prodCongr h₂) = Prod.map h₁ h₂ :=
  rfl

section

variable (α β γ)

/-- `α × β` is uniformly isomorphic to `β × α`. -/
def prodComm : α × β ≃ᵤ β × α where
  uniform_continuous_to_fun := uniform_continuous_snd.prod_mk uniform_continuous_fst
  uniform_continuous_inv_fun := uniform_continuous_snd.prod_mk uniform_continuous_fst
  toEquiv := Equivₓ.prodComm α β

@[simp]
theorem prod_comm_symm : (prodComm α β).symm = prodComm β α :=
  rfl

@[simp]
theorem coe_prod_comm : ⇑(prodComm α β) = Prod.swap :=
  rfl

/-- `(α × β) × γ` is uniformly isomorphic to `α × (β × γ)`. -/
def prodAssoc : (α × β) × γ ≃ᵤ α × β × γ where
  uniform_continuous_to_fun :=
    (uniform_continuous_fst.comp uniform_continuous_fst).prod_mk
      ((uniform_continuous_snd.comp uniform_continuous_fst).prod_mk uniform_continuous_snd)
  uniform_continuous_inv_fun :=
    (uniform_continuous_fst.prod_mk (uniform_continuous_fst.comp uniform_continuous_snd)).prod_mk
      (uniform_continuous_snd.comp uniform_continuous_snd)
  toEquiv := Equivₓ.prodAssoc α β γ

/-- `α × {*}` is uniformly isomorphic to `α`. -/
@[simps (config := { fullyApplied := false }) apply]
def prodPunit : α × PUnit ≃ᵤ α where
  toEquiv := Equivₓ.prodPunit α
  uniform_continuous_to_fun := uniform_continuous_fst
  uniform_continuous_inv_fun := uniform_continuous_id.prod_mk uniform_continuous_const

/-- `{*} × α` is uniformly isomorphic to `α`. -/
def punitProd : PUnit × α ≃ᵤ α :=
  (prodComm _ _).trans (prodPunit _)

@[simp]
theorem coe_punit_prod : ⇑(punitProd α) = Prod.snd :=
  rfl

end

/-- If `ι` has a unique element, then `ι → α` is homeomorphic to `α`. -/
@[simps (config := { fullyApplied := false })]
def funUnique (ι α : Type _) [Unique ι] [UniformSpace α] : (ι → α) ≃ᵤ α where
  toEquiv := Equivₓ.funUnique ι α
  uniform_continuous_to_fun := Pi.uniform_continuous_proj _ _
  uniform_continuous_inv_fun := uniform_continuous_pi.mpr fun _ => uniform_continuous_id

/-- Uniform isomorphism between dependent functions `Π i : fin 2, α i` and `α 0 × α 1`. -/
@[simps (config := { fullyApplied := false })]
def piFinTwo.{u} (α : Finₓ 2 → Type u) [∀ i, UniformSpace (α i)] : (∀ i, α i) ≃ᵤ α 0 × α 1 where
  toEquiv := piFinTwoEquiv α
  uniform_continuous_to_fun := (Pi.uniform_continuous_proj _ 0).prod_mk (Pi.uniform_continuous_proj _ 1)
  uniform_continuous_inv_fun :=
    uniform_continuous_pi.mpr <| Finₓ.forall_fin_two.2 ⟨uniform_continuous_fst, uniform_continuous_snd⟩

/-- Uniform isomorphism between `α² = fin 2 → α` and `α × α`. -/
@[simps (config := { fullyApplied := false })]
def finTwoArrow : (Finₓ 2 → α) ≃ᵤ α × α :=
  { piFinTwo fun _ => α with toEquiv := finTwoArrowEquiv α }

/-- A subset of a uniform space is uniformly isomorphic to its image under a uniform isomorphism.
-/
def image (e : α ≃ᵤ β) (s : Set α) : s ≃ᵤ e '' s where
  uniform_continuous_to_fun :=
    uniform_continuous_subtype_mk (e.UniformContinuous.comp uniform_continuous_subtype_val) fun x =>
      mem_image_of_mem _ x.2
  uniform_continuous_inv_fun :=
    uniform_continuous_subtype_mk (e.symm.UniformContinuous.comp uniform_continuous_subtype_val) fun x => by
      simpa using mem_image_of_mem e.symm x.2
  toEquiv := e.toEquiv.Image s

end UniformEquiv

/-- A uniform inducing equiv between uniform spaces is a uniform isomorphism. -/
@[simps]
def Equivₓ.toUniformEquivOfUniformInducing [UniformSpace α] [UniformSpace β] (f : α ≃ β) (hf : UniformInducing f) :
    α ≃ᵤ β :=
  { f with uniform_continuous_to_fun := hf.UniformContinuous,
    uniform_continuous_inv_fun :=
      hf.uniform_continuous_iff.2 <| by
        simpa using uniform_continuous_id }

