/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathbin.Data.FunLike.Embedding
import Mathbin.Data.Prod.Pprod
import Mathbin.Data.Set.Basic
import Mathbin.Data.Sigma.Basic
import Mathbin.Logic.Equiv.Basic

/-!
# Injective functions
-/


universe u v w x

namespace Function

/-- `α ↪ β` is a bundled injective function. -/
-- depending on cardinalities, an injective function may not exist
@[nolint has_inhabited_instance]
structure Embedding (α : Sort _) (β : Sort _) where
  toFun : α → β
  inj' : Injective to_fun

-- mathport name: «expr ↪ »
infixr:25 " ↪ " => Embedding

instance {α : Sort u} {β : Sort v} : CoeFun (α ↪ β) fun _ => α → β :=
  ⟨Embedding.toFun⟩

initialize_simps_projections Embedding (toFun → apply)

instance {α : Sort u} {β : Sort v} : EmbeddingLike (α ↪ β) α β where
  coe := Embedding.toFun
  injective' := Embedding.inj'
  coe_injective' := fun f g h => by
    cases f
    cases g
    congr

instance {α β : Sort _} : CanLift (α → β) (α ↪ β) where
  coe := coeFn
  cond := Injective
  prf := fun f hf => ⟨⟨f, hf⟩, rfl⟩

end Function

section Equivₓ

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

/-- Convert an `α ≃ β` to `α ↪ β`.

This is also available as a coercion `equiv.coe_embedding`.
The explicit `equiv.to_embedding` version is preferred though, since the coercion can have issues
inferring the type of the resulting embedding. For example:

```lean
-- Works:
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f.to_embedding = s.map f := by simp
-- Error, `f` has type `fin 3 ≃ fin 3` but is expected to have type `fin 3 ↪ ?m_1 : Type ?`
example (s : finset (fin 3)) (f : equiv.perm (fin 3)) : s.map f = s.map f.to_embedding := by simp
```
-/
@[simps]
protected def Equivₓ.toEmbedding : α ↪ β :=
  ⟨f, f.Injective⟩

instance Equivₓ.coeEmbedding : Coe (α ≃ β) (α ↪ β) :=
  ⟨Equivₓ.toEmbedding⟩

@[reducible]
instance Equivₓ.Perm.coeEmbedding : Coe (Equivₓ.Perm α) (α ↪ α) :=
  Equivₓ.coeEmbedding

@[simp]
theorem Equivₓ.coe_eq_to_embedding : ↑f = f.toEmbedding :=
  rfl

/-- Given an equivalence to a subtype, produce an embedding to the elements of the corresponding
set. -/
@[simps]
def Equivₓ.asEmbedding {p : β → Prop} (e : α ≃ Subtype p) : α ↪ β :=
  ⟨coe ∘ e, Subtype.coe_injective.comp e.Injective⟩

@[simp]
theorem Equivₓ.as_embedding_range {α β : Sort _} {p : β → Prop} (e : α ≃ Subtype p) :
    Set.Range e.asEmbedding = SetOf p :=
  Set.ext fun x =>
    ⟨fun ⟨y, h⟩ => h ▸ Subtype.coe_prop (e y), fun hs =>
      ⟨e.symm ⟨x, hs⟩, by
        simp ⟩⟩

end Equivₓ

namespace Function

namespace Embedding

theorem coe_injective {α β} : @Function.Injective (α ↪ β) (α → β) coeFn :=
  FunLike.coe_injective

@[ext]
theorem ext {α β} {f g : Embedding α β} (h : ∀ x, f x = g x) : f = g :=
  FunLike.ext f g h

theorem ext_iff {α β} {f g : Embedding α β} : (∀ x, f x = g x) ↔ f = g :=
  FunLike.ext_iff.symm

@[simp]
theorem to_fun_eq_coe {α β} (f : α ↪ β) : toFun f = f :=
  rfl

@[simp]
theorem coe_fn_mk {α β} (f : α → β) (i) : (@mk _ _ f i : α → β) = f :=
  rfl

@[simp]
theorem mk_coe {α β : Type _} (f : α ↪ β) (inj) : (⟨f, inj⟩ : α ↪ β) = f := by
  ext
  simp

protected theorem injective {α β} (f : α ↪ β) : Injective f :=
  EmbeddingLike.injective f

theorem apply_eq_iff_eq {α β} (f : α ↪ β) (x y : α) : f x = f y ↔ x = y :=
  EmbeddingLike.apply_eq_iff_eq f

/-- The identity map as a `function.embedding`. -/
@[refl, simps (config := { simpRhs := true })]
protected def refl (α : Sort _) : α ↪ α :=
  ⟨id, injective_id⟩

/-- Composition of `f : α ↪ β` and `g : β ↪ γ`. -/
@[trans, simps (config := { simpRhs := true })]
protected def trans {α β γ} (f : α ↪ β) (g : β ↪ γ) : α ↪ γ :=
  ⟨g ∘ f, g.Injective.comp f.Injective⟩

@[simp]
theorem equiv_to_embedding_trans_symm_to_embedding {α β : Sort _} (e : α ≃ β) :
    e.toEmbedding.trans e.symm.toEmbedding = Embedding.refl _ := by
  ext
  simp

@[simp]
theorem equiv_symm_to_embedding_trans_to_embedding {α β : Sort _} (e : α ≃ β) :
    e.symm.toEmbedding.trans e.toEmbedding = Embedding.refl _ := by
  ext
  simp

/-- Transfer an embedding along a pair of equivalences. -/
@[simps (config := { fullyApplied := false })]
protected def congr {α : Sort u} {β : Sort v} {γ : Sort w} {δ : Sort x} (e₁ : α ≃ β) (e₂ : γ ≃ δ) (f : α ↪ γ) : β ↪ δ :=
  (Equivₓ.toEmbedding e₁.symm).trans (f.trans e₂.toEmbedding)

/-- A right inverse `surj_inv` of a surjective function as an `embedding`. -/
protected noncomputable def ofSurjective {α β} (f : β → α) (hf : Surjective f) : α ↪ β :=
  ⟨surjInv hf, injective_surj_inv _⟩

/-- Convert a surjective `embedding` to an `equiv` -/
protected noncomputable def equivOfSurjective {α β} (f : α ↪ β) (hf : Surjective f) : α ≃ β :=
  Equivₓ.ofBijective f ⟨f.Injective, hf⟩

/-- There is always an embedding from an empty type. --/
protected def ofIsEmpty {α β} [IsEmpty α] : α ↪ β :=
  ⟨isEmptyElim, isEmptyElim⟩

/-- Change the value of an embedding `f` at one point. If the prescribed image
is already occupied by some `f a'`, then swap the values at these two points. -/
def setValue {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)] [∀ a', Decidable (f a' = b)] : α ↪ β :=
  ⟨fun a' => if a' = a then b else if f a' = b then f a else f a', by
    intro x y h
    dsimp'  at h
    split_ifs  at h <;>
      try
          subst b <;>
        try
            simp only [← f.injective.eq_iff] at * <;>
          cc⟩

theorem set_value_eq {α β} (f : α ↪ β) (a : α) (b : β) [∀ a', Decidable (a' = a)] [∀ a', Decidable (f a' = b)] :
    setValue f a b a = b := by
  simp [← set_value]

/-- Embedding into `option α` using `some`. -/
@[simps (config := { fullyApplied := false })]
protected def some {α} : α ↪ Option α :=
  ⟨some, Option.some_injective α⟩

/-- Embedding into `option α` using `coe`. Usually the correct synctatical form for `simp`. -/
@[simps (config := { fullyApplied := false })]
def coeOption {α} : α ↪ Option α :=
  ⟨coe, Option.some_injective α⟩

/-- Embedding into `with_top α`. -/
@[simps]
def coeWithTop {α} : α ↪ WithTop α :=
  { Embedding.some with toFun := coe }

/-- Given an embedding `f : α ↪ β` and a point outside of `set.range f`, construct an embedding
`option α ↪ β`. -/
@[simps]
def optionElim {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.Range f) : Option α ↪ β :=
  ⟨Option.elimₓ x f, Option.injective_iff.2 ⟨f.2, h⟩⟩

/-- Equivalence between embeddings of `option α` and a sigma type over the embeddings of `α`. -/
@[simps]
def optionEmbeddingEquiv (α β) : (Option α ↪ β) ≃ Σf : α ↪ β, ↥(Set.Range fᶜ) where
  toFun := fun f => ⟨coeOption.trans f, f none, fun ⟨x, hx⟩ => Option.some_ne_none x <| f.Injective hx⟩
  invFun := fun f => f.1.optionElim f.2 f.2.2
  left_inv := fun f =>
    ext <| by
      rintro (_ | _) <;> simp [← Option.coe_def]
  right_inv := fun ⟨f, y, hy⟩ => by
    ext <;> simp [← Option.coe_def]

/-- A version of `option.map` for `function.embedding`s. -/
@[simps (config := { fullyApplied := false })]
def optionMap {α β} (f : α ↪ β) : Option α ↪ Option β :=
  ⟨Option.map f, Option.map_injective f.Injective⟩

/-- Embedding of a `subtype`. -/
def subtype {α} (p : α → Prop) : Subtype p ↪ α :=
  ⟨coe, fun _ _ => Subtype.ext_val⟩

@[simp]
theorem coe_subtype {α} (p : α → Prop) : ⇑(subtype p) = coe :=
  rfl

/-- Choosing an element `b : β` gives an embedding of `punit` into `β`. -/
def punit {β : Sort _} (b : β) : PUnit ↪ β :=
  ⟨fun _ => b, by
    rintro ⟨⟩ ⟨⟩ _
    rfl⟩

/-- Fixing an element `b : β` gives an embedding `α ↪ α × β`. -/
@[simps]
def sectl (α : Sort _) {β : Sort _} (b : β) : α ↪ α × β :=
  ⟨fun a => (a, b), fun a a' h => congr_arg Prod.fst h⟩

/-- Fixing an element `a : α` gives an embedding `β ↪ α × β`. -/
@[simps]
def sectr {α : Sort _} (a : α) (β : Sort _) : β ↪ α × β :=
  ⟨fun b => (a, b), fun b b' h => congr_arg Prod.snd h⟩

/-- Restrict the codomain of an embedding. -/
def codRestrict {α β} (p : Set β) (f : α ↪ β) (H : ∀ a, f a ∈ p) : α ↪ p :=
  ⟨fun a => ⟨f a, H a⟩, fun a b h => f.Injective (@congr_arg _ _ _ _ Subtype.val h)⟩

@[simp]
theorem cod_restrict_apply {α β} (p) (f : α ↪ β) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

/-- If `e₁` and `e₂` are embeddings, then so is `prod.map e₁ e₂ : (a, b) ↦ (e₁ a, e₂ b)`. -/
def prodMap {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : α × γ ↪ β × δ :=
  ⟨Prod.map e₁ e₂, e₁.Injective.prod_map e₂.Injective⟩

@[simp]
theorem coe_prod_map {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : ⇑(e₁.prod_map e₂) = Prod.map e₁ e₂ :=
  rfl

/-- If `e₁` and `e₂` are embeddings, then so is `λ ⟨a, b⟩, ⟨e₁ a, e₂ b⟩ : pprod α γ → pprod β δ`. -/
def pprodMap {α β γ δ : Sort _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : PProd α γ ↪ PProd β δ :=
  ⟨fun x => ⟨e₁ x.1, e₂ x.2⟩, e₁.Injective.pprod_map e₂.Injective⟩

section Sum

open Sum

/-- If `e₁` and `e₂` are embeddings, then so is `sum.map e₁ e₂`. -/
def sumMap {α β γ δ : Type _} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : Sum α γ ↪ Sum β δ :=
  ⟨Sum.map e₁ e₂, fun s₁ s₂ h =>
    match s₁, s₂, h with
    | inl a₁, inl a₂, h => congr_arg inl <| e₁.Injective <| inl.injₓ h
    | inr b₁, inr b₂, h => congr_arg inr <| e₂.Injective <| inr.injₓ h⟩

@[simp]
theorem coe_sum_map {α β γ δ} (e₁ : α ↪ β) (e₂ : γ ↪ δ) : ⇑(sumMap e₁ e₂) = Sum.map e₁ e₂ :=
  rfl

/-- The embedding of `α` into the sum `α ⊕ β`. -/
@[simps]
def inl {α β : Type _} : α ↪ Sum α β :=
  ⟨Sum.inl, fun a b => Sum.inl.injₓ⟩

/-- The embedding of `β` into the sum `α ⊕ β`. -/
@[simps]
def inr {α β : Type _} : β ↪ Sum α β :=
  ⟨Sum.inr, fun a b => Sum.inr.injₓ⟩

end Sum

section Sigma

variable {α α' : Type _} {β : α → Type _} {β' : α' → Type _}

/-- `sigma.mk` as an `function.embedding`. -/
@[simps apply]
def sigmaMk (a : α) : β a ↪ Σx, β x :=
  ⟨Sigma.mk a, sigma_mk_injective⟩

/-- If `f : α ↪ α'` is an embedding and `g : Π a, β α ↪ β' (f α)` is a family
of embeddings, then `sigma.map f g` is an embedding. -/
@[simps apply]
def sigmaMap (f : α ↪ α') (g : ∀ a, β a ↪ β' (f a)) : (Σa, β a) ↪ Σa', β' a' :=
  ⟨Sigma.map f fun a => g a, f.Injective.sigma_map fun a => (g a).Injective⟩

end Sigma

/-- Define an embedding `(Π a : α, β a) ↪ (Π a : α, γ a)` from a family of embeddings
`e : Π a, (β a ↪ γ a)`. This embedding sends `f` to `λ a, e a (f a)`. -/
@[simps]
def piCongrRight {α : Sort _} {β γ : α → Sort _} (e : ∀ a, β a ↪ γ a) : (∀ a, β a) ↪ ∀ a, γ a :=
  ⟨fun f a => e a (f a), fun f₁ f₂ h => funext fun a => (e a).Injective (congr_fun h a)⟩

/-- An embedding `e : α ↪ β` defines an embedding `(γ → α) ↪ (γ → β)` that sends each `f`
to `e ∘ f`. -/
def arrowCongrRight {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) : (γ → α) ↪ γ → β :=
  piCongrRight fun _ => e

@[simp]
theorem arrow_congr_right_apply {α : Sort u} {β : Sort v} {γ : Sort w} (e : α ↪ β) (f : γ ↪ α) :
    arrowCongrRight e f = e ∘ f :=
  rfl

/-- An embedding `e : α ↪ β` defines an embedding `(α → γ) ↪ (β → γ)` for any inhabited type `γ`.
This embedding sends each `f : α → γ` to a function `g : β → γ` such that `g ∘ e = f` and
`g y = default` whenever `y ∉ range e`. -/
noncomputable def arrowCongrLeft {α : Sort u} {β : Sort v} {γ : Sort w} [Inhabited γ] (e : α ↪ β) : (α → γ) ↪ β → γ :=
  ⟨fun f => extendₓ e f default, fun f₁ f₂ h =>
    funext fun x => by
      simpa only [← extend_apply e.injective] using congr_fun h (e x)⟩

/-- Restrict both domain and codomain of an embedding. -/
protected def subtypeMap {α β} {p : α → Prop} {q : β → Prop} (f : α ↪ β) (h : ∀ ⦃x⦄, p x → q (f x)) :
    { x : α // p x } ↪ { y : β // q y } :=
  ⟨Subtype.map f h, Subtype.map_injective h f.2⟩

open Set

/-- `set.image` as an embedding `set α ↪ set β`. -/
@[simps apply]
protected def image {α β} (f : α ↪ β) : Set α ↪ Set β :=
  ⟨Image f, f.2.image_injective⟩

theorem swap_apply {α β : Type _} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y z : α) :
    Equivₓ.swap (f x) (f y) (f z) = f (Equivₓ.swap x y z) :=
  f.Injective.swap_apply x y z

theorem swap_comp {α β : Type _} [DecidableEq α] [DecidableEq β] (f : α ↪ β) (x y : α) :
    Equivₓ.swap (f x) (f y) ∘ f = f ∘ Equivₓ.swap x y :=
  f.Injective.swap_comp x y

end Embedding

end Function

namespace Equivₓ

open Function.Embedding

/-- The type of embeddings `α ↪ β` is equivalent to
    the subtype of all injective functions `α → β`. -/
def subtypeInjectiveEquivEmbedding (α β : Sort _) : { f : α → β // Function.Injective f } ≃ (α ↪ β) where
  toFun := fun f => ⟨f.val, f.property⟩
  invFun := fun f => ⟨f, f.Injective⟩
  left_inv := fun f => by
    simp
  right_inv := fun f => by
    ext
    rfl

/-- If `α₁ ≃ α₂` and `β₁ ≃ β₂`, then the type of embeddings `α₁ ↪ β₁`
is equivalent to the type of embeddings `α₂ ↪ β₂`. -/
@[congr, simps apply]
def embeddingCongr {α β γ δ : Sort _} (h : α ≃ β) (h' : γ ≃ δ) : (α ↪ γ) ≃ (β ↪ δ) where
  toFun := fun f => f.congr h h'
  invFun := fun f => f.congr h.symm h'.symm
  left_inv := fun x => by
    ext
    simp
  right_inv := fun x => by
    ext
    simp

@[simp]
theorem embedding_congr_refl {α β : Sort _} : embeddingCongr (Equivₓ.refl α) (Equivₓ.refl β) = Equivₓ.refl (α ↪ β) := by
  ext
  rfl

@[simp]
theorem embedding_congr_trans {α₁ β₁ α₂ β₂ α₃ β₃ : Sort _} (e₁ : α₁ ≃ α₂) (e₁' : β₁ ≃ β₂) (e₂ : α₂ ≃ α₃)
    (e₂' : β₂ ≃ β₃) :
    embeddingCongr (e₁.trans e₂) (e₁'.trans e₂') = (embeddingCongr e₁ e₁').trans (embeddingCongr e₂ e₂') :=
  rfl

@[simp]
theorem embedding_congr_symm {α₁ β₁ α₂ β₂ : Sort _} (e₁ : α₁ ≃ α₂) (e₂ : β₁ ≃ β₂) :
    (embeddingCongr e₁ e₂).symm = embeddingCongr e₁.symm e₂.symm :=
  rfl

theorem embedding_congr_apply_trans {α₁ β₁ γ₁ α₂ β₂ γ₂ : Sort _} (ea : α₁ ≃ α₂) (eb : β₁ ≃ β₂) (ec : γ₁ ≃ γ₂)
    (f : α₁ ↪ β₁) (g : β₁ ↪ γ₁) :
    Equivₓ.embeddingCongr ea ec (f.trans g) = (Equivₓ.embeddingCongr ea eb f).trans (Equivₓ.embeddingCongr eb ec g) :=
  by
  ext
  simp

@[simp]
theorem refl_to_embedding {α : Type _} : (Equivₓ.refl α).toEmbedding = Function.Embedding.refl α :=
  rfl

@[simp]
theorem trans_to_embedding {α β γ : Type _} (e : α ≃ β) (f : β ≃ γ) :
    (e.trans f).toEmbedding = e.toEmbedding.trans f.toEmbedding :=
  rfl

end Equivₓ

namespace Set

/-- The injection map is an embedding between subsets. -/
@[simps apply]
def embeddingOfSubset {α} (s t : Set α) (h : s ⊆ t) : s ↪ t :=
  ⟨fun x => ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h => by
    congr
    injection h⟩

end Set

section Subtype

variable {α : Type _}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` can be injectively split
into a sum of subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right. -/
def subtypeOrLeftEmbedding (p q : α → Prop) [DecidablePred p] : { x // p x ∨ q x } ↪ Sum { x // p x } { x // q x } :=
  ⟨fun x => if h : p x then Sum.inl ⟨x, h⟩ else Sum.inr ⟨x, x.Prop.resolve_left h⟩, by
    intro x y
    dsimp' only
    split_ifs <;> simp [← Subtype.ext_iff]⟩

theorem subtype_or_left_embedding_apply_left {p q : α → Prop} [DecidablePred p] (x : { x // p x ∨ q x }) (hx : p x) :
    subtypeOrLeftEmbedding p q x = Sum.inl ⟨x, hx⟩ :=
  dif_pos hx

theorem subtype_or_left_embedding_apply_right {p q : α → Prop} [DecidablePred p] (x : { x // p x ∨ q x }) (hx : ¬p x) :
    subtypeOrLeftEmbedding p q x = Sum.inr ⟨x, x.Prop.resolve_left hx⟩ :=
  dif_neg hx

/-- A subtype `{x // p x}` can be injectively sent to into a subtype `{x // q x}`,
if `p x → q x` for all `x : α`. -/
@[simps]
def Subtype.impEmbedding (p q : α → Prop) (h : p ≤ q) : { x // p x } ↪ { x // q x } :=
  ⟨fun x => ⟨x, h x x.Prop⟩, fun x y => by
    simp [← Subtype.ext_iff]⟩

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalent to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`disjoint p q`.

See also `equiv.sum_compl`, for when `is_compl p q`.  -/
@[simps apply]
def subtypeOrEquiv (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) :
    { x // p x ∨ q x } ≃ Sum { x // p x } { x // q x } where
  toFun := subtypeOrLeftEmbedding p q
  invFun :=
    Sum.elim (Subtype.impEmbedding _ _ fun x hx => (Or.inl hx : p x ∨ q x))
      (Subtype.impEmbedding _ _ fun x hx => (Or.inr hx : p x ∨ q x))
  left_inv := fun x => by
    by_cases' hx : p x
    · rw [subtype_or_left_embedding_apply_left _ hx]
      simp [← Subtype.ext_iff]
      
    · rw [subtype_or_left_embedding_apply_right _ hx]
      simp [← Subtype.ext_iff]
      
  right_inv := fun x => by
    cases x
    · simp only [← Sum.elim_inl]
      rw [subtype_or_left_embedding_apply_left]
      · simp
        
      · simpa using x.prop
        
      
    · simp only [← Sum.elim_inr]
      rw [subtype_or_left_embedding_apply_right]
      · simp
        
      · suffices ¬p x by
          simpa
        intro hp
        simpa using h x ⟨hp, x.prop⟩
        
      

@[simp]
theorem subtype_or_equiv_symm_inl (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) (x : { x // p x }) :
    (subtypeOrEquiv p q h).symm (Sum.inl x) = ⟨x, Or.inl x.Prop⟩ :=
  rfl

@[simp]
theorem subtype_or_equiv_symm_inr (p q : α → Prop) [DecidablePred p] (h : Disjoint p q) (x : { x // q x }) :
    (subtypeOrEquiv p q h).symm (Sum.inr x) = ⟨x, Or.inr x.Prop⟩ :=
  rfl

end Subtype

