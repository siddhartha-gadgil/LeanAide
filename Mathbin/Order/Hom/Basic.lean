/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathbin.Logic.Equiv.Option
import Mathbin.Order.RelIso
import Mathbin.Tactic.Monotonicity.Basic

/-!
# Order homomorphisms

This file defines order homomorphisms, which are bundled monotone functions. A preorder
homomorphism `f : α →o β` is a function `α → β` along with a proof that `∀ x y, x ≤ y → f x ≤ f y`.

## Main definitions

In this file we define the following bundled monotone maps:
 * `order_hom α β` a.k.a. `α →o β`: Preorder homomorphism.
    An `order_hom α β` is a function `f : α → β` such that `a₁ ≤ a₂ → f a₁ ≤ f a₂`
 * `order_embedding α β` a.k.a. `α ↪o β`: Relation embedding.
    An `order_embedding α β` is an embedding `f : α ↪ β` such that `a ≤ b ↔ f a ≤ f b`.
    Defined as an abbreviation of `@rel_embedding α β (≤) (≤)`.
* `order_iso`: Relation isomorphism.
    An `order_iso α β` is an equivalence `f : α ≃ β` such that `a ≤ b ↔ f a ≤ f b`.
    Defined as an abbreviation of `@rel_iso α β (≤) (≤)`.

We also define many `order_hom`s. In some cases we define two versions, one with `ₘ` suffix and
one without it (e.g., `order_hom.compₘ` and `order_hom.comp`). This means that the former
function is a "more bundled" version of the latter. We can't just drop the "less bundled" version
because the more bundled version usually does not work with dot notation.

* `order_hom.id`: identity map as `α →o α`;
* `order_hom.curry`: an order isomorphism between `α × β →o γ` and `α →o β →o γ`;
* `order_hom.comp`: composition of two bundled monotone maps;
* `order_hom.compₘ`: composition of bundled monotone maps as a bundled monotone map;
* `order_hom.const`: constant function as a bundled monotone map;
* `order_hom.prod`: combine `α →o β` and `α →o γ` into `α →o β × γ`;
* `order_hom.prodₘ`: a more bundled version of `order_hom.prod`;
* `order_hom.prod_iso`: order isomorphism between `α →o β × γ` and `(α →o β) × (α →o γ)`;
* `order_hom.diag`: diagonal embedding of `α` into `α × α` as a bundled monotone map;
* `order_hom.on_diag`: restrict a monotone map `α →o α →o β` to the diagonal;
* `order_hom.fst`: projection `prod.fst : α × β → α` as a bundled monotone map;
* `order_hom.snd`: projection `prod.snd : α × β → β` as a bundled monotone map;
* `order_hom.prod_map`: `prod.map f g` as a bundled monotone map;
* `pi.eval_order_hom`: evaluation of a function at a point `function.eval i` as a bundled
  monotone map;
* `order_hom.coe_fn_hom`: coercion to function as a bundled monotone map;
* `order_hom.apply`: application of a `order_hom` at a point as a bundled monotone map;
* `order_hom.pi`: combine a family of monotone maps `f i : α →o π i` into a monotone map
  `α →o Π i, π i`;
* `order_hom.pi_iso`: order isomorphism between `α →o Π i, π i` and `Π i, α →o π i`;
* `order_hom.subtyle.val`: embedding `subtype.val : subtype p → α` as a bundled monotone map;
* `order_hom.dual`: reinterpret a monotone map `α →o β` as a monotone map `αᵒᵈ →o βᵒᵈ`;
* `order_hom.dual_iso`: order isomorphism between `α →o β` and `(αᵒᵈ →o βᵒᵈ)ᵒᵈ`;
* `order_iso.compl`: order isomorphism `α ≃o αᵒᵈ` given by taking complements in a
  boolean algebra;

We also define two functions to convert other bundled maps to `α →o β`:

* `order_embedding.to_order_hom`: convert `α ↪o β` to `α →o β`;
* `rel_hom.to_order_hom`: convert a `rel_hom` between strict orders to a `order_hom`.

## Tags

monotone map, bundled morphism
-/


open OrderDual

variable {F α β γ δ : Type _}

/-- Bundled monotone (aka, increasing) function -/
structure OrderHom (α β : Type _) [Preorderₓ α] [Preorderₓ β] where
  toFun : α → β
  monotone' : Monotone to_fun

-- mathport name: «expr →o »
infixr:25 " →o " => OrderHom

/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_embedding (≤) (≤)`. -/
abbrev OrderEmbedding (α β : Type _) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)

-- mathport name: «expr ↪o »
infixl:25 " ↪o " => OrderEmbedding

/-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `rel_iso (≤) (≤)`. -/
abbrev OrderIso (α β : Type _) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)

-- mathport name: «expr ≃o »
infixl:25 " ≃o " => OrderIso

/-- `order_hom_class F α b` asserts that `F` is a type of `≤`-preserving morphisms. -/
abbrev OrderHomClass (F : Type _) (α β : outParam (Type _)) [LE α] [LE β] :=
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop)

/-- `order_iso_class F α β` states that `F` is a type of order isomorphisms.

You should extend this class when you extend `order_iso`. -/
class OrderIsoClass (F : Type _) (α β : outParam (Type _)) [LE α] [LE β] extends EquivLike F α β where
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b

export OrderIsoClass (map_le_map_iff)

attribute [simp] map_le_map_iff

instance [LE α] [LE β] [OrderIsoClass F α β] : CoeTₓ F (α ≃o β) :=
  ⟨fun f => ⟨f, fun _ _ => map_le_map_iff f⟩⟩

-- See note [lower instance priority]
instance (priority := 100) OrderIsoClass.toOrderHomClass [LE α] [LE β] [OrderIsoClass F α β] : OrderHomClass F α β :=
  { EquivLike.toEmbeddingLike with map_rel := fun f a b => (map_le_map_iff f).2 }

namespace OrderHomClass

variable [Preorderₓ α] [Preorderₓ β] [OrderHomClass F α β]

protected theorem monotone (f : F) : Monotone (f : α → β) := fun _ _ => map_rel f

protected theorem mono (f : F) : Monotone (f : α → β) := fun _ _ => map_rel f

instance : CoeTₓ F (α →o β) :=
  ⟨fun f => { toFun := f, monotone' := OrderHomClass.mono _ }⟩

end OrderHomClass

section OrderIsoClass

section LE

variable [LE α] [LE β] [OrderIsoClass F α β]

@[simp]
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b ≤ a ↔ b ≤ f a := by
  convert (map_le_map_iff _).symm
  exact (EquivLike.right_inv _ _).symm

@[simp]
theorem le_map_inv_iff (f : F) {a : α} {b : β} : a ≤ EquivLike.inv f b ↔ f a ≤ b := by
  convert (map_le_map_iff _).symm
  exact (EquivLike.right_inv _ _).symm

end LE

variable [Preorderₓ α] [Preorderₓ β] [OrderIsoClass F α β]

include β

theorem map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)

@[simp]
theorem map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a := by
  convert (map_lt_map_iff _).symm
  exact (EquivLike.right_inv _ _).symm

@[simp]
theorem lt_map_inv_iff (f : F) {a : α} {b : β} : a < EquivLike.inv f b ↔ f a < b := by
  convert (map_lt_map_iff _).symm
  exact (EquivLike.right_inv _ _).symm

end OrderIsoClass

namespace OrderHom

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ] [Preorderₓ δ]

/-- Helper instance for when there's too many metavariables to apply `fun_like.has_coe_to_fun`
directly. -/
instance : CoeFun (α →o β) fun _ => α → β :=
  ⟨OrderHom.toFun⟩

initialize_simps_projections OrderHom (toFun → coe)

protected theorem monotone (f : α →o β) : Monotone f :=
  f.monotone'

protected theorem mono (f : α →o β) : Monotone f :=
  f.Monotone

instance : OrderHomClass (α →o β) α β where
  coe := toFun
  coe_injective' := fun f g h => by
    cases f
    cases g
    congr
  map_rel := fun f => f.Monotone

@[simp]
theorem to_fun_eq_coe {f : α →o β} : f.toFun = f :=
  rfl

@[simp]
theorem coe_fun_mk {f : α → β} (hf : Monotone f) : (mk f hf : α → β) = f :=
  rfl

-- See library note [partially-applied ext lemmas]
@[ext]
theorem ext (f g : α →o β) (h : (f : α → β) = g) : f = g :=
  FunLike.coe_injective h

theorem coe_eq (f : α →o β) : coe f = f := by
  ext <;> rfl

/-- One can lift an unbundled monotone function to a bundled one. -/
instance : CanLift (α → β) (α →o β) where
  coe := coeFn
  cond := Monotone
  prf := fun f h => ⟨⟨f, h⟩, rfl⟩

/-- Copy of an `order_hom` with a new `to_fun` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy (f : α →o β) (f' : α → β) (h : f' = f) : α →o β :=
  ⟨f', h.symm.subst f.monotone'⟩

/-- The identity function as bundled monotone function. -/
@[simps (config := { fullyApplied := false })]
def id : α →o α :=
  ⟨id, monotone_id⟩

instance : Inhabited (α →o α) :=
  ⟨id⟩

/-- The preorder structure of `α →o β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
instance : Preorderₓ (α →o β) :=
  @Preorderₓ.lift (α →o β) (α → β) _ coeFn

instance {β : Type _} [PartialOrderₓ β] : PartialOrderₓ (α →o β) :=
  @PartialOrderₓ.lift (α →o β) (α → β) _ coeFn ext

theorem le_def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl

@[simp, norm_cast]
theorem coe_le_coe {f g : α →o β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl

@[simp]
theorem mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g :=
  Iff.rfl

@[mono]
theorem apply_mono {f g : α →o β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  (h₁ x).trans <| g.mono h₂

/-- Curry/uncurry as an order isomorphism between `α × β →o γ` and `α →o β →o γ`. -/
def curry : (α × β →o γ) ≃o (α →o β →o γ) where
  toFun := fun f =>
    ⟨fun x => ⟨Function.curry f x, fun y₁ y₂ h => f.mono ⟨le_rfl, h⟩⟩, fun x₁ x₂ h y => f.mono ⟨h, le_rfl⟩⟩
  invFun := fun f => ⟨Function.uncurry fun x => f x, fun x y h => (f.mono h.1 x.2).trans <| (f y.1).mono h.2⟩
  left_inv := fun f => by
    ext ⟨x, y⟩
    rfl
  right_inv := fun f => by
    ext x y
    rfl
  map_rel_iff' := fun f g => by
    simp [← le_def]

@[simp]
theorem curry_apply (f : α × β →o γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

@[simp]
theorem curry_symm_apply (f : α →o β →o γ) (x : α × β) : curry.symm f x = f x.1 x.2 :=
  rfl

/-- The composition of two bundled monotone functions. -/
@[simps (config := { fullyApplied := false })]
def comp (g : β →o γ) (f : α →o β) : α →o γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono]
theorem comp_mono ⦃g₁ g₂ : β →o γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →o β⦄ (hf : f₁ ≤ f₂) : g₁.comp f₁ ≤ g₂.comp f₂ := fun x =>
  (hg _).trans (g₂.mono <| hf _)

/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps (config := { fullyApplied := false })]
def compₘ : (β →o γ) →o (α →o β) →o α →o γ :=
  curry ⟨fun f : (β →o γ) × (α →o β) => f.1.comp f.2, fun f₁ f₂ h => comp_mono h.1 h.2⟩

@[simp]
theorem comp_id (f : α →o β) : comp f id = f := by
  ext
  rfl

@[simp]
theorem id_comp (f : α →o β) : comp id f = f := by
  ext
  rfl

/-- Constant function bundled as a `order_hom`. -/
@[simps (config := { fullyApplied := false })]
def const (α : Type _) [Preorderₓ α] {β : Type _} [Preorderₓ β] : β →o α →o β where
  toFun := fun b => ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' := fun b₁ b₂ h x => h

@[simp]
theorem const_comp (f : α →o β) (c : γ) : (const β c).comp f = const α c :=
  rfl

@[simp]
theorem comp_const (γ : Type _) [Preorderₓ γ] (f : α →o β) (c : α) : f.comp (const γ c) = const γ (f c) :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`order_hom`. -/
@[simps]
protected def prod (f : α →o β) (g : α →o γ) : α →o β × γ :=
  ⟨fun x => (f x, g x), fun x y h => ⟨f.mono h, g.mono h⟩⟩

@[mono]
theorem prod_mono {f₁ f₂ : α →o β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →o γ} (hg : g₁ ≤ g₂) : f₁.Prod g₁ ≤ f₂.Prod g₂ := fun x =>
  Prod.le_def.2 ⟨hf _, hg _⟩

theorem comp_prod_comp_same (f₁ f₂ : β →o γ) (g : α →o β) : (f₁.comp g).Prod (f₂.comp g) = (f₁.Prod f₂).comp g :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`order_hom`. This is a fully bundled version. -/
@[simps]
def prodₘ : (α →o β) →o (α →o γ) →o α →o β × γ :=
  curry ⟨fun f : (α →o β) × (α →o γ) => f.1.Prod f.2, fun f₁ f₂ h => prod_mono h.1 h.2⟩

/-- Diagonal embedding of `α` into `α × α` as a `order_hom`. -/
@[simps]
def diag : α →o α × α :=
  id.Prod id

/-- Restriction of `f : α →o α →o β` to the diagonal. -/
@[simps (config := { simpRhs := true })]
def onDiag (f : α →o α →o β) : α →o β :=
  (curry.symm f).comp diag

/-- `prod.fst` as a `order_hom`. -/
@[simps]
def fst : α × β →o α :=
  ⟨Prod.fst, fun x y h => h.1⟩

/-- `prod.snd` as a `order_hom`. -/
@[simps]
def snd : α × β →o β :=
  ⟨Prod.snd, fun x y h => h.2⟩

@[simp]
theorem fst_prod_snd : (fst : α × β →o α).Prod snd = id := by
  ext ⟨x, y⟩ : 2
  rfl

@[simp]
theorem fst_comp_prod (f : α →o β) (g : α →o γ) : fst.comp (f.Prod g) = f :=
  ext _ _ rfl

@[simp]
theorem snd_comp_prod (f : α →o β) (g : α →o γ) : snd.comp (f.Prod g) = g :=
  ext _ _ rfl

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps]
def prodIso : (α →o β × γ) ≃o (α →o β) × (α →o γ) where
  toFun := fun f => (fst.comp f, snd.comp f)
  invFun := fun f => f.1.Prod f.2
  left_inv := fun f => by
    ext <;> rfl
  right_inv := fun f => by
    ext <;> rfl
  map_rel_iff' := fun f g => forall_and_distrib.symm

/-- `prod.map` of two `order_hom`s as a `order_hom`. -/
@[simps]
def prodMap (f : α →o β) (g : γ →o δ) : α × γ →o β × δ :=
  ⟨Prod.map f g, fun x y h => ⟨f.mono h.1, g.mono h.2⟩⟩

variable {ι : Type _} {π : ι → Type _} [∀ i, Preorderₓ (π i)]

/-- Evaluation of an unbundled function at a point (`function.eval`) as a `order_hom`. -/
@[simps (config := { fullyApplied := false })]
def _root_.pi.eval_order_hom (i : ι) : (∀ j, π j) →o π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩

/-- The "forgetful functor" from `α →o β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps (config := { fullyApplied := false })]
def coeFnHom : (α →o β) →o α → β where
  toFun := fun f => f
  monotone' := fun x y h => h

/-- Function application `λ f, f a` (for fixed `a`) is a monotone function from the
monotone function space `α →o β` to `β`. See also `pi.eval_order_hom`.  -/
@[simps (config := { fullyApplied := false })]
def apply (x : α) : (α →o β) →o β :=
  (Pi.evalOrderHom x).comp coeFnHom

/-- Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`. -/
@[simps]
def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
  ⟨fun x i => f i x, fun x y h i => (f i).mono h⟩

/-- Order isomorphism between bundled monotone maps `α →o Π i, π i` and families of bundled monotone
maps `Π i, α →o π i`. -/
@[simps]
def piIso : (α →o ∀ i, π i) ≃o ∀ i, α →o π i where
  toFun := fun f i => (Pi.evalOrderHom i).comp f
  invFun := pi
  left_inv := fun f => by
    ext x i
    rfl
  right_inv := fun f => by
    ext x i
    rfl
  map_rel_iff' := fun f g => forall_swap

/-- `subtype.val` as a bundled monotone function.  -/
@[simps (config := { fullyApplied := false })]
def Subtype.val (p : α → Prop) : Subtype p →o α :=
  ⟨Subtype.val, fun x y h => h⟩

/-- There is a unique monotone map from a subsingleton to itself. -/
-- TODO[gh-6025]: make this a global instance once safe to do so
@[local instance]
def unique [Subsingleton α] : Unique (α →o α) where
  default := OrderHom.id
  uniq := fun a => ext _ _ (Subsingleton.elimₓ _ _)

theorem order_hom_eq_id [Subsingleton α] (g : α →o α) : g = OrderHom.id :=
  Subsingleton.elimₓ _ _

/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps]
protected def dual : (α →o β) ≃ (αᵒᵈ →o βᵒᵈ) where
  toFun := fun f => ⟨OrderDual.toDual ∘ f ∘ OrderDual.ofDual, f.mono.dual⟩
  invFun := fun f => ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩
  left_inv := fun f => ext _ _ rfl
  right_inv := fun f => ext _ _ rfl

@[simp]
theorem dual_id : (OrderHom.id : α →o α).dual = OrderHom.id :=
  rfl

@[simp]
theorem dual_comp (g : β →o γ) (f : α →o β) : (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
theorem symm_dual_id : OrderHom.dual.symm OrderHom.id = (OrderHom.id : α →o α) :=
  rfl

@[simp]
theorem symm_dual_comp (g : βᵒᵈ →o γᵒᵈ) (f : αᵒᵈ →o βᵒᵈ) :
    OrderHom.dual.symm (g.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f) :=
  rfl

/-- `order_hom.dual` as an order isomorphism. -/
def dualIso (α β : Type _) [Preorderₓ α] [Preorderₓ β] : (α →o β) ≃o (αᵒᵈ →o βᵒᵈ)ᵒᵈ where
  toEquiv := OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := fun f g => Iff.rfl

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `with_bot α →o with_bot β`. -/
@[simps (config := { fullyApplied := false })]
protected def withBotMap (f : α →o β) : WithBot α →o WithBot β :=
  ⟨WithBot.map f, f.mono.with_bot_map⟩

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `with_top α →o with_top β`. -/
@[simps (config := { fullyApplied := false })]
protected def withTopMap (f : α →o β) : WithTop α →o WithTop β :=
  ⟨WithTop.map f, f.mono.with_top_map⟩

end OrderHom

/-- Embeddings of partial orders that preserve `<` also preserve `≤`. -/
def RelEmbedding.orderEmbeddingOfLtEmbedding [PartialOrderₓ α] [PartialOrderₓ β]
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) : α ↪o β :=
  { f with
    map_rel_iff' := by
      intros
      simp [← le_iff_lt_or_eqₓ, ← f.map_rel_iff, ← f.injective.eq_iff] }

@[simp]
theorem RelEmbedding.order_embedding_of_lt_embedding_apply [PartialOrderₓ α] [PartialOrderₓ β]
    {f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)} {x : α} :
    RelEmbedding.orderEmbeddingOfLtEmbedding f x = f x :=
  rfl

namespace OrderEmbedding

variable [Preorderₓ α] [Preorderₓ β] (f : α ↪o β)

/-- `<` is preserved by order embeddings of preorders. -/
def ltEmbedding : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  { f with
    map_rel_iff' := by
      intros <;> simp [← lt_iff_le_not_leₓ, ← f.map_rel_iff] }

@[simp]
theorem lt_embedding_apply (x : α) : f.ltEmbedding x = f x :=
  rfl

@[simp]
theorem le_iff_le {a b} : f a ≤ f b ↔ a ≤ b :=
  f.map_rel_iff

@[simp]
theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
  f.ltEmbedding.map_rel_iff

@[simp]
theorem eq_iff_eq {a b} : f a = f b ↔ a = b :=
  f.Injective.eq_iff

protected theorem monotone : Monotone f :=
  OrderHomClass.monotone f

protected theorem strict_mono : StrictMono f := fun x y => f.lt_iff_lt.2

protected theorem acc (a : α) : Acc (· < ·) (f a) → Acc (· < ·) a :=
  f.ltEmbedding.Acc a

protected theorem well_founded : WellFounded ((· < ·) : β → β → Prop) → WellFounded ((· < ·) : α → α → Prop) :=
  f.ltEmbedding.WellFounded

protected theorem is_well_order [IsWellOrder β (· < ·)] : IsWellOrder α (· < ·) :=
  f.ltEmbedding.IsWellOrder

/-- An order embedding is also an order embedding between dual orders. -/
protected def dual : αᵒᵈ ↪o βᵒᵈ :=
  ⟨f.toEmbedding, fun a b => f.map_rel_iff⟩

/-- A version of `with_bot.map` for order embeddings. -/
@[simps (config := { fullyApplied := false })]
protected def withBotMap (f : α ↪o β) : WithBot α ↪o WithBot β :=
  { f.toEmbedding.option_map with toFun := WithBot.map f,
    map_rel_iff' := WithBot.map_le_iff f fun a b => f.map_rel_iff }

/-- A version of `with_top.map` for order embeddings. -/
@[simps (config := { fullyApplied := false })]
protected def withTopMap (f : α ↪o β) : WithTop α ↪o WithTop β :=
  { f.dual.with_bot_map.dual with toFun := WithTop.map f }

/-- To define an order embedding from a partial order to a preorder it suffices to give a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
def ofMapLeIff {α β} [PartialOrderₓ α] [Preorderₓ β] (f : α → β) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) : α ↪o β :=
  RelEmbedding.ofMapRelIff f hf

@[simp]
theorem coe_of_map_le_iff {α β} [PartialOrderₓ α] [Preorderₓ β] {f : α → β} (h) : ⇑(ofMapLeIff f h) = f :=
  rfl

/-- A strictly monotone map from a linear order is an order embedding. --/
def ofStrictMono {α β} [LinearOrderₓ α] [Preorderₓ β] (f : α → β) (h : StrictMono f) : α ↪o β :=
  ofMapLeIff f fun _ _ => h.le_iff_le

@[simp]
theorem coe_of_strict_mono {α β} [LinearOrderₓ α] [Preorderₓ β] {f : α → β} (h : StrictMono f) :
    ⇑(ofStrictMono f h) = f :=
  rfl

/-- Embedding of a subtype into the ambient type as an `order_embedding`. -/
@[simps (config := { fullyApplied := false })]
def subtype (p : α → Prop) : Subtype p ↪o α :=
  ⟨Function.Embedding.subtype p, fun x y => Iff.rfl⟩

/-- Convert an `order_embedding` to a `order_hom`. -/
@[simps (config := { fullyApplied := false })]
def toOrderHom {X Y : Type _} [Preorderₓ X] [Preorderₓ Y] (f : X ↪o Y) : X →o Y where
  toFun := f
  monotone' := f.Monotone

end OrderEmbedding

section RelHom

variable [PartialOrderₓ α] [Preorderₓ β]

namespace RelHom

variable (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotone
is weakly monotone. -/
@[simps (config := { fullyApplied := false })]
def toOrderHom : α →o β where
  toFun := f
  monotone' := StrictMono.monotone fun x y => f.map_rel

end RelHom

theorem RelEmbedding.to_order_hom_injective (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) :
    Function.Injective (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop)).toOrderHom := fun _ _ h =>
  f.Injective h

end RelHom

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ]

instance : OrderIsoClass (α ≃o β) α β where
  coe := fun f => f.toFun
  inv := fun f => f.invFun
  left_inv := fun f => f.left_inv
  right_inv := fun f => f.right_inv
  coe_injective' := fun f g h₁ h₂ => by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr
  map_le_map_iff := fun f => f.map_rel_iff'

@[simp]
theorem to_fun_eq_coe {f : α ≃o β} : f.toFun = f :=
  rfl

-- See note [partially-applied ext lemmas]
@[ext]
theorem ext {f g : α ≃o β} (h : (f : α → β) = g) : f = g :=
  FunLike.coe_injective h

/-- Reinterpret an order isomorphism as an order embedding. -/
def toOrderEmbedding (e : α ≃o β) : α ↪o β :=
  e.toRelEmbedding

@[simp]
theorem coe_to_order_embedding (e : α ≃o β) : ⇑e.toOrderEmbedding = e :=
  rfl

protected theorem bijective (e : α ≃o β) : Function.Bijective e :=
  e.toEquiv.Bijective

protected theorem injective (e : α ≃o β) : Function.Injective e :=
  e.toEquiv.Injective

protected theorem surjective (e : α ≃o β) : Function.Surjective e :=
  e.toEquiv.Surjective

@[simp]
theorem range_eq (e : α ≃o β) : Set.Range e = Set.Univ :=
  e.Surjective.range_eq

@[simp]
theorem apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
  e.toEquiv.apply_eq_iff_eq

/-- Identity order isomorphism. -/
def refl (α : Type _) [LE α] : α ≃o α :=
  RelIso.refl (· ≤ ·)

@[simp]
theorem coe_refl : ⇑(refl α) = id :=
  rfl

@[simp]
theorem refl_apply (x : α) : refl α x = x :=
  rfl

@[simp]
theorem refl_to_equiv : (refl α).toEquiv = Equivₓ.refl α :=
  rfl

/-- Inverse of an order isomorphism. -/
def symm (e : α ≃o β) : β ≃o α :=
  e.symm

@[simp]
theorem apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x

@[simp]
theorem symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[simp]
theorem symm_refl (α : Type _) [LE α] : (refl α).symm = refl α :=
  rfl

theorem apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
  e.toEquiv.apply_eq_iff_eq_symm_apply

theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq

@[simp]
theorem symm_symm (e : α ≃o β) : e.symm.symm = e := by
  ext
  rfl

theorem symm_injective : Function.Injective (symm : α ≃o β → β ≃o α) := fun e e' h => by
  rw [← e.symm_symm, h, e'.symm_symm]

@[simp]
theorem to_equiv_symm (e : α ≃o β) : e.toEquiv.symm = e.symm.toEquiv :=
  rfl

@[simp]
theorem symm_image_image (e : α ≃o β) (s : Set α) : e.symm '' (e '' s) = s :=
  e.toEquiv.symm_image_image s

@[simp]
theorem image_symm_image (e : α ≃o β) (s : Set β) : e '' (e.symm '' s) = s :=
  e.toEquiv.image_symm_image s

theorem image_eq_preimage (e : α ≃o β) (s : Set α) : e '' s = e.symm ⁻¹' s :=
  e.toEquiv.image_eq_preimage s

@[simp]
theorem preimage_symm_preimage (e : α ≃o β) (s : Set α) : e ⁻¹' (e.symm ⁻¹' s) = s :=
  e.toEquiv.preimage_symm_preimage s

@[simp]
theorem symm_preimage_preimage (e : α ≃o β) (s : Set β) : e.symm ⁻¹' (e ⁻¹' s) = s :=
  e.toEquiv.symm_preimage_preimage s

@[simp]
theorem image_preimage (e : α ≃o β) (s : Set β) : e '' (e ⁻¹' s) = s :=
  e.toEquiv.image_preimage s

@[simp]
theorem preimage_image (e : α ≃o β) (s : Set α) : e ⁻¹' (e '' s) = s :=
  e.toEquiv.preimage_image s

/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans]
def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  e.trans e'

@[simp]
theorem coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
theorem trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl

@[simp]
theorem refl_trans (e : α ≃o β) : (refl α).trans e = e := by
  ext x
  rfl

@[simp]
theorem trans_refl (e : α ≃o β) : e.trans (refl β) = e := by
  ext x
  rfl

/-- `prod.swap` as an `order_iso`. -/
def prodComm : α × β ≃o β × α where
  toEquiv := Equivₓ.prodComm α β
  map_rel_iff' := fun a b => Prod.swap_le_swap

@[simp]
theorem coe_prod_comm : ⇑(prodComm : α × β ≃o β × α) = Prod.swap :=
  rfl

@[simp]
theorem prod_comm_symm : (prodComm : α × β ≃o β × α).symm = prod_comm :=
  rfl

variable (α)

/-- The order isomorphism between a type and its double dual. -/
def dualDual : α ≃o αᵒᵈᵒᵈ :=
  refl α

@[simp]
theorem coe_dual_dual : ⇑(dualDual α) = to_dual ∘ to_dual :=
  rfl

@[simp]
theorem coe_dual_dual_symm : ⇑(dualDual α).symm = of_dual ∘ of_dual :=
  rfl

variable {α}

@[simp]
theorem dual_dual_apply (a : α) : dualDual α a = toDual (toDual a) :=
  rfl

@[simp]
theorem dual_dual_symm_apply (a : αᵒᵈᵒᵈ) : (dualDual α).symm a = ofDual (ofDual a) :=
  rfl

end LE

open Set

section Le

variable [LE α] [LE β] [LE γ]

@[simp]
theorem le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y :=
  e.map_rel_iff

theorem le_symm_apply (e : α ≃o β) {x : α} {y : β} : x ≤ e.symm y ↔ e x ≤ y :=
  e.rel_symm_apply

theorem symm_apply_le (e : α ≃o β) {x : α} {y : β} : e.symm y ≤ x ↔ y ≤ e x :=
  e.symm_apply_rel

end Le

variable [Preorderₓ α] [Preorderₓ β] [Preorderₓ γ]

protected theorem monotone (e : α ≃o β) : Monotone e :=
  e.toOrderEmbedding.Monotone

protected theorem strict_mono (e : α ≃o β) : StrictMono e :=
  e.toOrderEmbedding.StrictMono

@[simp]
theorem lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
  e.toOrderEmbedding.lt_iff_lt

/-- Converts an `order_iso` into a `rel_iso (<) (<)`. -/
def toRelIsoLt (e : α ≃o β) : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop) :=
  ⟨e.toEquiv, fun x y => lt_iff_lt e⟩

@[simp]
theorem to_rel_iso_lt_apply (e : α ≃o β) (x : α) : e.toRelIsoLt x = e x :=
  rfl

@[simp]
theorem to_rel_iso_lt_symm (e : α ≃o β) : e.toRelIsoLt.symm = e.symm.toRelIsoLt :=
  rfl

/-- Converts a `rel_iso (<) (<)` into an `order_iso`. -/
def ofRelIsoLt {α β} [PartialOrderₓ α] [PartialOrderₓ β] (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) :
    α ≃o β :=
  ⟨e.toEquiv, fun x y => by
    simp [← le_iff_eq_or_lt, ← e.map_rel_iff]⟩

@[simp]
theorem of_rel_iso_lt_apply {α β} [PartialOrderₓ α] [PartialOrderₓ β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) (x : α) : ofRelIsoLt e x = e x :=
  rfl

@[simp]
theorem of_rel_iso_lt_symm {α β} [PartialOrderₓ α] [PartialOrderₓ β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : (ofRelIsoLt e).symm = ofRelIsoLt e.symm :=
  rfl

@[simp]
theorem of_rel_iso_lt_to_rel_iso_lt {α β} [PartialOrderₓ α] [PartialOrderₓ β] (e : α ≃o β) :
    ofRelIsoLt (toRelIsoLt e) = e := by
  ext
  simp

@[simp]
theorem to_rel_iso_lt_of_rel_iso_lt {α β} [PartialOrderₓ α] [PartialOrderₓ β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : toRelIsoLt (ofRelIsoLt e) = e := by
  ext
  simp

/-- To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear orders,
    it suffices to prove `cmp a (g b) = cmp (f a) b`. --/
def ofCmpEqCmp {α β} [LinearOrderₓ α] [LinearOrderₓ β] (f : α → β) (g : β → α)
    (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
  have gf : ∀ a : α, a = g (f a) := by
    intro
    rw [← cmp_eq_eq_iff, h, cmp_self_eq_eq]
  { toFun := f, invFun := g, left_inv := fun a => (gf a).symm,
    right_inv := by
      intro
      rw [← cmp_eq_eq_iff, ← h, cmp_self_eq_eq],
    map_rel_iff' := by
      intros
      apply le_iff_le_of_cmp_eq_cmp
      convert (h _ _).symm
      apply gf }

/-- To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is enough to show
    that `g` is the inverse of `f`-/
def ofHomInv {F G : Type _} [OrderHomClass F α β] [OrderHomClass G β α] (f : F) (g : G)
    (h₁ : (f : α →o β).comp (g : β →o α) = OrderHom.id) (h₂ : (g : β →o α).comp (f : α →o β) = OrderHom.id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := FunLike.congr_fun h₂
  right_inv := FunLike.congr_fun h₁
  map_rel_iff' := fun a b =>
    ⟨fun h => by
      replace h := map_rel g h
      rwa [Equivₓ.coe_fn_mk, show g (f a) = (g : β →o α).comp (f : α →o β) a from rfl,
        show g (f b) = (g : β →o α).comp (f : α →o β) b from rfl, h₂] at h,
      fun h => (f : α →o β).Monotone h⟩

/-- Order isomorphism between two equal sets. -/
def setCongr (s t : Set α) (h : s = t) : s ≃o t where
  toEquiv := Equivₓ.setCongr h
  map_rel_iff' := fun x y => Iff.rfl

/-- Order isomorphism between `univ : set α` and `α`. -/
def Set.univ : (Set.Univ : Set α) ≃o α where
  toEquiv := Equivₓ.Set.univ α
  map_rel_iff' := fun x y => Iff.rfl

/-- Order isomorphism between `α → β` and `β`, where `α` has a unique element. -/
@[simps toEquiv apply]
def funUnique (α β : Type _) [Unique α] [Preorderₓ β] : (α → β) ≃o β where
  toEquiv := Equivₓ.funUnique α β
  map_rel_iff' := fun f g => by
    simp [← Pi.le_def, ← Unique.forall_iff]

@[simp]
theorem fun_unique_symm_apply {α β : Type _} [Unique α] [Preorderₓ β] :
    ((funUnique α β).symm : β → α → β) = Function.const α :=
  rfl

end OrderIso

namespace Equivₓ

variable [Preorderₓ α] [Preorderₓ β]

/-- If `e` is an equivalence with monotone forward and inverse maps, then `e` is an
order isomorphism. -/
def toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β :=
  ⟨e, fun x y =>
    ⟨fun h => by
      simpa only [← e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩

@[simp]
theorem coe_to_order_iso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : ⇑(e.toOrderIso h₁ h₂) = e :=
  rfl

@[simp]
theorem to_order_iso_to_equiv (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : (e.toOrderIso h₁ h₂).toEquiv = e :=
  rfl

end Equivₓ

/-- If a function `f` is strictly monotone on a set `s`, then it defines an order isomorphism
between `s` and its image. -/
protected noncomputable def StrictMonoOn.orderIso {α β} [LinearOrderₓ α] [Preorderₓ β] (f : α → β) (s : Set α)
    (hf : StrictMonoOn f s) : s ≃o f '' s where
  toEquiv := hf.InjOn.bij_on_image.Equiv _
  map_rel_iff' := fun x y => hf.le_iff_le x.2 y.2

namespace StrictMono

variable {α β} [LinearOrderₓ α] [Preorderₓ β]

variable (f : α → β) (h_mono : StrictMono f) (h_surj : Function.Surjective f)

/-- A strictly monotone function from a linear order is an order isomorphism between its domain and
its range. -/
@[simps apply]
protected noncomputable def orderIso : α ≃o Set.Range f where
  toEquiv := Equivₓ.ofInjective f h_mono.Injective
  map_rel_iff' := fun a b => h_mono.le_iff_le

/-- A strictly monotone surjective function from a linear order is an order isomorphism. -/
noncomputable def orderIsoOfSurjective : α ≃o β :=
  (h_mono.OrderIso f).trans <| (OrderIso.setCongr _ _ h_surj.range_eq).trans OrderIso.Set.univ

@[simp]
theorem coe_order_iso_of_surjective : (orderIsoOfSurjective f h_mono h_surj : α → β) = f :=
  rfl

@[simp]
theorem order_iso_of_surjective_symm_apply_self (a : α) : (orderIsoOfSurjective f h_mono h_surj).symm (f a) = a :=
  (orderIsoOfSurjective f h_mono h_surj).symm_apply_apply _

theorem order_iso_of_surjective_self_symm_apply (b : β) : f ((orderIsoOfSurjective f h_mono h_surj).symm b) = b :=
  (orderIsoOfSurjective f h_mono h_surj).apply_symm_apply _

/-- A strictly monotone function with a right inverse is an order isomorphism. -/
@[simps (config := { fullyApplied := False })]
def orderIsoOfRightInverse (g : β → α) (hg : Function.RightInverse g f) : α ≃o β :=
  { OrderEmbedding.ofStrictMono f h_mono with toFun := f, invFun := g, left_inv := fun x => h_mono.Injective <| hg _,
    right_inv := hg }

end StrictMono

/-- An order isomorphism is also an order isomorphism between dual orders. -/
protected def OrderIso.dual [LE α] [LE β] (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨f.toEquiv, fun _ _ => f.map_rel_iff⟩

section LatticeIsos

theorem OrderIso.map_bot' [LE α] [PartialOrderₓ β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x ≤ x')
    (hy : ∀ y', y ≤ y') : f x = y := by
  refine' le_antisymmₓ _ (hy _)
  rw [← f.apply_symm_apply y, f.map_rel_iff]
  apply hx

theorem OrderIso.map_bot [LE α] [PartialOrderₓ β] [OrderBot α] [OrderBot β] (f : α ≃o β) : f ⊥ = ⊥ :=
  f.map_bot' (fun _ => bot_le) fun _ => bot_le

theorem OrderIso.map_top' [LE α] [PartialOrderₓ β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x' ≤ x)
    (hy : ∀ y', y' ≤ y) : f x = y :=
  f.dual.map_bot' hx hy

theorem OrderIso.map_top [LE α] [PartialOrderₓ β] [OrderTop α] [OrderTop β] (f : α ≃o β) : f ⊤ = ⊤ :=
  f.dual.map_bot

theorem OrderEmbedding.map_inf_le [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α) : f (x⊓y) ≤ f x⊓f y :=
  f.Monotone.map_inf_le x y

theorem OrderEmbedding.le_map_sup [SemilatticeSup α] [SemilatticeSup β] (f : α ↪o β) (x y : α) : f x⊔f y ≤ f (x⊔y) :=
  f.Monotone.le_map_sup x y

theorem OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α) : f (x⊓y) = f x⊓f y := by
  refine' (f.to_order_embedding.map_inf_le x y).antisymm _
  simpa [f.symm.le_iff_le] using f.symm.to_order_embedding.map_inf_le (f x) (f y)

theorem OrderIso.map_sup [SemilatticeSup α] [SemilatticeSup β] (f : α ≃o β) (x y : α) : f (x⊔y) = f x⊔f y :=
  f.dual.map_inf x y

/-- Note that this goal could also be stated `(disjoint on f) a b` -/
theorem Disjoint.map_order_iso [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β] {a b : α} (f : α ≃o β)
    (ha : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [Disjoint, ← f.map_inf, ← f.map_bot]
  exact f.monotone ha

/-- Note that this goal could also be stated `(codisjoint on f) a b` -/
theorem Codisjoint.map_order_iso [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β] {a b : α} (f : α ≃o β)
    (ha : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [Codisjoint, ← f.map_sup, ← f.map_top]
  exact f.monotone ha

@[simp]
theorem disjoint_map_order_iso_iff [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β] {a b : α}
    (f : α ≃o β) : Disjoint (f a) (f b) ↔ Disjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_order_iso f.symm, fun h => h.map_order_iso f⟩

@[simp]
theorem codisjoint_map_order_iso_iff [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β] {a b : α}
    (f : α ≃o β) : Codisjoint (f a) (f b) ↔ Codisjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_order_iso f.symm, fun h => h.map_order_iso f⟩

namespace WithBot

/-- Taking the dual then adding `⊥` is the same as adding `⊤` then taking the dual. -/
protected def toDualTop [LE α] : WithBot αᵒᵈ ≃o (WithTop α)ᵒᵈ :=
  OrderIso.refl _

@[simp]
theorem to_dual_top_coe [LE α] (a : α) : WithBot.toDualTop ↑(toDual a) = toDual (a : WithTop α) :=
  rfl

@[simp]
theorem to_dual_top_symm_coe [LE α] (a : α) : WithBot.toDualTop.symm (toDual (a : WithTop α)) = ↑(toDual a) :=
  rfl

end WithBot

namespace WithTop

/-- Taking the dual then adding `⊤` is the same as adding `⊥` then taking the dual. -/
protected def toDualBot [LE α] : WithTop αᵒᵈ ≃o (WithBot α)ᵒᵈ :=
  OrderIso.refl _

@[simp]
theorem to_dual_bot_coe [LE α] (a : α) : WithTop.toDualBot ↑(toDual a) = toDual (a : WithBot α) :=
  rfl

@[simp]
theorem to_dual_bot_symm_coe [LE α] (a : α) : WithTop.toDualBot.symm (toDual (a : WithBot α)) = ↑(toDual a) :=
  rfl

end WithTop

namespace OrderIso

variable [PartialOrderₓ α] [PartialOrderₓ β] [PartialOrderₓ γ]

/-- A version of `equiv.option_congr` for `with_top`. -/
@[simps apply]
def withTopCongr (e : α ≃o β) : WithTop α ≃o WithTop β :=
  { e.toOrderEmbedding.with_top_map with toEquiv := e.toEquiv.optionCongr }

@[simp]
theorem with_top_congr_refl : (OrderIso.refl α).withTopCongr = OrderIso.refl _ :=
  RelIso.to_equiv_injective Equivₓ.option_congr_refl

@[simp]
theorem with_top_congr_symm (e : α ≃o β) : e.withTopCongr.symm = e.symm.withTopCongr :=
  RelIso.to_equiv_injective e.toEquiv.option_congr_symm

@[simp]
theorem with_top_congr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    e₁.withTopCongr.trans e₂.withTopCongr = (e₁.trans e₂).withTopCongr :=
  RelIso.to_equiv_injective <| e₁.toEquiv.option_congr_trans e₂.toEquiv

/-- A version of `equiv.option_congr` for `with_bot`. -/
@[simps apply]
def withBotCongr (e : α ≃o β) : WithBot α ≃o WithBot β :=
  { e.toOrderEmbedding.with_bot_map with toEquiv := e.toEquiv.optionCongr }

@[simp]
theorem with_bot_congr_refl : (OrderIso.refl α).withBotCongr = OrderIso.refl _ :=
  RelIso.to_equiv_injective Equivₓ.option_congr_refl

@[simp]
theorem with_bot_congr_symm (e : α ≃o β) : e.withBotCongr.symm = e.symm.withBotCongr :=
  RelIso.to_equiv_injective e.toEquiv.option_congr_symm

@[simp]
theorem with_bot_congr_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) :
    e₁.withBotCongr.trans e₂.withBotCongr = (e₁.trans e₂).withBotCongr :=
  RelIso.to_equiv_injective <| e₁.toEquiv.option_congr_trans e₂.toEquiv

end OrderIso

section BoundedOrder

variable [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] (f : α ≃o β)

include f

theorem OrderIso.is_compl {x y : α} (h : IsCompl x y) : IsCompl (f x) (f y) :=
  ⟨h.1.map_order_iso _, h.2.map_order_iso _⟩

theorem OrderIso.is_compl_iff {x y : α} : IsCompl x y ↔ IsCompl (f x) (f y) :=
  ⟨f.IsCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.IsCompl h⟩

theorem OrderIso.is_complemented [IsComplemented α] : IsComplemented β :=
  ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_is_compl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    refine' ⟨f y, f.symm.is_compl_iff.2 hy⟩⟩

theorem OrderIso.is_complemented_iff : IsComplemented α ↔ IsComplemented β :=
  ⟨by
    intro
    exact f.is_complemented, by
    intro
    exact f.symm.is_complemented⟩

end BoundedOrder

end LatticeIsos

section BooleanAlgebra

variable (α) [BooleanAlgebra α]

/-- Taking complements as an order isomorphism to the order dual. -/
@[simps]
def OrderIso.compl : α ≃o αᵒᵈ where
  toFun := OrderDual.toDual ∘ compl
  invFun := compl ∘ OrderDual.ofDual
  left_inv := compl_compl
  right_inv := compl_compl
  map_rel_iff' := fun x y => compl_le_compl_iff_le

theorem compl_strict_anti : StrictAnti (compl : α → α) :=
  (OrderIso.compl α).StrictMono

theorem compl_antitone : Antitone (compl : α → α) :=
  (OrderIso.compl α).Monotone

end BooleanAlgebra

