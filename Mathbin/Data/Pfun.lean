/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Jeremy Avigad, Simon Hudon
-/
import Mathbin.Data.Part
import Mathbin.Data.Rel

/-!
# Partial functions

This file defines partial functions. Partial functions are like functions, except they can also be
"undefined" on some inputs. We define them as functions `α → part β`.

## Definitions

* `pfun α β`: Type of partial functions from `α` to `β`. Defined as `α → part β` and denoted
  `α →. β`.
* `pfun.dom`: Domain of a partial function. Set of values on which it is defined. Not to be confused
  with the domain of a function `α → β`, which is a type (`α` presently).
* `pfun.fn`: Evaluation of a partial function. Takes in an element and a proof it belongs to the
  partial function's `dom`.
* `pfun.as_subtype`: Returns a partial function as a function from its `dom`.
* `pfun.to_subtype`: Restricts the codomain of a function to a subtype.
* `pfun.eval_opt`: Returns a partial function with a decidable `dom` as a function `a → option β`.
* `pfun.lift`: Turns a function into a partial function.
* `pfun.id`: The identity as a partial function.
* `pfun.comp`: Composition of partial functions.
* `pfun.restrict`: Restriction of a partial function to a smaller `dom`.
* `pfun.res`: Turns a function into a partial function with a prescribed domain.
* `pfun.fix` : First return map of a partial function `f : α →. β ⊕ α`.
* `pfun.fix_induction`: A recursion principle for `pfun.fix`.

### Partial functions as relations

Partial functions can be considered as relations, so we specialize some `rel` definitions to `pfun`:
* `pfun.image`: Image of a set under a partial function.
* `pfun.ran`: Range of a partial function.
* `pfun.preimage`: Preimage of a set under a partial function.
* `pfun.core`: Core of a set under a partial function.
* `pfun.graph`: Graph of a partial function `a →. β`as a `set (α × β)`.
* `pfun.graph'`: Graph of a partial function `a →. β`as a `rel α β`.

### `pfun α` as a monad

Monad operations:
* `pfun.pure`: The monad `pure` function, the constant `x` function.
* `pfun.bind`: The monad `bind` function, pointwise `part.bind`
* `pfun.map`: The monad `map` function, pointwise `part.map`.
-/


open Function

/-- `pfun α β`, or `α →. β`, is the type of partial functions from
  `α` to `β`. It is defined as `α → part β`. -/
def Pfun (α β : Type _) :=
  α → Part β

-- mathport name: «expr →. »
infixr:25 " →. " => Pfun

namespace Pfun

variable {α β γ δ : Type _}

instance : Inhabited (α →. β) :=
  ⟨fun a => Part.none⟩

/-- The domain of a partial function -/
def Dom (f : α →. β) : Set α :=
  { a | (f a).Dom }

@[simp]
theorem mem_dom (f : α →. β) (x : α) : x ∈ Dom f ↔ ∃ y, y ∈ f x := by
  simp [← dom, ← Part.dom_iff_mem]

theorem dom_eq (f : α →. β) : Dom f = { x | ∃ y, y ∈ f x } :=
  Set.ext (mem_dom f)

/-- Evaluate a partial function -/
def fn (f : α →. β) (a : α) : Dom f a → β :=
  (f a).get

@[simp]
theorem fn_apply (f : α →. β) (a : α) : f.fn a = (f a).get :=
  rfl

/-- Evaluate a partial function to return an `option` -/
def evalOpt (f : α →. β) [D : DecidablePred (· ∈ Dom f)] (x : α) : Option β :=
  @Part.toOption _ _ (D x)

/-- Partial function extensionality -/
theorem ext' {f g : α →. β} (H1 : ∀ a, a ∈ Dom f ↔ a ∈ Dom g) (H2 : ∀ a p q, f.fn a p = g.fn a q) : f = g :=
  funext fun a => Part.ext' (H1 a) (H2 a)

theorem ext {f g : α →. β} (H : ∀ a b, b ∈ f a ↔ b ∈ g a) : f = g :=
  funext fun a => Part.ext (H a)

/-- Turns a partial function into a function out of its domain. -/
def asSubtype (f : α →. β) (s : f.Dom) : β :=
  f.fn s s.2

/-- The type of partial functions `α →. β` is equivalent to
the type of pairs `(p : α → Prop, f : subtype p → β)`. -/
def equivSubtype : (α →. β) ≃ Σp : α → Prop, Subtype p → β :=
  ⟨fun f => ⟨fun a => (f a).Dom, asSubtype f⟩, fun f x => ⟨f.1 x, fun h => f.2 ⟨x, h⟩⟩, fun f =>
    funext fun a => Part.eta _, fun ⟨p, f⟩ => by
    dsimp' <;> congr <;> funext a <;> cases a <;> rfl⟩

theorem as_subtype_eq_of_mem {f : α →. β} {x : α} {y : β} (fxy : y ∈ f x) (domx : x ∈ f.Dom) :
    f.asSubtype ⟨x, domx⟩ = y :=
  Part.mem_unique (Part.get_mem _) fxy

/-- Turn a total function into a partial function. -/
protected def lift (f : α → β) : α →. β := fun a => Part.some (f a)

instance : Coe (α → β) (α →. β) :=
  ⟨Pfun.lift⟩

@[simp]
theorem lift_eq_coe (f : α → β) : Pfun.lift f = f :=
  rfl

@[simp]
theorem coe_val (f : α → β) (a : α) : (f : α →. β) a = Part.some (f a) :=
  rfl

@[simp]
theorem dom_coe (f : α → β) : (f : α →. β).Dom = Set.Univ :=
  rfl

theorem coe_injective : Injective (coe : (α → β) → α →. β) := fun f g h =>
  funext fun a => Part.some_injective <| congr_fun h a

/-- Graph of a partial function `f` as the set of pairs `(x, f x)` where `x` is in the domain of
`f`. -/
def Graph (f : α →. β) : Set (α × β) :=
  { p | p.2 ∈ f p.1 }

/-- Graph of a partial function as a relation. `x` and `y` are related iff `f x` is defined and
"equals" `y`. -/
def Graph' (f : α →. β) : Rel α β := fun x y => y ∈ f x

/-- The range of a partial function is the set of values
  `f x` where `x` is in the domain of `f`. -/
def Ran (f : α →. β) : Set β :=
  { b | ∃ a, b ∈ f a }

/-- Restrict a partial function to a smaller domain. -/
def restrict (f : α →. β) {p : Set α} (H : p ⊆ f.Dom) : α →. β := fun x => (f x).restrict (x ∈ p) (@H x)

@[simp]
theorem mem_restrict {f : α →. β} {s : Set α} (h : s ⊆ f.Dom) (a : α) (b : β) : b ∈ f.restrict h a ↔ a ∈ s ∧ b ∈ f a :=
  by
  simp [← restrict]

/-- Turns a function into a partial function with a prescribed domain. -/
def res (f : α → β) (s : Set α) : α →. β :=
  (Pfun.lift f).restrict s.subset_univ

theorem mem_res (f : α → β) (s : Set α) (a : α) (b : β) : b ∈ res f s a ↔ a ∈ s ∧ f a = b := by
  simp [← res, ← @eq_comm _ b]

theorem res_univ (f : α → β) : Pfun.res f Set.Univ = f :=
  rfl

theorem dom_iff_graph (f : α →. β) (x : α) : x ∈ f.Dom ↔ ∃ y, (x, y) ∈ f.Graph :=
  Part.dom_iff_mem

theorem lift_graph {f : α → β} {a b} : (a, b) ∈ (f : α →. β).Graph ↔ f a = b :=
  show (∃ h : True, f a = b) ↔ f a = b by
    simp

/-- The monad `pure` function, the total constant `x` function -/
protected def pure (x : β) : α →. β := fun _ => Part.some x

/-- The monad `bind` function, pointwise `part.bind` -/
def bind (f : α →. β) (g : β → α →. γ) : α →. γ := fun a => (f a).bind fun b => g b a

@[simp]
theorem bind_apply (f : α →. β) (g : β → α →. γ) (a : α) : f.bind g a = (f a).bind fun b => g b a :=
  rfl

/-- The monad `map` function, pointwise `part.map` -/
def map (f : β → γ) (g : α →. β) : α →. γ := fun a => (g a).map f

instance : Monadₓ (Pfun α) where
  pure := @Pfun.pure _
  bind := @Pfun.bind _
  map := @Pfun.map _

instance : IsLawfulMonad (Pfun α) where
  bind_pure_comp_eq_map := fun β γ f x => funext fun a => Part.bind_some_eq_map _ _
  id_map := fun β f => by
    funext a <;> dsimp' [← Functor.map, ← Pfun.map] <;> cases f a <;> rfl
  pure_bind := fun β γ x f => funext fun a => Part.bind_some.{u_1, u_2} _ (f x)
  bind_assoc := fun β γ δ f g k => funext fun a => (f a).bind_assoc (fun b => g b a) fun b => k b a

theorem pure_defined (p : Set α) (x : β) : p ⊆ (@Pfun.pure α _ x).Dom :=
  p.subset_univ

theorem bind_defined {α β γ} (p : Set α) {f : α →. β} {g : β → α →. γ} (H1 : p ⊆ f.Dom) (H2 : ∀ x, p ⊆ (g x).Dom) :
    p ⊆ (f >>= g).Dom := fun a ha => (⟨H1 ha, H2 _ ha⟩ : (f >>= g).Dom a)

/-- First return map. Transforms a partial function `f : α →. β ⊕ α` into the partial function
`α →. β` which sends `a : α` to the first value in `β` it hits by iterating `f`, if such a value
exists. By abusing notation to illustrate, either `f a` is in the `β` part of `β ⊕ α` (in which
case `f.fix a` returns `f a`), or it is undefined (in which case `f.fix a` is undefined as well), or
it is in the `α` part of `β ⊕ α` (in which case we repeat the procedure, so `f.fix a` will return
`f.fix (f a)`). -/
def fix (f : α →. Sum β α) : α →. β := fun a =>
  (Part.assert (Acc (fun x y => Sum.inr x ∈ f y) a)) fun h =>
    @WellFounded.fixF _ (fun x y => Sum.inr x ∈ f y) _
      (fun a IH =>
        (Part.assert (f a).Dom) fun hf => by
          cases' e : (f a).get hf with b a' <;> [exact Part.some b, exact IH _ ⟨hf, e⟩])
      a h

theorem dom_of_mem_fix {f : α →. Sum β α} {a : α} {b : β} (h : b ∈ f.fix a) : (f a).Dom := by
  let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
  rw [WellFounded.fix_F_eq] at h₂ <;> exact h₂.fst.fst

theorem mem_fix_iff {f : α →. Sum β α} {a : α} {b : β} :
    b ∈ f.fix a ↔ Sum.inl b ∈ f a ∨ ∃ a', Sum.inr a' ∈ f a ∧ b ∈ f.fix a' :=
  ⟨fun h => by
    let ⟨h₁, h₂⟩ := Part.mem_assert_iff.1 h
    rw [WellFounded.fix_F_eq] at h₂
    simp at h₂
    cases' h₂ with h₂ h₃
    cases' e : (f a).get h₂ with b' a' <;> simp [← e] at h₃
    · subst b'
      refine' Or.inl ⟨h₂, e⟩
      
    · exact Or.inr ⟨a', ⟨_, e⟩, Part.mem_assert _ h₃⟩
      ,
    fun h => by
    simp [← fix]
    rcases h with (⟨h₁, h₂⟩ | ⟨a', h, h₃⟩)
    · refine' ⟨⟨_, fun y h' => _⟩, _⟩
      · injection Part.mem_unique ⟨h₁, h₂⟩ h'
        
      · rw [WellFounded.fix_F_eq]
        simp [← h₁, ← h₂]
        
      
    · simp [← fix] at h₃
      cases' h₃ with h₃ h₄
      refine' ⟨⟨_, fun y h' => _⟩, _⟩
      · injection Part.mem_unique h h' with e
        exact e ▸ h₃
        
      · cases' h with h₁ h₂
        rw [WellFounded.fix_F_eq]
        simp [← h₁, ← h₂, ← h₄]
        
      ⟩

/-- If advancing one step from `a` leads to `b : β`, then `f.fix a = b` -/
theorem fix_stop {f : α →. Sum β α} (a : α) {b : β} (hb : Sum.inl b ∈ f a) : b ∈ f.fix a := by
  rw [Pfun.mem_fix_iff]
  exact Or.inl hb

/-- If advancing one step from `a` on `f` leads to `a' : α`, then `f.fix a = f.fix a'` -/
theorem fix_fwd {f : α →. Sum β α} (a a' : α) (ha' : Sum.inr a' ∈ f a) : f.fix a = f.fix a' := by
  ext b
  constructor
  · intro h
    obtain h' | ⟨a, h', e'⟩ := mem_fix_iff.1 h <;> cases Part.mem_unique ha' h'
    exact e'
    
  · intro h
    rw [Pfun.mem_fix_iff]
    right
    use a'
    exact ⟨ha', h⟩
    

/-- A recursion principle for `pfun.fix`. -/
@[elab_as_eliminator]
def fixInduction {f : α →. Sum β α} {b : β} {C : α → Sort _} {a : α} (h : b ∈ f.fix a)
    (H : ∀ a', b ∈ f.fix a' → (∀ a'', Sum.inr a'' ∈ f a' → C a'') → C a') : C a := by
  replace h := Part.mem_assert_iff.1 h
  have := h.snd
  revert this
  induction' h.fst with a ha IH
  intro h₂
  have fb : b ∈ f.fix a := Part.mem_assert_iff.2 ⟨⟨_, ha⟩, h₂⟩
  refine' H a fb fun a'' fa'' => _
  have ha'' : b ∈ f.fix a'' := by
    rwa [fix_fwd _ _ fa''] at fb
  have := (Part.mem_assert_iff.1 ha'').snd
  exact IH _ fa'' ⟨ha _ fa'', this⟩ this

/-- Another induction lemma for `b ∈ f.fix a` which allows one to prove a predicate `P` holds for
`a` given that `f a` inherits `P` from `a` and `P` holds for preimages of `b`.
-/
@[elab_as_eliminator]
def fixInduction' (f : α →. Sum β α) (b : β) {C : α → Sort _} {a : α} (h : b ∈ f.fix a)
    (hbase : ∀ a_final : α, Sum.inl b ∈ f a_final → C a_final)
    (hind : ∀ a₀ a₁ : α, b ∈ f.fix a₁ → Sum.inr a₁ ∈ f a₀ → C a₁ → C a₀) : C a := by
  refine' fix_induction h fun a' h ih => _
  cases' e : (f a').get (dom_of_mem_fix h) with b' a'' <;> replace e : _ ∈ f a' := ⟨_, e⟩
  · apply hbase
    convert e
    exact Part.mem_unique h (fix_stop _ e)
    
  · refine' hind _ _ _ e (ih _ e)
    rwa [fix_fwd _ _ e] at h
    

variable (f : α →. β)

/-- Image of a set under a partial function. -/
def Image (s : Set α) : Set β :=
  f.Graph'.Image s

theorem image_def (s : Set α) : f.Image s = { y | ∃ x ∈ s, y ∈ f x } :=
  rfl

theorem mem_image (y : β) (s : Set α) : y ∈ f.Image s ↔ ∃ x ∈ s, y ∈ f x :=
  Iff.rfl

theorem image_mono {s t : Set α} (h : s ⊆ t) : f.Image s ⊆ f.Image t :=
  Rel.image_mono _ h

theorem image_inter (s t : Set α) : f.Image (s ∩ t) ⊆ f.Image s ∩ f.Image t :=
  Rel.image_inter _ s t

theorem image_union (s t : Set α) : f.Image (s ∪ t) = f.Image s ∪ f.Image t :=
  Rel.image_union _ s t

/-- Preimage of a set under a partial function. -/
def Preimage (s : Set β) : Set α :=
  Rel.Image (fun x y => x ∈ f y) s

theorem preimage_def (s : Set β) : f.Preimage s = { x | ∃ y ∈ s, y ∈ f x } :=
  rfl

@[simp]
theorem mem_preimage (s : Set β) (x : α) : x ∈ f.Preimage s ↔ ∃ y ∈ s, y ∈ f x :=
  Iff.rfl

theorem preimage_subset_dom (s : Set β) : f.Preimage s ⊆ f.Dom := fun x ⟨y, ys, fxy⟩ => Part.dom_iff_mem.mpr ⟨y, fxy⟩

theorem preimage_mono {s t : Set β} (h : s ⊆ t) : f.Preimage s ⊆ f.Preimage t :=
  Rel.preimage_mono _ h

theorem preimage_inter (s t : Set β) : f.Preimage (s ∩ t) ⊆ f.Preimage s ∩ f.Preimage t :=
  Rel.preimage_inter _ s t

theorem preimage_union (s t : Set β) : f.Preimage (s ∪ t) = f.Preimage s ∪ f.Preimage t :=
  Rel.preimage_union _ s t

theorem preimage_univ : f.Preimage Set.Univ = f.Dom := by
  ext <;> simp [← mem_preimage, ← mem_dom]

/-- Core of a set `s : set β` with respect to a partial function `f : α →. β`. Set of all `a : α`
such that `f a ∈ s`, if `f a` is defined. -/
def Core (s : Set β) : Set α :=
  f.Graph'.Core s

theorem core_def (s : Set β) : f.Core s = { x | ∀ y, y ∈ f x → y ∈ s } :=
  rfl

@[simp]
theorem mem_core (x : α) (s : Set β) : x ∈ f.Core s ↔ ∀ y, y ∈ f x → y ∈ s :=
  Iff.rfl

theorem compl_dom_subset_core (s : Set β) : f.Domᶜ ⊆ f.Core s := fun x hx y fxy =>
  absurd ((mem_dom f x).mpr ⟨y, fxy⟩) hx

theorem core_mono {s t : Set β} (h : s ⊆ t) : f.Core s ⊆ f.Core t :=
  Rel.core_mono _ h

theorem core_inter (s t : Set β) : f.Core (s ∩ t) = f.Core s ∩ f.Core t :=
  Rel.core_inter _ s t

theorem mem_core_res (f : α → β) (s : Set α) (t : Set β) (x : α) : x ∈ (res f s).Core t ↔ x ∈ s → f x ∈ t := by
  simp [← mem_core, ← mem_res]

section

open Classical

theorem core_res (f : α → β) (s : Set α) (t : Set β) : (res f s).Core t = sᶜ ∪ f ⁻¹' t := by
  ext
  rw [mem_core_res]
  by_cases' h : x ∈ s <;> simp [← h]

end

theorem core_restrict (f : α → β) (s : Set β) : (f : α →. β).Core s = s.Preimage f := by
  ext x <;> simp [← core_def]

theorem preimage_subset_core (f : α →. β) (s : Set β) : f.Preimage s ⊆ f.Core s := fun x ⟨y, ys, fxy⟩ y' fxy' =>
  have : y = y' := Part.mem_unique fxy fxy'
  this ▸ ys

theorem preimage_eq (f : α →. β) (s : Set β) : f.Preimage s = f.Core s ∩ f.Dom :=
  Set.eq_of_subset_of_subset (Set.subset_inter (f.preimage_subset_core s) (f.preimage_subset_dom s))
    fun x ⟨xcore, xdom⟩ =>
    let y := (f x).get xdom
    have ys : y ∈ s := xcore _ (Part.get_mem _)
    show x ∈ f.Preimage s from ⟨(f x).get xdom, ys, Part.get_mem _⟩

theorem core_eq (f : α →. β) (s : Set β) : f.Core s = f.Preimage s ∪ f.Domᶜ := by
  rw [preimage_eq, Set.union_distrib_right, Set.union_comm (dom f), Set.compl_union_self, Set.inter_univ,
    Set.union_eq_self_of_subset_right (f.compl_dom_subset_core s)]

theorem preimage_as_subtype (f : α →. β) (s : Set β) : f.asSubtype ⁻¹' s = Subtype.val ⁻¹' f.Preimage s := by
  ext x
  simp only [← Set.mem_preimage, ← Set.mem_set_of_eq, ← Pfun.asSubtype, ← Pfun.mem_preimage]
  show f.fn x.val _ ∈ s ↔ ∃ y ∈ s, y ∈ f x.val
  exact
    Iff.intro (fun h => ⟨_, h, Part.get_mem _⟩) fun ⟨y, ys, fxy⟩ =>
      have : f.fn x.val x.property ∈ f x.val := Part.get_mem _
      Part.mem_unique fxy this ▸ ys

/-- Turns a function into a partial function to a subtype. -/
def toSubtype (p : β → Prop) (f : α → β) : α →. Subtype p := fun a => ⟨p (f a), Subtype.mk _⟩

@[simp]
theorem dom_to_subtype (p : β → Prop) (f : α → β) : (toSubtype p f).Dom = { a | p (f a) } :=
  rfl

@[simp]
theorem to_subtype_apply (p : β → Prop) (f : α → β) (a : α) : toSubtype p f a = ⟨p (f a), Subtype.mk _⟩ :=
  rfl

theorem dom_to_subtype_apply_iff {p : β → Prop} {f : α → β} {a : α} : (toSubtype p f a).Dom ↔ p (f a) :=
  Iff.rfl

theorem mem_to_subtype_iff {p : β → Prop} {f : α → β} {a : α} {b : Subtype p} : b ∈ toSubtype p f a ↔ ↑b = f a := by
  rw [to_subtype_apply, Part.mem_mk_iff, exists_subtype_mk_eq_iff, eq_comm]

/-- The identity as a partial function -/
protected def id (α : Type _) : α →. α :=
  Part.some

@[simp]
theorem coe_id (α : Type _) : ((id : α → α) : α →. α) = Pfun.id α :=
  rfl

@[simp]
theorem id_apply (a : α) : Pfun.id α a = Part.some a :=
  rfl

/-- Composition of partial functions as a partial function. -/
def comp (f : β →. γ) (g : α →. β) : α →. γ := fun a => (g a).bind f

@[simp]
theorem comp_apply (f : β →. γ) (g : α →. β) (a : α) : f.comp g a = (g a).bind f :=
  rfl

@[simp]
theorem id_comp (f : α →. β) : (Pfun.id β).comp f = f :=
  ext fun _ _ => by
    simp

@[simp]
theorem comp_id (f : α →. β) : f.comp (Pfun.id α) = f :=
  ext fun _ _ => by
    simp

@[simp]
theorem dom_comp (f : β →. γ) (g : α →. β) : (f.comp g).Dom = g.Preimage f.Dom := by
  ext
  simp_rw [mem_preimage, mem_dom, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_distrib_right]
  rw [exists_comm]
  simp_rw [And.comm]

@[simp]
theorem preimage_comp (f : β →. γ) (g : α →. β) (s : Set γ) : (f.comp g).Preimage s = g.Preimage (f.Preimage s) := by
  ext
  simp_rw [mem_preimage, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_distrib_right, ←
    exists_and_distrib_left]
  rw [exists_comm]
  simp_rw [and_assoc, And.comm]

@[simp]
theorem _root_.part.bind_comp (f : β →. γ) (g : α →. β) (a : Part α) : a.bind (f.comp g) = (a.bind g).bind f := by
  ext c
  simp_rw [Part.mem_bind_iff, comp_apply, Part.mem_bind_iff, exists_prop, ← exists_and_distrib_right, ←
    exists_and_distrib_left]
  rw [exists_comm]
  simp_rw [and_assoc]

@[simp]
theorem comp_assoc (f : γ →. δ) (g : β →. γ) (h : α →. β) : (f.comp g).comp h = f.comp (g.comp h) :=
  ext fun _ _ => by
    simp only [← comp_apply, ← Part.bind_comp]

-- This can't be `simp`
theorem coe_comp (g : β → γ) (f : α → β) : ((g ∘ f : α → γ) : α →. γ) = (g : β →. γ).comp f :=
  ext fun _ _ => by
    simp only [← coe_val, ← comp_apply, ← Part.bind_some]

end Pfun

