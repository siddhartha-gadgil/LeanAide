/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
import Mathbin.Data.Sum.Order
import Mathbin.Order.InitialSeg
import Mathbin.SetTheory.Cardinal.Basic

/-!
# Ordinals

Ordinals are defined as equivalences of well-ordered sets under order isomorphism. They are endowed
with a total order, where an ordinal is smaller than another one if it embeds into it as an
initial segment (or, equivalently, in any way). This total order is well founded.

## Main definitions

* `ordinal`: the type of ordinals (in a given universe)
* `ordinal.type r`: given a well-founded order `r`, this is the corresponding ordinal
* `ordinal.typein r a`: given a well-founded order `r` on a type `α`, and `a : α`, the ordinal
  corresponding to all elements smaller than `a`.
* `enum r o h`: given a well-order `r` on a type `α`, and an ordinal `o` strictly smaller than
  the ordinal corresponding to `r` (this is the assumption `h`), returns the `o`-th element of `α`.
  In other words, the elements of `α` can be enumerated using ordinals up to `type r`.
* `ordinal.card o`: the cardinality of an ordinal `o`.
* `ordinal.lift` lifts an ordinal in universe `u` to an ordinal in universe `max u v`.
  For a version registering additionally that this is an initial segment embedding, see
  `ordinal.lift.initial_seg`.
  For a version regiserting that it is a principal segment embedding if `u < v`, see
  `ordinal.lift.principal_seg`.
* `ordinal.omega` or `ω` is the order type of `ℕ`. This definition is universe polymorphic:
  `ordinal.omega.{u} : ordinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.

* `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. The main properties of addition
  (and the other operations on ordinals) are stated and proved in `ordinal_arithmetic.lean`. Here,
  we only introduce it and prove its basic properties to deduce the fact that the order on ordinals
  is total (and well founded).
* `succ o` is the successor of the ordinal `o`.
* `ordinal.min`: the minimal element of a nonempty indexed family of ordinals
* `cardinal.ord c`: when `c` is a cardinal, `ord c` is the smallest ordinal with this cardinality.
  It is the canonical way to represent a cardinal with an ordinal.

A conditionally complete linear order with bot structure is registered on ordinals, where `⊥` is
`0`, the ordinal corresponding to the empty type, and `Inf` is the minimum for nonempty sets and `0`
for the empty set by convention.

## Notations

* `ω` is a notation for the first infinite ordinal in the locale `ordinal`.
-/


noncomputable section

open Function Cardinal Set Equivₓ Order

open Classical Cardinal InitialSeg

universe u v w

variable {α : Type _} {β : Type _} {γ : Type _} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop}

/-! ### Well order on an arbitrary type -/


section WellOrderingThm

parameter {σ : Type u}

open Function

theorem nonempty_embedding_to_cardinal : Nonempty (σ ↪ Cardinal.{u}) :=
  (Embedding.total _ _).resolve_left fun ⟨⟨f, hf⟩⟩ =>
    let g : σ → Cardinal.{u} := invFun f
    let ⟨x, (hx : g x = 2 ^ Sum g)⟩ := inv_fun_surjectiveₓ hf (2 ^ Sum g)
    have : g x ≤ Sum g := le_sum.{u, u} g x
    not_le_of_gtₓ
      (by
        rw [hx] <;> exact cantor _)
      this

/-- An embedding of any type to the set of cardinals. -/
def embeddingToCardinal : σ ↪ Cardinal.{u} :=
  Classical.choice nonempty_embedding_to_cardinal

/-- Any type can be endowed with a well order, obtained by pulling back the well order over
cardinals by some embedding. -/
def WellOrderingRel : σ → σ → Prop :=
  embeddingToCardinal ⁻¹'o (· < ·)

instance WellOrderingRel.is_well_order : IsWellOrder σ WellOrderingRel :=
  (RelEmbedding.preimage _ _).IsWellOrder

end WellOrderingThm

/-! ### Definition of ordinals -/


/-- Bundled structure registering a well order on a type. Ordinals will be defined as a quotient
of this type. -/
structure WellOrder : Type (u + 1) where
  α : Type u
  R : α → α → Prop
  wo : IsWellOrder α r

attribute [instance] WellOrder.wo

namespace WellOrder

instance : Inhabited WellOrder :=
  ⟨⟨Pempty, _, EmptyRelation.is_well_order⟩⟩

end WellOrder

/-- Equivalence relation on well orders on arbitrary types in universe `u`, given by order
isomorphism. -/
instance Ordinal.isEquivalent : Setoidₓ WellOrder where
  R := fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => Nonempty (r ≃r s)
  iseqv :=
    ⟨fun ⟨α, r, _⟩ => ⟨RelIso.refl _⟩, fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩ => ⟨e.symm⟩,
      fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `ordinal.{u}` is the type of well orders in `Type u`, up to order isomorphism. -/
def Ordinal : Type (u + 1) :=
  Quotientₓ Ordinal.isEquivalent

instance hasWellFoundedOut (o : Ordinal) : HasWellFounded o.out.α :=
  ⟨o.out.R, o.out.wo.wf⟩

instance linearOrderOut (o : Ordinal) : LinearOrderₓ o.out.α :=
  IsWellOrder.linearOrder o.out.R

instance is_well_order_out_lt (o : Ordinal) : IsWellOrder o.out.α (· < ·) :=
  o.out.wo

namespace Ordinal

/-- The order type of a well order is an ordinal. -/
def type (r : α → α → Prop) [wo : IsWellOrder α r] : Ordinal :=
  ⟦⟨α, r, wo⟩⟧

/-- The order type of an element inside a well order. For the embedding as a principal segment, see
`typein.principal_seg`. -/
def typein (r : α → α → Prop) [IsWellOrder α r] (a : α) : Ordinal :=
  type (Subrel r { b | r b a })

@[simp]
theorem type_def' (w : WellOrder) : ⟦w⟧ = type w.R := by
  cases w
  rfl

@[simp]
theorem type_def (r) [wo : IsWellOrder α r] : (⟦⟨α, r, wo⟩⟧ : Ordinal) = type r :=
  rfl

theorem type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r = type s ↔ Nonempty (r ≃r s) :=
  Quotientₓ.eq

theorem _root_.rel_iso.ordinal_type_eq {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (h : r ≃r s) : type r = type s :=
  type_eq.2 ⟨h⟩

@[simp]
theorem type_lt (o : Ordinal) : type ((· < ·) : o.out.α → o.out.α → Prop) = o :=
  (type_def' _).symm.trans <| Quotientₓ.out_eq o

@[simp]
theorem type_preimage {α β : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) : type (f ⁻¹'o r) = type r :=
  (RelIso.preimage f r).ordinal_type_eq

@[elab_as_eliminator]
theorem induction_on {C : Ordinal → Prop} (o : Ordinal) (H : ∀ (α r) [IsWellOrder α r], C (type r)) : C o :=
  (Quot.induction_on o) fun ⟨α, r, wo⟩ => @H α r wo

/-! ### The order on ordinals -/


instance : PartialOrderₓ Ordinal where
  le := fun a b =>
    (Quotientₓ.liftOn₂ a b fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => Nonempty (r ≼i s))
      fun ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩ =>
      propext
        ⟨fun ⟨h⟩ => ⟨(InitialSeg.ofIso f.symm).trans <| h.trans (InitialSeg.ofIso g)⟩, fun ⟨h⟩ =>
          ⟨(InitialSeg.ofIso f).trans <| h.trans (InitialSeg.ofIso g.symm)⟩⟩
  lt := fun a b =>
    (Quotientₓ.liftOn₂ a b fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => Nonempty (r ≺i s))
      fun ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩ =>
      propext
        ⟨fun ⟨h⟩ => ⟨PrincipalSeg.equivLt f.symm <| h.ltLe (InitialSeg.ofIso g)⟩, fun ⟨h⟩ =>
          ⟨PrincipalSeg.equivLt f <| h.ltLe (InitialSeg.ofIso g.symm)⟩⟩
  le_refl := Quot.ind fun ⟨α, r, wo⟩ => ⟨InitialSeg.refl _⟩
  le_trans := fun a b c => (Quotientₓ.induction_on₃ a b c) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩
  lt_iff_le_not_le := fun a b =>
    (Quotientₓ.induction_on₂ a b) fun ⟨α, r, _⟩ ⟨β, s, _⟩ =>
      ⟨fun ⟨f⟩ => ⟨⟨f⟩, fun ⟨g⟩ => (f.ltLe g).irrefl _⟩, fun ⟨⟨f⟩, h⟩ =>
        Sum.recOn f.lt_or_eq (fun g => ⟨g⟩) fun g => (h ⟨InitialSeg.ofIso g.symm⟩).elim⟩
  le_antisymm := fun a b =>
    (Quotientₓ.induction_on₂ a b) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨h₁⟩ ⟨h₂⟩ => Quot.sound ⟨InitialSeg.antisymm h₁ h₂⟩

/-- Ordinal less-equal is defined such that
  well orders `r` and `s` satisfy `type r ≤ type s` if there exists
  a function embedding `r` as an initial segment of `s`. -/
add_decl_doc ordinal.partial_order.le

/-- Ordinal less-than is defined such that
  well orders `r` and `s` satisfy `type r < type s` if there exists
  a function embedding `r` as a principal segment of `s`. -/
add_decl_doc ordinal.partial_order.lt

theorem type_le {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r ≤ type s ↔ Nonempty (r ≼i s) :=
  Iff.rfl

theorem type_le' {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r ≤ type s ↔ Nonempty (r ↪r s) :=
  ⟨fun ⟨f⟩ => ⟨f⟩, fun ⟨f⟩ => ⟨f.collapse⟩⟩

@[simp]
theorem type_lt_iff {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] :
    type r < type s ↔ Nonempty (r ≺i s) :=
  Iff.rfl

/-- Given two ordinals `α ≤ β`, then `initial_seg_out α β` is the initial segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def initialSegOut {α β : Ordinal} (h : α ≤ β) :
    InitialSeg ((· < ·) : α.out.α → α.out.α → Prop) ((· < ·) : β.out.α → β.out.α → Prop) := by
  change α.out.r ≼i β.out.r
  rw [← Quotientₓ.out_eq α, ← Quotientₓ.out_eq β] at h
  revert h
  cases Quotientₓ.out α
  cases Quotientₓ.out β
  exact Classical.choice

/-- Given two ordinals `α < β`, then `principal_seg_out α β` is the principal segment embedding
of `α` to `β`, as map from a model type for `α` to a model type for `β`. -/
def principalSegOut {α β : Ordinal} (h : α < β) :
    PrincipalSeg ((· < ·) : α.out.α → α.out.α → Prop) ((· < ·) : β.out.α → β.out.α → Prop) := by
  change α.out.r ≺i β.out.r
  rw [← Quotientₓ.out_eq α, ← Quotientₓ.out_eq β] at h
  revert h
  cases Quotientₓ.out α
  cases Quotientₓ.out β
  exact Classical.choice

theorem typein_lt_type (r : α → α → Prop) [IsWellOrder α r] (a : α) : typein r a < type r :=
  ⟨PrincipalSeg.ofElement _ _⟩

theorem typein_lt_self {o : Ordinal} (i : o.out.α) : typein (· < ·) i < o := by
  simp_rw [← type_lt o]
  apply typein_lt_type

@[simp]
theorem typein_top {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] (f : r ≺i s) :
    typein s f.top = type r :=
  Eq.symm <|
    Quot.sound
      ⟨RelIso.ofSurjective (RelEmbedding.codRestrict _ f f.lt_top) fun ⟨a, h⟩ => by
          rcases f.down'.1 h with ⟨b, rfl⟩ <;> exact ⟨b, rfl⟩⟩

@[simp]
theorem typein_apply {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] (f : r ≼i s)
    (a : α) : Ordinal.typein s (f a) = Ordinal.typein r a :=
  Eq.symm <|
    Quotientₓ.sound
      ⟨RelIso.ofSurjective
          (RelEmbedding.codRestrict _ ((Subrel.relEmbedding _ _).trans f) fun ⟨x, h⟩ => by
            rw [RelEmbedding.trans_apply] <;> exact f.to_rel_embedding.map_rel_iff.2 h)
          fun ⟨y, h⟩ => by
          rcases f.init' h with ⟨a, rfl⟩ <;>
            exact ⟨⟨a, f.to_rel_embedding.map_rel_iff.1 h⟩, Subtype.eq <| RelEmbedding.trans_apply _ _ _⟩⟩

@[simp]
theorem typein_lt_typein (r : α → α → Prop) [IsWellOrder α r] {a b : α} : typein r a < typein r b ↔ r a b :=
  ⟨fun ⟨f⟩ => by
    have : f.top.1 = a := by
      let f' := PrincipalSeg.ofElement r a
      let g' := f.trans (PrincipalSeg.ofElement r b)
      have : g'.top = f'.top := by
        rw [Subsingleton.elimₓ f' g']
      exact this
    rw [← this]
    exact f.top.2, fun h =>
    ⟨PrincipalSeg.codRestrict _ (PrincipalSeg.ofElement r a) (fun x => @trans _ r _ _ _ _ x.2 h) h⟩⟩

theorem typein_surj (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) : ∃ a, typein r a = o :=
  induction_on o (fun β s _ ⟨f⟩ => ⟨f.top, typein_top _⟩) h

theorem typein_injective (r : α → α → Prop) [IsWellOrder α r] : Injective (typein r) :=
  injective_of_increasing r (· < ·) (typein r) fun x y => (typein_lt_typein r).2

@[simp]
theorem typein_inj (r : α → α → Prop) [IsWellOrder α r] {a b} : typein r a = typein r b ↔ a = b :=
  (typein_injective r).eq_iff

/-! ### Enumerating elements in a well-order with ordinals. -/


/-- `enum r o h` is the `o`-th element of `α` ordered by `r`.
  That is, `enum` maps an initial segment of the ordinals, those
  less than the order type of `r`, to the elements of `α`. -/
def enum (r : α → α → Prop) [IsWellOrder α r] (o) : o < type r → α :=
  (Quot.recOn o fun ⟨β, s, _⟩ h => (Classical.choice h).top) fun ⟨β, s, _⟩ ⟨γ, t, _⟩ ⟨h⟩ => by
    skip
    refine' funext fun H₂ : type t < type r => _
    have H₁ : type s < type r := by
      rwa [type_eq.2 ⟨h⟩]
    have :
      ∀ {o e} (H : o < type r),
        @Eq.ndrec (fun o : Ordinal => o < type r → α) (fun h : type s < type r => (Classical.choice h).top) e H =
          (Classical.choice H₁).top :=
      by
      intros
      subst e
    exact (this H₂).trans (PrincipalSeg.top_eq h (Classical.choice H₁) (Classical.choice H₂))

theorem enum_type {α β} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s] (f : s ≺i r)
    {h : type s < type r} : enum r (type s) h = f.top :=
  PrincipalSeg.top_eq (RelIso.refl _) _ _

@[simp]
theorem enum_typein (r : α → α → Prop) [IsWellOrder α r] (a : α) : enum r (typein r a) (typein_lt_type r a) = a :=
  enum_type (PrincipalSeg.ofElement r a)

@[simp]
theorem typein_enum (r : α → α → Prop) [IsWellOrder α r] {o} (h : o < type r) : typein r (enum r o h) = o := by
  let ⟨a, e⟩ := typein_surj r h
  clear _let_match <;> subst e <;> rw [enum_typein]

theorem enum_lt_enum {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Ordinal} (h₁ : o₁ < type r) (h₂ : o₂ < type r) :
    r (enum r o₁ h₁) (enum r o₂ h₂) ↔ o₁ < o₂ := by
  rw [← typein_lt_typein r, typein_enum, typein_enum]

theorem rel_iso_enum' {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≃r s) (o : Ordinal) : ∀ (hr : o < type r) (hs : o < type s), f (enum r o hr) = enum s o hs := by
  refine' induction_on o _
  rintro γ t wo ⟨g⟩ ⟨h⟩
  skip
  rw [enum_type g, enum_type (PrincipalSeg.ltEquiv g f)]
  rfl

theorem rel_iso_enum {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} [IsWellOrder α r] [IsWellOrder β s]
    (f : r ≃r s) (o : Ordinal) (hr : o < type r) :
    f (enum r o hr) =
      enum s o
        (by
          convert hr using 1
          apply Quotientₓ.sound
          exact ⟨f.symm⟩) :=
  rel_iso_enum' _ _ _ _

theorem lt_wf : @WellFounded Ordinal (· < ·) :=
  ⟨fun a =>
    (induction_on a) fun α r wo =>
      suffices ∀ a, Acc (· < ·) (typein r a) from
        ⟨_, fun o h =>
          let ⟨a, e⟩ := typein_surj r h
          e ▸ this a⟩
      fun a =>
      (Acc.recOnₓ (wo.wf.apply a)) fun x H IH =>
        ⟨_, fun o h => by
          rcases typein_surj r (lt_transₓ h (typein_lt_type r _)) with ⟨b, rfl⟩
          exact IH _ ((typein_lt_typein r).1 h)⟩⟩

instance : HasWellFounded Ordinal :=
  ⟨(· < ·), lt_wf⟩

/-- Reformulation of well founded induction on ordinals as a lemma that works with the
`induction` tactic, as in `induction i using ordinal.induction with i IH`. -/
theorem induction {p : Ordinal.{u} → Prop} (i : Ordinal.{u}) (h : ∀ j, (∀ k, k < j → p k) → p j) : p i :=
  lt_wf.induction i h

/-- Principal segment version of the `typein` function, embedding a well order into
  ordinals as a principal segment. -/
def typein.principalSeg {α : Type u} (r : α → α → Prop) [IsWellOrder α r] : @PrincipalSeg α Ordinal.{u} r (· < ·) :=
  ⟨RelEmbedding.ofMonotone (typein r) fun a b => (typein_lt_typein r).2, type r, fun b =>
    ⟨fun h => ⟨enum r _ h, typein_enum r h⟩, fun ⟨a, e⟩ => e ▸ typein_lt_type _ _⟩⟩

@[simp]
theorem typein.principal_seg_coe (r : α → α → Prop) [IsWellOrder α r] :
    (typein.principalSeg r : α → Ordinal) = typein r :=
  rfl

/-! ### Cardinality of ordinals -/


/-- The cardinal of an ordinal is the cardinality of any type on which a relation with that order
type is defined. -/
def card : Ordinal → Cardinal :=
  (Quotientₓ.map WellOrder.α) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨e⟩ => ⟨e.toEquiv⟩

@[simp]
theorem card_type (r : α → α → Prop) [IsWellOrder α r] : card (type r) = # α :=
  rfl

@[simp]
theorem card_typein {r : α → α → Prop} [wo : IsWellOrder α r] (x : α) : # { y // r y x } = (typein r x).card :=
  rfl

theorem card_le_card {o₁ o₂ : Ordinal} : o₁ ≤ o₂ → card o₁ ≤ card o₂ :=
  (induction_on o₁) fun α r _ => (induction_on o₂) fun β s _ ⟨⟨⟨f, _⟩, _⟩⟩ => ⟨f⟩

instance : Zero Ordinal :=
  ⟨type <| @EmptyRelation Pempty⟩

instance : Inhabited Ordinal :=
  ⟨0⟩

theorem type_eq_zero_of_empty (r) [IsWellOrder α r] [IsEmpty α] : type r = 0 :=
  (RelIso.relIsoOfIsEmpty r _).ordinal_type_eq

@[simp]
theorem type_eq_zero_iff_is_empty [IsWellOrder α r] : type r = 0 ↔ IsEmpty α :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    s.toEquiv.isEmpty,
    @type_eq_zero_of_empty α r _⟩

theorem type_ne_zero_iff_nonempty [IsWellOrder α r] : type r ≠ 0 ↔ Nonempty α := by
  simp

theorem type_ne_zero_of_nonempty (r) [IsWellOrder α r] [h : Nonempty α] : type r ≠ 0 :=
  type_ne_zero_iff_nonempty.2 h

theorem type_pempty : type (@EmptyRelation Pempty) = 0 :=
  rfl

theorem type_empty : type (@EmptyRelation Empty) = 0 :=
  type_eq_zero_of_empty _

@[simp]
theorem card_zero : card 0 = 0 :=
  rfl

protected theorem zero_le (o : Ordinal) : 0 ≤ o :=
  (induction_on o) fun α r _ => ⟨⟨⟨Embedding.ofIsEmpty, isEmptyElim⟩, isEmptyElim⟩⟩

instance : OrderBot Ordinal :=
  ⟨0, Ordinal.zero_le⟩

@[simp]
protected theorem le_zero {o : Ordinal} : o ≤ 0 ↔ o = 0 := by
  simp only [← le_antisymm_iffₓ, ← Ordinal.zero_le, ← and_trueₓ]

protected theorem pos_iff_ne_zero {o : Ordinal} : 0 < o ↔ o ≠ 0 := by
  simp only [← lt_iff_le_and_ne, ← Ordinal.zero_le, ← true_andₓ, ← Ne.def, ← eq_comm]

@[simp]
theorem out_empty_iff_eq_zero {o : Ordinal} : IsEmpty o.out.α ↔ o = 0 := by
  rw [← @type_eq_zero_iff_is_empty o.out.α (· < ·), type_lt]

theorem eq_zero_of_out_empty (o : Ordinal) [h : IsEmpty o.out.α] : o = 0 :=
  out_empty_iff_eq_zero.1 h

instance is_empty_out_zero : IsEmpty (0 : Ordinal).out.α :=
  out_empty_iff_eq_zero.2 rfl

@[simp]
theorem out_nonempty_iff_ne_zero {o : Ordinal} : Nonempty o.out.α ↔ o ≠ 0 := by
  rw [← @type_ne_zero_iff_nonempty o.out.α (· < ·), type_lt]

theorem ne_zero_of_out_nonempty (o : Ordinal) [h : Nonempty o.out.α] : o ≠ 0 :=
  out_nonempty_iff_ne_zero.1 h

instance : One Ordinal :=
  ⟨type <| @EmptyRelation PUnit⟩

theorem type_eq_one_of_unique (r) [IsWellOrder α r] [Unique α] : type r = 1 :=
  (RelIso.relIsoOfUniqueOfIrrefl r _).ordinal_type_eq

@[simp]
theorem type_eq_one_iff_unique [IsWellOrder α r] : type r = 1 ↔ Nonempty (Unique α) :=
  ⟨fun h =>
    let ⟨s⟩ := type_eq.1 h
    ⟨s.toEquiv.unique⟩,
    fun ⟨h⟩ => @type_eq_one_of_unique α r _ h⟩

theorem type_punit : type (@EmptyRelation PUnit) = 1 :=
  rfl

theorem type_unit : type (@EmptyRelation Unit) = 1 :=
  rfl

@[simp]
theorem card_one : card 1 = 1 :=
  rfl

/-! ### Lifting ordinals to a higher universe -/


/-- The universe lift operation for ordinals, which embeds `ordinal.{u}` as
  a proper initial segment of `ordinal.{v}` for `v > u`. For the initial segment version,
  see `lift.initial_seg`. -/
def lift (o : Ordinal.{v}) : Ordinal.{max v u} :=
  (Quotientₓ.liftOn o fun w => type <| ULift.down ⁻¹'o w.R) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨f⟩ =>
    Quot.sound ⟨(RelIso.preimage Equivₓ.ulift r).trans <| f.trans (RelIso.preimage Equivₓ.ulift s).symm⟩

@[simp]
theorem type_ulift (r : α → α → Prop) [IsWellOrder α r] : type (ULift.down ⁻¹'o r) = lift.{v} (type r) :=
  rfl

theorem _root_.rel_iso.ordinal_lift_type_eq {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellOrder α r] [IsWellOrder β s] (f : r ≃r s) : lift.{v} (type r) = lift.{u} (type s) :=
  ((RelIso.preimage Equivₓ.ulift r).trans <| f.trans (RelIso.preimage Equivₓ.ulift s).symm).ordinal_type_eq

@[simp]
theorem type_lift_preimage {α : Type u} {β : Type v} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    lift.{u} (type (f ⁻¹'o r)) = lift.{v} (type r) :=
  (RelIso.preimage f r).ordinal_lift_type_eq

/-- `lift.{(max u v) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a =>
    (induction_on a) fun α r _ =>
      Quotientₓ.sound ⟨(RelIso.preimage Equivₓ.ulift r).trans (RelIso.preimage Equivₓ.ulift r).symm⟩

/-- `lift.{(max v u) u}` equals `lift.{v u}`. Using `set_option pp.universes true` will make it much
    easier to understand what's happening when using this lemma. -/
@[simp]
theorem lift_umax' : lift.{max v u, u} = lift.{v, u} :=
  lift_umax

/-- An ordinal lifted to a lower or equal universe equals itself. -/
@[simp]
theorem lift_id' (a : Ordinal) : lift a = a :=
  (induction_on a) fun α r _ => Quotientₓ.sound ⟨RelIso.preimage Equivₓ.ulift r⟩

/-- An ordinal lifted to the same universe equals itself. -/
@[simp]
theorem lift_id : ∀ a, lift.{u, u} a = a :=
  lift_id'.{u, u}

/-- An ordinal lifted to the zero universe equals itself. -/
@[simp]
theorem lift_uzero (a : Ordinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a

@[simp]
theorem lift_lift (a : Ordinal) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  (induction_on a) fun α r _ =>
    Quotientₓ.sound
      ⟨(RelIso.preimage Equivₓ.ulift _).trans <|
          (RelIso.preimage Equivₓ.ulift _).trans (RelIso.preimage Equivₓ.ulift _).symm⟩

theorem lift_type_le {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) ≤ lift.{max u w} (type s) ↔ Nonempty (r ≼i s) :=
  ⟨fun ⟨f⟩ =>
    ⟨(InitialSeg.ofIso (RelIso.preimage Equivₓ.ulift r).symm).trans <|
        f.trans (InitialSeg.ofIso (RelIso.preimage Equivₓ.ulift s))⟩,
    fun ⟨f⟩ =>
    ⟨(InitialSeg.ofIso (RelIso.preimage Equivₓ.ulift r)).trans <|
        f.trans (InitialSeg.ofIso (RelIso.preimage Equivₓ.ulift s).symm)⟩⟩

theorem lift_type_eq {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) = lift.{max u w} (type s) ↔ Nonempty (r ≃r s) :=
  Quotientₓ.eq.trans
    ⟨fun ⟨f⟩ => ⟨(RelIso.preimage Equivₓ.ulift r).symm.trans <| f.trans (RelIso.preimage Equivₓ.ulift s)⟩, fun ⟨f⟩ =>
      ⟨(RelIso.preimage Equivₓ.ulift r).trans <| f.trans (RelIso.preimage Equivₓ.ulift s).symm⟩⟩

theorem lift_type_lt {α : Type u} {β : Type v} {r s} [IsWellOrder α r] [IsWellOrder β s] :
    lift.{max v w} (type r) < lift.{max u w} (type s) ↔ Nonempty (r ≺i s) := by
  have :=
      @RelEmbedding.is_well_order _ _ (@Equivₓ.ulift.{max v w} α ⁻¹'o r) r (RelIso.preimage Equivₓ.ulift.{max v w} r)
        _ <;>
    have :=
        @RelEmbedding.is_well_order _ _ (@Equivₓ.ulift.{max u w} β ⁻¹'o s) s (RelIso.preimage Equivₓ.ulift.{max u w} s)
          _ <;>
      exact
        ⟨fun ⟨f⟩ =>
          ⟨(f.equivLt (RelIso.preimage Equivₓ.ulift r).symm).ltLe (InitialSeg.ofIso (RelIso.preimage Equivₓ.ulift s))⟩,
          fun ⟨f⟩ =>
          ⟨(f.equivLt (RelIso.preimage Equivₓ.ulift r)).ltLe (InitialSeg.ofIso (RelIso.preimage Equivₓ.ulift s).symm)⟩⟩

@[simp]
theorem lift_le {a b : Ordinal} : lift.{u, v} a ≤ lift b ↔ a ≤ b :=
  (induction_on a) fun α r _ =>
    (induction_on b) fun β s _ => by
      rw [← lift_umax]
      exact lift_type_le

@[simp]
theorem lift_inj {a b : Ordinal} : lift a = lift b ↔ a = b := by
  simp only [← le_antisymm_iffₓ, ← lift_le]

@[simp]
theorem lift_lt {a b : Ordinal} : lift a < lift b ↔ a < b := by
  simp only [← lt_iff_le_not_leₓ, ← lift_le]

@[simp]
theorem lift_zero : lift 0 = 0 :=
  type_eq_zero_of_empty _

@[simp]
theorem lift_one : lift 1 = 1 :=
  type_eq_one_of_unique _

@[simp]
theorem lift_card (a) : (card a).lift = card (lift a) :=
  (induction_on a) fun α r _ => rfl

theorem lift_down' {a : Cardinal.{u}} {b : Ordinal.{max u v}} (h : card b ≤ a.lift) : ∃ a', lift a' = b :=
  let ⟨c, e⟩ := Cardinal.lift_down h
  Cardinal.induction_on c
    (fun α =>
      (induction_on b) fun β s _ e' => by
        skip
        rw [card_type, ← Cardinal.lift_id'.{max u v, u} (# β), ← Cardinal.lift_umax.{u, v},
          lift_mk_eq.{u, max u v, max u v}] at e'
        cases' e' with f
        have g := RelIso.preimage f s
        have := (g : ⇑f ⁻¹'o s ↪r s).IsWellOrder
        have := lift_type_eq.{u, max u v, max u v}.2 ⟨g⟩
        rw [lift_id, lift_umax.{u, v}] at this
        exact ⟨_, this⟩)
    e

theorem lift_down {a : Ordinal.{u}} {b : Ordinal.{max u v}} (h : b ≤ lift a) : ∃ a', lift a' = b :=
  @lift_down' (card a) _
    (by
      rw [lift_card] <;> exact card_le_card h)

theorem le_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} : b ≤ lift a ↔ ∃ a', lift a' = b ∧ a' ≤ a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down h
    ⟨a', e, lift_le.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_le.2 h⟩

theorem lt_lift_iff {a : Ordinal.{u}} {b : Ordinal.{max u v}} : b < lift a ↔ ∃ a', lift a' = b ∧ a' < a :=
  ⟨fun h =>
    let ⟨a', e⟩ := lift_down (le_of_ltₓ h)
    ⟨a', e, lift_lt.1 <| e.symm ▸ h⟩,
    fun ⟨a', e, h⟩ => e ▸ lift_lt.2 h⟩

/-- Initial segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as an initial segment when `u ≤ v`. -/
def lift.initialSeg : @InitialSeg Ordinal.{u} Ordinal.{max u v} (· < ·) (· < ·) :=
  ⟨⟨⟨lift.{v}, fun a b => lift_inj.1⟩, fun a b => lift_lt⟩, fun a b h => lift_down (le_of_ltₓ h)⟩

@[simp]
theorem lift.initial_seg_coe : (lift.initialSeg : Ordinal → Ordinal) = lift :=
  rfl

/-! ### The first infinite ordinal `omega` -/


/-- `ω` is the first infinite ordinal, defined as the order type of `ℕ`. -/
def omega : Ordinal.{u} :=
  lift <| @type ℕ (· < ·) _

-- mathport name: «exprω»
localized [Ordinal] notation "ω" => Ordinal.omega

/-- Note that the presence of this lemma makes `simp [omega]` form a loop. -/
@[simp]
theorem type_nat_lt : @type ℕ (· < ·) _ = ω :=
  (lift_id _).symm

@[simp]
theorem card_omega : card ω = ℵ₀ :=
  rfl

@[simp]
theorem lift_omega : lift ω = ω :=
  lift_lift _

/-!
### Definition and first properties of addition on ordinals

In this paragraph, we introduce the addition on ordinals, and prove just enough properties to
deduce that the order on ordinals is total (and therefore well-founded). Further properties of
the addition, together with properties of the other operations, are proved in
`ordinal_arithmetic.lean`.
-/


/-- `o₁ + o₂` is the order on the disjoint union of `o₁` and `o₂` obtained by declaring that
  every element of `o₁` is smaller than every element of `o₂`. -/
instance : Add Ordinal.{u} :=
  ⟨fun o₁ o₂ =>
    (Quotientₓ.liftOn₂ o₁ o₂ fun ⟨α, r, wo⟩ ⟨β, s, wo'⟩ => type (Sum.Lex r s))
      fun ⟨α₁, r₁, o₁⟩ ⟨α₂, r₂, o₂⟩ ⟨β₁, s₁, p₁⟩ ⟨β₂, s₂, p₂⟩ ⟨f⟩ ⟨g⟩ => Quot.sound ⟨RelIso.sumLexCongr f g⟩⟩

instance : AddMonoidWithOneₓ Ordinal.{u} where
  add := (· + ·)
  zero := 0
  one := 1
  zero_add := fun o =>
    (induction_on o) fun α r _ => Eq.symm <| Quotientₓ.sound ⟨⟨(emptySum Pempty α).symm, fun a b => Sum.lex_inr_inr⟩⟩
  add_zero := fun o =>
    (induction_on o) fun α r _ => Eq.symm <| Quotientₓ.sound ⟨⟨(sumEmpty α Pempty).symm, fun a b => Sum.lex_inl_inl⟩⟩
  add_assoc := fun o₁ o₂ o₃ =>
    (Quotientₓ.induction_on₃ o₁ o₂ o₃) fun ⟨α, r, _⟩ ⟨β, s, _⟩ ⟨γ, t, _⟩ =>
      Quot.sound
        ⟨⟨sumAssoc _ _ _, fun a b => by
            rcases a with (⟨a | a⟩ | a) <;>
              rcases b with (⟨b | b⟩ | b) <;>
                simp only [← sum_assoc_apply_inl_inl, ← sum_assoc_apply_inl_inr, ← sum_assoc_apply_inr, ←
                  Sum.lex_inl_inl, ← Sum.lex_inr_inr, ← Sum.Lex.sep, ← Sum.lex_inr_inl]⟩⟩

@[simp]
theorem card_add (o₁ o₂ : Ordinal) : card (o₁ + o₂) = card o₁ + card o₂ :=
  (induction_on o₁) fun α r _ => (induction_on o₂) fun β s _ => rfl

@[simp]
theorem type_sum_lex {α β : Type u} (r : α → α → Prop) (s : β → β → Prop) [IsWellOrder α r] [IsWellOrder β s] :
    type (Sum.Lex r s) = type r + type s :=
  rfl

@[simp]
theorem card_nat (n : ℕ) : card.{u} n = n := by
  induction n <;> [rfl, simp only [← card_add, ← card_one, ← Nat.cast_succₓ, *]]

instance add_covariant_class_le : CovariantClass Ordinal.{u} Ordinal.{u} (· + ·) (· ≤ ·) :=
  ⟨fun c a b h => by
    revert h c
    exact
      (induction_on a) fun α₁ r₁ _ =>
        (induction_on b) fun α₂ r₂ _ ⟨⟨⟨f, fo⟩, fi⟩⟩ c =>
          (induction_on c) fun β s _ =>
            ⟨⟨⟨(embedding.refl _).sum_map f, fun a b =>
                  match a, b with
                  | Sum.inl a, Sum.inl b => sum.lex_inl_inl.trans sum.lex_inl_inl.symm
                  | Sum.inl a, Sum.inr b => by
                    apply iff_of_true <;> apply Sum.Lex.sep
                  | Sum.inr a, Sum.inl b => by
                    apply iff_of_false <;> exact Sum.lex_inr_inl
                  | Sum.inr a, Sum.inr b => sum.lex_inr_inr.trans <| fo.trans sum.lex_inr_inr.symm⟩,
                fun a b H =>
                match a, b, H with
                | _, Sum.inl b, _ => ⟨Sum.inl b, rfl⟩
                | Sum.inl a, Sum.inr b, H => (Sum.lex_inr_inl H).elim
                | Sum.inr a, Sum.inr b, H =>
                  let ⟨w, h⟩ := fi _ _ (Sum.lex_inr_inr.1 H)
                  ⟨Sum.inr w, congr_arg Sum.inr h⟩⟩⟩⟩

instance add_swap_covariant_class_le : CovariantClass Ordinal.{u} Ordinal.{u} (swap (· + ·)) (· ≤ ·) :=
  ⟨fun c a b h => by
    revert h c
    exact
      (induction_on a) fun α₁ r₁ hr₁ =>
        (induction_on b) fun α₂ r₂ hr₂ ⟨⟨⟨f, fo⟩, fi⟩⟩ c =>
          (induction_on c) fun β s hs =>
            (@type_le' _ _ _ _ (@Sum.Lex.is_well_order _ _ _ _ hr₁ hs) (@Sum.Lex.is_well_order _ _ _ _ hr₂ hs)).2
              ⟨⟨f.sum_map (embedding.refl _), fun a b => by
                  constructor <;> intro H
                  · cases' a with a a <;> cases' b with b b <;> cases H <;> constructor <;> [rwa [← fo], assumption]
                    
                  · cases H <;> constructor <;> [rwa [fo], assumption]
                    ⟩⟩⟩

theorem le_add_right (a b : Ordinal) : a ≤ a + b := by
  simpa only [← add_zeroₓ] using add_le_add_left (Ordinal.zero_le b) a

theorem le_add_left (a b : Ordinal) : a ≤ b + a := by
  simpa only [← zero_addₓ] using add_le_add_right (Ordinal.zero_le b) a

instance : LinearOrderₓ Ordinal :=
  { Ordinal.partialOrder with
    le_total := fun a b =>
      match lt_or_eq_of_leₓ (le_add_left b a), lt_or_eq_of_leₓ (le_add_right a b) with
      | Or.inr h, _ => by
        rw [h] <;> exact Or.inl (le_add_right _ _)
      | _, Or.inr h => by
        rw [h] <;> exact Or.inr (le_add_left _ _)
      | Or.inl h₁, Or.inl h₂ =>
        induction_on a
          (fun α₁ r₁ _ =>
            (induction_on b) fun α₂ r₂ _ ⟨f⟩ ⟨g⟩ => by
              skip
              rw [← typein_top f, ← typein_top g, le_iff_lt_or_eqₓ, le_iff_lt_or_eqₓ, typein_lt_typein,
                typein_lt_typein]
              rcases trichotomous_of (Sum.Lex r₁ r₂) g.top f.top with (h | h | h) <;> [exact Or.inl (Or.inl h),
                · left
                  right
                  rw [h]
                  ,
                exact Or.inr (Or.inl h)])
          h₁ h₂,
    decidableLe := Classical.decRel _ }

instance : IsWellOrder Ordinal (· < ·) :=
  ⟨lt_wf⟩

private theorem succ_le_iff' {a b : Ordinal} : a + 1 ≤ b ↔ a < b :=
  ⟨lt_of_lt_of_leₓ
      ((induction_on a) fun α r _ =>
        ⟨⟨⟨⟨fun x => Sum.inl x, fun _ _ => Sum.inl.injₓ⟩, fun _ _ => Sum.lex_inl_inl⟩, Sum.inr PUnit.unit, fun b =>
            Sum.recOn b (fun x => ⟨fun _ => ⟨x, rfl⟩, fun _ => Sum.Lex.sep _ _⟩) fun x =>
              Sum.lex_inr_inr.trans ⟨False.elim, fun ⟨x, H⟩ => Sum.inl_ne_inr H⟩⟩⟩),
    (induction_on a) fun α r hr =>
      (induction_on b) fun β s hs ⟨⟨f, t, hf⟩⟩ => by
        refine'
          ⟨⟨@RelEmbedding.ofMonotone (Sum α PUnit) β _ _ (@Sum.Lex.is_well_order _ _ _ _ hr _).1.1
                (@is_asymm_of_is_trans_of_is_irrefl _ _ hs.1.2.2 hs.1.2.1) (Sum.rec _ _) fun a b => _,
              fun a b => _⟩⟩
        · exact f
          
        · exact fun _ => t
          
        · rcases a with (a | _) <;> rcases b with (b | _)
          · simpa only [← Sum.lex_inl_inl] using f.map_rel_iff.2
            
          · intro
            rw [hf]
            exact ⟨_, rfl⟩
            
          · exact False.elim ∘ Sum.lex_inr_inl
            
          · exact False.elim ∘ Sum.lex_inr_inr.1
            
          
        · rcases a with (a | _)
          · intro h
            have := @PrincipalSeg.init _ _ _ _ hs.1.2.2 ⟨f, t, hf⟩ _ _ h
            cases' this with w h
            exact ⟨Sum.inl w, h⟩
            
          · intro h
            cases' (hf b).1 h with w h
            exact ⟨Sum.inl w, h⟩
            
          ⟩

instance : NoMaxOrder Ordinal :=
  ⟨fun a => ⟨_, succ_le_iff'.1 le_rfl⟩⟩

instance : SuccOrder Ordinal.{u} :=
  SuccOrder.ofSuccLeIff (fun o => o + 1) fun a b => succ_le_iff'

@[simp]
theorem add_one_eq_succ (o : Ordinal) : o + 1 = succ o :=
  rfl

@[simp]
theorem typein_le_typein (r : α → α → Prop) [IsWellOrder α r] {x x' : α} : typein r x ≤ typein r x' ↔ ¬r x' x := by
  rw [← not_ltₓ, typein_lt_typein]

@[simp]
theorem typein_le_typein' (o : Ordinal) {x x' : o.out.α} : typein (· < ·) x ≤ typein (· < ·) x' ↔ x ≤ x' := by
  rw [typein_le_typein]
  exact not_ltₓ

@[simp]
theorem enum_le_enum (r : α → α → Prop) [IsWellOrder α r] {o o' : Ordinal} (ho : o < type r) (ho' : o' < type r) :
    ¬r (enum r o' ho') (enum r o ho) ↔ o ≤ o' := by
  rw [← @not_ltₓ _ _ o' o, enum_lt_enum ho']

@[simp]
theorem enum_le_enum' (a : Ordinal) {o o' : Ordinal} (ho : o < type (· < ·)) (ho' : o' < type (· < ·)) :
    enum (· < ·) o ho ≤ @enum a.out.α (· < ·) _ o' ho' ↔ o ≤ o' := by
  rw [← enum_le_enum (· < ·), ← not_ltₓ]

theorem enum_zero_le {r : α → α → Prop} [IsWellOrder α r] (h0 : 0 < type r) (a : α) : ¬r a (enum r 0 h0) := by
  rw [← enum_typein r a, enum_le_enum r]
  apply Ordinal.zero_le

theorem enum_zero_le' {o : Ordinal} (h0 : 0 < o) (a : o.out.α) :
    @enum o.out.α (· < ·) _ 0
        (by
          rwa [type_lt]) ≤
      a :=
  by
  rw [← not_ltₓ]
  apply enum_zero_le

theorem le_enum_succ {o : Ordinal} (a : (succ o).out.α) :
    a ≤
      @enum (succ o).out.α (· < ·) _ o
        (by
          rw [type_lt]
          exact lt_succ o) :=
  by
  rw [← enum_typein (· < ·) a, enum_le_enum', ← lt_succ_iff]
  apply typein_lt_self

@[simp]
theorem enum_inj {r : α → α → Prop} [IsWellOrder α r] {o₁ o₂ : Ordinal} (h₁ : o₁ < type r) (h₂ : o₂ < type r) :
    enum r o₁ h₁ = enum r o₂ h₂ ↔ o₁ = o₂ :=
  ⟨fun h => by
    by_contra hne
    cases' lt_or_gt_of_neₓ hne with hlt hlt <;> apply (IsWellOrder.is_irrefl r).1
    · rwa [← @enum_lt_enum α r _ o₁ o₂ h₁ h₂, h] at hlt
      
    · change _ < _ at hlt
      rwa [← @enum_lt_enum α r _ o₂ o₁ h₂ h₁, h] at hlt
      ,
    fun h => by
    simp_rw [h]⟩

/-- A well order `r` is order isomorphic to the set of ordinals smaller than `type r`. -/
@[simps]
def enumIso (r : α → α → Prop) [IsWellOrder α r] : Subrel (· < ·) (· < type r) ≃r r where
  toFun := fun x => enum r x.1 x.2
  invFun := fun x => ⟨typein r x, typein_lt_type r x⟩
  left_inv := fun ⟨o, h⟩ => Subtype.ext_val (typein_enum _ _)
  right_inv := fun h => enum_typein _ _
  map_rel_iff' := by
    rintro ⟨a, _⟩ ⟨b, _⟩
    apply enum_lt_enum

/-- The order isomorphism between ordinals less than `o` and `o.out.α`. -/
@[simps]
noncomputable def enumIsoOut (o : Ordinal) : Set.Iio o ≃o o.out.α where
  toFun := fun x =>
    enum (· < ·) x.1 <| by
      rw [type_lt]
      exact x.2
  invFun := fun x => ⟨typein (· < ·) x, typein_lt_self x⟩
  left_inv := fun ⟨o', h⟩ => Subtype.ext_val (typein_enum _ _)
  right_inv := fun h => enum_typein _ _
  map_rel_iff' := by
    rintro ⟨a, _⟩ ⟨b, _⟩
    apply enum_le_enum'

/-- `o.out.α` is an `order_bot` whenever `0 < o`. -/
def outOrderBotOfPos {o : Ordinal} (ho : 0 < o) : OrderBot o.out.α :=
  ⟨_, enum_zero_le' ho⟩

theorem enum_zero_eq_bot {o : Ordinal} (ho : 0 < o) :
    enum (· < ·) 0
        (by
          rwa [type_lt]) =
      by
      have H := out_order_bot_of_pos ho
      exact ⊥ :=
  rfl

/-- `univ.{u v}` is the order type of the ordinals of `Type u` as a member
  of `ordinal.{v}` (when `u < v`). It is an inaccessible cardinal. -/
-- intended to be used with explicit universe parameters
@[nolint check_univs]
def univ : Ordinal.{max (u + 1) v} :=
  lift.{v, u + 1} (@type Ordinal (· < ·) _)

theorem univ_id : univ.{u, u + 1} = @type Ordinal (· < ·) _ :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

/-- Principal segment version of the lift operation on ordinals, embedding `ordinal.{u}` in
  `ordinal.{v}` as a principal segment when `u < v`. -/
def lift.principalSeg : @PrincipalSeg Ordinal.{u} Ordinal.{max (u + 1) v} (· < ·) (· < ·) :=
  ⟨↑lift.initial_seg.{u, max (u + 1) v}, univ.{u, v}, by
    refine' fun b => induction_on b _
    intro β s _
    rw [univ, ← lift_umax]
    constructor <;> intro h
    · rw [← lift_id (type s)] at h⊢
      cases' lift_type_lt.1 h with f
      cases' f with f a hf
      exists a
      revert hf
      apply induction_on a
      intro α r _ hf
      refine'
        lift_type_eq.{u, max (u + 1) v, max (u + 1) v}.2 ⟨(RelIso.ofSurjective (RelEmbedding.ofMonotone _ _) _).symm⟩
      · exact fun b => enum r (f b) ((hf _).2 ⟨_, rfl⟩)
        
      · refine' fun a b h => (typein_lt_typein r).1 _
        rw [typein_enum, typein_enum]
        exact f.map_rel_iff.2 h
        
      · intro a'
        cases' (hf _).1 (typein_lt_type _ a') with b e
        exists b
        simp
        simp [← e]
        
      
    · cases' h with a e
      rw [← e]
      apply induction_on a
      intro α r _
      exact lift_type_lt.{u, u + 1, max (u + 1) v}.2 ⟨typein.principal_seg r⟩
      ⟩

@[simp]
theorem lift.principal_seg_coe : (lift.principalSeg.{u, v} : Ordinal → Ordinal) = lift.{max (u + 1) v} :=
  rfl

@[simp]
theorem lift.principal_seg_top : lift.principalSeg.top = univ :=
  rfl

theorem lift.principal_seg_top' : lift.principalSeg.{u, u + 1}.top = @type Ordinal (· < ·) _ := by
  simp only [← lift.principal_seg_top, ← univ_id]

/-! ### Minimum -/


/-- The minimal element of a nonempty family of ordinals -/
def min {ι} (I : Nonempty ι) (f : ι → Ordinal) : Ordinal :=
  lt_wf.min (Set.Range f)
    (let ⟨i⟩ := I
    ⟨_, Set.mem_range_self i⟩)

theorem min_eq {ι} (I) (f : ι → Ordinal) : ∃ i, min I f = f i :=
  let ⟨i, e⟩ := lt_wf.min_mem (Set.Range f) _
  ⟨i, e.symm⟩

theorem min_le {ι I} (f : ι → Ordinal) (i) : min I f ≤ f i :=
  le_of_not_gtₓ <| lt_wf.not_lt_min (Set.Range f) _ (Set.mem_range_self i)

theorem le_min {ι I} {f : ι → Ordinal} {a} : a ≤ min I f ↔ ∀ i, a ≤ f i :=
  ⟨fun h i => le_transₓ h (min_le _ _), fun h =>
    let ⟨i, e⟩ := min_eq I f
    e.symm ▸ h i⟩

@[simp]
theorem lift_min {ι} (I) (f : ι → Ordinal) : lift (min I f) = min I (lift ∘ f) :=
  le_antisymmₓ (le_min.2 fun a => lift_le.2 <| min_le _ a) <| by
    let ⟨i, e⟩ := min_eq I (lift ∘ f)
    rw [e] <;>
      exact
        lift_le.2
          (le_minₓ.2 fun j =>
            lift_le.1 <| by
              have := min_le (lift ∘ f) j <;> rwa [e] at this)

instance : ConditionallyCompleteLinearOrderBot Ordinal :=
  IsWellOrder.conditionallyCompleteLinearOrderBot _

@[simp]
theorem bot_eq_zero : (⊥ : Ordinal) = 0 :=
  rfl

@[simp]
theorem max_zero_left : ∀ a : Ordinal, max 0 a = a :=
  max_bot_left

@[simp]
theorem max_zero_right : ∀ a : Ordinal, max a 0 = a :=
  max_bot_right

@[simp]
theorem max_eq_zero {a b : Ordinal} : max a b = 0 ↔ a = 0 ∧ b = 0 :=
  max_eq_bot

protected theorem not_lt_zero (o : Ordinal) : ¬o < 0 :=
  not_lt_bot

theorem eq_zero_or_pos : ∀ a : Ordinal, a = 0 ∨ 0 < a :=
  eq_bot_or_bot_lt

@[simp]
theorem Inf_empty : inf (∅ : Set Ordinal) = 0 :=
  dif_neg not_nonempty_empty

end Ordinal

/-! ### Representing a cardinal with an ordinal -/


namespace Cardinal

open Ordinal

@[simp]
theorem mk_ordinal_out (o : Ordinal) : # o.out.α = o.card :=
  (Ordinal.card_type _).symm.trans <| by
    rw [Ordinal.type_lt]

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. For the order-embedding version, see `ord.order_embedding`. -/
def ord (c : Cardinal) : Ordinal := by
  let ι := fun α => { r // IsWellOrder α r }
  have : ∀ α, ι α := fun α =>
    ⟨WellOrderingRel, by
      infer_instance⟩
  let F := fun α => Ordinal.min ⟨this _⟩ fun i : ι α => ⟦⟨α, i.1, i.2⟩⟧
  refine' Quot.liftOn c F _
  suffices : ∀ {α β}, α ≈ β → F α ≤ F β
  exact fun α β h => le_antisymmₓ (this h) (this (Setoidₓ.symm h))
  intro α β h
  cases' h with f
  refine' Ordinal.le_min.2 fun i => _
  have := @RelEmbedding.is_well_order _ _ (f ⁻¹'o i.1) _ (↑(RelIso.preimage f i.1)) i.2
  rw [← show type (f ⁻¹'o i.1) = ⟦⟨β, i.1, i.2⟩⟧ from Quot.sound ⟨RelIso.preimage f i.1⟩]
  exact Ordinal.min_le (fun i : ι α => ⟦⟨α, i.1, i.2⟩⟧) ⟨_, _⟩

theorem ord_eq_min (α : Type u) :
    ord (# α) =
      @Ordinal.min { r // IsWellOrder α r }
        ⟨⟨WellOrderingRel, by
            infer_instance⟩⟩
        fun i => ⟦⟨α, i.1, i.2⟩⟧ :=
  rfl

theorem ord_eq (α) : ∃ (r : α → α → Prop)(wo : IsWellOrder α r), ord (# α) = @type α r wo :=
  let ⟨⟨r, wo⟩, h⟩ :=
    @Ordinal.min_eq { r // IsWellOrder α r }
      ⟨⟨WellOrderingRel, by
          infer_instance⟩⟩
      fun i : { r // IsWellOrder α r } => ⟦⟨α, i.1, i.2⟩⟧
  ⟨r, wo, h⟩

theorem ord_le_type (r : α → α → Prop) [IsWellOrder α r] : ord (# α) ≤ Ordinal.type r :=
  @Ordinal.min_le { r // IsWellOrder α r }
    ⟨⟨WellOrderingRel, by
        infer_instance⟩⟩
    (fun i : { r // IsWellOrder α r } => ⟦⟨α, i.1, i.2⟩⟧) ⟨r, _⟩

theorem ord_le {c o} : ord c ≤ o ↔ c ≤ o.card :=
  (induction_on c) fun α =>
    (Ordinal.induction_on o) fun β s _ => by
      let ⟨r, _, e⟩ := ord_eq α
      skip
      simp only [← card_type]
      constructor <;> intro h
      · rw [e] at h
        exact
          let ⟨f⟩ := h
          ⟨f.toEmbedding⟩
        
      · cases' h with f
        have g := RelEmbedding.preimage f s
        have := RelEmbedding.is_well_order g
        exact le_transₓ (ord_le_type _) (type_le'.2 ⟨g⟩)
        

theorem lt_ord {c o} : o < ord c ↔ o.card < c := by
  rw [← not_leₓ, ← not_leₓ, ord_le]

@[simp]
theorem card_ord (c) : (ord c).card = c :=
  (Quotientₓ.induction_on c) fun α => by
    let ⟨r, _, e⟩ := ord_eq α
    simp only [← mk_def, ← e, ← card_type]

theorem ord_card_le (o : Ordinal) : o.card.ord ≤ o :=
  ord_le.2 le_rfl

theorem lt_ord_succ_card (o : Ordinal) : o < (succ o.card).ord := by
  rw [lt_ord]
  apply lt_succ

@[simp]
theorem ord_le_ord {c₁ c₂} : ord c₁ ≤ ord c₂ ↔ c₁ ≤ c₂ := by
  simp only [← ord_le, ← card_ord]

@[simp]
theorem ord_lt_ord {c₁ c₂} : ord c₁ < ord c₂ ↔ c₁ < c₂ := by
  simp only [← lt_ord, ← card_ord]

@[simp]
theorem ord_zero : ord 0 = 0 :=
  le_antisymmₓ (ord_le.2 <| zero_le _) (Ordinal.zero_le _)

@[simp]
theorem ord_nat (n : ℕ) : ord n = n :=
  le_antisymmₓ
      (ord_le.2 <| by
        simp only [← card_nat]) <|
    by
    induction' n with n IH
    · apply Ordinal.zero_le
      
    · exact succ_le_of_lt (IH.trans_lt <| ord_lt_ord.2 <| nat_cast_lt.2 (Nat.lt_succ_selfₓ n))
      

@[simp]
theorem ord_one : ord 1 = 1 := by
  simpa using ord_nat 1

@[simp]
theorem lift_ord (c) : (ord c).lift = ord (lift c) :=
  eq_of_forall_ge_iff fun o =>
    le_iff_le_iff_lt_iff_lt.2 <| by
      constructor <;> intro h
      · rcases Ordinal.lt_lift_iff.1 h with ⟨a, e, h⟩
        rwa [← e, lt_ord, ← lift_card, lift_lt, ← lt_ord]
        
      · rw [lt_ord] at h
        rcases lift_down' (le_of_ltₓ h) with ⟨o, rfl⟩
        rw [← lift_card, lift_lt] at h
        rwa [Ordinal.lift_lt, lt_ord]
        

theorem mk_ord_out (c : Cardinal) : # c.ord.out.α = c := by
  simp

theorem card_typein_lt (r : α → α → Prop) [IsWellOrder α r] (x : α) (h : ord (# α) = type r) :
    card (typein r x) < # α := by
  rw [← lt_ord, h]
  apply typein_lt_type

theorem card_typein_out_lt (c : Cardinal) (x : c.ord.out.α) : card (typein (· < ·) x) < c := by
  rw [← lt_ord]
  apply typein_lt_self

theorem ord_injective : Injective ord := by
  intro c c' h
  rw [← card_ord c, ← card_ord c', h]

/-- The ordinal corresponding to a cardinal `c` is the least ordinal
  whose cardinal is `c`. This is the order-embedding version. For the regular function, see `ord`.
-/
def ord.orderEmbedding : Cardinal ↪o Ordinal :=
  RelEmbedding.orderEmbeddingOfLtEmbedding ((RelEmbedding.ofMonotone Cardinal.ord) fun a b => Cardinal.ord_lt_ord.2)

@[simp]
theorem ord.order_embedding_coe : (ord.orderEmbedding : Cardinal → Ordinal) = ord :=
  rfl

/-- The cardinal `univ` is the cardinality of ordinal `univ`, or
  equivalently the cardinal of `ordinal.{u}`, or `cardinal.{u}`,
  as an element of `cardinal.{v}` (when `u < v`). -/
-- intended to be used with explicit universe parameters
@[nolint check_univs]
def univ :=
  lift.{v, u + 1} (# Ordinal)

theorem univ_id : univ.{u, u + 1} = # Ordinal :=
  lift_id _

@[simp]
theorem lift_univ : lift.{w} univ.{u, v} = univ.{u, max v w} :=
  lift_lift _

theorem univ_umax : univ.{u, max (u + 1) v} = univ.{u, v} :=
  congr_fun lift_umax _

theorem lift_lt_univ (c : Cardinal) : lift.{u + 1, u} c < univ.{u, u + 1} := by
  simpa only [← lift.principal_seg_coe, ← lift_ord, ← lift_succ, ← ord_le, ← succ_le_iff] using
    le_of_ltₓ (lift.principalSeg.{u, u + 1}.lt_top (succ c).ord)

theorem lift_lt_univ' (c : Cardinal) : lift.{max (u + 1) v, u} c < univ.{u, v} := by
  simpa only [← lift_lift, ← lift_univ, ← univ_umax] using lift_lt.{_, max (u + 1) v}.2 (lift_lt_univ c)

@[simp]
theorem ord_univ : ord univ.{u, v} = Ordinal.univ.{u, v} :=
  le_antisymmₓ (ord_card_le _) <|
    le_of_forall_lt fun o h =>
      lt_ord.2
        (by
          rcases lift.principalSeg.{u, v}.down'.1
              (by
                simpa only [← lift.principal_seg_coe] using h) with
            ⟨o', rfl⟩
          simp only [← lift.principal_seg_coe]
          rw [← lift_card]
          apply lift_lt_univ')

theorem lt_univ {c} : c < univ.{u, u + 1} ↔ ∃ c', c = lift.{u + 1, u} c' :=
  ⟨fun h => by
    have := ord_lt_ord.2 h
    rw [ord_univ] at this
    cases'
      lift.principalSeg.{u, u + 1}.down'.1
        (by
          simpa only [← lift.principal_seg_top] ) with
      o e
    have := card_ord c
    rw [← e, lift.principal_seg_coe, ← lift_card] at this
    exact ⟨_, this.symm⟩, fun ⟨c', e⟩ => e.symm ▸ lift_lt_univ _⟩

theorem lt_univ' {c} : c < univ.{u, v} ↔ ∃ c', c = lift.{max (u + 1) v, u} c' :=
  ⟨fun h => by
    let ⟨a, e, h'⟩ := lt_lift_iff.1 h
    rw [← univ_id] at h'
    rcases lt_univ.{u}.1 h' with ⟨c', rfl⟩
    exact
      ⟨c', by
        simp only [← e.symm, ← lift_lift]⟩,
    fun ⟨c', e⟩ => e.symm ▸ lift_lt_univ' _⟩

theorem small_iff_lift_mk_lt_univ {α : Type u} : Small.{v} α ↔ Cardinal.lift (# α) < univ.{v, max u (v + 1)} := by
  rw [lt_univ']
  constructor
  · rintro ⟨β, e⟩
    exact ⟨# β, lift_mk_eq.{u, _, v + 1}.2 e⟩
    
  · rintro ⟨c, hc⟩
    exact ⟨⟨c.out, lift_mk_eq.{u, _, v + 1}.1 (hc.trans (congr rfl c.mk_out.symm))⟩⟩
    

end Cardinal

namespace Ordinal

@[simp]
theorem card_univ : card univ = Cardinal.univ :=
  rfl

@[simp]
theorem nat_le_card {o} {n : ℕ} : (n : Cardinal) ≤ card o ↔ (n : Ordinal) ≤ o := by
  rw [← Cardinal.ord_le, Cardinal.ord_nat]

@[simp]
theorem nat_lt_card {o} {n : ℕ} : (n : Cardinal) < card o ↔ (n : Ordinal) < o := by
  rw [← succ_le_iff, ← succ_le_iff, ← nat_succ, nat_le_card]
  rfl

@[simp]
theorem card_lt_nat {o} {n : ℕ} : card o < n ↔ o < n :=
  lt_iff_lt_of_le_iff_le nat_le_card

@[simp]
theorem card_le_nat {o} {n : ℕ} : card o ≤ n ↔ o ≤ n :=
  le_iff_le_iff_lt_iff_lt.2 nat_lt_card

@[simp]
theorem card_eq_nat {o} {n : ℕ} : card o = n ↔ o = n := by
  simp only [← le_antisymm_iffₓ, ← card_le_nat, ← nat_le_card]

@[simp]
theorem type_fintype (r : α → α → Prop) [IsWellOrder α r] [Fintype α] : type r = Fintype.card α := by
  rw [← card_eq_nat, card_type, mk_fintype]

theorem type_fin (n : ℕ) : @type (Finₓ n) (· < ·) _ = n := by
  simp

end Ordinal

