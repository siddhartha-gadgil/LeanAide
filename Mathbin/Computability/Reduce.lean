/-
Copyright (c) 2019 Minchao Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Minchao Wu, Mario Carneiro
-/
import Mathbin.Computability.Halting

/-!
# Strong reducibility and degrees.

This file defines the notions of computable many-one reduction and one-one
reduction between sets, and shows that the corresponding degrees form a
semilattice.

## Notations

This file uses the local notation `⊕'` for `sum.elim` to denote the disjoint union of two degrees.

## References

* [Robert Soare, *Recursively enumerable sets and degrees*][soare1987]

## Tags

computability, reducibility, reduction
-/


universe u v w

open Function

/-- `p` is many-one reducible to `q` if there is a computable function translating questions about `p`
to questions about `q`.
-/
def ManyOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ ∀ a, p a ↔ q (f a)

-- mathport name: «expr ≤₀ »
infixl:1000 " ≤₀ " => ManyOneReducible

theorem ManyOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop) (h : Computable f) :
    (fun a => q (f a)) ≤₀ q :=
  ⟨f, h, fun a => Iff.rfl⟩

@[refl]
theorem many_one_reducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₀ p :=
  ⟨id, Computable.id, by
    simp ⟩

@[trans]
theorem ManyOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} : p ≤₀ q → q ≤₀ r → p ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, fun a =>
      ⟨fun h => by
        rwa [← h₂, ← h₁], fun h => by
        rwa [h₁, h₂]⟩⟩

theorem reflexive_many_one_reducible {α} [Primcodable α] : Reflexive (@ManyOneReducible α α _ _) :=
  many_one_reducible_refl

theorem transitive_many_one_reducible {α} [Primcodable α] : Transitive (@ManyOneReducible α α _ _) := fun p q r =>
  ManyOneReducible.trans

/-- `p` is one-one reducible to `q` if there is an injective computable function translating questions
about `p` to questions about `q`.
-/
def OneOneReducible {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  ∃ f, Computable f ∧ Injective f ∧ ∀ a, p a ↔ q (f a)

-- mathport name: «expr ≤₁ »
infixl:1000 " ≤₁ " => OneOneReducible

theorem OneOneReducible.mk {α β} [Primcodable α] [Primcodable β] {f : α → β} (q : β → Prop) (h : Computable f)
    (i : Injective f) : (fun a => q (f a)) ≤₁ q :=
  ⟨f, h, i, fun a => Iff.rfl⟩

@[refl]
theorem one_one_reducible_refl {α} [Primcodable α] (p : α → Prop) : p ≤₁ p :=
  ⟨id, Computable.id, injective_id, by
    simp ⟩

@[trans]
theorem OneOneReducible.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} : p ≤₁ q → q ≤₁ r → p ≤₁ r
  | ⟨f, c₁, i₁, h₁⟩, ⟨g, c₂, i₂, h₂⟩ =>
    ⟨g ∘ f, c₂.comp c₁, i₂.comp i₁, fun a =>
      ⟨fun h => by
        rwa [← h₂, ← h₁], fun h => by
        rwa [h₁, h₂]⟩⟩

theorem OneOneReducible.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    p ≤₁ q → p ≤₀ q
  | ⟨f, c, i, h⟩ => ⟨f, c, h⟩

theorem OneOneReducible.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β → Prop) (h : Computable e) :
    (q ∘ e) ≤₁ q :=
  OneOneReducible.mk _ h e.Injective

theorem OneOneReducible.of_equiv_symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (q : β → Prop)
    (h : Computable e.symm) : q ≤₁ (q ∘ e) := by
  convert OneOneReducible.of_equiv _ h <;> funext <;> simp

theorem reflexive_one_one_reducible {α} [Primcodable α] : Reflexive (@OneOneReducible α α _ _) :=
  one_one_reducible_refl

theorem transitive_one_one_reducible {α} [Primcodable α] : Transitive (@OneOneReducible α α _ _) := fun p q r =>
  OneOneReducible.trans

namespace ComputablePred

variable {α : Type _} {β : Type _} {σ : Type _}

variable [Primcodable α] [Primcodable β] [Primcodable σ]

open Computable

theorem computable_of_many_one_reducible {p : α → Prop} {q : β → Prop} (h₁ : p ≤₀ q) (h₂ : ComputablePred q) :
    ComputablePred p := by
  rcases h₁ with ⟨f, c, hf⟩
  rw [show p = fun a => q (f a) from Set.ext hf]
  rcases computable_iff.1 h₂ with ⟨g, hg, rfl⟩
  exact
    ⟨by
      infer_instance, by
      simpa using hg.comp c⟩

theorem computable_of_one_one_reducible {p : α → Prop} {q : β → Prop} (h : p ≤₁ q) :
    ComputablePred q → ComputablePred p :=
  computable_of_many_one_reducible h.to_many_one

end ComputablePred

/-- `p` and `q` are many-one equivalent if each one is many-one reducible to the other. -/
def ManyOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₀ q ∧ q ≤₀ p

/-- `p` and `q` are one-one equivalent if each one is one-one reducible to the other. -/
def OneOneEquiv {α β} [Primcodable α] [Primcodable β] (p : α → Prop) (q : β → Prop) :=
  p ≤₁ q ∧ q ≤₁ p

@[refl]
theorem many_one_equiv_refl {α} [Primcodable α] (p : α → Prop) : ManyOneEquiv p p :=
  ⟨many_one_reducible_refl _, many_one_reducible_refl _⟩

@[symm]
theorem ManyOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    ManyOneEquiv p q → ManyOneEquiv q p :=
  And.swap

@[trans]
theorem ManyOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} : ManyOneEquiv p q → ManyOneEquiv q r → ManyOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩

theorem equivalence_of_many_one_equiv {α} [Primcodable α] : Equivalenceₓ (@ManyOneEquiv α α _ _) :=
  ⟨many_one_equiv_refl, fun x y => ManyOneEquiv.symm, fun x y z => ManyOneEquiv.trans⟩

@[refl]
theorem one_one_equiv_refl {α} [Primcodable α] (p : α → Prop) : OneOneEquiv p p :=
  ⟨one_one_reducible_refl _, one_one_reducible_refl _⟩

@[symm]
theorem OneOneEquiv.symm {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    OneOneEquiv p q → OneOneEquiv q p :=
  And.swap

@[trans]
theorem OneOneEquiv.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} : OneOneEquiv p q → OneOneEquiv q r → OneOneEquiv p r
  | ⟨pq, qp⟩, ⟨qr, rq⟩ => ⟨pq.trans qr, rq.trans qp⟩

theorem equivalence_of_one_one_equiv {α} [Primcodable α] : Equivalenceₓ (@OneOneEquiv α α _ _) :=
  ⟨one_one_equiv_refl, fun x y => OneOneEquiv.symm, fun x y z => OneOneEquiv.trans⟩

theorem OneOneEquiv.to_many_one {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    OneOneEquiv p q → ManyOneEquiv p q
  | ⟨pq, qp⟩ => ⟨pq.to_many_one, qp.to_many_one⟩

/-- a computable bijection -/
def Equivₓ.Computable {α β} [Primcodable α] [Primcodable β] (e : α ≃ β) :=
  Computable e ∧ Computable e.symm

theorem Equivₓ.Computable.symm {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} : e.Computable → e.symm.Computable :=
  And.swap

theorem Equivₓ.Computable.trans {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {e₁ : α ≃ β} {e₂ : β ≃ γ} :
    e₁.Computable → e₂.Computable → (e₁.trans e₂).Computable
  | ⟨l₁, r₁⟩, ⟨l₂, r₂⟩ => ⟨l₂.comp l₁, r₁.comp r₂⟩

theorem Computable.eqv (α) [Denumerable α] : (Denumerable.eqv α).Computable :=
  ⟨Computable.encode, Computable.of_nat _⟩

theorem Computable.equiv₂ (α β) [Denumerable α] [Denumerable β] : (Denumerable.equiv₂ α β).Computable :=
  (Computable.eqv _).trans (Computable.eqv _).symm

theorem OneOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable) {p} :
    OneOneEquiv (p ∘ e) p :=
  ⟨OneOneReducible.of_equiv _ h.1, OneOneReducible.of_equiv_symm _ h.2⟩

theorem ManyOneEquiv.of_equiv {α β} [Primcodable α] [Primcodable β] {e : α ≃ β} (h : e.Computable) {p} :
    ManyOneEquiv (p ∘ e) p :=
  (OneOneEquiv.of_equiv h).to_many_one

theorem ManyOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} (h : ManyOneEquiv p q) : p ≤₀ r ↔ q ≤₀ r :=
  ⟨h.2.trans, h.1.trans⟩

theorem ManyOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop}
    {q : β → Prop} {r : γ → Prop} (h : ManyOneEquiv q r) : p ≤₀ q ↔ p ≤₀ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩

theorem OneOneEquiv.le_congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} (h : OneOneEquiv p q) : p ≤₁ r ↔ q ≤₁ r :=
  ⟨h.2.trans, h.1.trans⟩

theorem OneOneEquiv.le_congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} (h : OneOneEquiv q r) : p ≤₁ q ↔ p ≤₁ r :=
  ⟨fun h' => h'.trans h.1, fun h' => h'.trans h.2⟩

theorem ManyOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} (h : ManyOneEquiv p q) : ManyOneEquiv p r ↔ ManyOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right

theorem ManyOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} (h : ManyOneEquiv q r) : ManyOneEquiv p q ↔ ManyOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left

theorem OneOneEquiv.congr_left {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} (h : OneOneEquiv p q) : OneOneEquiv p r ↔ OneOneEquiv q r :=
  and_congr h.le_congr_left h.le_congr_right

theorem OneOneEquiv.congr_right {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} (h : OneOneEquiv q r) : OneOneEquiv p q ↔ OneOneEquiv p r :=
  and_congr h.le_congr_right h.le_congr_left

@[simp]
theorem Ulower.down_computable {α} [Primcodable α] : (Ulower.equiv α).Computable :=
  ⟨Primrec.ulower_down.to_comp, Primrec.ulower_up.to_comp⟩

theorem many_one_equiv_up {α} [Primcodable α] {p : α → Prop} : ManyOneEquiv (p ∘ Ulower.up) p :=
  ManyOneEquiv.of_equiv Ulower.down_computable.symm

-- mathport name: «expr ⊕' »
local infixl:1001 " ⊕' " => Sum.elim

open Nat.Primrec

theorem OneOneReducible.disjoin_left {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    p ≤₁ p ⊕' q :=
  ⟨Sum.inl, Computable.sum_inl, fun x y => Sum.inl.inj_iff.1, fun a => Iff.rfl⟩

theorem OneOneReducible.disjoin_right {α β} [Primcodable α] [Primcodable β] {p : α → Prop} {q : β → Prop} :
    q ≤₁ p ⊕' q :=
  ⟨Sum.inr, Computable.sum_inr, fun x y => Sum.inr.inj_iff.1, fun a => Iff.rfl⟩

theorem disjoin_many_one_reducible {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} : p ≤₀ r → q ≤₀ r → p ⊕' q ≤₀ r
  | ⟨f, c₁, h₁⟩, ⟨g, c₂, h₂⟩ =>
    ⟨Sum.elim f g, Computable.id.sum_cases (c₁.comp Computable.snd).to₂ (c₂.comp Computable.snd).to₂, fun x => by
      cases x <;> [apply h₁, apply h₂]⟩

theorem disjoin_le {α β γ} [Primcodable α] [Primcodable β] [Primcodable γ] {p : α → Prop} {q : β → Prop}
    {r : γ → Prop} : p ⊕' q ≤₀ r ↔ p ≤₀ r ∧ q ≤₀ r :=
  ⟨fun h => ⟨OneOneReducible.disjoin_left.to_many_one.trans h, OneOneReducible.disjoin_right.to_many_one.trans h⟩,
    fun ⟨h₁, h₂⟩ => disjoin_many_one_reducible h₁ h₂⟩

variable {α : Type u} [Primcodable α] [Inhabited α]

variable {β : Type v} [Primcodable β] [Inhabited β]

variable {γ : Type w} [Primcodable γ] [Inhabited γ]

/-- Computable and injective mapping of predicates to sets of natural numbers.
-/
def ToNat (p : Set α) : Set ℕ :=
  { n | p ((Encodable.decode α n).getOrElse default) }

@[simp]
theorem to_nat_many_one_reducible {p : Set α} : ToNat p ≤₀ p :=
  ⟨fun n => (Encodable.decode α n).getOrElse default,
    Computable.option_get_or_else Computable.decode (Computable.const _), fun _ => Iff.rfl⟩

@[simp]
theorem many_one_reducible_to_nat {p : Set α} : p ≤₀ ToNat p :=
  ⟨Encodable.encode, Computable.encode, by
    simp [← ToNat, ← SetOf]⟩

@[simp]
theorem many_one_reducible_to_nat_to_nat {p : Set α} {q : Set β} : ToNat p ≤₀ ToNat q ↔ p ≤₀ q :=
  ⟨fun h => many_one_reducible_to_nat.trans (h.trans to_nat_many_one_reducible), fun h =>
    to_nat_many_one_reducible.trans (h.trans many_one_reducible_to_nat)⟩

@[simp]
theorem to_nat_many_one_equiv {p : Set α} : ManyOneEquiv (ToNat p) p := by
  simp [← ManyOneEquiv]

@[simp]
theorem many_one_equiv_to_nat (p : Set α) (q : Set β) : ManyOneEquiv (ToNat p) (ToNat q) ↔ ManyOneEquiv p q := by
  simp [← ManyOneEquiv]

/-- A many-one degree is an equivalence class of sets up to many-one equivalence. -/
def ManyOneDegree : Type :=
  Quotientₓ (⟨ManyOneEquiv, equivalence_of_many_one_equiv⟩ : Setoidₓ (Set ℕ))

namespace ManyOneDegree

/-- The many-one degree of a set on a primcodable type. -/
def of (p : α → Prop) : ManyOneDegree :=
  Quotientₓ.mk' (ToNat p)

@[elab_as_eliminator]
protected theorem ind_on {C : ManyOneDegree → Prop} (d : ManyOneDegree) (h : ∀ p : Set ℕ, C (of p)) : C d :=
  Quotientₓ.induction_on' d h

/-- Lifts a function on sets of natural numbers to many-one degrees.
-/
@[elab_as_eliminator, reducible]
protected def liftOn {φ} (d : ManyOneDegree) (f : Set ℕ → φ) (h : ∀ p q, ManyOneEquiv p q → f p = f q) : φ :=
  Quotientₓ.liftOn' d f h

@[simp]
protected theorem lift_on_eq {φ} (p : Set ℕ) (f : Set ℕ → φ) (h : ∀ p q, ManyOneEquiv p q → f p = f q) :
    (of p).liftOn f h = f p :=
  rfl

/-- Lifts a binary function on sets of natural numbers to many-one degrees.
-/
@[elab_as_eliminator, reducible, simp]
protected def liftOn₂ {φ} (d₁ d₂ : ManyOneDegree) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) : φ :=
  d₁.liftOn
    (fun p =>
      d₂.liftOn (f p) fun q₁ q₂ hq =>
        h _ _ _ _
          (by
            rfl)
          hq)
    (by
      intro p₁ p₂ hp
      induction d₂ using ManyOneDegree.ind_on
      apply h
      assumption
      rfl)

@[simp]
protected theorem lift_on₂_eq {φ} (p q : Set ℕ) (f : Set ℕ → Set ℕ → φ)
    (h : ∀ p₁ p₂ q₁ q₂, ManyOneEquiv p₁ p₂ → ManyOneEquiv q₁ q₂ → f p₁ q₁ = f p₂ q₂) :
    (of p).liftOn₂ (of q) f h = f p q :=
  rfl

@[simp]
theorem of_eq_of {p : α → Prop} {q : β → Prop} : of p = of q ↔ ManyOneEquiv p q := by
  simp [← of, ← Quotientₓ.eq']

instance : Inhabited ManyOneDegree :=
  ⟨of (∅ : Set ℕ)⟩

/-- For many-one degrees `d₁` and `d₂`, `d₁ ≤ d₂` if the sets in `d₁` are many-one reducible to the
sets in `d₂`.
-/
instance : LE ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    (ManyOneDegree.liftOn₂ d₁ d₂ (· ≤₀ ·)) fun p₁ p₂ q₁ q₂ hp hq => propext (hp.le_congr_left.trans hq.le_congr_right)⟩

@[simp]
theorem of_le_of {p : α → Prop} {q : β → Prop} : of p ≤ of q ↔ p ≤₀ q :=
  many_one_reducible_to_nat_to_nat

private theorem le_refl (d : ManyOneDegree) : d ≤ d := by
  induction d using ManyOneDegree.ind_on <;> simp

private theorem le_antisymm {d₁ d₂ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₁ → d₁ = d₂ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  intro hp hq
  simp_all only [← ManyOneEquiv, ← of_le_of, ← of_eq_of, ← true_andₓ]

private theorem le_trans {d₁ d₂ d₃ : ManyOneDegree} : d₁ ≤ d₂ → d₂ ≤ d₃ → d₁ ≤ d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  apply ManyOneReducible.trans

instance : PartialOrderₓ ManyOneDegree where
  le := (· ≤ ·)
  le_refl := le_reflₓ
  le_trans := fun _ _ _ => le_transₓ
  le_antisymm := fun _ _ => le_antisymmₓ

/-- The join of two degrees, induced by the disjoint union of two underlying sets. -/
instance : Add ManyOneDegree :=
  ⟨fun d₁ d₂ =>
    d₁.liftOn₂ d₂ (fun a b => of (a ⊕' b))
      (by
        rintro a b c d ⟨hl₁, hr₁⟩ ⟨hl₂, hr₂⟩
        rw [of_eq_of]
        exact
          ⟨disjoin_many_one_reducible (hl₁.trans one_one_reducible.disjoin_left.to_many_one)
              (hl₂.trans one_one_reducible.disjoin_right.to_many_one),
            disjoin_many_one_reducible (hr₁.trans one_one_reducible.disjoin_left.to_many_one)
              (hr₂.trans one_one_reducible.disjoin_right.to_many_one)⟩)⟩

@[simp]
theorem add_of (p : Set α) (q : Set β) : of (p ⊕' q) = of p + of q :=
  of_eq_of.mpr
    ⟨disjoin_many_one_reducible (many_one_reducible_to_nat.trans OneOneReducible.disjoin_left.to_many_one)
        (many_one_reducible_to_nat.trans OneOneReducible.disjoin_right.to_many_one),
      disjoin_many_one_reducible (to_nat_many_one_reducible.trans OneOneReducible.disjoin_left.to_many_one)
        (to_nat_many_one_reducible.trans OneOneReducible.disjoin_right.to_many_one)⟩

@[simp]
protected theorem add_le {d₁ d₂ d₃ : ManyOneDegree} : d₁ + d₂ ≤ d₃ ↔ d₁ ≤ d₃ ∧ d₂ ≤ d₃ := by
  induction d₁ using ManyOneDegree.ind_on
  induction d₂ using ManyOneDegree.ind_on
  induction d₃ using ManyOneDegree.ind_on
  simpa only [add_of, ← of_le_of] using disjoin_le

@[simp]
protected theorem le_add_left (d₁ d₂ : ManyOneDegree) : d₁ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1
      (by
        rfl)).1

@[simp]
protected theorem le_add_right (d₁ d₂ : ManyOneDegree) : d₂ ≤ d₁ + d₂ :=
  (ManyOneDegree.add_le.1
      (by
        rfl)).2

instance : SemilatticeSup ManyOneDegree :=
  { ManyOneDegree.partialOrder with sup := (· + ·), le_sup_left := ManyOneDegree.le_add_left,
    le_sup_right := ManyOneDegree.le_add_right, sup_le := fun a b c h₁ h₂ => ManyOneDegree.add_le.2 ⟨h₁, h₂⟩ }

end ManyOneDegree

