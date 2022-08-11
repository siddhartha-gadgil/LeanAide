/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Yury G. Kudryashov
-/
import Mathbin.Data.Option.Basic

/-!
# Disjoint union of types

This file proves basic results about the sum type `α ⊕ β`.

`α ⊕ β` is the type made of a copy of `α` and a copy of `β`. It is also called *disjoint union*.

## Main declarations

* `sum.get_left`: Retrieves the left content of `x : α ⊕ β` or returns `none` if it's coming from
  the right.
* `sum.get_right`: Retrieves the right content of `x : α ⊕ β` or returns `none` if it's coming from
  the left.
* `sum.is_left`: Returns whether `x : α ⊕ β` comes from the left component or not.
* `sum.is_right`: Returns whether `x : α ⊕ β` comes from the right component or not.
* `sum.map`: Maps `α ⊕ β` to `γ ⊕ δ` component-wise.
* `sum.elim`: Nondependent eliminator/induction principle for `α ⊕ β`.
* `sum.swap`: Maps `α ⊕ β` to `β ⊕ α` by swapping components.
* `sum.lex`: Lexicographic order on `α ⊕ β` induced by a relation on `α` and a relation on `β`.

## Notes

The definition of `sum` takes values in `Type*`. This effectively forbids `Prop`- valued sum types.
To this effect, we have `psum`, which takes value in `Sort*` and carries a more complicated
universe signature in consequence. The `Prop` version is `or`.
-/


universe u v w x

variable {α : Type u} {α' : Type w} {β : Type v} {β' : Type x} {γ δ : Type _}

namespace Sum

deriving instance DecidableEq for Sum

@[simp]
theorem forall {p : Sum α β → Prop} : (∀ x, p x) ↔ (∀ a, p (inl a)) ∧ ∀ b, p (inr b) :=
  ⟨fun h => ⟨fun a => h _, fun b => h _⟩, fun ⟨h₁, h₂⟩ => Sum.rec h₁ h₂⟩

@[simp]
theorem exists {p : Sum α β → Prop} : (∃ x, p x) ↔ (∃ a, p (inl a)) ∨ ∃ b, p (inr b) :=
  ⟨fun h =>
    match h with
    | ⟨inl a, h⟩ => Or.inl ⟨a, h⟩
    | ⟨inr b, h⟩ => Or.inr ⟨b, h⟩,
    fun h =>
    match h with
    | Or.inl ⟨a, h⟩ => ⟨inl a, h⟩
    | Or.inr ⟨b, h⟩ => ⟨inr b, h⟩⟩

theorem inl_injective : Function.Injective (inl : α → Sum α β) := fun x y => inl.injₓ

theorem inr_injective : Function.Injective (inr : β → Sum α β) := fun x y => inr.injₓ

section get

/-- Check if a sum is `inl` and if so, retrieve its contents. -/
@[simp]
def getLeft : Sum α β → Option α
  | inl a => some a
  | inr _ => none

/-- Check if a sum is `inr` and if so, retrieve its contents. -/
@[simp]
def getRight : Sum α β → Option β
  | inr b => some b
  | inl _ => none

/-- Check if a sum is `inl`. -/
@[simp]
def isLeft : Sum α β → Bool
  | inl _ => true
  | inr _ => false

/-- Check if a sum is `inr`. -/
@[simp]
def isRight : Sum α β → Bool
  | inl _ => false
  | inr _ => true

variable {x y : Sum α β}

theorem get_left_eq_none_iff : x.getLeft = none ↔ x.isRight := by
  cases x <;> simp only [← get_left, ← is_right, ← coe_sort_tt, ← coe_sort_ff, ← eq_self_iff_true]

theorem get_right_eq_none_iff : x.getRight = none ↔ x.isLeft := by
  cases x <;> simp only [← get_right, ← is_left, ← coe_sort_tt, ← coe_sort_ff, ← eq_self_iff_true]

end get

theorem inl.inj_iff {a b} : (inl a : Sum α β) = inl b ↔ a = b :=
  ⟨inl.injₓ, congr_arg _⟩

theorem inr.inj_iff {a b} : (inr a : Sum α β) = inr b ↔ a = b :=
  ⟨inr.injₓ, congr_arg _⟩

theorem inl_ne_inr {a : α} {b : β} : inl a ≠ inr b :=
  fun.

theorem inr_ne_inl {a : α} {b : β} : inr b ≠ inl a :=
  fun.

/-- Define a function on `α ⊕ β` by giving separate definitions on `α` and `β`. -/
protected def elim {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum α β → γ := fun x => Sum.recOn x f g

@[simp]
theorem elim_inl {α β γ : Sort _} (f : α → γ) (g : β → γ) (x : α) : Sum.elim f g (inl x) = f x :=
  rfl

@[simp]
theorem elim_inr {α β γ : Sort _} (f : α → γ) (g : β → γ) (x : β) : Sum.elim f g (inr x) = g x :=
  rfl

@[simp]
theorem elim_comp_inl {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum.elim f g ∘ inl = f :=
  rfl

@[simp]
theorem elim_comp_inr {α β γ : Sort _} (f : α → γ) (g : β → γ) : Sum.elim f g ∘ inr = g :=
  rfl

@[simp]
theorem elim_inl_inr {α β : Sort _} : @Sum.elim α β _ inl inr = id :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl

theorem comp_elim {α β γ δ : Sort _} (f : γ → δ) (g : α → γ) (h : β → γ) :
    f ∘ Sum.elim g h = Sum.elim (f ∘ g) (f ∘ h) :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl

@[simp]
theorem elim_comp_inl_inr {α β γ : Sort _} (f : Sum α β → γ) : Sum.elim (f ∘ inl) (f ∘ inr) = f :=
  funext fun x => Sum.casesOn x (fun _ => rfl) fun _ => rfl

/-- Map `α ⊕ β` to `α' ⊕ β'` sending `α` to `α'` and `β` to `β'`. -/
protected def map (f : α → α') (g : β → β') : Sum α β → Sum α' β' :=
  Sum.elim (inl ∘ f) (inr ∘ g)

@[simp]
theorem map_inl (f : α → α') (g : β → β') (x : α) : (inl x).map f g = inl (f x) :=
  rfl

@[simp]
theorem map_inr (f : α → α') (g : β → β') (x : β) : (inr x).map f g = inr (g x) :=
  rfl

@[simp]
theorem map_map {α'' β''} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
    ∀ x : Sum α β, (x.map f g).map f' g' = x.map (f' ∘ f) (g' ∘ g)
  | inl a => rfl
  | inr b => rfl

@[simp]
theorem map_comp_map {α'' β''} (f' : α' → α'') (g' : β' → β'') (f : α → α') (g : β → β') :
    Sum.map f' g' ∘ Sum.map f g = Sum.map (f' ∘ f) (g' ∘ g) :=
  funext <| map_map f' g' f g

@[simp]
theorem map_id_id (α β) : Sum.map (@id α) (@id β) = id :=
  funext fun x => Sum.recOn x (fun _ => rfl) fun _ => rfl

theorem elim_comp_map {α β γ δ ε : Sort _} {f₁ : α → β} {f₂ : β → ε} {g₁ : γ → δ} {g₂ : δ → ε} :
    Sum.elim f₂ g₂ ∘ Sum.map f₁ g₁ = Sum.elim (f₂ ∘ f₁) (g₂ ∘ g₁) := by
  ext (_ | _) <;> rfl

open Function (update update_eq_iff update_comp_eq_of_injective update_comp_eq_of_forall_ne)

@[simp]
theorem update_elim_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : α → γ} {g : β → γ} {i : α} {x : γ} :
    update (Sum.elim f g) (inl i) x = Sum.elim (update f i x) g :=
  update_eq_iff.2
    ⟨by
      simp , by
      simp (config := { contextual := true })⟩

@[simp]
theorem update_elim_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : α → γ} {g : β → γ} {i : β} {x : γ} :
    update (Sum.elim f g) (inr i) x = Sum.elim f (update g i x) :=
  update_eq_iff.2
    ⟨by
      simp , by
      simp (config := { contextual := true })⟩

@[simp]
theorem update_inl_comp_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {x : γ} :
    update f (inl i) x ∘ inl = update (f ∘ inl) i x :=
  update_comp_eq_of_injective _ inl_injective _ _

@[simp]
theorem update_inl_apply_inl [DecidableEq α] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i j : α} {x : γ} :
    update f (inl i) x (inl j) = update (f ∘ inl) i x j := by
  rw [← update_inl_comp_inl]

@[simp]
theorem update_inl_comp_inr [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {x : γ} :
    update f (inl i) x ∘ inr = f ∘ inr :=
  (update_comp_eq_of_forall_ne _ _) fun _ => inr_ne_inl

@[simp]
theorem update_inl_apply_inr [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {j : β} {x : γ} :
    update f (inl i) x (inr j) = f (inr j) :=
  Function.update_noteq inr_ne_inl _ _

@[simp]
theorem update_inr_comp_inl [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : β} {x : γ} :
    update f (inr i) x ∘ inl = f ∘ inl :=
  (update_comp_eq_of_forall_ne _ _) fun _ => inl_ne_inr

@[simp]
theorem update_inr_apply_inl [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : α} {j : β} {x : γ} :
    update f (inr j) x (inl i) = f (inl i) :=
  Function.update_noteq inl_ne_inr _ _

@[simp]
theorem update_inr_comp_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i : β} {x : γ} :
    update f (inr i) x ∘ inr = update (f ∘ inr) i x :=
  update_comp_eq_of_injective _ inr_injective _ _

@[simp]
theorem update_inr_apply_inr [DecidableEq β] [DecidableEq (Sum α β)] {f : Sum α β → γ} {i j : β} {x : γ} :
    update f (inr i) x (inr j) = update (f ∘ inr) i x j := by
  rw [← update_inr_comp_inr]

/-- Swap the factors of a sum type -/
def swap : Sum α β → Sum β α :=
  Sum.elim inr inl

@[simp]
theorem swap_inl (x : α) : swap (inl x : Sum α β) = inr x :=
  rfl

@[simp]
theorem swap_inr (x : β) : swap (inr x : Sum α β) = inl x :=
  rfl

@[simp]
theorem swap_swap (x : Sum α β) : swap (swap x) = x := by
  cases x <;> rfl

@[simp]
theorem swap_swap_eq : swap ∘ swap = @id (Sum α β) :=
  funext <| swap_swap

@[simp]
theorem swap_left_inverse : Function.LeftInverse (@swap α β) swap :=
  swap_swap

@[simp]
theorem swap_right_inverse : Function.RightInverse (@swap α β) swap :=
  swap_swap

section LiftRel

/-- Lifts pointwise two relations between `α` and `γ` and between `β` and `δ` to a relation between
`α ⊕ β` and `γ ⊕ δ`. -/
inductive LiftRel (r : α → γ → Prop) (s : β → δ → Prop) : Sum α β → Sum γ δ → Prop
  | inl {a c} : r a c → lift_rel (inl a) (inl c)
  | inr {b d} : s b d → lift_rel (inr b) (inr d)

attribute [protected] lift_rel.inl lift_rel.inr

variable {r r₁ r₂ : α → γ → Prop} {s s₁ s₂ : β → δ → Prop} {a : α} {b : β} {c : γ} {d : δ} {x : Sum α β} {y : Sum γ δ}

@[simp]
theorem lift_rel_inl_inl : LiftRel r s (inl a) (inl c) ↔ r a c :=
  ⟨fun h => by
    cases h
    assumption, LiftRel.inl⟩

@[simp]
theorem not_lift_rel_inl_inr : ¬LiftRel r s (inl a) (inr d) :=
  fun.

@[simp]
theorem not_lift_rel_inr_inl : ¬LiftRel r s (inr b) (inl c) :=
  fun.

@[simp]
theorem lift_rel_inr_inr : LiftRel r s (inr b) (inr d) ↔ s b d :=
  ⟨fun h => by
    cases h
    assumption, LiftRel.inr⟩

instance [∀ a c, Decidable (r a c)] [∀ b d, Decidable (s b d)] :
    ∀ (ab : Sum α β) (cd : Sum γ δ), Decidable (LiftRel r s ab cd)
  | inl a, inl c => decidableOfIff' _ lift_rel_inl_inl
  | inl a, inr d => Decidable.isFalse not_lift_rel_inl_inr
  | inr b, inl c => Decidable.isFalse not_lift_rel_inr_inl
  | inr b, inr d => decidableOfIff' _ lift_rel_inr_inr

theorem LiftRel.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b) (h : LiftRel r₁ s₁ x y) :
    LiftRel r₂ s₂ x y := by
  cases h
  exacts[lift_rel.inl (hr _ _ ‹_›), lift_rel.inr (hs _ _ ‹_›)]

theorem LiftRel.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : LiftRel r₁ s x y) : LiftRel r₂ s x y :=
  (h.mono hr) fun _ _ => id

theorem LiftRel.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : LiftRel r s₁ x y) : LiftRel r s₂ x y :=
  h.mono (fun _ _ => id) hs

protected theorem LiftRel.swap (h : LiftRel r s x y) : LiftRel s r x.swap y.swap := by
  cases h
  exacts[lift_rel.inr ‹_›, lift_rel.inl ‹_›]

@[simp]
theorem lift_rel_swap_iff : LiftRel s r x.swap y.swap ↔ LiftRel r s x y :=
  ⟨fun h => by
    rw [← swap_swap x, ← swap_swap y]
    exact h.swap, LiftRel.swap⟩

end LiftRel

section Lex

/-- Lexicographic order for sum. Sort all the `inl a` before the `inr b`, otherwise use the
respective order on `α` or `β`. -/
inductive Lex (r : α → α → Prop) (s : β → β → Prop) : Sum α β → Sum α β → Prop
  | inl {a₁ a₂} (h : r a₁ a₂) : lex (inl a₁) (inl a₂)
  | inr {b₁ b₂} (h : s b₁ b₂) : lex (inr b₁) (inr b₂)
  | sep (a b) : lex (inl a) (inr b)

attribute [protected] Sum.Lex.inl Sum.Lex.inr

attribute [simp] lex.sep

variable {r r₁ r₂ : α → α → Prop} {s s₁ s₂ : β → β → Prop} {a a₁ a₂ : α} {b b₁ b₂ : β} {x y : Sum α β}

@[simp]
theorem lex_inl_inl : Lex r s (inl a₁) (inl a₂) ↔ r a₁ a₂ :=
  ⟨fun h => by
    cases h
    assumption, Lex.inl⟩

@[simp]
theorem lex_inr_inr : Lex r s (inr b₁) (inr b₂) ↔ s b₁ b₂ :=
  ⟨fun h => by
    cases h
    assumption, Lex.inr⟩

@[simp]
theorem lex_inr_inl : ¬Lex r s (inr b) (inl a) :=
  fun.

instance [DecidableRel r] [DecidableRel s] : DecidableRel (Lex r s)
  | inl a, inl c => decidableOfIff' _ lex_inl_inl
  | inl a, inr d => Decidable.isTrue (Lex.sep _ _)
  | inr b, inl c => Decidable.isFalse lex_inr_inl
  | inr b, inr d => decidableOfIff' _ lex_inr_inr

protected theorem LiftRel.lex {a b : Sum α β} (h : LiftRel r s a b) : Lex r s a b := by
  cases h
  exacts[lex.inl ‹_›, lex.inr ‹_›]

theorem lift_rel_subrelation_lex : Subrelation (LiftRel r s) (Lex r s) := fun a b => LiftRel.lex

theorem Lex.mono (hr : ∀ a b, r₁ a b → r₂ a b) (hs : ∀ a b, s₁ a b → s₂ a b) (h : Lex r₁ s₁ x y) : Lex r₂ s₂ x y := by
  cases h
  exacts[lex.inl (hr _ _ ‹_›), lex.inr (hs _ _ ‹_›), lex.sep _ _]

theorem Lex.mono_left (hr : ∀ a b, r₁ a b → r₂ a b) (h : Lex r₁ s x y) : Lex r₂ s x y :=
  (h.mono hr) fun _ _ => id

theorem Lex.mono_right (hs : ∀ a b, s₁ a b → s₂ a b) (h : Lex r s₁ x y) : Lex r s₂ x y :=
  h.mono (fun _ _ => id) hs

theorem lex_acc_inl {a} (aca : Acc r a) : Acc (Lex r s) (inl a) := by
  induction' aca with a H IH
  constructor
  intro y h
  cases' h with a' _ h'
  exact IH _ h'

theorem lex_acc_inr (aca : ∀ a, Acc (Lex r s) (inl a)) {b} (acb : Acc s b) : Acc (Lex r s) (inr b) := by
  induction' acb with b H IH
  constructor
  intro y h
  cases' h with _ _ _ b' _ h' a
  · exact IH _ h'
    
  · exact aca _
    

theorem lex_wf (ha : WellFounded r) (hb : WellFounded s) : WellFounded (Lex r s) :=
  have aca : ∀ a, Acc (Lex r s) (inl a) := fun a => lex_acc_inl (ha.apply a)
  ⟨fun x => Sum.recOn x aca fun b => lex_acc_inr aca (hb.apply b)⟩

end Lex

end Sum

open Sum

namespace Function

theorem Injective.sum_elim {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g) (hfg : ∀ a b, f a ≠ g b) :
    Injective (Sum.elim f g)
  | inl x, inl y, h => congr_arg inl <| hf h
  | inl x, inr y, h => (hfg x y h).elim
  | inr x, inl y, h => (hfg y x h.symm).elim
  | inr x, inr y, h => congr_arg inr <| hg h

theorem Injective.sum_map {f : α → β} {g : α' → β'} (hf : Injective f) (hg : Injective g) : Injective (Sum.map f g)
  | inl x, inl y, h => congr_arg inl <| hf <| inl.injₓ h
  | inr x, inr y, h => congr_arg inr <| hg <| inr.injₓ h

theorem Surjective.sum_map {f : α → β} {g : α' → β'} (hf : Surjective f) (hg : Surjective g) : Surjective (Sum.map f g)
  | inl y =>
    let ⟨x, hx⟩ := hf y
    ⟨inl x, congr_arg inl hx⟩
  | inr y =>
    let ⟨x, hx⟩ := hg y
    ⟨inr x, congr_arg inr hx⟩

end Function

/-!
### Ternary sum

Abbreviations for the maps from the summands to `α ⊕ β ⊕ γ`. This is useful for pattern-matching.
-/


namespace Sum3

/-- The map from the first summand into a ternary sum. -/
@[matchPattern, simp, reducible]
def in₀ (a) : Sum α (Sum β γ) :=
  inl a

/-- The map from the second summand into a ternary sum. -/
@[matchPattern, simp, reducible]
def in₁ (b) : Sum α (Sum β γ) :=
  inr <| inl b

/-- The map from the third summand into a ternary sum. -/
@[matchPattern, simp, reducible]
def in₂ (c) : Sum α (Sum β γ) :=
  inr <| inr c

end Sum3

